(* *********************************************************************)
(*                                                                     *)
(*              The CompCert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Interfaces at the boundary of the verified linker. A function body
    is represented by its calling signature. Global variable metadata
    specific to an intermediate language is erased. *)
Require Import Coqlib Maps AST Linking.
Require Ctypes.

Definition definition_interface {F V} (f: F -> fundef signature)
    (d: globdef F V): globdef (fundef signature) unit :=
  match d with
  | Gfun fd => Gfun (f fd)
  | Gvar v => Gvar (mkglobvar tt v.(gvar_init) v.(gvar_readonly) v.(gvar_volatile))
  end.

Definition fundef_interface {F} (sig_of: F -> signature) (fd: fundef F) : fundef signature :=
  match fd with
  | Internal f => Internal (sig_of f)
  | External ef => External ef
  end.

Definition c_fundef_interface {F} (sig_of: F -> signature) (fd: Ctypes.fundef F) : fundef signature :=
  match fd with
  | Ctypes.Internal f => Internal (sig_of f)
  | Ctypes.External ef _ _ _ => External ef
  end.

Definition public_defined {F V} (p: program F V) : Prop :=
  forall id, In id p.(prog_public) -> id <> p.(prog_main) ->
  (prog_defmap p)!id <> None.

Record preserves_interface {F V G W}
    (src: F -> fundef signature) (dst: G -> fundef signature)
    (p: program F V) (q: program G W) : Prop := {
  same_main: q.(prog_main) = p.(prog_main);
  same_public: q.(prog_public) = p.(prog_public);
  kept_def: forall id td,
    (prog_defmap q)!id = Some td ->
    exists d, (prog_defmap p)!id = Some d /\
      definition_interface src d = definition_interface dst td;
  keeps_public: forall id d,
    In id p.(prog_public) -> (prog_defmap p)!id = Some d ->
    (prog_defmap q)!id <> None;
  keeps_main: forall d,
    (prog_defmap p)!(prog_main p) = Some d ->
    (prog_defmap q)!(prog_main q) <> None
}.

Lemma interface_refl: forall F V e (p: program F V), preserves_interface e e p p.
Proof. intros; constructor; eauto; congruence. Qed.

Lemma interface_trans:
  forall F V G W H X e1 e2 e3 (p: program F V) (q: program G W) (r: program H X),
  preserves_interface e1 e2 p q -> preserves_interface e2 e3 q r ->
  preserves_interface e1 e3 p r.
Proof.
  intros until r. intros [MAIN PUB KEPT KEEP START] [MAIN' PUB' KEPT' KEEP' START'].
  constructor; try congruence.
  - intros id td TD. apply KEPT' in TD as [d [DEF EQ]].
    apply KEPT in DEF as [sd [DEF EQ']]. exists sd. split; congruence.
  - intros id d IN DEF. destruct ((prog_defmap q)!id) as [qd|] eqn:Q.
    + eapply KEEP'; [now rewrite PUB|eassumption].
    + exfalso. eapply KEEP; eauto.
  - intros d DEF. destruct ((prog_defmap q)!(prog_main q)) as [qd|] eqn:Q.
    + exact (START' qd eq_refl).
    + exfalso. eapply START; eauto.
Qed.

Lemma public_defined_source:
  forall F V G W e1 e2 (p: program F V) (q: program G W),
  preserves_interface e1 e2 p q -> public_defined q -> public_defined p.
Proof.
  intros until q. intros [MAIN PUB KEPT KEEP START] DEF id IN NE.
  assert ((prog_defmap q)!id <> None) by (apply DEF; congruence).
  destruct ((prog_defmap q)!id) as [d|] eqn:Q; try contradiction.
  apply KEPT in Q as [sd [Q EQ]]. congruence.
Qed.

Lemma public_defined_target:
  forall F V G W e1 e2 (p: program F V) (q: program G W),
  preserves_interface e1 e2 p q -> public_defined p -> public_defined q.
Proof.
  intros until q. intros [MAIN PUB KEPT KEEP START] DEF id IN NE.
  assert ((prog_defmap p)!id <> None) by (apply DEF; congruence).
  destruct ((prog_defmap p)!id) as [d|] eqn:Q; try contradiction.
  eapply KEEP; eauto. congruence.
Qed.

Section MATCH_INTERFACE.
Context {C F V G W: Type} {LC: Linker C}.
Variable e1: F -> fundef signature.
Variable e2: G -> fundef signature.
Variable fm: C -> F -> G -> Prop.
Variable vm: V -> W -> Prop.
Hypothesis same_function_interface: forall ctx f tf, fm ctx f tf -> e1 f = e2 tf.

Lemma match_prog_interface: forall ctx (p: program F V) (q: program G W),
  match_program_gen fm vm ctx p q ->
  preserves_interface e1 e2 p q.
Proof.
  intros ctx p q MATCH.
  pose proof (match_program_defmap fm vm _ _ _ MATCH) as DEFS.
  destruct MATCH as [_ [MAIN PUBLIC]]. constructor; try assumption.

  - intros id td TD. specialize (DEFS id). rewrite TD in DEFS.
    inv DEFS. eexists; split; eauto.
    match goal with H: match_globdef _ _ _ _ _ |- _ => inv H end.
    + cbn. f_equal. eauto.
    + match goal with H: match_globvar _ _ _ |- _ => inv H; reflexivity end.
  - intros id d _ D. specialize (DEFS id). rewrite D in DEFS. inv DEFS. congruence.
  - intros d D. rewrite MAIN.
    specialize (DEFS (prog_main p)). rewrite D in DEFS. inv DEFS. congruence.
Qed.

End MATCH_INTERFACE.

Section AST_LINK.
Context {F V: Type} {LF: Linker F} {LV: Linker V}.

Local Transparent Linker_prog.

Lemma ast_link_defmap:
  forall (p1 p2 p: program F V) id,
  link p1 p2 = Some p ->
  (prog_defmap p)!id =
  link_prog_merge (prog_defmap p1)!id (prog_defmap p2)!id.
Proof.
  intros p1 p2 p id LINK.
  apply link_prog_inv in LINK as [_ [_ ->]].
  rewrite prog_defmap_elements, PTree.gcombine; auto.
Qed.

Lemma ast_link_main:
  forall (p1 p2 p: program F V),
  link p1 p2 = Some p ->
  p.(prog_main) = p1.(prog_main) /\ p.(prog_main) = p2.(prog_main).
Proof.
  intros until p. intros LINK.
  apply link_prog_inv in LINK as [MAIN [_ ->]]. simpl; auto.
Qed.

Lemma ast_link_public:
  forall (p1 p2 p: program F V),
  link p1 p2 = Some p -> p.(prog_public) = p1.(prog_public) ++ p2.(prog_public).
Proof. intros until p. intros LINK. apply link_prog_inv in LINK as [_ [_ ->]]. reflexivity. Qed.

Lemma ast_link_overlap:
  forall (p1 p2 p: program F V) id d1 d2,
  link p1 p2 = Some p ->
  (prog_defmap p1)!id = Some d1 ->
  (prog_defmap p2)!id = Some d2 ->
  In id p1.(prog_public) /\ In id p2.(prog_public) /\ exists d, link d1 d2 = Some d.
Proof.
  intros until d2. intros LINK. apply link_prog_inv in LINK as [_ [OVERLAP _]].
  auto.
Qed.

Lemma ast_link_has_def:
  forall (p1 p2 p: program F V) id,
  link p1 p2 = Some p ->
  ((prog_defmap p)!id <> None <->
   (prog_defmap p1)!id <> None \/ (prog_defmap p2)!id <> None).
Proof.
  intros p1 p2 p id LINK. rewrite (ast_link_defmap _ _ _ _ LINK).
  destruct ((prog_defmap p1)!id) as [d1|] eqn:P1,
    ((prog_defmap p2)!id) as [d2|] eqn:P2; simpl; try tauto; try solve [intuition discriminate].
  destruct (ast_link_overlap _ _ _ _ _ _ LINK P1 P2) as [_ [_ [d ->]]].
  intuition discriminate.
Qed.

Lemma ast_link_public_defined:
  forall (p1 p2 p: program F V),
  public_defined p1 -> public_defined p2 ->
  link p1 p2 = Some p -> public_defined p.
Proof.
  intros p1 p2 p DEF1 DEF2 LINK id IN NE.
  rewrite (ast_link_public _ _ _ LINK), in_app_iff in IN.
  destruct (ast_link_main _ _ _ LINK) as [MAIN1 MAIN2].
  apply (ast_link_has_def _ _ _ id LINK).
  destruct IN; [left; apply DEF1|right; apply DEF2]; congruence.
Qed.

End AST_LINK.

Section MIXED_LINK.
Context {F V G W: Type} {LF: Linker F} {LV: Linker V} {LG: Linker G} {LW: Linker W}.
Variables (src: F -> fundef signature) (dst: G -> fundef signature).

Hypothesis source_merge : forall (a b c: globdef F V),
  link a b = Some c ->
  link (definition_interface src a) (definition_interface src b) =
    Some (definition_interface src c).
Hypothesis target_merge : forall (a b: globdef G W) i,
  link (definition_interface dst a) (definition_interface dst b) = Some i ->
  exists c, link a b = Some c /\ definition_interface dst c = i.

Lemma link_preserves_interface:
  forall (p1 p2 p: program F V) (q1 q2: program G W),
  preserves_interface src dst p1 q1 ->
  preserves_interface src dst p2 q2 ->
  public_defined p1 -> public_defined p2 ->
  link p1 p2 = Some p ->
  exists q, link q1 q2 = Some q /\ preserves_interface src dst p q.
Proof.
  intros p1 p2 p q1 q2 INT1 INT2 PUB1 PUB2 LINK.
  pose proof (public_defined_target _ _ _ _ _ _ _ _ INT1 PUB1) as TPUB1.
  pose proof (public_defined_target _ _ _ _ _ _ _ _ INT2 PUB2) as TPUB2.
  destruct INT1 as [MAIN1 PUBLIC1 KEPT1 KEEP1 START1].
  destruct INT2 as [MAIN2 PUBLIC2 KEPT2 KEEP2 START2].
  assert (LINK_MAIN: prog_main q1 = prog_main q2).
  { destruct (ast_link_main _ _ _ LINK); congruence. }
  assert (LINK_DEFS: forall id gd1 gd2,
    (prog_defmap q1)!id = Some gd1 -> (prog_defmap q2)!id = Some gd2 ->
    In id (prog_public q1) /\ In id (prog_public q2) /\ link gd1 gd2 <> None).
  { intros id gd1 gd2 TD1 TD2.
    apply KEPT1 in TD1 as [sd1 [SD1 SH1]].
    apply KEPT2 in TD2 as [sd2 [SD2 SH2]].
    destruct (ast_link_overlap _ _ _ _ _ _ LINK SD1 SD2) as [IN1 [IN2 [d DEF]]].
    rewrite PUBLIC1, PUBLIC2. repeat split; try assumption.
    apply source_merge in DEF. rewrite SH1, SH2 in DEF.
    apply target_merge in DEF as [td [DEF _]]. congruence. }
  Local Transparent Linker_prog.
  eexists. split; [exact (link_prog_succeeds _ _ LINK_MAIN LINK_DEFS)|].
  match goal with
  | |- preserves_interface _ _ _ ?q =>
      pose proof (link_prog_succeeds q1 q2 LINK_MAIN LINK_DEFS) as QLINK;
      change (link q1 q2 = Some q) in QLINK;
      assert (KEEP_LINK_MAIN: forall id, id = prog_main p ->
        (prog_defmap p)!id <> None -> (prog_defmap q)!id <> None)
  end.
  { intros id EQ DEF.
    destruct (ast_link_main _ _ _ LINK) as [A1 A2].
    apply (ast_link_has_def _ _ _ id QLINK).
    apply (ast_link_has_def _ _ _ id LINK) in DEF.
    destruct DEF as [E1|E2].
    - left. rewrite EQ, A1 in E1. rewrite EQ, A1, <- MAIN1.
      destruct ((prog_defmap p1)!(prog_main p1)) as [d1|]; eauto; contradiction.
    - right. rewrite EQ, A2 in E2. rewrite EQ, A2, <- MAIN2.
      destruct ((prog_defmap p2)!(prog_main p2)) as [d2|]; eauto; contradiction. }
  constructor.
  - destruct (ast_link_main _ _ _ LINK) as [A _].
    destruct (ast_link_main _ _ _ QLINK) as [B _]. congruence.
  - rewrite (ast_link_public _ _ _ QLINK), (ast_link_public _ _ _ LINK), PUBLIC1, PUBLIC2.
    reflexivity.
  - intros id td.
    rewrite (ast_link_defmap _ _ _ id QLINK), (ast_link_defmap _ _ _ id LINK).
    destruct ((prog_defmap q1)!id) as [td1|] eqn:Q1,
      ((prog_defmap q2)!id) as [td2|] eqn:Q2; simpl; try discriminate.
    + destruct (KEPT1 _ _ Q1) as [sd1 [SD1 SH1]].
      destruct (KEPT2 _ _ Q2) as [sd2 [SD2 SH2]].
      destruct (ast_link_overlap _ _ _ _ _ _ LINK SD1 SD2) as [_ [_ [d DEF]]].
      rewrite SD1, SD2. cbn [link_prog_merge]. rewrite DEF.
      apply source_merge in DEF. rewrite SH1, SH2 in DEF.
      apply target_merge in DEF as [d' [DEF SHAPE]]. intros EQ.
      assert (td = d') by congruence. subst td. exists d; auto.

    + intros EQ; inv EQ. destruct (KEPT1 _ _ Q1) as [d [SD1 SH1]].
      rewrite SD1. destruct ((prog_defmap p2)!id) as [sd2|] eqn:SD2; simpl; eauto.
      destruct (ast_link_overlap _ _ _ _ _ _ LINK SD1 SD2) as [_ [IN2 _]].
      exfalso; eapply KEEP2; eauto.
    + intros EQ; inv EQ. destruct (KEPT2 _ _ Q2) as [d [SD2 SH2]].
      rewrite SD2. destruct ((prog_defmap p1)!id) as [sd1|] eqn:SD1; simpl; eauto.
      destruct (ast_link_overlap _ _ _ _ _ _ LINK SD1 SD2) as [IN1 _].
      exfalso; eapply KEEP1; eauto.
  - intros id d IN DEF.
    destruct (peq id (prog_main p)) as [EQ|NE].
    + apply KEEP_LINK_MAIN; congruence.
    + eapply (ast_link_public_defined q1 q2 _ TPUB1 TPUB2 QLINK).

      * rewrite (ast_link_public _ _ _ QLINK), PUBLIC1, PUBLIC2,
          <- (ast_link_public _ _ _ LINK). exact IN.
      * destruct (ast_link_main _ _ _ LINK), (ast_link_main _ _ _ QLINK). congruence.
  - intros d DEF.
    destruct (ast_link_main _ _ _ LINK), (ast_link_main _ _ _ QLINK).
    apply KEEP_LINK_MAIN; congruence.
Qed.

End MIXED_LINK.

Local Transparent Linker_def Linker_vardef Linker_fundef Linker_unit Ctypes.Linker_fundef.

Lemma c_definition_interface_link:
  forall F sig_of (a b c: globdef (Ctypes.fundef F) Ctypes.type),
  link a b = Some c ->
  link (definition_interface (c_fundef_interface sig_of) a)
       (definition_interface (c_fundef_interface sig_of) b) =
    Some (definition_interface (c_fundef_interface sig_of) c).
Proof.
  intros F sig_of [f1|[t1 i1 r1 v1]] [f2|[t2 i2 r2 v2]] c LINK;
    cbn [link Linker_def link_def] in LINK; try discriminate.
  - destruct f1 as [f1|ef1 args1 res1 cc1], f2 as [f2|ef2 args2 res2 cc2];
      cbn [link Ctypes.Linker_fundef Ctypes.link_fundef] in LINK; try discriminate.
    + destruct ef2; inv LINK. reflexivity.
    + destruct ef1; inv LINK. reflexivity.
    + destruct (external_function_eq ef1 ef2) as [SAME|NE]; cbn in LINK; try discriminate.
      destruct (_ && _ && _)%bool; inv LINK.
      cbn [definition_interface c_fundef_interface link Linker_def link_def Linker_fundef link_fundef].
      now rewrite dec_eq_true.
  - cbn [link Linker_vardef] in LINK. unfold link_vardef in LINK. cbn [ gvar_info gvar_init gvar_readonly gvar_volatile] in LINK.

    destruct (link t1 t2) as [t|]; try discriminate.
    destruct (link i1 i2) as [i|] eqn:INIT; try discriminate.
    destruct (Bool.eqb r1 r2 && Bool.eqb v1 v2)%bool eqn:FLAGS; inv LINK.
    cbn [definition_interface link Linker_def link_def Linker_vardef link_vardef
      Linker_unit gvar_info gvar_init gvar_readonly gvar_volatile].
    now rewrite INIT, FLAGS.
Qed.

Lemma ast_definition_interface_link_inv:
  forall F sig_of (a b: globdef (fundef F) unit) i,
  link (definition_interface (fundef_interface sig_of) a)
       (definition_interface (fundef_interface sig_of) b) = Some i ->
  exists c, link a b = Some c /\ definition_interface (fundef_interface sig_of) c = i.
Proof.
  intros F sig_of [f1|[[] i1 r1 v1]] [f2|[[] i2 r2 v2]] i LINK;
    cbn [definition_interface link Linker_def link_def] in LINK; try discriminate.
  - destruct f1 as [f1|ef1], f2 as [f2|ef2];
      cbn [fundef_interface link Linker_fundef link_fundef] in LINK; try discriminate.
    + destruct ef2; inv LINK. eexists; split; reflexivity.
    + destruct ef1; inv LINK. eexists; split; reflexivity.
    + destruct (external_function_eq ef1 ef2); inv LINK.
      exists (Gfun (External ef2)). split; [|reflexivity].
      cbn [link Linker_def link_def Linker_fundef link_fundef].
      now rewrite dec_eq_true.
  - cbn [definition_interface gvar_info gvar_init gvar_readonly gvar_volatile] in LINK.
    destruct (link _ _) as [v|] eqn:VAR; inv LINK.
    exists (Gvar v). split.
    + cbn [link Linker_def link_def]. now rewrite VAR.
    + destruct v as [[]]; reflexivity.
Qed.

Lemma c_link_ast:
  forall F (p1 p2 p: Ctypes.program F),
  link p1 p2 = Some p ->
  link (Ctypes.program_of_program p1) (Ctypes.program_of_program p2) =
    Some (Ctypes.program_of_program p).
Proof.
  Local Transparent Ctypes.Linker_program.
  intros F p1 p2 p LINK.
  cbn [link Ctypes.Linker_program] in LINK. unfold Ctypes.link_program in LINK.
  destruct (link (Ctypes.program_of_program p1) (Ctypes.program_of_program p2))
    as [pp|]; try discriminate.
  destruct (Ctypes.lift_option (link (Ctypes.prog_types p1) (Ctypes.prog_types p2)))
    as [[typs EQ]|EQ]; try discriminate.
  destruct (Ctypes.link_build_composite_env _ _ _ _ _ _ _ EQ) as [env [P _]].
  inv LINK. destruct pp; reflexivity.
Qed.

Theorem link_mixed_interfaces:
  forall F G (src_sig: F -> signature) (dst_sig: G -> signature)
    (sources: nlist (Ctypes.program F)) (targets: nlist (program (fundef G) unit)) p,
  nlist_forall2
    (fun source target =>
      preserves_interface (c_fundef_interface src_sig) (fundef_interface dst_sig)
        (Ctypes.program_of_program source) target /\
      public_defined (Ctypes.program_of_program source)) sources targets ->
  link_list sources = Some p ->
  exists q, link_list targets = Some q /\
    preserves_interface (c_fundef_interface src_sig) (fundef_interface dst_sig)
      (Ctypes.program_of_program p) q /\ public_defined (Ctypes.program_of_program p).
Proof.
  intros F G src_sig dst_sig sources targets p CERT. revert p.
  induction CERT; simpl; intros p LINK.
  - inv LINK. exists b; auto.
  - destruct (link_list l) as [p'|] eqn:LINKTAIL; try discriminate.
    destruct (IHCERT _ eq_refl) as (q' & TAIL & INT & DEF).
    destruct H as [HEAD PUB].
    pose proof (c_link_ast _ _ _ _ LINK) as CLINK.
    destruct (link_preserves_interface _ _
      (c_definition_interface_link _ src_sig) (ast_definition_interface_link_inv _ dst_sig)
      _ _ _ _ _ HEAD INT PUB DEF CLINK) as [q [QLINK MERGED]].
    exists q. rewrite TAIL, QLINK. split; [reflexivity|]. split; [exact MERGED|].
    exact (ast_link_public_defined _ _ _ PUB DEF CLINK).
Qed.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Keep the compilation unit's definition map as a witness for each
    transformed function, including after verified separate linking. *)
Require Import Coqlib Maps AST Linking Integers Values Events Globalenvs.
Require Import Ctypes Cop Clight ArrayPair.

Definition match_fundef (cu: Clight.program) (f tf: Clight.fundef) : Prop :=
  tf = transf_fundef cu f.

Definition match_prog (p tp: Clight.program) : Prop :=
  Linking.match_program_gen match_fundef eq p p tp /\ prog_types tp = prog_types p.

Lemma transf_program_match : forall p, match_prog p (transf_program p).
Proof.
  intros p. split; [|reflexivity].
  unfold Linking.match_program_gen. split; [|split; reflexivity].
  change (list_forall2 (match_ident_globdef match_fundef eq p)
    (prog_defs p)
    (map (transform_program_globdef (transf_fundef p)) (prog_defs p))).
  induction (prog_defs p) as [|[id [fd|v]] defs IH].
  - constructor.
  - constructor; [|exact IH]. split; [reflexivity|].
    apply match_globdef_fun with (ctx' := p); [apply linkorder_refl|reflexivity].
  - constructor; [|exact IH]. split; [reflexivity|].
    destruct v. constructor. constructor. reflexivity.
Qed.

Global Instance TransfArrayPairLink : TransfLink match_prog.
Proof.
  red; intros. eapply Ctypes.link_match_program_gen; eauto.
  intros cu1 cu2 f1 tf1 f2 tf2 f LINK M1 M2.
  unfold match_fundef in *. subst tf1 tf2.
  Local Transparent Linker_fundef.
  change (link_fundef f1 f2 = Some f) in LINK.
  change (exists tf, link_fundef (transf_fundef cu1 f1) (transf_fundef cu2 f2) = Some tf /\
    (tf = transf_fundef cu1 f \/ tf = transf_fundef cu2 f)).
  destruct f1, f2; cbn [link_fundef transf_fundef] in *; try discriminate;
    repeat match goal with H: context [match ?x with _ => _ end] |- _ =>
      destruct x; try discriminate end;
    inv LINK; eauto.
Qed.

Lemma find_funct_translated : forall prog tprog,
  match_prog prog tprog ->
  forall v fd, Genv.find_funct (globalenv prog) v = Some fd ->
  exists cu tf, Genv.find_funct (globalenv tprog) v = Some tf /\
    tf = transf_fundef cu fd /\ linkorder cu prog.
Proof. intros prog tprog MATCH. exact (Genv.find_funct_match (proj1 MATCH)). Qed.

Lemma find_funct_ptr_translated : forall prog tprog,
  match_prog prog tprog ->
  forall b fd, Genv.find_funct_ptr (globalenv prog) b = Some fd ->
  exists cu tf, Genv.find_funct_ptr (globalenv tprog) b = Some tf /\
    tf = transf_fundef cu fd /\ linkorder cu prog.
Proof. intros prog tprog MATCH. exact (Genv.find_funct_ptr_match (proj1 MATCH)). Qed.

(** Linking cannot replace an already internal definition. The function
    selected by the checker therefore remains the one the call executes. *)
Lemma linked_internal_def : forall (cu p: Clight.program) id f,
  linkorder cu p ->
  (AST.prog_defmap cu)!id = Some (Gfun (Internal f)) ->
  (AST.prog_defmap p)!id = Some (Gfun (Internal f)).
Proof.
  intros cu p id f ORDER DEF.
  change (linkorder_program cu p) in ORDER.
  destruct ORDER as [ORDER _].
  destruct (prog_defmap_linkorder _ _ _ _ ORDER DEF) as [gd [GDEF GDORDER]].
  change (linkorder_def (Gfun (Internal f)) gd) in GDORDER.
  inversion GDORDER as [f1 f2 FD |]; subst.
  change (linkorder_fundef (Internal f) f2) in FD. inv FD.
  exact GDEF.
Qed.

Lemma linked_internal_symbol : forall (cu p: Clight.program) id f,
  linkorder cu p ->
  (AST.prog_defmap cu)!id = Some (Gfun (Internal f)) ->
  exists b, Genv.find_symbol (globalenv p) id = Some b /\
    Genv.find_funct (globalenv p) (Vptr b Ptrofs.zero) = Some (Internal f).
Proof.
  intros cu p id f ORDER DEF.
  apply (linked_internal_def cu p id f ORDER) in DEF.
  apply Genv.find_def_symbol in DEF as [b [SYMBOL DEF]].
  exists b; split; [exact SYMBOL|].
  rewrite Genv.find_funct_find_funct_ptr, Genv.find_funct_ptr_iff. exact DEF.
Qed.

Lemma eval_linked_worker : forall (cu p: Clight.program) id f tyargs tyres cc le m v,
  linkorder cu p ->
  (AST.prog_defmap cu)!id = Some (Gfun (Internal f)) ->
  eval_expr (globalenv p) empty_env le m (Evar id (Tfunction tyargs tyres cc)) v ->
  Genv.find_funct (globalenv p) v = Some (Internal f).
Proof.
  intros cu p id f tyargs tyres cc le m v ORDER DEF EV.
  destruct (linked_internal_symbol cu p id f ORDER DEF) as [b [SYMBOL FUN]].
  inv EV.
  match goal with H: eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _ => inv H end.
  - match goal with
    | H: empty_env!_ = Some _ |- _ => unfold empty_env in H; rewrite PTree.gempty in H; discriminate
    end.
  - assert (loc = b) by congruence. subst loc.
    match goal with H: deref_loc _ _ _ _ _ _ |- _ => inv H end;
      try discriminate; exact FUN.
Qed.

Lemma caller_call_inv : forall (cu prog: Clight.program) c le m k t after n,
  let p := call_loop c in
  let ge := globalenv prog in
  linkorder cu prog ->
  (AST.prog_defmap cu)!(call_worker c) = Some (Gfun (Internal (source_template p))) ->
  array_anchor p = None ->
  le!(call_count c) = Some n ->
  (forall v, eval_expr ge empty_env le m (guard_address (call_address c)) v ->
     exists b ofs, v = Vptr b ofs) ->
  step2 ge (State (caller_source c) (caller_call c) k empty_env le m) t after ->
  t = E0 /\ exists b ofs,
    eval_expr ge empty_env le m (guard_address (call_address c)) (Vptr b ofs) /\
    after = Callstate (Internal (source_template p)) (Vptr b ofs :: n :: nil)
      (Kcall None (caller_source c) empty_env le k) m.
Proof.
  intros cu prog c le m k t after n p ge ORDER WORKER ANCHOR COUNT ADDRESS STEP.
  assert (TYPE: type_of_function (source_template p) =
    Tfunction (tuint_ptr :: tuint :: nil) Tvoid cc_default).
  { unfold type_of_function, source_template, parameters, anchored.
    rewrite ANCHOR. reflexivity. }
  unfold caller_call in STEP. fold p in STEP. rewrite TYPE in STEP.
  inv STEP; try solve [intuition discriminate].
  match goal with
  | CLASS: classify_fun _ = fun_case_f _ _ _ |- _ =>
      cbn [typeof classify_fun] in CLASS; inv CLASS
  end.
  match goal with
  | EV: eval_expr _ _ _ _ (Evar _ _) _,
    FIND: Genv.find_funct _ _ = Some _ |- _ =>
      pose proof (eval_linked_worker _ _ _ _ _ _ _ _ _ _ ORDER WORKER EV) as KNOWN;
      fold ge in KNOWN;
      rewrite KNOWN in FIND; inv FIND
  end.
  match goal with
  | ARGS: eval_exprlist _ _ _ _ (_ :: _ :: nil) _ _ |- _ => inv ARGS
  end.
  match goal with
  | ARGS: eval_exprlist _ _ _ _ (_ :: nil) _ _ |- _ => inv ARGS
  end.
  match goal with
  | ARGS: eval_exprlist _ _ _ _ nil _ _ |- _ => inv ARGS
  end.
  match goal with
  | EV: eval_expr _ _ _ _ (Etempvar _ _) _ |- _ => inv EV
  end;
  try match goal with H: eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inv H end.
  match goal with
  | H: le!(call_count c) = Some _ |- _ => rewrite COUNT in H; inv H
  end.
  match goal with
  | EV: eval_expr _ _ _ _ (guard_address _) ?v,
    CAST: sem_cast ?v _ _ _ = Some _ |- _ =>
      destruct (ADDRESS _ EV) as [b [ofs ->]];
      assert (CAST_ID: sem_cast (Vptr b ofs) (typeof (guard_address (call_address c))) tuint_ptr m =
          Some (Vptr b ofs))
        by (destruct (call_address c) as [id len al [[off sign]|]]; reflexivity);
      rewrite CAST_ID in CAST; inv CAST
  end.
  match goal with
  | CAST: sem_cast ?raw (typeof (Etempvar _ _)) tuint m = Some _ |- _ =>
      destruct raw; cbn in CAST; inv CAST
  end.
  split; [reflexivity|]. eauto.
Qed.

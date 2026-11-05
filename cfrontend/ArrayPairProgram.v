(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib Maps AST Linking Integers Values Memory Events Globalenvs Smallstep.
Require Import Ctypes Cop Clight ArrayPair ArrayPairMatch.

Definition match_prog (p tp: Clight.program) : Prop :=
  Linking.match_program (fun _ f tf => tf = transf_fundef f) eq p tp /\
  prog_types tp = prog_types p.

Lemma transf_program_match : forall p, match_prog p (transf_program p).
Proof.
  intros. split; [apply match_transform_program | reflexivity].
Qed.

Global Instance TransfArrayPairLink : TransfLink match_prog.
Proof.
  red; intros. eapply Ctypes.link_match_program; eauto.
  intros f1 tf1 f2 tf2 f LINK -> ->.
  Local Transparent Linker_fundef.
  change (link_fundef f1 f2 = Some f) in LINK.
  change (exists tf, link_fundef (transf_fundef f1) (transf_fundef f2) = Some tf /\
    tf = transf_fundef f).
  destruct f1, f2; simpl in *; try discriminate;
    repeat match goal with H: context [match ?x with _ => _ end] |- _ =>
      destruct x; try discriminate end;
    inv LINK; eauto.
Qed.

(** Selected functions contain no calls. Consequently every suspended
    caller runs its original body and the continuations can be shared. *)
Fixpoint original_callers (k: cont) : Prop :=
  match k with
  | Kstop => True
  | Kseq _ k | Kloop1 _ _ k | Kloop2 _ _ k | Kswitch k => original_callers k
  | Kcall _ f _ _ k => selected f = None /\ original_callers k
  end.

Lemma original_callers_call_cont : forall k,
  original_callers k -> original_callers (call_cont k).
Proof. induction k; simpl; auto. Qed.

Scheme stmt_mut := Induction for statement Sort Prop
  with lbl_stmt_mut := Induction for labeled_statements Sort Prop.
Combined Scheme stmt_lbl_mut from stmt_mut, lbl_stmt_mut.

Lemma find_label_callers : forall lbl,
  (forall s k s' k', find_label lbl s k = Some (s', k') ->
    original_callers k -> original_callers k') /\
  (forall ls k s' k', find_label_ls lbl ls k = Some (s', k') ->
    original_callers k -> original_callers k').
Proof.
  intros lbl. apply stmt_lbl_mut; simpl; intros; try discriminate;
    repeat match goal with
    | H: context [match ?x with _ => _ end] |- _ =>
        destruct x eqn:?; try discriminate
    | H: context [if ?x then _ else _] |- _ => destruct x eqn:?
    end; try match goal with H: Some _ = Some _ |- _ => inv H end; eauto.
Qed.

Lemma bind_extra_temp : forall params args le le' id v,
  ~In id (var_names params) ->
  bind_parameter_temps params args le = Some le' ->
  bind_parameter_temps params args (PTree.set id v le) = Some (PTree.set id v le').
Proof.
  induction params as [|[p ty] ps IH]; destruct args as [|arg args]; simpl;
    intros le le' id v FRESH BIND; try discriminate.
  - now inv BIND.
  - assert (COMMUTE: PTree.set p arg (PTree.set id v le) = PTree.set id v (PTree.set p arg le)).
    { apply PTree.extensionality; intro j. repeat rewrite PTree.gsspec.
      destruct (peq j p), (peq j id); subst; intuition. }
    rewrite COMMUTE. eapply IH; eauto.
Qed.

Lemma entry_selected : forall ge tge p args m e le m',
  function_entry2 ge (source_template p) args m e le m' ->
  function_entry2 tge (target_template p) args m e (PTree.set (scratch p) Vundef le) m'.
Proof.
  intros ge tge p args m e le m' ENTRY. inversion ENTRY as [VARS PARAMS DISJOINT ALLOC BIND]; subst.
  assert (FRESH: ~ In (scratch p) (var_names (parameters p))).
  { unfold parameters. destruct (wide p); cbn [var_names map fst].
    - intros [E | []]. apply (scratch_bound p); symmetry; exact E.
    - intros [E | [E | []]].
      + apply (scratch_pointer p); symmetry; exact E.
      + apply (scratch_bound p); symmetry; exact E. }
  cbn [source_template fn_vars] in ALLOC. inv ALLOC.
  constructor; try assumption.
  - change (list_disjoint (var_names (parameters p)) (scratch p :: var_names (scalar_temps p))).
    apply list_disjoint_cons_r; assumption.
  - constructor.
  - change (bind_parameter_temps (parameters p) args
      (PTree.set (scratch p) Vundef (create_undef_temps (scalar_temps p))) =
      Some (PTree.set (scratch p) Vundef le)).
    eapply bind_extra_temp; eauto.
Qed.

Section PROGRAM.
Variables prog tprog: Clight.program.
Hypothesis MATCH: match_prog prog tprog.
Let ge := globalenv prog.
Let tge := globalenv tprog.

Lemma comp_env_preserved : genv_cenv tge = genv_cenv ge.
Proof.
  unfold ge, tge, globalenv; simpl.
  pose proof (prog_comp_env_eq prog) as C.
  pose proof (prog_comp_env_eq tprog) as TC.
  rewrite (proj2 MATCH) in TC. congruence.
Qed.

Lemma symbols_preserved : forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf (proj1 MATCH)). Qed.

Lemma senv_preserved : Senv.equiv ge tge.
Proof. exact (Genv.senv_transf (proj1 MATCH)). Qed.

Lemma find_funct_translated : forall v fd, Genv.find_funct ge v = Some fd ->
  Genv.find_funct tge v = Some (transf_fundef fd).
Proof. exact (Genv.find_funct_transf (proj1 MATCH)). Qed.

Lemma find_funct_ptr_translated : forall b fd, Genv.find_funct_ptr ge b = Some fd ->
  Genv.find_funct_ptr tge b = Some (transf_fundef fd).
Proof. exact (Genv.find_funct_ptr_transf (proj1 MATCH)). Qed.

Lemma type_preserved : forall fd, type_of_fundef (transf_fundef fd) = type_of_fundef fd.
Proof.
  destruct fd; simpl; auto. unfold type_of_function.
  destruct (metadata_preserved f) as [RET [CC [PARAM VAR]]]. now rewrite RET, CC, PARAM.
Qed.

Lemma eval_preserved : forall e le m,
  (forall a v, eval_expr ge e le m a v -> eval_expr tge e le m a v) /\
  (forall a b ofs bf, eval_lvalue ge e le m a b ofs bf -> eval_lvalue tge e le m a b ofs bf).
Proof.
  intros e le m. apply eval_expr_lvalue_ind; intros;
    try solve [econstructor; eauto; rewrite ?comp_env_preserved, ?symbols_preserved; eauto].
  - rewrite <- comp_env_preserved. constructor.
  - rewrite <- comp_env_preserved. constructor.
Qed.

Lemma exprlist_preserved : forall e le m al ty vl,
  eval_exprlist ge e le m al ty vl -> eval_exprlist tge e le m al ty vl.
Proof.
  induction 1; econstructor; eauto. eapply (proj1 (eval_preserved _ _ _)); eauto.
Qed.

Lemma alloc_preserved : forall e m vars e' m',
  alloc_variables ge e m vars e' m' -> alloc_variables tge e m vars e' m'.
Proof. induction 1; econstructor; eauto. rewrite comp_env_preserved; auto. Qed.

Lemma blocks_preserved : forall e, blocks_of_env tge e = blocks_of_env ge e.
Proof.
  intros. unfold blocks_of_env. apply map_ext. intros [id [b ty]].
  unfold block_of_binding. now rewrite comp_env_preserved.
Qed.

Lemma entry_preserved : forall f args m e le m',
  function_entry2 ge f args m e le m' -> function_entry2 tge f args m e le m'.
Proof. intros. inv H. constructor; eauto using alloc_preserved. Qed.

Inductive ordinary_match : state -> state -> Prop :=
  | match_normal : forall f s k e le m,
      selected f = None -> original_callers k ->
      ordinary_match (State f s k e le m) (State f s k e le m)
  | match_call : forall fd args k m,
      original_callers k -> is_call_cont k ->
      ordinary_match (Callstate fd args k m) (Callstate (transf_fundef fd) args k m)
  | match_return : forall v k m,
      original_callers k -> ordinary_match (Returnstate v k m) (Returnstate v k m).

Local Hint Resolve exprlist_preserved original_callers_call_cont : core.
Local Hint Extern 2 (eval_expr tge _ _ _ _ _) => eapply (proj1 (eval_preserved _ _ _)) : core.
Local Hint Extern 2 (eval_lvalue tge _ _ _ _ _ _ _) => eapply (proj2 (eval_preserved _ _ _)) : core.

Lemma step_normal : forall f s k e le m t after,
  step2 ge (State f s k e le m) t after ->
  selected f = None -> original_callers k ->
  exists ta, step2 tge (State f s k e le m) t ta /\ ordinary_match after ta.
Proof.
  intros until after. intros STEP SELECT STACK. inv STEP;
    try solve [eexists; split; [econstructor; eauto | constructor; simpl in *; auto]].
  - eexists; split.
    + eapply step_assign; eauto. rewrite comp_env_preserved; eauto.
    + constructor; auto.
  - eexists; split.
    + eapply step_call with (fd := transf_fundef fd); eauto using find_funct_translated.
      rewrite type_preserved; auto.
    + constructor; simpl; auto.
  - eexists; split.
    + eapply step_builtin; eauto. eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    + constructor; auto.
  - eexists; split.
    + eapply step_return_0; eauto. rewrite blocks_preserved; eauto.
    + constructor; auto.
  - eexists; split.
    + eapply step_return_1; eauto. rewrite blocks_preserved; eauto.
    + constructor; auto.
  - eexists; split.
    + eapply step_skip_call; eauto. rewrite blocks_preserved; eauto.
    + constructor; auto.
  - eexists; split.
    + eapply step_goto; eauto.
    + constructor; auto. eapply (proj1 (find_label_callers lbl)); eauto.
Qed.

Lemma initial_simulation : forall s,
  initial_state prog s -> exists ts, initial_state tprog ts /\ ordinary_match s ts.
Proof.
  intros s INIT. inv INIT.
  exists (Callstate (transf_fundef f) nil Kstop m0). split.
  - eapply initial_state_intro with (b := b).
    + eapply (Genv.init_mem_transf (proj1 MATCH)); eauto.
    + rewrite symbols_preserved.
      exact (eq_trans (f_equal (Genv.find_symbol ge) (match_program_main (proj1 MATCH))) H0).
    + eapply find_funct_ptr_translated; eauto.
    + rewrite type_preserved; eauto.
  - constructor; exact I.
Qed.

Section SELECTED_LOOPS.

Variable loop_match : plan -> cont -> nat -> state -> state -> Prop.

Hypothesis loop_init : forall p k e le v m,
  well_formed p ->
  exists rank, loop_match p k rank
    (State (source_template p) (source_body p) k e le m)
    (State (target_template p) (target_body p) k e (PTree.set (scratch p) v le) m).

Hypothesis loop_step : forall p k rank s t after ts,
  well_formed p -> is_call_cont k -> loop_match p k rank s ts -> step2 ge s t after ->
  exists next_rank ta,
    (plus step2 tge ts t ta \/ (t = E0 /\ ta = ts /\ (next_rank < rank)%nat)) /\
    (loop_match p k next_rank after ta \/
     exists v m, after = Returnstate v k m /\ ta = Returnstate v k m).

Hypothesis loop_nonfinal : forall p k rank s ts r,
  loop_match p k rank s ts -> ~ final_state s r.

Inductive match_states : nat -> state -> state -> Prop :=
  | match_ordinary : forall s ts, ordinary_match s ts -> match_states O s ts
  | match_selected : forall p k rank s ts,
      well_formed p -> original_callers k -> is_call_cont k ->
      loop_match p k rank s ts -> match_states rank s ts.

Lemma ordinary_step : forall s t after ts,
  step2 ge s t after -> ordinary_match s ts ->
  exists rank ta, plus step2 tge ts t ta /\ match_states rank after ta.
Proof.
  intros s t after ts STEP MATCHED. inv MATCHED.
  - destruct (step_normal _ _ _ _ _ _ _ _ STEP H H0) as [ta [ST MA]].
    exists O, ta; split. now apply plus_one. now constructor.
  - inv STEP.
    + destruct (selected f) as [p|] eqn:SELECT.
      * destruct (selected_sound _ _ SELECT) as [-> WF].
        destruct (loop_init p k e le Vundef m1 WF) as [rank LM].
        exists rank, (State (target_template p) (target_body p) k e (PTree.set (scratch p) Vundef le) m1).
        split.
        -- cbn [transf_fundef]. unfold transf_function. rewrite SELECT.
           apply plus_one. apply step_internal_function. eapply entry_selected; eauto.
        -- eapply match_selected; eauto.
      * exists O, (State f (fn_body f) k e le m1). split.
        -- cbn [transf_fundef]. unfold transf_function. rewrite SELECT.
           apply plus_one. apply step_internal_function. eapply entry_preserved; eauto.
        -- constructor. constructor; auto.
    + exists O, (Returnstate vres k m'). split.
      * apply plus_one. eapply step_external_function.
        eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      * constructor. constructor; auto.
  - inv STEP. simpl in H. destruct H as [SELECT STACK].
    exists O, (State f Sskip k0 e (set_opttemp optid v le) m). split.
    + apply plus_one. constructor.
    + constructor. constructor; auto.
Qed.

Lemma steps_simulate : forall rank s t after ts,
  step2 ge s t after -> match_states rank s ts ->
  exists next_rank ta,
    (plus step2 tge ts t ta \/ (star step2 tge ts t ta /\ (next_rank < rank)%nat)) /\
    match_states next_rank after ta.
Proof.
  intros rank s t after ts STEP M. inv M.
  - destruct (ordinary_step _ _ _ _ STEP H) as [rank [ta [ST MA]]].
    exists rank, ta. auto.
  - destruct (loop_step _ _ _ _ _ _ _ H H1 H2 STEP) as [j [ta [ST MA]]].
    assert (SIM: plus step2 tge ts t ta \/ (star step2 tge ts t ta /\ (j < rank)%nat)).
    { destruct ST as [PLUS|[-> [-> LT]]]; auto using star_refl. }
    destruct MA as [LOOP|[v [m [-> ->]]]].
    + exists j, ta. split; auto. eapply match_selected; eauto.
    + exists O, (Returnstate v k m). split.
      * destruct SIM as [PLUS|[STAR LT]]; auto. right. split; auto; lia.
      * constructor. constructor; auto.
Qed.

Lemma program_simulation : forward_simulation (semantics2 prog) (semantics2 tprog).
Proof.
  apply Forward_simulation with lt match_states; constructor.
  - apply lt_wf.
  - intros s INIT. destruct (initial_simulation _ INIT) as [ts [TI TM]].
    exists O, ts; split; auto. now constructor.
  - intros rank s ts r M FINAL. inv M.
    + inv FINAL. inv H. constructor.
    + exfalso. eapply loop_nonfinal; eauto.
  - intros. eapply steps_simulate; eauto.
  - exact (proj1 (proj2 senv_preserved)).
Qed.

End SELECTED_LOOPS.
End PROGRAM.

Require ArrayPairLocal.

Theorem transf_program_correct : forall prog tprog,
  match_prog prog tprog -> forward_simulation (semantics2 prog) (semantics2 tprog).
Proof.
  intros prog tprog MATCH.
  eapply program_simulation with
    (loop_match := fun p k => ArrayPairLocal.local_match (globalenv prog) (globalenv tprog) p k k).
  - exact MATCH.
  - apply ArrayPairLocal.local_init.
  - intros. eapply ArrayPairLocal.local_step; eauto using blocks_preserved, symbols_preserved.
  - intros p k rank s ts r LOCAL FINAL. inv FINAL. inv LOCAL.
Qed.

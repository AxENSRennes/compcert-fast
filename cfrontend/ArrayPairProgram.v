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
Require Import ArrayPairBase ArrayPairTarget ArrayPairLocal.
Require ArrayPairTurn.

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

Lemma entry_selected : forall ge tge p g args m e le m',
  function_entry2 ge (source_function p g) args m e le m' ->
  function_entry2 tge (target_function p g) args m e (PTree.set (scratch p) Vundef le) m'.
Proof.
  intros ge tge p g args m e le m' ENTRY. inversion ENTRY as [VARS PARAMS DISJOINT ALLOC BIND]; subst.
  assert (FRESH: ~ In (scratch p) (var_names (parameters p))).
  { unfold parameters. destruct (anchored p); cbn [var_names map fst].
    - intros [E | []]. apply (scratch_bound p); symmetry; exact E.
    - intros [E | [E | []]].
      + apply (scratch_pointer p); symmetry; exact E.
      + apply (scratch_bound p); symmetry; exact E. }
  destruct g; cbn [source_function with_body source_template fn_vars] in ALLOC; inv ALLOC;
    constructor; try assumption;
    try solve [apply list_disjoint_cons_r; assumption | constructor |
      eapply bind_extra_temp; eauto].
Qed.

Local Open Scope Z_scope.

Lemma guard_address_type : forall g, typeconv (typeof (guard_address g)) = tuint_ptr.
Proof. intros [id len al [[k sign] | ]]; reflexivity. Qed.

Local Lemma guard_displacement_aligned :
  forall id len al k sign,
  valid_guard (AlignmentGuard id len al (Some (k, sign))) = true ->
  (8 | Ptrofs.unsigned (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int sign k))).
Proof.
  intros id len al k sign VALID.
  set (i := offset_index (Some (k, sign))) in *.
  change (N.leb 3 al && Z.leb 0 i && Z.ltb i len && Z.even i = true) in VALID.
  apply andb_true_iff in VALID as [TEST EVEN].
  apply andb_true_iff in TEST as [TEST _].
  apply andb_true_iff in TEST as [_ NONNEG].
  apply Z.leb_le in NONNEG.
  apply Z.even_spec in EVEN as [q EVEN].
  assert (RANGE: 0 <= i <= 4294967295).
  { split; [exact NONNEG|]. unfold i. destruct sign; cbn [offset_index].
    - pose proof (Int.signed_range k) as RANGE.
      change Int.max_signed with 2147483647 in RANGE. lia.
    - exact (proj2 (Int.unsigned_range_2 k)). }
  assert (OFFSET: ptrofs_of_int sign k = Ptrofs.repr i) by (destruct sign; reflexivity).
  rewrite OFFSET. unfold Ptrofs.mul.
  change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
  rewrite (Ptrofs.unsigned_repr i) by
    (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  rewrite Ptrofs.unsigned_repr by
    (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  exists q. lia.
Qed.

Lemma guard_address_replay :
  forall ge e le m g v,
  valid_guard g = true ->
  eval_expr ge e le m (guard_address g) v ->
  exists b ofs, v = Vptr b ofs /\ (8 | Ptrofs.unsigned ofs) /\
    forall le', eval_expr ge e le' m (guard_address g) v.
Proof.
  intros ge e le m [id len al off] v VALID EV.
  destruct off as [[k sign] | ].
  - cbn [guard_address guard_array guard_length guard_alignment guard_offset] in EV.
    inv EV.
    2: { match goal with H: eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inv H end. }
    match goal with
    | BASE: eval_expr _ _ _ _ (Evar _ _) _, ARG: eval_expr _ _ _ _ (Econst_int _ _) _ |- _ =>
        apply array_expr_inv in BASE as (b & -> & BIND);
        inv ARG
    end.
    2: { match goal with H: eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inv H end. }
    match goal with
    | ADD: sem_binary_operation _ Oadd _ _ _ _ _ = Some _ |- _ =>
        change (Some (Vptr b (Ptrofs.add Ptrofs.zero
          (Ptrofs.mul (Ptrofs.repr 4) (ptrofs_of_int sign k)))) = Some v) in ADD;
        inv ADD
    end.
    eexists b, _; split; [reflexivity|]. split.
    + rewrite Ptrofs.add_zero_l. eapply guard_displacement_aligned; eauto.
    + intro le'. eapply eval_Ebinop.
      * apply array_binding_eval. exact BIND.
      * apply eval_Econst_int.
      * reflexivity.
  - apply array_expr_inv in EV as (b & -> & BIND).
    exists b, Ptrofs.zero. split; [reflexivity|]. split.
    + rewrite Ptrofs.unsigned_zero. apply Z.divide_0_r.
    + intro le'. apply array_binding_eval. exact BIND.
Qed.

Local Lemma pointer_comparison_true : forall m v b ofs,
  cmp_ptr m Ceq v (Vptr b ofs) = Some Vtrue -> v = Vptr b ofs.
Proof.
  intros m v b ofs H. unfold cmp_ptr in H. destruct v as [|i|i|f|f|b' ofs'];
    cbn [Archi.ptr64 Val.cmplu_bool negb] in H; try discriminate.
  - destruct (Int64.eq i Int64.zero && (Mem.valid_pointer m b (Ptrofs.unsigned ofs) || Mem.valid_pointer m b (Ptrofs.unsigned ofs - 1)));
      discriminate.
  - destruct (eq_block b' b) as [->|NE].
    + destruct ((Mem.valid_pointer m b (Ptrofs.unsigned ofs') || Mem.valid_pointer m b (Ptrofs.unsigned ofs' - 1)) &&
          (Mem.valid_pointer m b (Ptrofs.unsigned ofs) || Mem.valid_pointer m b (Ptrofs.unsigned ofs - 1))); try discriminate.
      cbn [Ptrofs.cmpu option_map] in H. destruct (Ptrofs.eq ofs' ofs) eqn:E;
        try discriminate. now apply Ptrofs.same_if_eq in E; subst.
    + destruct (Mem.valid_pointer m b' (Ptrofs.unsigned ofs') &&
          Mem.valid_pointer m b (Ptrofs.unsigned ofs)); discriminate.
Qed.

Local Lemma guard_test_replay : forall ge e le m p g v b,
  valid_guard g = true ->
  eval_expr ge e le m (guard_test p g) v ->
  bool_val v (typeof (guard_test p g)) m = Some b ->
  eval_expr ge e (PTree.set (scratch p) Vundef le) m (guard_test p g) v /\
  (b = true -> base_ready (aligned_pointer_plan p) le).
Proof.
  intros ge e le m p g v b VALID TEST BOOL.
  unfold guard_test in TEST.
  apply ArrayPairTurn.eval_binop_inv in TEST as (vp & va & PTR & ADDR & CMP).
  apply ArrayPairTurn.eval_temp_inv in PTR.
  apply (guard_address_replay _ _ _ _ _ _ VALID) in ADDR as (blk & ofs & -> & ALIGN & REPLAY).
  split.
  - unfold guard_test. eapply eval_Ebinop; [|apply REPLAY|exact CMP].
    apply eval_Etempvar. rewrite PTree.gso; [exact PTR|pose proof (scratch_pointer p); congruence].
  - intros ->. unfold base_ready. cbn [aligned_pointer_plan pointer].
    intros _ blk' ofs' PTR'. rewrite PTR in PTR'. inv PTR'.
    change (sem_cmp Ceq (Vptr blk' ofs') tuint_ptr (Vptr blk ofs)
      (typeof (guard_address g)) m = Some v) in CMP.
    unfold sem_cmp, classify_cmp in CMP.
    rewrite guard_address_type in CMP.
    change (cmp_ptr m Ceq (Vptr blk' ofs') (Vptr blk ofs) = Some v) in CMP.
    assert (EQ: cmp_ptr m Ceq (Vptr blk' ofs') (Vptr blk ofs) = Some Vtrue).
    { unfold cmp_ptr in CMP |- *. cbn [Archi.ptr64] in CMP |- *.
      destruct (Val.cmplu_bool (Mem.valid_pointer m) Ceq (Vptr blk' ofs') (Vptr blk ofs))
        as [[]|]; inversion CMP; subst v; try discriminate.
      reflexivity. }
    apply pointer_comparison_true in EQ. inv EQ. exact ALIGN.
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

Definition source_test p g := Sifthenelse (guard_test p g) (source_body p) (source_body p).
Definition target_test p g := Sifthenelse (guard_test p g)
  (target_body (aligned_pointer_plan p)) (target_body p).

Inductive guard_cursor (p: plan) (g: alignment_guard) (k: cont)
    : statement -> cont -> statement -> cont -> Prop :=
  | guard_start: guard_cursor p g k (guarded_source p g) k (guarded_target p g) k
  | guard_skip: guard_cursor p g k
      Sskip (Kseq (source_test p g) k) Sskip (Kseq (target_test p g) k)
  | guard_branch: guard_cursor p g k (source_test p g) k (target_test p g) k.

Inductive match_states : nat -> state -> state -> Prop :=
  | match_ordinary : forall s ts, ordinary_match s ts -> match_states O s ts
  | match_selected : forall p sf tf k rank s ts,
      well_formed p -> original_callers k -> is_call_cont k ->
      local_match ge tge p sf tf k k rank s ts -> match_states rank s ts
  | match_guarded : forall p g k s sk ts tk e le,
      well_formed p -> pointer_wide p = false -> valid_guard g = true ->
      original_callers k -> is_call_cont k ->
      guard_cursor p g k s sk ts tk ->
      forall m, match_states O
        (State (source_function p (Some g)) s sk e le m)
        (State (target_function p (Some g)) ts tk e (PTree.set (scratch p) Vundef le) m).

Lemma ordinary_step : forall s t after ts,
  step2 ge s t after -> ordinary_match s ts ->
  exists rank ta, plus step2 tge ts t ta /\ match_states rank after ta.
Proof.
  intros s t after ts STEP MATCHED. inv MATCHED.
  - destruct (step_normal _ _ _ _ _ _ _ _ STEP H H0) as [ta [ST MA]].
    exists O, ta; split. now apply plus_one. now constructor.
  - inv STEP.
    + destruct (selected f) as [[p g]|] eqn:SELECT.
      * destruct (selected_sound _ _ _ SELECT) as [-> [WF [NARROW VALID]]].
        assert (ENTER: step2 tge (Callstate (transf_fundef (Internal (source_function p g))) args k m)
          E0 (State (target_function p g) (fn_body (target_function p g)) k
              e (PTree.set (scratch p) Vundef le) m1)).
        { cbn [transf_fundef]. unfold transf_function. rewrite SELECT.
          apply step_internal_function. eapply entry_selected; eauto. }
        destruct g as [test|].
        -- exists O. eexists. split; [apply plus_one; exact ENTER|].
           eapply match_guarded; eauto. constructor.
        -- assert (BASE: base_ready p le) by (unfold base_ready; congruence).
           destruct (local_init ge tge p (source_template p) (target_template p) k e le Vundef m1 BASE)
             as [rank LM].
           exists rank. eexists. split; [apply plus_one; exact ENTER|].
           eapply match_selected; eauto.
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

Local Lemma guarded_step : forall p g k s sk ts tk e le m t after,
  well_formed p -> pointer_wide p = false -> valid_guard g = true ->
  original_callers k -> is_call_cont k -> guard_cursor p g k s sk ts tk ->
  step2 ge (State (source_function p (Some g)) s sk e le m) t after ->
  exists rank ta,
    plus step2 tge (State (target_function p (Some g)) ts tk e
      (PTree.set (scratch p) Vundef le) m) t ta /\ match_states rank after ta.
Proof.
  intros p g k s sk ts tk e le m t after WF NARROW VALID CALLERS CALL CURSOR STEP.
  destruct CURSOR.
  - unfold guarded_source, with_skip in STEP. inv STEP; cbn [is_call_cont] in *; try contradiction.
    exists O. eexists. split.
    + apply plus_one. apply step_seq.
    + eapply match_guarded; eauto. apply guard_skip.


  - inv STEP; cbn [is_call_cont] in *; try contradiction.
    exists O. eexists. split.
    + apply plus_one. apply step_skip_seq.
    + eapply match_guarded; eauto. apply guard_branch.
  - unfold source_test in STEP. inv STEP; cbn [is_call_cont] in *; try contradiction.
    match goal with
    | EV: eval_expr _ _ _ _ (guard_test p g) ?v,
      BOOL: bool_val ?v _ _ = Some ?b |- _ =>
        destruct (guard_test_replay _ _ _ _ _ _ _ _ VALID EV BOOL) as [REPLAY READY];
        assert (NEXT: step2 tge
          (State (target_function p (Some g)) (target_test p g) k e
            (PTree.set (scratch p) Vundef le) m) E0
          (State (target_function p (Some g))
            (if b then target_body (aligned_pointer_plan p) else target_body p) k e
            (PTree.set (scratch p) Vundef le) m))
          by (unfold target_test; eapply step_ifthenelse; eauto);
        destruct b
    end.
    + destruct (local_init ge tge (aligned_pointer_plan p)
        (source_function p (Some g)) (target_function p (Some g))
        k e le Vundef m (READY eq_refl)) as [rank LM].
      exists rank. eexists. split; [apply plus_one; exact NEXT|].
      eapply match_selected with (p := aligned_pointer_plan p) (k := k); eauto.
    + assert (BASE: base_ready p le) by (unfold base_ready; congruence).
      destruct (local_init ge tge p (source_function p (Some g)) (target_function p (Some g))
        k e le Vundef m BASE) as [rank LM].
      exists rank. eexists. split; [apply plus_one; exact NEXT|].
      eapply match_selected with (p := p) (k := k); eauto.
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
  - destruct (local_step ge tprog _ _ _ _ _ _ _ _ _ blocks_preserved symbols_preserved H H1 H2 STEP) as [j [ta [ST MA]]].
    assert (SIM: plus step2 tge ts t ta \/ (star step2 tge ts t ta /\ (j < rank)%nat)).
    { destruct ST as [PLUS|[-> [-> LT]]]; auto using star_refl. }
    destruct MA as [LOOP|[v [m [-> ->]]]].
    + exists j, ta. split; auto. eapply match_selected; eauto.
    + exists O, (Returnstate v k m). split.
      * destruct SIM as [PLUS|[STAR LT]]; auto. right. split; auto; lia.
      * constructor. constructor; auto.
  - destruct (guarded_step _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4 STEP)
      as [j [ta [ST MA]]].
    exists j, ta. auto.
Qed.

Lemma program_simulation : forward_simulation (semantics2 prog) (semantics2 tprog).
Proof.
  apply Forward_simulation with lt match_states; constructor.
  - apply lt_wf.
  - intros s INIT. destruct (initial_simulation _ INIT) as [ts [TI TM]].
    exists O, ts; split; auto. now constructor.
  - intros rank s ts r M FINAL. inv M.
    + inv FINAL. inv H. constructor.
    + inv FINAL. inv H2.
    + inv FINAL.
  - intros. eapply steps_simulate; eauto.
  - exact (proj1 (proj2 senv_preserved)).
Qed.

End PROGRAM.

Theorem transf_program_correct : forall prog tprog,
  match_prog prog tprog -> forward_simulation (semantics2 prog) (semantics2 tprog).
Proof. exact program_simulation. Qed.

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
Require Import ArrayPairBase ArrayPairTarget ArrayPairLocal ArrayPairContext ArrayPairCallproof.
Require ArrayPairTurn.

Definition match_prog := ArrayPairContext.match_prog.
Definition transf_program_match := ArrayPairContext.transf_program_match.

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
Proof. exact (Genv.find_symbol_match (proj1 MATCH)). Qed.

Lemma senv_preserved : Senv.equiv ge tge.
Proof. exact (Genv.senv_match (proj1 MATCH)). Qed.

Lemma type_preserved : forall cu fd, type_of_fundef (transf_fundef cu fd) = type_of_fundef fd.
Proof.
  intros cu [f|]; simpl; auto. unfold transf_function.
  destruct (selected_call cu f) as [c|] eqn:SELECT.
  - apply selected_call_sound in SELECT as [-> _]. reflexivity.
  - unfold type_of_function.
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
      ordinary_match (State f s k e le m) (State f s k e le m)
  | match_call : forall cu fd args k m,
      linkorder cu prog -> is_call_cont k ->
      ordinary_match (Callstate fd args k m) (Callstate (transf_fundef cu fd) args k m)
  | match_return : forall v k m,
      ordinary_match (Returnstate v k m) (Returnstate v k m).

Local Hint Resolve exprlist_preserved : core.
Local Hint Extern 2 (eval_expr tge _ _ _ _ _) => eapply (proj1 (eval_preserved _ _ _)) : core.
Local Hint Extern 2 (eval_lvalue tge _ _ _ _ _ _ _) => eapply (proj2 (eval_preserved _ _ _)) : core.

Lemma step_normal : forall f s k e le m t after,
  step2 ge (State f s k e le m) t after ->
  exists ta, step2 tge (State f s k e le m) t ta /\ ordinary_match after ta.
Proof.
  intros until after. intros STEP. inv STEP;
    try solve [eexists; split; [econstructor; eauto | constructor]].
  - eexists; split.
    + eapply step_assign; eauto. rewrite comp_env_preserved; eauto.
    + constructor; auto.
  - match goal with H: Genv.find_funct _ _ = Some _ |- _ =>
      destruct (find_funct_translated _ _ MATCH _ _ H) as [cu [tf [FIND [-> LINK]]]]
    end.
    eexists; split.
    + eapply step_call with (fd := transf_fundef cu fd); eauto.
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
Qed.

Lemma initial_simulation : forall s,
  initial_state prog s -> exists ts, initial_state tprog ts /\ ordinary_match s ts.
Proof.
  intros s INIT. inv INIT.
  match goal with H: Genv.find_funct_ptr _ _ = Some _ |- _ =>
    destruct (find_funct_ptr_translated _ _ MATCH _ _ H) as [cu [tf [FIND [-> LINK]]]]
  end.
  exists (Callstate (transf_fundef cu f) nil Kstop m0). split.
  - eapply initial_state_intro with (b := b).
    + eapply (Genv.init_mem_match (proj1 MATCH)); eauto.
    + rewrite symbols_preserved.
      exact (eq_trans (f_equal (Genv.find_symbol ge) (match_program_gen_main _ _ _ _ _ (proj1 MATCH))) H0).
    + exact FIND.
    + rewrite type_preserved; eauto.
  - constructor; simpl; auto.
Qed.

Definition source_test p g := Sifthenelse (guard_test p g) (source_body p) (source_body p).
Definition target_test p g := Sifthenelse (guard_test p g)
  (target_body (aligned_pointer_plan p)) (target_body p).

Inductive entry_cursor (src dst: statement) (k: cont)
    : statement -> cont -> statement -> cont -> Prop :=
  | entry_start: entry_cursor src dst k (with_skip src) k (with_skip dst) k
  | entry_skip: entry_cursor src dst k Sskip (Kseq src k) Sskip (Kseq dst k)
  | entry_body: entry_cursor src dst k src k dst k.

Definition worker_cont (c: call_plan) (n: val) (k: cont) :=
  Kcall None (caller_source c) empty_env (caller_env c n) k.

Inductive return_context : cont -> cont -> Prop :=
  | return_shared: forall k, is_call_cont k -> return_context k k
  | return_inlined: forall c n k, is_call_cont k -> return_context (worker_cont c n k) k.

Record call_witness (c: call_plan) : Prop := {
  call_well_formed: well_formed (call_loop c);
  call_is_pointer: array_anchor (call_loop c) = None;
  call_is_aligned: valid_guard (call_address c) = true;
  call_local_worker: exists cu, linkorder cu prog /\
    (AST.prog_defmap cu)!(call_worker c) =
      Some (Gfun (Internal (source_template (call_loop c))))
}.

Inductive match_states : nat -> state -> state -> Prop :=
  | match_ordinary : forall s ts, ordinary_match s ts -> match_states O s ts
  | match_selected : forall p sf tf k tk rank s ts,
      well_formed p -> return_context k tk ->
      local_match ge tge p sf tf k tk rank s ts -> match_states rank s ts
  | match_guarded : forall p g k s sk ts tk e le,
      well_formed p -> pointer_wide p = false -> valid_guard g = true ->
      is_call_cont k ->
      entry_cursor (source_test p g) (target_test p g) k s sk ts tk ->
      forall m, match_states O
        (State (source_function p (Some g)) s sk e le m)
        (State (target_function p (Some g)) ts tk e (PTree.set (scratch p) Vundef le) m)
  | match_caller: forall c k s sk ts tk n m,
      call_witness c -> is_call_cont k ->
      entry_cursor (caller_call c) (caller_setup c) k s sk ts tk ->
      match_states 1%nat
        (State (caller_source c) s sk empty_env (caller_env c n) m)
        (State (caller_target c) ts tk empty_env (target_caller_env c n) m)
  | match_worker_entry: forall c k n ptr m,
      well_formed (call_loop c) -> array_anchor (call_loop c) = None -> is_call_cont k ->
      eval_expr tge empty_env (target_caller_env c n) m (guard_address (call_address c)) ptr ->
      base_ready (aligned_pointer_plan (call_loop c)) (worker_env (call_loop c) ptr n) ->
      match_states O
        (Callstate (Internal (source_template (call_loop c))) (ptr :: n :: nil) (worker_cont c n k) m)
        (State (caller_target c) (caller_setup c) k empty_env (target_caller_env c n) m)
  | match_worker_return: forall c k n m,
      is_call_cont k ->
      match_states 2%nat (Returnstate Vundef (worker_cont c n k) m) (Returnstate Vundef k m)
  | match_caller_return: forall c k n m,
      is_call_cont k ->
      match_states 1%nat (State (caller_source c) Sskip k empty_env (caller_env c n) m)
        (Returnstate Vundef k m).

Lemma ordinary_step : forall s t after ts,
  step2 ge s t after -> ordinary_match s ts ->
  exists rank ta, plus step2 tge ts t ta /\ match_states rank after ta.
Proof.
  intros s t after ts STEP MATCHED. inv MATCHED.
  - destruct (step_normal _ _ _ _ _ _ _ _ STEP) as [ta [ST MA]].
    exists O, ta; split. now apply plus_one. now constructor.
  - inv STEP.
    + destruct (selected_call cu f) as [c|] eqn:SELECT_CALL.
      * destruct (selected_call_sound _ _ _ SELECT_CALL)
          as [-> [ALIGN [WORKER [WF [NARROW [NOARRAY [i INDEX]]]]]]].
        match goal with ENTRY: function_entry2 _ (caller_source c) _ _ _ _ _ |- _ =>
          apply caller_entry_inv in ENTRY as [-> [-> [n [-> ->]]]]
        end.
        exists 1%nat. eexists. split.
        -- apply plus_one. cbn [transf_fundef]. unfold transf_function. rewrite SELECT_CALL.
           apply step_internal_function. eapply caller_entry_target; eauto.
        -- eapply match_caller; eauto.
           ++ constructor; eauto.
           ++ apply entry_start.
      * destruct (selected f) as [[p g]|] eqn:SELECT.
        -- destruct (selected_sound _ _ _ SELECT) as [-> [WF [NARROW VALID]]].
           assert (ENTER: step2 tge
             (Callstate (transf_fundef cu (Internal (source_function p g))) args k m)
             E0 (State (target_function p g) (fn_body (target_function p g)) k
                 e (PTree.set (scratch p) Vundef le) m1)).
           { cbn [transf_fundef]. unfold transf_function, local_transf_function.
             rewrite SELECT_CALL, SELECT.
             apply step_internal_function. eapply entry_selected; eauto. }
           destruct g as [test|].
           ++ exists O. eexists. split; [apply plus_one; exact ENTER|].
              eapply match_guarded; eauto. constructor.
           ++ assert (BASE: base_ready p le) by (unfold base_ready; congruence).
              destruct (local_init ge tge p (source_template p) (target_template p)
                k k e le Vundef m1 BASE) as [rank LM].
              exists rank. eexists. split; [apply plus_one; exact ENTER|].
              eapply match_selected; eauto using return_shared.
        -- exists O, (State f (fn_body f) k e le m1). split.
           ++ cbn [transf_fundef]. unfold transf_function, local_transf_function.
              rewrite SELECT_CALL, SELECT.
              apply plus_one. apply step_internal_function. eapply entry_preserved; eauto.
           ++ constructor. constructor.
    + exists O, (Returnstate vres k m'). split.
      * apply plus_one. eapply step_external_function.
        eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      * constructor. constructor.
  - inv STEP.
    exists O, (State f Sskip k0 e (set_opttemp optid v le) m). split.
    + apply plus_one. constructor.
    + constructor. constructor.
Qed.

Local Lemma guarded_step : forall p g k s sk ts tk e le m t after,
  well_formed p -> pointer_wide p = false -> valid_guard g = true ->
  is_call_cont k -> entry_cursor (source_test p g) (target_test p g) k s sk ts tk ->
  step2 ge (State (source_function p (Some g)) s sk e le m) t after ->
  exists rank ta,
    plus step2 tge (State (target_function p (Some g)) ts tk e
      (PTree.set (scratch p) Vundef le) m) t ta /\ match_states rank after ta.
Proof.
  intros p g k s sk ts tk e le m t after WF NARROW VALID CALL CURSOR STEP.
  destruct CURSOR.
  - unfold with_skip in STEP. inv STEP; cbn [is_call_cont] in *; try contradiction.
    exists O. eexists. split.
    + apply plus_one. apply step_seq.
    + eapply match_guarded; eauto. apply entry_skip.
  - inv STEP; cbn [is_call_cont] in *; try contradiction.
    exists O. eexists. split.
    + apply plus_one. apply step_skip_seq.
    + eapply match_guarded; eauto. apply entry_body.
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
        k k e le Vundef m (READY eq_refl)) as [rank LM].
      exists rank. eexists. split; [apply plus_one; exact NEXT|].
      eapply match_selected with (p := aligned_pointer_plan p) (k := k) (tk := k); eauto using return_shared.
    + assert (BASE: base_ready p le) by (unfold base_ready; congruence).
      destruct (local_init ge tge p (source_function p (Some g)) (target_function p (Some g))
        k k e le Vundef m BASE) as [rank LM].
      exists rank. eexists. split; [apply plus_one; exact NEXT|].
      eapply match_selected with (p := p) (k := k) (tk := k); eauto using return_shared.
Qed.

Local Lemma caller_step : forall c k s sk ts tk n m t after,
  call_witness c -> is_call_cont k ->
  entry_cursor (caller_call c) (caller_setup c) k s sk ts tk ->
  step2 ge (State (caller_source c) s sk empty_env (caller_env c n) m) t after ->
  let target := State (caller_target c) ts tk empty_env (target_caller_env c n) m in
  exists rank ta,
    (plus step2 tge target t ta \/ (star step2 tge target t ta /\ (rank < 1)%nat)) /\
    match_states rank after ta.
Proof.
  intros c k s sk ts tk n m t after WITNESS CALL CURSOR STEP. cbn zeta.
  destruct CURSOR.
  - unfold with_skip in STEP. inv STEP; cbn [is_call_cont] in *; try contradiction.
    exists 1%nat. eexists. split.
    + left. apply plus_one. apply step_seq.
    + eapply match_caller; eauto. apply entry_skip.
  - inv STEP; cbn [is_call_cont] in *; try contradiction.
    exists 1%nat. eexists. split.
    + left. apply plus_one. apply step_skip_seq.
    + eapply match_caller; eauto. apply entry_body.
  - destruct WITNESS as [WF NOARRAY VALID [cu [LINK WORKER]]].
    assert (ADDRESS: forall v,
      eval_expr ge empty_env (caller_env c n) m (guard_address (call_address c)) v ->
      exists b ofs, v = Vptr b ofs).
    { intros v EV. destruct (guard_address_replay _ _ _ _ _ _ VALID EV) as (b & ofs & EQ & _).
      eauto. }
    destruct (caller_call_inv cu prog c _ m k t after n LINK WORKER NOARRAY
      (caller_env_count c n) ADDRESS STEP) as [-> (b & ofs & EVAL & ->)].
    destruct (guard_address_replay _ _ _ _ _ _ VALID EVAL)
      as (blk & off & EQ & ALIGN & REPLAY). inv EQ.
    exists O, (State (caller_target c) (caller_setup c) k empty_env (target_caller_env c n) m).
    split; [right; split; [apply star_refl|lia]|].
    unfold worker_cont. apply match_worker_entry; auto.
    unfold base_ready. cbn [aligned_pointer_plan pointer].
    intros _ other delta PTR. rewrite worker_env_pointer in PTR by exact WF. inv PTR.
    exact ALIGN.
Qed.

Local Lemma worker_entry_step : forall c k n ptr m t after,
  well_formed (call_loop c) -> array_anchor (call_loop c) = None -> is_call_cont k ->
  eval_expr tge empty_env (target_caller_env c n) m (guard_address (call_address c)) ptr ->
  base_ready (aligned_pointer_plan (call_loop c)) (worker_env (call_loop c) ptr n) ->
  step2 ge (Callstate (Internal (source_template (call_loop c))) (ptr :: n :: nil)
    (worker_cont c n k) m) t after ->
  exists rank ta,
    plus step2 tge
      (State (caller_target c) (caller_setup c) k empty_env (target_caller_env c n) m) t ta /\
    match_states rank after ta.
Proof.
  intros c k n ptr m t after WF NOARRAY CALL EVAL BASE STEP. inv STEP.
  match goal with ENTRY: function_entry2 _ (source_template (call_loop c)) _ _ _ _ _ |- _ =>
    apply (worker_entry_inv _ _ _ _ _ _ _ _ NOARRAY) in ENTRY as [-> [-> ->]]
  end.
  destruct (local_init ge tge (aligned_pointer_plan (call_loop c))
    (source_template (call_loop c)) (caller_target c) (worker_cont c n k) k
    empty_env (worker_env (call_loop c) ptr n) Vundef m BASE) as [rank LOOP].
  exists rank. eexists. split.
  - exact (caller_setup_exec tge c k m ptr n WF EVAL).
  - eapply match_selected with (p := aligned_pointer_plan (call_loop c)); eauto using return_inlined.
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
  - assert (CALLS: is_call_cont k /\ is_call_cont tk) by (inv H0; simpl; auto).
    destruct CALLS as [CALL TCALL].
    destruct (local_step ge tprog p sf tf k tk rank s t after ts
      blocks_preserved symbols_preserved H CALL TCALL H1 STEP) as [j [ta [ST MA]]].
    destruct MA as [LOOP|[m [-> ->]]].
    + exists j, ta. split.
      * destruct ST as [PLUS|[-> [-> LT]]]; auto using star_refl.
      * eapply match_selected; eauto.
    + destruct ST as [PLUS|[_ [EQ _]]]; [|rewrite <- EQ in H1; inv H1].
      inv H0.
      * exists O, (Returnstate Vundef tk m). split; [now left|].
        constructor. constructor.
      * exists 2%nat, (Returnstate Vundef tk m). split; [now left|].
        now constructor.
  - destruct (guarded_step _ _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3 STEP)
      as [j [ta [ST MA]]].
    exists j, ta. auto.
  - eapply caller_step; eauto.
  - destruct (worker_entry_step _ _ _ _ _ _ _ H H0 H1 H2 H3 STEP)
      as [j [ta [ST MA]]].
    exists j, ta. auto.
  - unfold worker_cont in STEP. inv STEP.
    exists 1%nat, (Returnstate Vundef k m). split.
    + right. split; [apply star_refl|lia].
    + now constructor.
  - inv STEP; cbn [is_call_cont] in *; try contradiction.
    match goal with FREE: Mem.free_list _ _ = Some _ |- _ =>
      cbn [blocks_of_env empty_env PTree.elements Mem.free_list] in FREE; inv FREE
    end.
    exists O. eexists. split.
    + right. split; [apply star_refl|lia].
    + constructor. constructor.
Qed.

Lemma program_simulation : forward_simulation (semantics2 prog) (semantics2 tprog).
Proof.
  apply Forward_simulation with lt match_states; constructor.
  - apply lt_wf.
  - intros s INIT. destruct (initial_simulation _ INIT) as [ts [TI TM]].
    exists O, ts; split; auto. now constructor.
  - intros rank s ts r M FINAL. inv M.
    + inv FINAL. inv H. constructor.
    + inv FINAL. inv H1.
    + inv FINAL.
    + inv FINAL.
    + inv FINAL.
    + inv FINAL.
    + inv FINAL.
  - intros. eapply steps_simulate; eauto.
  - exact (proj1 (proj2 senv_preserved)).
Qed.

End PROGRAM.

Theorem transf_program_correct : forall prog tprog,
  match_prog prog tprog -> forward_simulation (semantics2 prog) (semantics2 tprog).
Proof. exact program_simulation. Qed.

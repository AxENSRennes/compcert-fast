(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(* Correctness of a constrained, pure adjacent-instruction scheduler.
   Distributed under the INRIA Non-Commercial License Agreement. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Schedule.

Record valid_pair (f: function) (pair: scheduled_pair) : Prop := {
  valid_first: (fn_code f)!(first_pc pair) =
    Some (Iop (first_op pair) (first_args pair) (first_dst pair) (second_pc pair));
  valid_second: (fn_code f)!(second_pc pair) =
    Some (Iop (second_op pair) (second_args pair) (second_dst pair) (after_pc pair));
  different_pcs: first_pc pair <> second_pc pair;
  safe_entry: fn_entrypoint f <> second_pc pair;
  different_dsts: first_dst pair <> second_dst pair;
  independent_second: ~ In (first_dst pair) (second_args pair);
  independent_first: ~ In (second_dst pair) (first_args pair);
  unique_predecessor: forall pc instr,
    (fn_code f)!pc = Some instr -> In (second_pc pair) (successors_instr instr) ->
    pc = first_pc pair
}.

Lemma predecessor_check_sound:
  forall f a b, predecessor_check f a b = true ->
  forall pc instr, (fn_code f)!pc = Some instr ->
  In b (successors_instr instr) -> pc = a.
Proof.
  unfold predecessor_check; intros f a b CHECK pc instr GET IN.
  rewrite forallb_forall in CHECK.
  assert (MEMBER: In (pc,instr) (PTree.elements (fn_code f)))
    by (apply PTree.elements_correct; auto).
  specialize (CHECK (pc,instr) MEMBER). simpl in CHECK.
  destruct (in_dec peq b (successors_instr instr)); try contradiction.
  destruct (peq pc a); congruence.
Qed.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof. intros. eapply match_transform_program; eauto. Qed.

Lemma validate_candidate_sound:
  forall f a b pair, validate_candidate f a b = Some pair -> valid_pair f pair.
Proof.
  unfold validate_candidate; intros f a b pair.
  destruct (fn_code f)!a as [i|] eqn:FIRST; try discriminate.
  destruct i; try discriminate.
  destruct (fn_code f)!b as [i|] eqn:SECOND; try discriminate.
  destruct i; try discriminate.
  destruct (peq n b); try discriminate. subst n.
  destruct (peq a b); try discriminate.
  destruct (peq (fn_entrypoint f) b); try discriminate.
  destruct (peq r r0); try discriminate.
  destruct (in_dec peq r l0); try discriminate.
  destruct (in_dec peq r0 l); try discriminate.
  destruct (predecessor_check f a b) eqn:PRED; try discriminate.
  intro EQ; inv EQ. constructor; simpl; auto.
  eapply predecessor_check_sound; eauto.
Qed.

Lemma find_candidate_sound:
  forall f nodes pair, find_candidate f nodes = Some pair -> valid_pair f pair.
Proof.
  induction nodes; simpl; intros; try discriminate.
  destruct (fn_code f)!a as [i|] eqn:GET; eauto.
  destruct i; eauto.
  destruct (validate_candidate f a n) eqn:VAL; eauto.
  inv H. eapply validate_candidate_sound; eauto.
Qed.

Lemma selected_pair_sound:
  forall f pair, selected_pair f = Some pair -> valid_pair f pair.
Proof. unfold selected_pair; intros; eapply find_candidate_sound; eauto. Qed.

Lemma regs_set_disjoint:
  forall (rs: regset) (dst: reg) (value: val) (args: list reg), ~ In dst args ->
  (rs#dst <- value) ## args = rs ## args.
Proof.
  induction args; simpl; intros; auto.
  rewrite Regmap.gso by tauto. f_equal. apply IHargs. tauto.
Qed.

Lemma regs_set_commute:
  forall (rs: regset) d1 d2 v1 v2, d1 <> d2 ->
  (rs#d1 <- v1)#d2 <- v2 = (rs#d2 <- v2)#d1 <- v1.
Proof.
  intros [default values] d1 d2 v1 v2 NE.
  unfold Regmap.set, PMap.set; simpl. f_equal.
  apply PTree.extensionality; intro r. rewrite !PTree.gsspec.
  destruct (peq r d1), (peq r d2); congruence.
Qed.

Definition safe_pc (f: function) (pc: node) : Prop :=
  match selected_pair f with Some plan => pc <> second_pc plan | None => True end.

Lemma metadata_preserved:
  forall f,
  fn_sig (transf_function f) = fn_sig f /\
  fn_stacksize (transf_function f) = fn_stacksize f /\
  fn_params (transf_function f) = fn_params f /\
  fn_entrypoint (transf_function f) = fn_entrypoint f.
Proof. unfold transf_function; intros; destruct (selected_pair f); simpl; tauto. Qed.

Lemma entry_safe:
  forall f, safe_pc f (fn_entrypoint f).
Proof.
  unfold safe_pc; intros. destruct (selected_pair f) as [pair|] eqn:SELECT; auto.
  eapply safe_entry. eapply selected_pair_sound; eauto.
Qed.

Lemma transformed_first:
  forall f pair, selected_pair f = Some pair ->
  (fn_code (transf_function f))!(first_pc pair) =
    Some (Iop (second_op pair) (second_args pair) (second_dst pair) (second_pc pair)).
Proof. unfold transf_function; intros. rewrite H. simpl. apply PTree.gss. Qed.

Lemma transformed_second:
  forall f pair, selected_pair f = Some pair ->
  (fn_code (transf_function f))!(second_pc pair) =
    Some (Iop (first_op pair) (first_args pair) (first_dst pair) (after_pc pair)).
Proof.
  unfold transf_function; intros. rewrite H. simpl. rewrite PTree.gso.
  apply PTree.gss.
  assert (first_pc pair <> second_pc pair).
  { eapply different_pcs. eapply selected_pair_sound; eauto. }
  congruence.
Qed.

Lemma normal_classification:
  forall f pc, safe_pc f pc ->
  (exists pair, selected_pair f = Some pair /\ pc = first_pc pair) \/
  ((fn_code (transf_function f))!pc = (fn_code f)!pc /\
   forall instr next, (fn_code f)!pc = Some instr ->
     In next (successors_instr instr) -> safe_pc f next).
Proof.
  intros f pc SAFE. unfold safe_pc in SAFE.
  destruct (selected_pair f) as [pair|] eqn:SELECT.
  - destruct (peq pc (first_pc pair)).
    + left. eauto.
    + right. split.
      * unfold transf_function. rewrite SELECT. simpl. rewrite !PTree.gso; auto.
      * unfold safe_pc. rewrite SELECT. intros instr next GET IN EQ. subst next.
        apply n. eapply unique_predecessor; eauto. eapply selected_pair_sound; eauto.
  - right. split.
    + unfold transf_function. rewrite SELECT. auto.
    + unfold safe_pc. rewrite SELECT. auto.
Qed.

Section PRESERVATION.
Variables prog tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma functions_translated:
  forall v f, Genv.find_funct ge v = Some f ->
  Genv.find_funct tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated:
  forall v f, Genv.find_funct_ptr ge v = Some f ->
  Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof. destruct f; simpl; auto. apply metadata_preserved. Qed.
Lemma find_function_translated:
  forall ros rs fd, find_function ge ros rs = Some fd ->
  find_function tge ros rs = Some (transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  eapply functions_translated; eauto.
  rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
  eapply function_ptr_translated; eauto.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frame: forall res f sp pc rs (SAFE: safe_pc f pc),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp pc rs).

Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_normal: forall stk f sp pc rs m stk'
      (STACKS: list_forall2 match_frames stk stk') (SAFE: safe_pc f pc),
      match_states (State stk f sp pc rs m)
        (State stk' (transf_function f) sp pc rs m)
  | match_intermediate: forall stk f sp rs m stk' plan value
      (STACKS: list_forall2 match_frames stk stk')
      (SELECT: selected_pair f = Some plan)
      (EVAL: eval_operation ge sp (first_op plan) rs##(first_args plan) m = Some value),
      match_states
        (State stk f sp (second_pc plan) (rs#(first_dst plan) <- value) m)
        (State stk' (transf_function f) sp (first_pc plan) rs m)
  | match_call: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | match_return: forall stk value m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk value m) (Returnstate stk' value m).

Definition measure (st: RTL.state) : nat :=
  match st with
  | State _ f _ pc _ _ =>
      match selected_pair f with
      | Some plan => if peq pc (second_pc plan) then O else S O
      | None => S O
      end
  | _ => S O
  end.

Lemma normal_step:
  forall stk f sp pc rs m trace after,
  RTL.step ge (State stk f sp pc rs m) trace after ->
  forall stk', list_forall2 match_frames stk stk' -> safe_pc f pc ->
  (exists target, plus RTL.step tge (State stk' (transf_function f) sp pc rs m) trace target /\
     match_states after target) \/
  (measure after < measure (State stk f sp pc rs m) /\ trace = E0 /\
     match_states after (State stk' (transf_function f) sp pc rs m))%nat.
Proof.
  intros stk f sp pc rs m trace after STEP stk' STACKS SAFE.
  destruct (normal_classification f pc SAFE) as [[plan [SELECT PC]] | [GET NEXT]].
  - subst pc. pose proof (selected_pair_sound _ _ SELECT) as VALID.
    pose proof (valid_first _ _ VALID) as FIRST.
    inversion STEP; subst; try congruence.
    rewrite FIRST in H7. inv H7.
    right. split.
    + unfold measure. rewrite SELECT. simpl.
      destruct (peq (second_pc plan) (second_pc plan)); try congruence.
      destruct (peq (first_pc plan) (second_pc plan)); simpl; try lia.
      elim (different_pcs _ _ VALID). auto.
    + split; auto. econstructor; eauto.
  - inversion STEP; subst.
    + left. econstructor; split.
      apply plus_one. eapply exec_Inop; eauto. rewrite GET; eauto.
      constructor; auto. eapply NEXT; eauto. simpl; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Iop; eauto. rewrite GET; eauto.
      instantiate (1 := v). rewrite <- H8. apply eval_operation_preserved. exact symbols_preserved.
      constructor; auto. eapply NEXT; eauto. simpl; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Iload; eauto. rewrite GET; eauto.
      rewrite <- H8. apply eval_addressing_preserved. exact symbols_preserved.
      constructor; auto. eapply NEXT; eauto. simpl; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Istore; eauto. rewrite GET; eauto.
      rewrite <- H8. apply eval_addressing_preserved. exact symbols_preserved.
      constructor; auto. eapply NEXT; eauto. simpl; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Icall with (fd := transf_fundef fd); eauto.
      rewrite GET, sig_preserved; eauto. eapply find_function_translated; eauto.
      constructor. constructor; auto. constructor. eapply NEXT; eauto. simpl; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
      rewrite GET, sig_preserved; eauto. eapply find_function_translated; eauto.
      rewrite (proj1 (proj2 (metadata_preserved f))); eauto.
      constructor; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Ibuiltin; eauto. rewrite GET; eauto.
      eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      constructor; auto. eapply NEXT; eauto. simpl; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Icond; eauto. rewrite GET; eauto.
      constructor; auto. eapply NEXT; eauto. simpl. destruct b; auto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Ijumptable; eauto. rewrite GET; eauto.
      constructor; auto. eapply NEXT; eauto. simpl. eapply list_nth_z_in; eauto.
    + left. econstructor; split.
      apply plus_one. eapply exec_Ireturn; eauto. rewrite GET; eauto.
      rewrite (proj1 (proj2 (metadata_preserved f))); eauto.
      constructor; auto.
Qed.

Lemma after_safe:
  forall f plan, selected_pair f = Some plan -> safe_pc f (after_pc plan).
Proof.
  intros f plan SELECT. pose proof (selected_pair_sound _ _ SELECT) as VALID.
  unfold safe_pc. rewrite SELECT. intro EQ.
  assert (second_pc plan = first_pc plan).
  { eapply unique_predecessor; eauto. eapply valid_second; eauto.
    simpl. left. symmetry. auto. }
  elim (different_pcs _ _ VALID). congruence.
Qed.

Lemma intermediate_step:
  forall stk f sp rs m plan value trace after,
  selected_pair f = Some plan ->
  eval_operation ge sp (first_op plan) rs##(first_args plan) m = Some value ->
  RTL.step ge (State stk f sp (second_pc plan) (rs#(first_dst plan) <- value) m) trace after ->
  forall stk', list_forall2 match_frames stk stk' ->
  exists target,
    plus RTL.step tge (State stk' (transf_function f) sp (first_pc plan) rs m) trace target /\
    match_states after target.
Proof.
  intros stk f sp rs m plan value trace after SELECT EVAL STEP stk' STACKS.
  pose proof (selected_pair_sound _ _ SELECT) as VALID.
  pose proof (valid_second _ _ VALID) as SECOND.
  inversion STEP; subst; try congruence.
  rewrite SECOND in H7. inv H7.
  rewrite regs_set_disjoint in H8 by (eapply independent_second; eauto).
  exists (State stk' (transf_function f) sp (after_pc plan)
                 (((rs#(first_dst plan) <- value))#(second_dst plan) <- v) m).
  split.
  - rewrite regs_set_commute by (eapply different_dsts; eauto).
    eapply plus_two.
    + eapply exec_Iop. eapply transformed_first; eauto.
      rewrite <- H8. apply eval_operation_preserved. exact symbols_preserved.
    + eapply exec_Iop. eapply transformed_second; eauto.
      rewrite regs_set_disjoint by (eapply independent_first; eauto).
      rewrite <- EVAL. apply eval_operation_preserved. exact symbols_preserved.
    + reflexivity.
  - constructor; auto. eapply after_safe; eauto.
Qed.

Lemma step_simulation:
  forall source trace after,
  RTL.step ge source trace after ->
  forall target, match_states source target ->
  (exists target_after, plus RTL.step tge target trace target_after /\
                        match_states after target_after) \/
  (measure after < measure source /\ trace = E0 /\ match_states after target)%nat.
Proof.
  intros source trace after STEP target MATCH. inv MATCH.
  - eapply normal_step; eauto.
  - left. eapply intermediate_step; eauto.
  - inversion STEP; subst.
    + left. destruct (metadata_preserved f) as [SIG [STACK [PARAM ENTRY]]].
      exists (State stk' (transf_function f) (Vptr stk0 Ptrofs.zero)
                    (fn_entrypoint f) (init_regs args (fn_params f)) m'). split.
      * apply plus_one.
        assert (RUN: RTL.step tge (Callstate stk' (Internal (transf_function f)) args m)
          E0 (State stk' (transf_function f) (Vptr stk0 Ptrofs.zero)
             (fn_entrypoint (transf_function f))
             (init_regs args (fn_params (transf_function f))) m')).
        { eapply exec_function_internal; rewrite ?SIG, ?STACK; eauto. }
        rewrite ENTRY, PARAM in RUN. exact RUN.
      * constructor; auto. apply entry_safe.
    + left. econstructor; split. apply plus_one.
      eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto. apply senv_preserved.
      constructor; auto.
  - inversion STEP; subst. inv STACKS. inv H1.
    left. econstructor; split. apply plus_one. eapply exec_return; eauto.
    constructor; auto.
Qed.

Lemma transf_initial_states:
  forall source, RTL.initial_state prog source ->
  exists target, RTL.initial_state tprog target /\ match_states source target.
Proof.
  intros. inv H. econstructor; split. econstructor.
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
  eapply function_ptr_translated; eauto.
  rewrite <- H3. apply sig_preserved.
  constructor. constructor.
Qed.

Lemma transf_final_states:
  forall source target result,
  match_states source target -> RTL.final_state source result -> RTL.final_state target result.
Proof. intros. inv H0. inv H. inv STACKS. constructor. Qed.

Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved.
  exact transf_initial_states.
  exact transf_final_states.
  exact step_simulation.
Qed.

End PRESERVATION.

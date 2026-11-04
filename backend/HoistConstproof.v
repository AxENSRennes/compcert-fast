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

(** Semantic preservation of pure constant hoisting. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL HoistConst.

Lemma fresh_reg_use:
  forall f pc i r, (fn_code f)!pc = Some i -> In r (instr_uses i) -> Plt r (fresh_reg f).
Proof. unfold fresh_reg; intros. generalize (max_reg_function_use _ _ _ _ H H0). extlia. Qed.
Lemma fresh_reg_def:
  forall f pc i r, (fn_code f)!pc = Some i -> instr_defs i = Some r -> r <> fresh_reg f.
Proof. unfold fresh_reg; intros. generalize (max_reg_function_def _ _ _ _ H H0). extlia. Qed.
Lemma fresh_node_ne:
  forall f pc i, (fn_code f)!pc = Some i -> pc <> fresh_node f.
Proof. unfold fresh_node; intros. generalize (max_pc_function_sound _ _ _ H). extlia. Qed.

Definition regs_match (f: function) (rs trs: regset) : Prop :=
  (forall r, Plt r (fresh_reg f) -> trs#r = rs#r) /\
  match chosen f with Some n => trs#(fresh_reg f) = Vint n | None => True end.

Lemma regs_match_list:
  forall f rs trs rl,
  regs_match f rs trs -> (forall r, In r rl -> Plt r (fresh_reg f)) -> trs##rl = rs##rl.
Proof. intros f rs trs rl [A B] C. apply list_map_exten. intros; symmetry; apply A; auto. Qed.

Lemma regs_match_set:
  forall f rs trs r v,
  regs_match f rs trs -> r <> fresh_reg f ->
  regs_match f (rs#r <- v) (trs#r <- v).
Proof.
  intros f rs trs r v [A B] NE. split.
  - intros x LT. rewrite !Regmap.gsspec. destruct (peq x r); auto.
  - destruct (chosen f); auto. rewrite Regmap.gso; congruence.
Qed.

Lemma regs_match_setres:
  forall f rs trs res v,
  regs_match f rs trs ->
  (match res with BR r => r <> fresh_reg f | _ => True end) ->
  regs_match f (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto. apply regs_match_set; auto. Qed.

Inductive instr_spec (f: function): instruction -> instruction -> Prop :=
  | instr_default: forall i, instr_spec f i i
  | instr_hoisted: forall n r s,
      chosen f = Some n ->
      instr_spec f (Iop (Ointconst n) nil r s) (Iop Omove (fresh_reg f :: nil) r s).

Lemma transf_instr_spec:
  forall f i, instr_spec f i (transf_instr f i).
Proof.
  intros f i. destruct i; try constructor.
  destruct o; try constructor. destruct l; try constructor.
  unfold transf_instr.
  destruct (chosen f) as [k|] eqn:CHOICE; try constructor.
  destruct (Int.eq k n0) eqn:E.
  - apply Int.same_if_eq in E. subst n0. apply instr_hoisted; auto.
  - constructor.
Qed.

Lemma transf_instr_cached_agrees:
  forall f n i, chosen f = Some n ->
  transf_instr_cached n (fresh_reg f) i = transf_instr f i.
Proof.
  intros f n i C. unfold transf_instr_cached, transf_instr.
  destruct i; try reflexivity. destruct o; try reflexivity.
  destruct l; try reflexivity. rewrite C. reflexivity.
Qed.

Lemma transf_function_at:
  forall f pc i, (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!pc = Some (transf_instr f i).
Proof.
  intros. unfold transf_function. destruct (chosen f) as [n|] eqn:C.
  - simpl. rewrite PTree.gso by (eapply fresh_node_ne; eauto).
    rewrite PTree.gmap1, H. simpl.
    rewrite transf_instr_cached_agrees by exact C. reflexivity.
  - rewrite H. f_equal. unfold transf_instr. rewrite C.
    destruct i; try reflexivity. destruct o; try reflexivity. destruct l; reflexivity.
Qed.
Lemma transf_function_sig:
  forall f, fn_sig (transf_function f) = fn_sig f.
Proof. intros. unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_params:
  forall f, fn_params (transf_function f) = fn_params f.
Proof. intros. unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_stacksize:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof. intros. unfold transf_function; destruct (chosen f); reflexivity. Qed.

Definition match_prog (p tp: program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof. intros. eapply match_transform_program; eauto. Qed.

Section PRESERVATION.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Lemma functions_translated:
  forall v f, Genv.find_funct ge v = Some f -> Genv.find_funct tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated:
  forall v f, Genv.find_funct_ptr ge v = Some f -> Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig (transf_fundef f) = funsig f.
Proof. destruct f; simpl; auto. apply transf_function_sig. Qed.

Lemma builtin_arg_regs:
  forall f rs trs sp m arg v,
  regs_match f rs trs ->
  eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  (forall r, In r (params_of_builtin_arg arg) -> Plt r (fresh_reg f)) ->
  eval_builtin_arg ge (fun r => trs#r) sp m arg v.
Proof.
  intros f rs trs sp m arg v REGS EV. induction EV; simpl; intros;
  try (constructor; eauto using in_or_app).
  rewrite <- (proj1 REGS x) by eauto with coqlib. constructor.
Qed.
Lemma builtin_args_regs:
  forall f rs trs sp m args vl,
  regs_match f rs trs ->
  eval_builtin_args ge (fun r => rs#r) sp m args vl ->
  (forall r, In r (params_of_builtin_args args) -> Plt r (fresh_reg f)) ->
  eval_builtin_args ge (fun r => trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl REGS EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs, in_or_app.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs trs
      (REGS: regs_match f rs trs) (RES: res <> fresh_reg f),
      match_frames (Stackframe res f sp pc rs) (Stackframe res (transf_function f) sp pc trs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs trs m stk'
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match f rs trs),
      match_states (State stk f sp pc rs m) (State stk' (transf_function f) sp pc trs m)
  | match_callstates: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | match_returnstates: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m) (Returnstate stk' v m).

Ltac AT :=
  match goal with
  | [ A: (fn_code ?f)!?pc = Some ?i |- _ ] =>
    pose proof (transf_function_at f pc i A) as CODE;
    assert (USES: forall r, In r (instr_uses i) -> Plt r (fresh_reg f))
      by (intros; eapply fresh_reg_use; eauto);
    assert (DEFS: forall r, instr_defs i = Some r -> r <> fresh_reg f)
      by (intros; eapply fresh_reg_def; eauto)
  end.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', plus RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try AT.
  - econstructor; split. apply plus_one. eapply exec_Inop; eauto.
    constructor; auto.
  - pose proof (transf_instr_spec f (Iop op args res pc')) as SPEC.
    remember (transf_instr f (Iop op args res pc')) as ti eqn:TI in CODE, SPEC.
    inv SPEC.
    + match goal with E: _ = transf_instr f _ |- _ => rewrite <- E in CODE end.
      econstructor; split. apply plus_one. eapply exec_Iop; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
      rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
      constructor; auto. apply regs_match_set; eauto.
    + match goal with E: _ = transf_instr f _ |- _ => rewrite <- E in CODE end.
      simpl in H0. inv H0.
      econstructor; split. apply plus_one. eapply exec_Iop; eauto.
      pose proof (proj2 REGS) as TEMP. rewrite H6 in TEMP.
      simpl. rewrite TEMP. reflexivity.
      constructor; auto. apply regs_match_set; eauto.
  - econstructor; split. apply plus_one. eapply exec_Iload; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    constructor; auto. apply regs_match_set; eauto.
  - econstructor; split. apply plus_one. eapply exec_Istore; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    rewrite (proj1 REGS) by (apply USES; simpl; auto). eauto.
    constructor; auto.
  - assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite (proj1 REGS) by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. apply plus_one. eapply exec_Icall; eauto.
    apply sig_preserved.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor. constructor; auto. constructor; auto.
  - assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite (proj1 REGS) by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. apply plus_one. eapply exec_Itailcall; eauto.
    apply sig_preserved. rewrite transf_function_stacksize; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor; auto.
  - econstructor; split. apply plus_one. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply builtin_args_regs; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto. apply regs_match_setres; auto. destruct res; simpl; auto.
  - econstructor; split. apply plus_one. eapply exec_Icond; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto). eauto.
    constructor; auto.
  - econstructor; split. apply plus_one. eapply exec_Ijumptable; eauto.
    rewrite (proj1 REGS) by (apply USES; simpl; auto). eauto.
    constructor; auto.
  - econstructor; split. apply plus_one. eapply exec_Ireturn; eauto.
    rewrite transf_function_stacksize; eauto.
    destruct or; simpl. rewrite (proj1 REGS) by (apply USES; simpl; auto). constructor; auto.
    constructor; auto.
  - destruct (chosen f) as [n|] eqn:CHOICE.
    + exists (State stk' (transf_function f) (Vptr stk Ptrofs.zero) (fn_entrypoint f)
              ((init_regs args (fn_params f))#(fresh_reg f) <- (Vint n)) m'). split.
      eapply plus_two.
      eapply exec_function_internal; rewrite ?transf_function_sig, ?transf_function_stacksize; eauto.
      unfold transf_function. rewrite CHOICE. simpl.
      eapply exec_Iop. apply PTree.gss. reflexivity. reflexivity.
      constructor; auto. split.
      intros r LT. rewrite Regmap.gso by extlia. auto.
      rewrite CHOICE. apply Regmap.gss.
    + econstructor; split. apply plus_one. eapply exec_function_internal;
        rewrite ?transf_function_sig, ?transf_function_stacksize; eauto.
      assert (ENTRY: fn_entrypoint (transf_function f) = fn_entrypoint f).
      { unfold transf_function. rewrite CHOICE. auto. }
      rewrite ENTRY, transf_function_params.
      constructor; auto. split; auto. rewrite CHOICE; auto.
  - econstructor; split. apply plus_one. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto.
  - inv STACKS. inv H1. econstructor; split. apply plus_one. eapply exec_return; eauto.
    constructor; auto. apply regs_match_set; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split. econstructor.
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
  eapply function_ptr_translated; eauto. rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.
Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. intros. inv H0. inv H. inv STACKS. constructor. Qed.
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_plus.
  apply senv_preserved. eexact transf_initial_states. eexact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.

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

(** Semantic preservation of packing/extraction lowering. *)
Require Import Coqlib Maps AST Linking Integers Zbits.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Experimental LowerLong.

Lemma lower_makelong_values:
  forall hi lo,
  Val.addl (eval_extend Xuns32 hi amount_32)
    (eval_extend Xuns32 lo amount_zero) = Val.longofwords hi lo.
Proof.
  intros hi lo. destruct hi,lo; simpl; auto.
  unfold eval_extend,amount_32,amount_zero; simpl.
  assert (C32: Int.ltu (Int.repr 32) Int64.iwordsize' = true) by reflexivity.
  assert (C0: Int.ltu Int.zero Int64.iwordsize' = true) by reflexivity.
  rewrite C32,C0. simpl. f_equal.
  unfold Int64.shl'. rewrite Int.unsigned_zero,Z.shiftl_0_r,Int64.repr_unsigned.
  rewrite Int.unsigned_repr by (change (0 <= 32 <= 4294967295); lia).
  assert (HI: Int64.unsigned (Int64.repr (Int.unsigned i)) = Int.unsigned i).
  { apply Int64.unsigned_repr. generalize (Int.unsigned_range_2 i).
    change Int.max_unsigned with 4294967295; change Int64.max_unsigned with 18446744073709551615; lia. }
  rewrite HI,Int64.ofwords_add. unfold Int64.add.
  apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l. rewrite Zshiftl_mul_two_p by lia. apply Int64.eqm_refl.
  - apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
Qed.
Lemma lower_highlong_values:
  forall v, Val.loword (eval_shiftl Slsr v amount_32) = Val.hiword v.
Proof. destruct v; reflexivity. Qed.

Inductive instr_spec (f: function) (pc: node): instruction -> instruction -> Prop :=
 | spec_default: forall i, instr_spec f pc i (Experimental.map_successors base i)
 | spec_make: forall hi lo dst s,
     instr_spec f pc (Iop Omakelong (hi :: lo :: nil) dst s)
       (Iop (Oextend Xuns32 amount_32) (hi :: nil) (fresh_reg f) (after pc))
 | spec_high: forall r dst s,
     instr_spec f pc (Iop Ohighlong (r :: nil) dst s)
       (Iop (Oshiftl Slsr amount_32) (r :: nil) (fresh_reg f) (after pc))
 | spec_bad_make: forall args dst s, length args <> 2%nat ->
     instr_spec f pc (Iop Omakelong args dst s) (Inop (base s))
 | spec_bad_high: forall args dst s, length args <> 1%nat ->
     instr_spec f pc (Iop Ohighlong args dst s) (Inop (base s)).
Lemma first_instr_spec:
  forall f pc i, instr_spec f pc i (first_instr f pc i).
Proof.
  intros f pc i. destruct i; try apply spec_default.
  destruct o; try apply spec_default.
  - destruct l as [|hi [|lo [|extra rest]]]; simpl; try (apply spec_bad_make; simpl; lia).
    apply spec_make.
  - destruct l as [|a [|extra rest]]; simpl; try (apply spec_bad_high; simpl; lia).
    apply spec_high.
Qed.
Lemma bad_make_eval:
  forall F V (g: Genv.t F V) sp vl m, length vl <> 2%nat -> eval_operation g sp Omakelong vl m = None.
Proof. intros. destruct vl as [|a [|b [|extra rest]]]; simpl in *; congruence. Qed.
Lemma bad_high_eval:
  forall F V (g: Genv.t F V) sp vl m, length vl <> 1%nat -> eval_operation g sp Ohighlong vl m = None.
Proof. intros. destruct vl as [|a [|extra rest]]; simpl in *; congruence. Qed.
Lemma code_base:
  forall f pc i, (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!(base pc) = Some (first_instr f pc i).
Proof. intros. unfold transf_function,base; simpl. rewrite PTree.gNode,PTree.gmap,H; reflexivity. Qed.
Lemma next_instr_option_matches:
  forall f pc i, needs_second i = true ->
  next_instr_option f i = Some (next_instr f pc i).
Proof.
  intros f pc i N. destruct i; try discriminate.
  destruct o; try discriminate.
  - destruct l as [|hi [|lo [|extra rest]]]; try discriminate; reflexivity.
  - destruct l as [|a [|extra rest]]; try discriminate; reflexivity.
Qed.
Lemma code_next:
  forall f pc i, (fn_code f)!pc = Some i -> needs_second i = true ->
  (fn_code (transf_function f))!(after pc) = Some (next_instr f pc i).
Proof.
  intros. unfold transf_function,after; simpl.
  rewrite PTree.gNode,PTree.gmap_filter1,H. apply next_instr_option_matches; auto.
Qed.
Lemma fresh_use:
  forall f pc i r, (fn_code f)!pc = Some i -> In r (instr_uses i) -> Plt r (fresh_reg f).
Proof. unfold fresh_reg; intros; generalize (max_reg_function_use _ _ _ _ H H0); extlia. Qed.
Lemma transf_function_sig: forall f, fn_sig (transf_function f) = fn_sig f.
Proof. reflexivity. Qed.
Lemma transf_function_params: forall f, fn_params (transf_function f) = fn_params f.
Proof. reflexivity. Qed.
Lemma transf_function_stacksize: forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof. reflexivity. Qed.
Definition regs_match (f: function) (rs trs: regset): Prop :=
  forall r, Plt r (fresh_reg f) -> trs#r = rs#r.
Lemma regs_match_list:
  forall f rs trs rl, regs_match f rs trs ->
  (forall r, In r rl -> Plt r (fresh_reg f)) -> trs##rl = rs##rl.
Proof. intros. apply list_map_exten. intros; symmetry; eauto. Qed.
Lemma regs_match_set:
  forall f rs trs r v, regs_match f rs trs -> regs_match f (rs#r <- v) (trs#r <- v).
Proof. unfold regs_match; intros; rewrite !Regmap.gsspec; destruct (peq r0 r); auto. Qed.
Lemma regs_match_temp:
  forall f rs trs v, regs_match f rs trs -> regs_match f rs (trs#(fresh_reg f) <- v).
Proof. unfold regs_match; intros; rewrite Regmap.gso by extlia; auto. Qed.
Lemma regs_match_setres:
  forall f rs trs res v, regs_match f rs trs ->
  regs_match f (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto using regs_match_set. Qed.
Definition match_prog (p tp: program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Lemma transf_program_match: forall p, match_prog p (transf_program p).
Proof. intros; eapply match_transform_program; eauto. Qed.
Global Instance TransfLowerLongLink: TransfLink match_prog := TransfTotalLink transf_function.
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
Lemma symbols_preserved: forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig (transf_fundef f) = funsig f.
Proof. destruct f; simpl; auto. Qed.
Lemma builtin_arg_regs:
  forall f rs trs sp m arg v, regs_match f rs trs ->
  eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  (forall r, In r (params_of_builtin_arg arg) -> Plt r (fresh_reg f)) ->
  eval_builtin_arg ge (fun r => trs#r) sp m arg v.
Proof.
  intros f rs trs sp m arg v REGS EV. induction EV; simpl; intros;
  try (constructor; eauto using in_or_app).
  rewrite <- (REGS x) by eauto with coqlib. constructor.
Qed.
Lemma builtin_args_regs:
  forall f rs trs sp m args vl, regs_match f rs trs ->
  eval_builtin_args ge (fun r => rs#r) sp m args vl ->
  (forall r, In r (params_of_builtin_args args) -> Plt r (fresh_reg f)) ->
  eval_builtin_args ge (fun r => trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl REGS EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs, in_or_app.
Qed.
Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs trs (REGS: regs_match f rs trs),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp (base pc) trs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs trs m stk'
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match f rs trs),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (base pc) trs m)
  | match_callstates: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | match_returnstates: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m) (Returnstate stk' v m).
Ltac AT :=
  match goal with
  | [ A: (fn_code ?f)!?pc = Some ?i |- _ ] =>
    pose proof (code_base f pc i A) as CODE;
    pose proof (first_instr_spec f pc i) as SPEC;
    assert (USES: forall r, In r (instr_uses i) -> Plt r (fresh_reg f))
      by (intros; eapply fresh_use; eauto)
  end.
Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', plus RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try AT.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Inop; eauto. constructor; auto.
  - cbn [first_instr Experimental.map_successors] in CODE.
    inversion SPEC as [i|hi lo dst succ|r dst succ|args' dst succ BAD|args' dst succ BAD]; subst;
      try match goal with E: @eq instruction _ _ |- _ => rewrite <- E in CODE end.
    + simpl Experimental.map_successors in CODE.
      econstructor; split. apply plus_one. eapply exec_Iop; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
      rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
      constructor; auto. apply regs_match_set; auto.
    + simpl in H0. inv H0.
      exists (State stk' (transf_function f) sp (base pc')
        ((trs#(fresh_reg f) <- (eval_extend Xuns32 rs#hi amount_32))
             #res <- (Val.longofwords rs#hi rs#lo)) m). split.
      * eapply plus_two.
        eapply exec_Iop; eauto. simpl. rewrite REGS by (apply USES; simpl; auto). reflexivity.
        eapply exec_Iop.
        eapply eq_trans. eapply code_next; eauto. reflexivity.
        simpl. rewrite Regmap.gss,Regmap.gso by (generalize (USES lo); simpl; extlia).
        rewrite REGS by (apply USES; simpl; auto). rewrite lower_makelong_values. reflexivity.
        traceEq.
      * constructor; auto. apply regs_match_set. apply regs_match_temp; auto.
    + simpl in H0. inv H0.
      exists (State stk' (transf_function f) sp (base pc')
        ((trs#(fresh_reg f) <- (eval_shiftl Slsr rs#r amount_32))
             #res <- (Val.hiword rs#r)) m). split.
      * eapply plus_two.
        eapply exec_Iop; eauto. simpl. rewrite REGS by (apply USES; simpl; auto). reflexivity.
        eapply exec_Iop.
        eapply eq_trans. eapply code_next; eauto. reflexivity.
        simpl. rewrite Regmap.gss.
        change (Some (Val.loword (eval_shiftl Slsr rs#r amount_32)) = Some (Val.hiword rs#r)).
        rewrite lower_highlong_values. reflexivity.
        traceEq.
      * constructor; auto. apply regs_match_set. apply regs_match_temp; auto.
    + rewrite bad_make_eval in H0 by (rewrite length_map; auto). discriminate.
    + rewrite bad_high_eval in H0 by (rewrite length_map; auto). discriminate.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Iload; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    constructor; auto. apply regs_match_set; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Istore; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    rewrite REGS by (apply USES; simpl; auto). eauto. constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite REGS by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. apply plus_one. eapply exec_Icall; eauto. rewrite sig_preserved; auto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor. constructor; auto. constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite REGS by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. apply plus_one. eapply exec_Itailcall; eauto. rewrite sig_preserved; auto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply builtin_args_regs; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto. apply regs_match_setres; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Icond; eauto.
    rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto). eauto.
    replace (if b then base ifso else base ifnot) with (base (if b then ifso else ifnot)) by (destruct b; auto).
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Ijumptable; eauto.
    rewrite REGS by (apply USES; simpl; auto). eauto.
    rewrite list_nth_z_map,H1; simpl; eauto. constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. apply plus_one. eapply exec_Ireturn; eauto.
    destruct or; simpl. rewrite REGS by (apply USES; simpl; auto). constructor; auto. constructor; auto.
  - econstructor; split. apply plus_one. eapply exec_function_internal; eauto.
    change (fn_entrypoint (transf_function f)) with (base (fn_entrypoint f)).
    rewrite transf_function_params. constructor; auto. unfold regs_match; auto.
  - econstructor; split. apply plus_one. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved. constructor; auto.
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

Definition supported (i: instruction): Prop :=
  match i with Iop Omakelong _ _ _ | Iop Ohighlong _ _ _ => False | _ => True end.
Lemma first_instr_supported:
  forall f pc i, supported (first_instr f pc i).
Proof.
  intros f pc i. destruct i; try exact I.
  unfold first_instr. destruct o; try exact I.
  - destruct l as [|hi [|lo [|extra rest]]]; exact I.
  - destruct l as [|a [|extra rest]]; exact I.
Qed.
Lemma next_instr_supported:
  forall f pc i, supported (next_instr f pc i).
Proof.
  intros f pc i. destruct i; try exact I.
  unfold next_instr. destruct o; try exact I.
  - destruct l as [|hi [|lo [|extra rest]]]; exact I.
  - destruct l as [|a [|extra rest]]; exact I.
Qed.
Lemma next_option_supported:
  forall f i ti, next_instr_option f i = Some ti -> supported ti.
Proof.
  intros f i ti GET. destruct i; try discriminate. destruct o; try discriminate.
  - destruct l as [|hi [|lo [|extra rest]]]; try discriminate. inv GET; exact I.
  - destruct l as [|a [|extra rest]]; try discriminate. inv GET; exact I.
Qed.
Theorem all_unsupported_operations_removed:
  forall f pc i, (fn_code (transf_function f))!pc = Some i -> supported i.
Proof.
  intros f pc i GET. unfold transf_function in GET; simpl in GET.
  destruct pc; rewrite PTree.gNode in GET.
  - rewrite PTree.gmap_filter1 in GET. destruct ((fn_code f)!pc) eqn:S; try discriminate.
    eapply next_option_supported; eauto.
  - rewrite PTree.gmap in GET. destruct ((fn_code f)!pc) eqn:S; try discriminate.
    inv GET; apply first_instr_supported.
  - discriminate.
Qed.

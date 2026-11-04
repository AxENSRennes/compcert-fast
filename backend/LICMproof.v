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

(** Preservation of total, memory-independent invariant operation motion. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL LICM.

Lemma total_operation:
  forall (F V: Type) (ge: Genv.t F V) sp op vl m,
  total_arity op (length vl) = true ->
  exists v, eval_operation ge sp op vl m = Some v.
Proof.
  intros F V ge sp op vl m TOTAL.
  destruct op; destruct vl as [|v1 [|v2 [|v3 [|v4 vl]]]];
  simpl in TOTAL; try discriminate; eexists; reflexivity.
Qed.
Lemma choose_in_sound:
  forall items f fuel b,
  (forall pc i, In (pc,i) items -> (fn_code f)!pc = Some i) ->
  choose_in f fuel items = Some b ->
  exists pc dst next, (fn_code f)!pc = Some (Iop (invariant_op b) (invariant_args b) dst next) /\
  op_depends_on_memory (invariant_op b) = false /\
  total_arity (invariant_op b) (length (invariant_args b)) = true /\
  forallb (immutable f) (invariant_args b) = true.
Proof.
  induction items as [|[pc i] rest IH]; simpl; intros f fuel b GET CHOICE; try discriminate.
  destruct i; try solve [eapply IH; eauto with coqlib].
  destruct fuel; try discriminate.
  destruct (eligible f o l && HoistConst.cyclic f pc (Iop o l r n)) eqn:E.
  - inv CHOICE. apply andb_true_iff in E. destruct E as [E _].
    unfold eligible in E. repeat rewrite andb_true_iff in E.
    destruct E as [[[MEM TOTAL] IMM] _]. apply negb_true_iff in MEM.
    exists pc,r,n; simpl. repeat split; auto.
  - eapply IH; eauto with coqlib.
Qed.
Lemma chosen_sound:
  forall f b, chosen f = Some b ->
  exists pc dst next, (fn_code f)!pc = Some (Iop (invariant_op b) (invariant_args b) dst next) /\
  op_depends_on_memory (invariant_op b) = false /\
  total_arity (invariant_op b) (length (invariant_args b)) = true /\
  forallb (immutable f) (invariant_args b) = true.
Proof.
  unfold chosen. intros f b CHOICE.
  destruct (Nat.leb (length (PTree.elements (fn_code f))) 512); try discriminate.
  eapply choose_in_sound; eauto. intros. eapply PTree.elements_complete; eauto.
Qed.
Lemma fresh_reg_use:
  forall f pc i r, (fn_code f)!pc = Some i -> In r (instr_uses i) -> Plt r (fresh_reg f).
Proof. unfold fresh_reg; intros. generalize (max_reg_function_use _ _ _ _ H H0). extlia. Qed.
Lemma fresh_reg_def:
  forall f pc i r, (fn_code f)!pc = Some i -> instr_defs i = Some r -> r <> fresh_reg f.
Proof. unfold fresh_reg; intros. generalize (max_reg_function_def _ _ _ _ H H0). extlia. Qed.
Lemma fresh_node_ne:
  forall f pc i, (fn_code f)!pc = Some i -> pc <> fresh_node f.
Proof. unfold fresh_node; intros. generalize (max_pc_function_sound _ _ _ H). extlia. Qed.
Lemma invariant_arg_bound:
  forall f b r, chosen f = Some b -> In r (invariant_args b) -> Plt r (fresh_reg f).
Proof.
  intros. destruct (chosen_sound _ _ H) as (pc & dst & next & GET & _).
  eapply fresh_reg_use; eauto.
Qed.
Definition result_safe (f: function) (dst: reg) : Prop :=
  forall b, chosen f = Some b -> ~ In dst (invariant_args b).
Lemma immutable_def:
  forall f pc i dst, (fn_code f)!pc = Some i -> instr_defs i = Some dst -> result_safe f dst.
Proof.
  intros f pc i dst GET DEF b C IN.
  destruct (chosen_sound _ _ C) as (p & d & n & G & MEM & TOTAL & IMM).
  rewrite forallb_forall in IMM. specialize (IMM dst IN). unfold immutable in IMM.
  rewrite forallb_forall in IMM. specialize (IMM (pc,i) (PTree.elements_correct _ _ GET)).
  simpl in IMM. rewrite DEF in IMM. destruct (peq dst dst); congruence.
Qed.
Lemma get_list_set_other:
  forall (rs: regset) (args: list reg) dst v, ~ In dst args -> (rs#dst <- v)##args = rs##args.
Proof.
  intros. apply list_map_exten. intros. rewrite Regmap.gso; auto. intro EQ; subst; auto.
Qed.
Definition regs_match {F V: Type} (ge: Genv.t F V) (f: function) (sp: val) (rs trs: regset) : Prop :=
  (forall r, Plt r (fresh_reg f) -> trs#r = rs#r) /\
  match chosen f with
  | Some b => eval_operation ge sp (invariant_op b) rs##(invariant_args b) Mem.empty = Some trs#(fresh_reg f)
  | None => True end.
Lemma regs_match_list:
  forall (F V: Type) (ge: Genv.t F V) f sp rs trs rl,
  regs_match ge f sp rs trs -> (forall r, In r rl -> Plt r (fresh_reg f)) -> trs##rl = rs##rl.
Proof. intros F V ge f sp rs trs rl [A B] C. apply list_map_exten. intros; symmetry; apply A; auto. Qed.
Arguments regs_match_list {F V} ge f sp rs trs rl _ _.
Lemma regs_match_set:
  forall (F V: Type) (ge: Genv.t F V) f sp rs trs r v,
  regs_match ge f sp rs trs -> r <> fresh_reg f -> result_safe f r ->
  regs_match ge f sp (rs#r <- v) (trs#r <- v).
Proof.
  intros F V ge f sp rs trs r v [A B] NE SAFE. split.
  - intros x LT. rewrite !Regmap.gsspec. destruct (peq x r); auto.
  - destruct (chosen f) as [b|] eqn:C; auto.
    rewrite get_list_set_other by (apply (SAFE b C)). rewrite Regmap.gso; auto.
Qed.
Lemma regs_match_setres:
  forall (F V: Type) (ge: Genv.t F V) f sp rs trs res v,
  regs_match ge f sp rs trs ->
  (match res with BR r => r <> fresh_reg f /\ result_safe f r | _ => True end) ->
  regs_match ge f sp (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto. destruct H0. apply regs_match_set; auto. Qed.
Inductive instr_spec (f: function): instruction -> instruction -> Prop :=
  | instr_default: forall i, instr_spec f i i
  | instr_hoisted: forall b r s, chosen f = Some b ->
      instr_spec f (Iop (invariant_op b) (invariant_args b) r s)
                   (Iop Omove (fresh_reg f :: nil) r s).
Lemma transf_instr_spec:
  forall f i, instr_spec f i (transf_instr f i).
Proof.
  intros f i. destruct i; try constructor. unfold transf_instr.
  destruct (chosen f) as [b|] eqn:C; try constructor. unfold transf_instr_cached.
  destruct (Op.eq_operation o (invariant_op b)); try constructor.
  destruct (list_eq_dec peq l (invariant_args b)); try constructor.
  subst. apply instr_hoisted; auto.
Qed.
Lemma transf_function_at:
  forall f pc i, (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!pc = Some (transf_instr f i).
Proof.
  intros. unfold transf_function. destruct (chosen f) as [b|] eqn:C.
  - simpl. rewrite PTree.gso by (eapply fresh_node_ne; eauto).
    rewrite PTree.gmap1, H. destruct i; simpl; try reflexivity. unfold transf_instr. rewrite C. reflexivity.
  - rewrite H. destruct i; simpl; try reflexivity. unfold transf_instr. rewrite C. reflexivity.
Qed.
Lemma transf_function_sig: forall f, fn_sig (transf_function f) = fn_sig f.
Proof. intros. unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_params: forall f, fn_params (transf_function f) = fn_params f.
Proof. intros. unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_stacksize: forall f, fn_stacksize (transf_function f) = fn_stacksize f.
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
  regs_match ge f sp rs trs ->
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
  regs_match ge f sp rs trs ->
  eval_builtin_args ge (fun r => rs#r) sp m args vl ->
  (forall r, In r (params_of_builtin_args args) -> Plt r (fresh_reg f)) ->
  eval_builtin_args ge (fun r => trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl REGS EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs, in_or_app.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs trs
      (REGS: regs_match ge f sp rs trs) (RES: res <> fresh_reg f) (SAFE: result_safe f res),
      match_frames (Stackframe res f sp pc rs) (Stackframe res (transf_function f) sp pc trs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs trs m stk'
      (STACKS: list_forall2 match_frames stk stk') (REGS: regs_match ge f sp rs trs),
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
      by (intros; eapply fresh_reg_def; eauto);
    assert (SAFE: forall r, instr_defs i = Some r -> result_safe f r)
      by (intros; eapply immutable_def; eauto)
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
      rewrite (regs_match_list ge f _ rs trs args REGS) by (intros; apply USES; auto).
      rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
      constructor; auto. apply regs_match_set; eauto.
    + match goal with E: _ = transf_instr f _ |- _ => rewrite <- E in CODE end.
      match goal with C: chosen f = Some ?b |- _ =>
        destruct (chosen_sound f b C) as (pc0 & dst0 & next0 & G & MEM & TOTAL & IMM);
        pose proof (proj2 REGS) as TEMP; rewrite C in TEMP end.
      rewrite (@op_depends_on_memory_correct _ _ _ _ _ _ m Mem.empty MEM) in H0.
      rewrite H0 in TEMP. inv TEMP.
      econstructor; split. apply plus_one. eapply exec_Iop; eauto.
      simpl. reflexivity.
      constructor; auto. apply regs_match_set; eauto.
  - econstructor; split. apply plus_one. eapply exec_Iload; eauto.
    rewrite (regs_match_list ge f _ rs trs args REGS) by (intros; apply USES; auto).
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    constructor; auto. apply regs_match_set; eauto.
  - econstructor; split. apply plus_one. eapply exec_Istore; eauto.
    rewrite (regs_match_list ge f _ rs trs args REGS) by (intros; apply USES; simpl; auto).
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
    rewrite (regs_match_list ge f _ rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor. constructor; auto. constructor; auto.
  - assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
    { unfold find_function in *. destruct ros as [r|id].
      rewrite (proj1 REGS) by (apply USES; simpl; auto). apply functions_translated; auto.
      rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
      apply function_ptr_translated; auto. }
    econstructor; split. apply plus_one. eapply exec_Itailcall; eauto.
    apply sig_preserved. rewrite transf_function_stacksize; eauto.
    rewrite (regs_match_list ge f _ rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
    constructor; auto.
  - econstructor; split. apply plus_one. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply builtin_args_regs; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto. apply regs_match_setres; auto. destruct res; simpl; auto.
  - econstructor; split. apply plus_one. eapply exec_Icond; eauto.
    rewrite (regs_match_list ge f _ rs trs args REGS) by (intros; apply USES; simpl; auto). eauto.
    constructor; auto.
  - econstructor; split. apply plus_one. eapply exec_Ijumptable; eauto.
    rewrite (proj1 REGS) by (apply USES; simpl; auto). eauto.
    constructor; auto.
  - econstructor; split. apply plus_one. eapply exec_Ireturn; eauto.
    rewrite transf_function_stacksize; eauto.
    destruct or; simpl. rewrite (proj1 REGS) by (apply USES; simpl; auto). constructor; auto.
    constructor; auto.
  - destruct (chosen f) as [b|] eqn:CHOICE.
    + destruct (chosen_sound f b CHOICE) as (pc0 & dst0 & next0 & GET & MEM & TOTAL & IMM).
      assert (EX: exists v, eval_operation ge (Vptr stk Ptrofs.zero)
                  (invariant_op b) (init_regs args (fn_params f))##(invariant_args b) Mem.empty = Some v).
      { apply total_operation. rewrite list_length_map. exact TOTAL. }
      destruct EX as [v EVAL].
      exists (State stk' (transf_function f) (Vptr stk Ptrofs.zero) (fn_entrypoint f)
              ((init_regs args (fn_params f))#(fresh_reg f) <- v) m'). split.
      eapply plus_two.
      eapply exec_function_internal; rewrite ?transf_function_sig, ?transf_function_stacksize; eauto.
      unfold transf_function. rewrite CHOICE. simpl.
      eapply exec_Iop. apply PTree.gss.
      rewrite eval_operation_preserved with (ge1 := ge) by exact symbols_preserved.
      rewrite (@op_depends_on_memory_correct _ _ _ _ _ _ m' Mem.empty MEM). exact EVAL.
      reflexivity.
      constructor; auto. split.
      intros r LT. rewrite Regmap.gso by extlia. auto.
      rewrite CHOICE, Regmap.gss. exact EVAL.
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

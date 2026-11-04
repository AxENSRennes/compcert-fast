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

(** Correctness of delayed, immutable-register loop unswitching. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Experimental Experimentalproof Unswitch.

Lemma choose_in_sound:
  forall items loops f b,
  (forall pc i, In (pc,i) items -> (fn_code f)!pc = Some i) ->
  choose_in loops f items = Some b ->
  (fn_code f)!(branch_pc b) = Some
    (Icond (Ccompimm (branch_cmp b) (branch_imm b)) (branch_reg b :: nil) (branch_yes b) (branch_no b)) /\
  immutable f (branch_reg b) = true.
Proof.
  induction items as [|[pc i] rest IH]; simpl; intros; try discriminate.
  destruct i; try solve [eapply IH; eauto with coqlib].
  destruct c; try solve [eapply IH; eauto with coqlib].
  destruct l as [|r restargs]; try solve [eapply IH; eauto with coqlib].
  destruct restargs; try solve [eapply IH; eauto with coqlib].
  destruct (immutable f r && (negb loops || HoistConst.cyclic f pc (Icond (Ccompimm c n1) (r :: nil) n n0))) eqn:B.
  - inv H0. apply andb_true_iff in B. split; simpl; tauto || eauto with coqlib.
  - eapply IH; eauto with coqlib.
Qed.
Lemma chosen_sound:
  forall f b, chosen f = Some b ->
  (fn_code f)!(branch_pc b) = Some
    (Icond (Ccompimm (branch_cmp b) (branch_imm b)) (branch_reg b :: nil) (branch_yes b) (branch_no b)) /\
  immutable f (branch_reg b) = true.
Proof.
  unfold chosen; intros. destruct (choose_in true f (PTree.elements (fn_code f))) eqn:C.
  - inv H. eapply choose_in_sound; eauto. intros. eapply PTree.elements_complete; eauto.
  - eapply choose_in_sound; eauto. intros. eapply PTree.elements_complete; eauto.
Qed.
Lemma immutable_def:
  forall f b pc i dst,
  chosen f = Some b -> (fn_code f)!pc = Some i -> instr_defs i = Some dst -> dst <> branch_reg b.
Proof.
  intros. apply chosen_sound in H. destruct H as [_ IMM].
  unfold immutable in IMM. rewrite forallb_forall in IMM.
  specialize (IMM (pc,i) (PTree.elements_correct _ _ H0)). simpl in IMM. rewrite H1 in IMM.
  destruct (peq dst (branch_reg b)); congruence.
Qed.
Lemma copy_code_at:
  forall f b mode pc i,
  (fn_code f)!pc = Some i ->
  (copy_code f b)!(tag mode pc) = Some (copy_instr b mode pc i).
Proof.
  intros. unfold copy_code, tag. destruct mode as [|[]]; rewrite !PTree.gNode;
  rewrite PTree.gmap, H; reflexivity.
Qed.
Lemma transf_function_sig: forall f, fn_sig (transf_function f) = fn_sig f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_params: forall f, fn_params (transf_function f) = fn_params f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_stacksize: forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof. intros; unfold transf_function; destruct (chosen f); reflexivity. Qed.
Lemma transf_function_entry: forall f, fn_entrypoint (transf_function f) = label f Normal (fn_entrypoint f).
Proof. intros; unfold transf_function,label; destruct (chosen f); reflexivity. Qed.

Definition phase_valid (f: function) (mode: phase) (rs: regset) : Prop :=
  match chosen f, mode with
  | Some b, Known answer => Val.cmp_bool (branch_cmp b) rs#(branch_reg b) (Vint (branch_imm b)) = Some answer
  | _, _ => True
  end.
Definition result_safe (f: function) (dst: reg) : Prop :=
  forall b, chosen f = Some b -> dst <> branch_reg b.
Lemma phase_valid_set:
  forall f mode rs dst v,
  phase_valid f mode rs -> result_safe f dst -> phase_valid f mode (rs#dst <- v).
Proof.
  unfold phase_valid,result_safe; intros.
  destruct (chosen f) as [b|] eqn:C; auto. destruct mode; auto.
  rewrite Regmap.gso; auto. intro EQ. apply (H0 b eq_refl); auto.
Qed.
Lemma phase_valid_setres:
  forall f mode rs res v,
  phase_valid f mode rs ->
  (match res with BR r => result_safe f r | _ => True end) ->
  phase_valid f mode (regmap_setres res v rs).
Proof. destruct res; simpl; intros; auto. apply phase_valid_set; auto. Qed.

Inductive instr_spec (f: function) (mode: phase): instruction -> instruction -> Prop :=
  | instr_default: forall i,
      instr_spec f mode i (Experimental.map_successors (label f mode) i)
  | instr_learn: forall b,
      chosen f = Some b -> mode = Normal ->
      instr_spec f mode
        (Icond (Ccompimm (branch_cmp b) (branch_imm b)) (branch_reg b :: nil) (branch_yes b) (branch_no b))
        (Icond (Ccompimm (branch_cmp b) (branch_imm b)) (branch_reg b :: nil)
          (label f (Known true) (branch_yes b)) (label f (Known false) (branch_no b)))
  | instr_known: forall b answer,
      chosen f = Some b -> mode = Known answer ->
      instr_spec f mode
        (Icond (Ccompimm (branch_cmp b) (branch_imm b)) (branch_reg b :: nil) (branch_yes b) (branch_no b))
        (Inop (label f mode (if answer then branch_yes b else branch_no b))).
Lemma transf_function_at:
  forall f mode pc i, (fn_code f)!pc = Some i ->
  exists ti, (fn_code (transf_function f))!(label f mode pc) = Some ti /\ instr_spec f mode i ti.
Proof.
  intros. unfold transf_function,label. destruct (chosen f) as [b|] eqn:C.
  - exists (copy_instr b mode pc i). split. apply copy_code_at; auto.
    unfold copy_instr. destruct (peq pc (branch_pc b)).
    + subst pc. destruct (chosen_sound _ _ C) as [GET IMM]. rewrite H in GET. inv GET.
      assert (LABEL: forall mode pc, label f mode pc = tag mode pc).
      { intros. unfold label. rewrite C. auto. }
      destruct mode as [|answer].
      * rewrite <- (LABEL (Known true) (branch_yes b)),
          <- (LABEL (Known false) (branch_no b)). apply instr_learn; auto.
      * rewrite <- (LABEL (Known answer) (if answer then branch_yes b else branch_no b)).
        apply instr_known with (b := b); auto.
    + replace (tag mode) with (label f mode).
      constructor. unfold label. rewrite C. reflexivity.
  - exists i; split; auto.
    replace i with (Experimental.map_successors (label f mode) i) at 2.
    constructor. unfold label. rewrite C. apply Experimentalproof.map_successors_id.
Qed.

Lemma phase_valid_normal: forall f rs, phase_valid f Normal rs.
Proof. intros. unfold phase_valid. destruct (chosen f); auto. Qed.
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
  | match_frames_intro: forall res f sp pc rs mode
      (INV: phase_valid f mode rs) (RES: result_safe f res),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp (label f mode pc) rs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' mode
      (STACKS: list_forall2 match_frames stk stk') (INV: phase_valid f mode rs),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp (label f mode pc) rs m)
  | match_callstates: forall stk fd args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk fd args m) (Callstate stk' (transf_fundef fd) args m)
  | match_returnstates: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m) (Returnstate stk' v m).

Ltac AT :=
  match goal with
  | [ A: (fn_code ?f)!?pc = Some ?i, V: phase_valid ?f ?mode _ |- _ ] =>
    assert (SAFE: forall dst, instr_defs i = Some dst -> result_safe f dst)
      by (unfold result_safe; intros; eapply immutable_def; eauto);
    destruct (transf_function_at f mode pc i A) as [ti [CODE SPEC]]
  end.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try AT.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Inop; eauto. constructor; auto.
  - inversion SPEC; subst; try clear SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Iop; eauto.
    instantiate (1 := v). rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
    constructor; auto. apply phase_valid_set; eauto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split.
    assert (eval_addressing tge sp addr rs ## args = Some a).
    { rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved. }
    eapply exec_Iload; eauto. constructor; auto. apply phase_valid_set; eauto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split.
    assert (eval_addressing tge sp addr rs ## args = Some a).
    { rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved. }
    eapply exec_Istore; eauto. constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto. apply sig_preserved.
    constructor. constructor; auto. constructor; eauto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto. apply sig_preserved.
    rewrite transf_function_stacksize; eauto. constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto. apply phase_valid_setres; auto. destruct res; simpl; auto.
  - inv SPEC.
    + simpl Experimental.map_successors in CODE.
      econstructor; split. eapply exec_Icond; eauto.
      replace (if b then label f mode ifso else label f mode ifnot)
        with (label f mode (if b then ifso else ifnot)) by (destruct b; auto).
      constructor; auto.
    + econstructor; split. eapply exec_Icond; eauto.
      replace (if b then label f (Known true) (branch_yes b0)
                       else label f (Known false) (branch_no b0))
        with (label f (Known b) (if b then branch_yes b0 else branch_no b0)) by (destruct b; auto).
      constructor; auto. unfold phase_valid.
      match goal with C: chosen f = Some _ |- _ => rewrite C end. exact H0.
    + unfold phase_valid in INV.
      match goal with C: chosen f = Some _ |- _ => rewrite C in INV end. simpl in INV.
      assert (b = answer) by (simpl in H0; congruence). subst answer.
      econstructor; split. eapply exec_Inop; eauto. constructor; auto.
      unfold phase_valid. match goal with C: chosen f = Some _ |- _ => rewrite C end. exact INV.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Ijumptable; eauto. rewrite list_nth_z_map, H1; simpl; eauto.
    constructor; auto.
  - inv SPEC. simpl Experimental.map_successors in CODE.
    econstructor; split. eapply exec_Ireturn; eauto. rewrite transf_function_stacksize; eauto.
    constructor; auto.
  - simpl. econstructor; split. eapply exec_function_internal; eauto.
    rewrite transf_function_sig; eauto. rewrite transf_function_stacksize; eauto.
    rewrite transf_function_params, transf_function_entry.
    constructor; auto. apply phase_valid_normal.
  - econstructor; split. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved. constructor; auto.
  - inv STACKS. inv H1.
    econstructor; split. eapply exec_return; eauto.
    constructor; auto. apply phase_valid_set; auto.
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
  eapply forward_simulation_step.
  apply senv_preserved. eexact transf_initial_states. eexact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.

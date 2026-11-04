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

(* Correctness of validated two-traversal peeling. Distributed under the
   INRIA Non-Commercial License Agreement of this repository. *)
Require Import Coqlib Maps Errors AST Linking Integers.
Require Import Values Memory Globalenvs Events Smallstep.
Require Import Op Registers RTL Experimental PeelTwo.

Lemma map_successors_id:
  forall i, map_successors (fun pc => pc) i = i.
Proof.
  destruct i; simpl; auto. f_equal. apply map_id.
Qed.

Lemma check_function_properties:
  forall f tf rho,
  check_function f tf rho = true ->
  fn_sig tf = fn_sig f /\ fn_params tf = fn_params f /\
  fn_stacksize tf = fn_stacksize f /\
  rho (fn_entrypoint tf) = fn_entrypoint f /\
  present (fn_code tf) (fn_entrypoint tf) = true /\
  (forall pc ti, (fn_code tf)!pc = Some ti ->
    (fn_code f)!(rho pc) = Some (map_successors rho ti) /\
    forall s, In s (successors_instr ti) -> present (fn_code tf) s = true).
Proof.
  unfold check_function; intros f tf rho.
  destruct (signature_eq _ _); try discriminate.
  destruct (list_eq_dec _ _ _); try discriminate.
  destruct (zeq _ _); try discriminate.
  destruct (peq _ _); try discriminate.
  rewrite andb_true_iff. intros [ENTRY CHECK].
  split; [congruence|]. split; [congruence|]. split; [congruence|].
  split; [auto|]. split; [auto|].
  intros pc ti GET.
  apply forallb_forall with (x := (pc, ti)) in CHECK.
  2: apply PTree.elements_correct; auto.
  simpl in CHECK. unfold check_node in CHECK.
  destruct ((fn_code f)!(rho pc)) as [si|] eqn:LOOK; try discriminate.
  destruct (instruction_eq _ _); try discriminate. subst si.
  split; auto. intros s IN. apply forallb_forall with (x := s) in CHECK; auto.
Qed.

Lemma transf_function_sig:
  forall f, fn_sig (transf_function f) = fn_sig f.
Proof.
  intros. unfold transf_function. destruct (accepted f) eqn:ACC; auto.
  unfold accepted in ACC. apply check_function_properties in ACC. tauto.
Qed.
Lemma transf_function_params:
  forall f, fn_params (transf_function f) = fn_params f.
Proof.
  intros. unfold transf_function. destruct (accepted f) eqn:ACC; auto.
  unfold accepted in ACC. apply check_function_properties in ACC. tauto.
Qed.
Lemma transf_function_stacksize:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  intros. unfold transf_function. destruct (accepted f) eqn:ACC; auto.
  unfold accepted in ACC. apply check_function_properties in ACC. tauto.
Qed.

Lemma entry_match:
  forall f, match_pc f (fn_entrypoint f) (fn_entrypoint (transf_function f)).
Proof.
  intros. unfold match_pc, source_node, transf_function.
  destruct (accepted f) eqn:ACC.
  - unfold accepted in ACC. apply check_function_properties in ACC.
    destruct ACC as [_ [_ [_ [A [B C]]]]]. auto.
  - split; auto. discriminate.
Qed.

Lemma transf_function_at:
  forall f pc tpc si,
  match_pc f pc tpc -> (fn_code f)!pc = Some si ->
  exists ti,
    (fn_code (transf_function f))!tpc = Some ti /\
    map_successors (source_node f) ti = si /\
    (forall s, In s (successors_instr ti) ->
       match_pc f (source_node f s) s).
Proof.
  intros f pc tpc si [PC PRESENT] GET.
  unfold source_node, transf_function in *.
  destruct (accepted f) eqn:ACC.
  - specialize (PRESENT eq_refl). unfold present in PRESENT.
    destruct ((fn_code (candidate f))!tpc) as [ti|] eqn:TI; try discriminate.
    pose proof ACC as ACCBOOL.
    unfold accepted in ACC. apply check_function_properties in ACC.
    destruct ACC as [_ [_ [_ [_ [_ NODES]]]]].
    destruct (NODES _ _ TI) as [SRC SUCC].
    exists ti; split; auto. split. congruence.
    intros s IN. unfold match_pc, source_node, transf_function.
    rewrite ACCBOOL. split; auto.
  - subst tpc. exists si; split; auto. split. apply map_successors_id.
    intros s IN. unfold match_pc, source_node, transf_function. rewrite ACC.
    split; auto. discriminate.
Qed.

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
  | match_frames_intro: forall res f sp pc rs tpc
      (PC: match_pc f pc tpc),
      match_frames (Stackframe res f sp pc rs)
                   (Stackframe res (transf_function f) sp tpc rs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' tpc
      (STACKS: list_forall2 match_frames stk stk')
      (PC: match_pc f pc tpc),
      match_states (State stk f sp pc rs m)
                   (State stk' (transf_function f) sp tpc rs m)
  | match_callstates: forall stk f args m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Callstate stk f args m)
                   (Callstate stk' (transf_fundef f) args m)
  | match_returnstates: forall stk v m stk'
      (STACKS: list_forall2 match_frames stk stk'),
      match_states (Returnstate stk v m) (Returnstate stk' v m).

Ltac GET_INSTR :=
  match goal with
  | [ A: (fn_code ?f)!?pc = Some ?i, B: match_pc ?f ?pc ?tpc |- _ ] =>
    destruct (transf_function_at f pc tpc i B A) as [ti [CODE [EQ NEXT]]];
    destruct ti; simpl map_successors in EQ; inv EQ
  end.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS; try GET_INSTR.
  - econstructor; split. eapply exec_Inop; eauto.
    constructor; auto. apply NEXT; simpl; auto.
  - econstructor; split. eapply exec_Iop; eauto.
    instantiate (1 := v). rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
    constructor; auto. apply NEXT; simpl; auto.
  - econstructor; split.
    assert (eval_addressing tge sp addr rs ## args = Some a).
    { rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved. }
    eapply exec_Iload; eauto.
    constructor; auto. apply NEXT; simpl; auto.
  - econstructor; split.
    assert (eval_addressing tge sp addr rs ## args = Some a).
    { rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved. }
    eapply exec_Istore; eauto.
    constructor; auto. apply NEXT; simpl; auto.
  - econstructor; split.
    eapply exec_Icall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto. apply sig_preserved.
    constructor. constructor; auto. constructor. apply NEXT; simpl; auto.
  - econstructor; split.
    eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
    eapply find_function_translated; eauto. apply sig_preserved.
    rewrite transf_function_stacksize; eauto.
    constructor; auto.
  - econstructor; split.
    eapply exec_Ibuiltin; eauto.
    eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto. apply NEXT; simpl; auto.
  - econstructor; split. eapply exec_Icond; eauto.
    destruct b; constructor; auto; apply NEXT; simpl; auto.
  - rewrite list_nth_z_map in H1.
    destruct (list_nth_z l (Int.unsigned n)) as [ts|] eqn:LOOK; inv H1.
    econstructor; split. eapply exec_Ijumptable; eauto.
    constructor; auto. apply NEXT. eapply list_nth_z_in; eauto.
  - econstructor; split. eapply exec_Ireturn; eauto.
    rewrite transf_function_stacksize; eauto. constructor; auto.
  - simpl. econstructor; split. eapply exec_function_internal; eauto.
    rewrite transf_function_sig; eauto.
    rewrite transf_function_stacksize; eauto.
    rewrite transf_function_params. constructor; auto. apply entry_match.
  - econstructor; split. eapply exec_function_external; eauto.
    eapply external_call_symbols_preserved; eauto. apply senv_preserved.
    constructor; auto.
  - inv STACKS. inv H1. econstructor; split. eapply exec_return; eauto.
    constructor; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split. econstructor.
  eapply (Genv.init_mem_transf TRANSL); eauto.
  rewrite symbols_preserved. rewrite (match_program_main TRANSL). eauto.
  eapply function_ptr_translated; eauto.
  rewrite <- H3; apply sig_preserved.
  constructor. constructor.
Qed.
Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. intros. inv H0. inv H. inv STACKS. constructor. Qed.
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  apply senv_preserved. eexact transf_initial_states.
  eexact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.

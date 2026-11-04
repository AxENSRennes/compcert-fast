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

(** Soundness of guarded adjacent-load forwarding. *)
Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL LoadForward.

Record valid_pair (f: function) (p: forwarding) : Prop := Valid_pair {
  pair_first: f.(fn_code)!(first_pc p) = Some(Iload (load_chunk p) (load_addr p) (load_args p) (first_reg p) (second_pc p));
  pair_second: f.(fn_code)!(second_pc p) = Some(Iload (load_chunk p) (load_addr p) (load_args p) (second_reg p) (after_pc p));
  pair_distinct: first_pc p <> second_pc p;
  pair_not_entry: second_pc p <> f.(fn_entrypoint);
  pair_stable: ~ In (first_reg p) (load_args p);
  pair_unique: forall pc i, f.(fn_code)!pc = Some i ->
      In (second_pc p) (successors_instr i) -> pc = first_pc p
}.

Lemma existsb_peq: forall x xs, existsb (peq x) xs = true <-> In x xs.
Proof.
  intros; rewrite existsb_exists; split.
  - intros (y & IN & EQ). apply proj_sumbool_true in EQ. subst; auto.
  - intro IN. exists x; split; auto. apply proj_sumbool_is_true; auto.
Qed.
Lemma unique_predecessor_sound:
  forall f a b, unique_predecessor f a b = true ->
  forall pc i, f.(fn_code)!pc = Some i -> In b (successors_instr i) -> pc = a.
Proof.
  intros f a b U pc i CODE IN. unfold unique_predecessor in U.
  apply forallb_forall with (x := (pc,i)) in U.
  - simpl in U. assert (existsb (peq b) (successors_instr i) = true) by (apply existsb_peq; auto).
    rewrite H in U. apply proj_sumbool_true in U. auto.
  - apply PTree.elements_correct; auto.
Qed.
Lemma candidate_at_sound:
  forall f a p, candidate_at f a = Some p -> valid_pair f p.
Proof.
  intros f a p. unfold candidate_at.
  destruct (fn_code f)!a as [i|] eqn:F; try discriminate.
  destruct i as [n|op args dst n|chunk addr args r1 b|chunk addr args src n|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret]; try discriminate.
  destruct (fn_code f)!b as [i|] eqn:S; try discriminate.
  destruct i as [n|op args2 dst n|chunk2 addr2 args2 r2 s|chunk2 addr2 args2 src n|sg ros args2 dst n|sg ros args2|ef args2 res n|cond args2 yes no|arg tbl|ret]; try discriminate.
  destruct (chunk_eq chunk chunk2); try discriminate; subst chunk2.
  destruct (eq_addressing addr addr2); try discriminate; subst addr2.
  destruct (list_eq_dec peq args args2); try discriminate; subst args2.
  destruct (negb (peq a b) && negb (peq b (fn_entrypoint f)) &&
     negb (existsb (peq r1) args) && unique_predecessor f a b) eqn:CHECK; try discriminate.
  intro EQ. inv EQ. InvBooleans. constructor; simpl; auto.
  - destruct (peq a b); simpl in *; congruence.
  - destruct (peq b (fn_entrypoint f)); simpl in *; congruence.
  - intro IN. assert (existsb (peq r1) args = true) by (apply existsb_peq; auto).
    rewrite H1 in H2. discriminate.
  - eapply unique_predecessor_sound; eauto.
Qed.
Lemma selected_sound: forall f p, selected f = Some p -> valid_pair f p.
Proof.
  intros f p. unfold selected.
  generalize (PTree.elements (fn_code f)). induction l as [|[a i] tail]; simpl; try discriminate.
  destruct (candidate_at f a) as [p'|] eqn:C.
  - intro EQ. inv EQ. eapply candidate_at_sound; eauto.
  - apply IHtail.
Qed.

Lemma transformed_fields: forall f,
  fn_sig (transf_function f) = fn_sig f /\
  fn_params (transf_function f) = fn_params f /\
  fn_stacksize (transf_function f) = fn_stacksize f /\
  fn_entrypoint (transf_function f) = fn_entrypoint f.
Proof. intros. unfold transf_function. destruct (selected f); repeat split; reflexivity. Qed.
Lemma transformed_code:
  forall f pc i, (fn_code f)!pc = Some i ->
  (fn_code (transf_function f))!pc = Some (transf_instr f pc i).
Proof.
  intros f pc i H. unfold transf_function.
  destruct (selected f) eqn:SEL.
  - simpl. rewrite PTree.gmap, H. reflexivity.
  - unfold transf_instr. rewrite SEL. auto.
Qed.
Lemma nonload_unchanged:
  forall f pc i, is_load i = false -> transf_instr f pc i = i.
Proof. intros. destruct i; simpl in *; try discriminate; unfold transf_instr; destruct (selected f); auto. Qed.
Lemma special_successor:
  forall f p pc i s, selected f = Some p -> (fn_code f)!pc = Some i ->
  In s (successors_instr i) -> s = second_pc p ->
  pc = first_pc p /\ i = Iload (load_chunk p) (load_addr p) (load_args p) (first_reg p) (second_pc p).
Proof.
  intros. pose proof (selected_sound _ _ H) as V.
  assert (pc = first_pc p) by (eapply pair_unique; eauto; congruence).
  subst pc. split; auto. pose proof (pair_first _ _ V). congruence.
Qed.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Global Instance TransfLoadForwardLink : TransfLink match_prog := TransfTotalLink transf_function.
Lemma transf_program_match: forall p, match_prog p (transf_program p).
Proof. intros. apply match_transform_program. Qed.

Section PRESERVATION.
Variables prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Lemma functions_translated: forall v f,
  Genv.find_funct ge v = Some f -> Genv.find_funct tge v = Some(transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated: forall v f,
  Genv.find_funct_ptr ge v = Some f -> Genv.find_funct_ptr tge v = Some(transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved: forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig(transf_fundef f) = funsig f.
Proof. destruct f; simpl; auto. apply (proj1 (transformed_fields f)). Qed.
Lemma find_function_translated: forall ros rs fd,
  find_function ge ros rs = Some fd -> find_function tge ros rs = Some(transf_fundef fd).
Proof.
  unfold find_function; intros. destruct ros as [r|id].
  - eapply functions_translated; eauto.
  - rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
    eapply function_ptr_translated; eauto.
Qed.

Definition available f sp pc rs m :=
  forall p, selected f = Some p -> pc = second_pc p ->
  exists a, eval_addressing ge sp (load_addr p) rs##(load_args p) = Some a /\
            Mem.loadv (load_chunk p) m a = Some(rs#(first_reg p)).
Definition not_second f pc := forall p, selected f = Some p -> pc <> second_pc p.
Lemma available_not_second:
  forall f sp pc rs m, not_second f pc -> available f sp pc rs m.
Proof. unfold available, not_second; intros f sp pc rs m NOT p SEL EQ.
  exfalso. exact (NOT p SEL EQ). Qed.
Lemma nonload_successor:
  forall f pc i s, (fn_code f)!pc = Some i -> is_load i = false ->
  In s (successors_instr i) -> not_second f s.
Proof.
  unfold not_second; intros f pc i s CODE NON IN p SEL EQ.
  destruct (special_successor _ _ _ _ _ SEL CODE IN EQ) as [_ OP]. subst i; discriminate.
Qed.
Lemma entry_not_second: forall f, not_second f (fn_entrypoint f).
Proof.
  unfold not_second; intros f p SEL EQ.
  pose proof (pair_not_entry _ _ (selected_sound _ _ SEL)); congruence.
Qed.
Lemma regs_set_args:
  forall (rs:regset) (r:reg) (v:val) (args:list reg), ~ In r args -> (rs#r <- v)##args = rs##args.
Proof.
  induction args; simpl; intros; auto.
  rewrite Regmap.gso by tauto. rewrite IHargs by tauto. reflexivity.
Qed.
Lemma available_after_load:
  forall f sp pc rs m chunk addr args dst s a v,
  (fn_code f)!pc = Some(Iload chunk addr args dst s) ->
  eval_addressing ge sp addr rs##args = Some a -> Mem.loadv chunk m a = Some v ->
  available f sp s (rs#dst <- v) m.
Proof.
  unfold available. intros f sp pc rs m chunk addr args dst s a v CODE ADDR LOAD p SEL EQ.
  destruct (special_successor _ _ _ _ _ SEL CODE (or_introl eq_refl) EQ) as [PC OP].
  inv OP. exists a. split.
  - rewrite regs_set_args by (eapply pair_stable; eapply selected_sound; eauto). auto.
  - rewrite Regmap.gss. auto.
Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs,
      not_second f pc ->
      match_frames (Stackframe res f sp pc rs) (Stackframe res (transf_function f) sp pc rs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_regular: forall stk stk' f sp pc rs m,
      list_forall2 match_frames stk stk' -> available f sp pc rs m ->
      match_states (State stk f sp pc rs m) (State stk' (transf_function f) sp pc rs m)
  | match_call: forall stk stk' f args m,
      list_forall2 match_frames stk stk' ->
      match_states (Callstate stk f args m) (Callstate stk' (transf_fundef f) args m)
  | match_return: forall stk stk' v m,
      list_forall2 match_frames stk stk' ->
      match_states (Returnstate stk v m) (Returnstate stk' v m).

Lemma lookup_nonload:
  forall f pc i, (fn_code f)!pc = Some i -> is_load i = false ->
  (fn_code (transf_function f))!pc = Some i.
Proof. intros. rewrite (transformed_code _ _ _ H). rewrite nonload_unchanged; auto. Qed.

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS;
  try match goal with CODE: (fn_code ?f)!?pc = Some ?i |- _ =>
      pose proof (lookup_nonload _ _ _ CODE eq_refl) as TCODE
  end.
- (* nop *)
  econstructor; split. eapply exec_Inop; eauto.
  constructor; auto. apply available_not_second. eapply nonload_successor; eauto; simpl; auto.
- (* op *)
  econstructor; split. eapply exec_Iop; eauto.
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  constructor; auto. apply available_not_second. eapply nonload_successor; eauto; simpl; auto.
- (* load *)
  pose proof (transformed_code _ _ _ H) as TCODE.
  unfold transf_instr in TCODE.
  destruct (selected f) as [p|] eqn:SEL.
  + destruct (peq pc (second_pc p)) as [EQ|NE].
    * subst pc.
      pose proof (pair_second _ _ (selected_sound _ _ SEL)) as SECOND.
      rewrite H in SECOND. inv SECOND.
      match goal with AV: available _ _ _ _ _ |- _ =>
        destruct (AV p SEL eq_refl) as (a0 & ADDR & LOAD) end.
      assert (a0 = a) by congruence. subst a0.
      assert (v = rs#(first_reg p)) by congruence. subst v.
      econstructor; split. eapply exec_Iop; eauto. simpl. reflexivity.
      constructor; auto. eapply available_after_load; eauto.
    * econstructor; split. eapply exec_Iload; eauto.
      rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
      constructor; auto. eapply available_after_load; eauto.
  + econstructor; split. eapply exec_Iload; eauto.
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    constructor; auto. eapply available_after_load; eauto.
- (* store *)
  econstructor; split. eapply exec_Istore; eauto.
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  constructor; auto. apply available_not_second. eapply nonload_successor; eauto; simpl; auto.
- (* call *)
  econstructor; split. eapply exec_Icall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto. apply sig_preserved.
  constructor. constructor; auto. constructor.
  eapply nonload_successor; eauto; simpl; auto.
- (* tailcall *)
  econstructor; split. eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto. apply sig_preserved.
  rewrite (proj1 (proj2 (proj2 (transformed_fields f)))) . eauto.
  constructor; auto.
- (* builtin *)
  econstructor; split. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto. apply available_not_second. eapply nonload_successor; eauto; simpl; auto.
- (* conditional *)
  econstructor; split. eapply exec_Icond; eauto.
  constructor; auto. apply available_not_second. eapply nonload_successor; eauto; simpl; destruct b; auto.
- (* jump table *)
  econstructor; split. eapply exec_Ijumptable; eauto.
  constructor; auto. apply available_not_second. eapply nonload_successor; eauto; simpl.
  eapply list_nth_z_in; eauto.
- (* return *)
  econstructor; split. eapply exec_Ireturn; eauto.
  rewrite (proj1 (proj2 (proj2 (transformed_fields f)))) . eauto.
  constructor; auto.
- (* internal entry *)
  simpl. econstructor; split.
  replace (fn_entrypoint f) with (fn_entrypoint (transf_function f)) by (apply (proj2 (proj2 (proj2 (transformed_fields f))))).
  replace (fn_params f) with (fn_params (transf_function f)) by (apply (proj1 (proj2 (transformed_fields f)))).
  eapply exec_function_internal; eauto.
  rewrite (proj1 (transformed_fields f)); auto.
  rewrite (proj1 (proj2 (proj2 (transformed_fields f)))); eauto.
  rewrite (proj2 (proj2 (proj2 (transformed_fields f)))).
  rewrite (proj1 (proj2 (transformed_fields f))).
  constructor; auto. apply available_not_second. apply entry_not_second.
- (* external entry *)
  econstructor; split. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return into caller *)
  match goal with ST: list_forall2 _ _ _ |- _ => inv ST end.
  match goal with FR: match_frames _ _ |- _ => inv FR end.
  econstructor; split. eapply exec_return; eauto.
  constructor; auto. apply available_not_second; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split.
  econstructor.
  - eapply (Genv.init_mem_transf TRANSL); eauto.
  - replace (prog_main tprog) with (prog_main prog).
    rewrite symbols_preserved. exact H1.
    symmetry. exact (match_program_main TRANSL).
  - eapply function_ptr_translated; eauto.
  - rewrite <- H3. apply sig_preserved.
  - constructor. constructor.
Qed.
Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof. intros. inv H0. inv H.
  match goal with ST: list_forall2 _ _ _ |- _ => inv ST end. constructor. Qed.
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_step.
  - apply senv_preserved.
  - eexact transf_initial_states.
  - eexact transf_final_states.
  - exact step_simulation.
Qed.
End PRESERVATION.

(** Executable regressions of the checked pattern, independent of heuristics. *)
Module Regression.
Definition base_addr := Aindexed Int64.zero.
Definition first := Iload Mint32 base_addr (1%positive::nil) 2%positive 2%positive.
Definition second := Iload Mint32 base_addr (1%positive::nil) 3%positive 3%positive.
Definition code0 := PTree.set 1%positive first
  (PTree.set 2%positive second
   (PTree.set 3%positive (Ireturn (Some 3%positive)) (PTree.empty instruction))).
Definition fixture := mkfunction signature_main nil 0%Z code0 1%positive.
Example valid_pair_detected: exists p, candidate_at fixture 1%positive = Some p.
Proof. vm_compute. eexists; reflexivity. Qed.
Example repeated_load_replaced:
  (fn_code (transf_function fixture))!2%positive =
  Some (Iop Omove (2%positive::nil) 3%positive 3%positive).
Proof. vm_compute. reflexivity. Qed.
Definition other_pred := mkfunction signature_main nil 0%Z
  (PTree.set 4%positive (Inop 2%positive) code0) 1%positive.
Example multiple_predecessors_rejected: candidate_at other_pred 1%positive = None.
Proof. vm_compute. reflexivity. Qed.
Definition entry_second := mkfunction signature_main nil 0%Z code0 2%positive.
Example entry_target_rejected: candidate_at entry_second 1%positive = None.
Proof. vm_compute. reflexivity. Qed.
End Regression.

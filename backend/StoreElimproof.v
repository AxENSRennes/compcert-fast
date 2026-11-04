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

(** Adjacent overwritten-store elimination: byte-level overwrite foundation. *)
Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memdata Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL StoreElim.

Lemma zmap_set_commute:
  forall (c: ZMap.t memval) p q x y, p <> q ->
  ZMap.set p x (ZMap.set q y c) = ZMap.set q y (ZMap.set p x c).
Proof.
  intros. unfold ZMap.set, PMap.set; simpl. f_equal.
  apply PTree.extensionality; intro i. repeat rewrite PTree.gsspec.
  assert (ZIndexed.index p <> ZIndexed.index q).
  { intro EQ. apply H. apply ZIndexed.index_inj; auto. }
  repeat destruct (peq _ _); subst; congruence.
Qed.
Lemma setN_commute_before:
  forall bytes c p q value, q < p ->
  ZMap.set q value (Mem.setN bytes p c) = Mem.setN bytes p (ZMap.set q value c).
Proof.
  induction bytes; simpl; intros; auto.
  rewrite IHbytes by lia. rewrite zmap_set_commute by lia. reflexivity.
Qed.
Lemma setN_overwrite_same_length:
  forall bytes1 bytes2 p c, length bytes1 = length bytes2 ->
  Mem.setN bytes2 p (Mem.setN bytes1 p c) = Mem.setN bytes2 p c.
Proof.
  induction bytes1; destruct bytes2; simpl; intros; try discriminate; auto.
  rewrite setN_commute_before by lia. rewrite ZMap.set2.
  apply IHbytes1. congruence.
Qed.
Lemma memory_fields_ext:
  forall (m1 m2: Mem.mem), Mem.mem_contents m1 = Mem.mem_contents m2 ->
  Mem.mem_access m1 = Mem.mem_access m2 -> Mem.nextblock m1 = Mem.nextblock m2 -> m1 = m2.
Proof. intros. destruct m1, m2; simpl in *. apply Mem.mkmem_ext; auto. Qed.
Lemma store_overwrite:
  forall chunk m b ofs v1 m1 v2 m2,
  Mem.store chunk m b ofs v1 = Some m1 ->
  Mem.store chunk m1 b ofs v2 = Some m2 ->
  Mem.store chunk m b ofs v2 = Some m2.
Proof.
  intros chunk m b ofs v1 m1 v2 m2 S1 S2.
  assert (VALID: Mem.valid_access m chunk b ofs Writable).
  { eapply Mem.store_valid_access_3; eauto. }
  destruct (Mem.valid_access_store _ _ _ _ v2 VALID) as [m3 S3].
  assert (m3 = m2).
  { apply memory_fields_ext.
    - rewrite (Mem.store_mem_contents _ _ _ _ _ _ S3).
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ S2).
      rewrite (Mem.store_mem_contents _ _ _ _ _ _ S1).
      rewrite PMap.gss.
      rewrite setN_overwrite_same_length by (rewrite !encode_val_length; auto).
      rewrite PMap.set2. reflexivity.
    - rewrite (Mem.store_access _ _ _ _ _ _ S3).
      rewrite (Mem.store_access _ _ _ _ _ _ S2).
      rewrite (Mem.store_access _ _ _ _ _ _ S1). reflexivity.
    - rewrite (Mem.nextblock_store _ _ _ _ _ _ S3).
      rewrite (Mem.nextblock_store _ _ _ _ _ _ S2).
      rewrite (Mem.nextblock_store _ _ _ _ _ _ S1). reflexivity. }
  congruence.
Qed.
Lemma storev_overwrite:
  forall chunk m address v1 m1 v2 m2,
  Mem.storev chunk m address v1 = Some m1 ->
  Mem.storev chunk m1 address v2 = Some m2 ->
  Mem.storev chunk m address v2 = Some m2.
Proof.
  intros chunk m address v1 m1 v2 m2 S1 S2.
  unfold Mem.storev in *; destruct address; try discriminate.
  destruct (zle (Ptrofs.unsigned i + size_chunk chunk) Ptrofs.modulus); try discriminate.
  eapply store_overwrite; eauto.
Qed.

Record valid_pair (f: function) (p: store_pair) : Prop := Valid_pair {
  pair_first: f.(fn_code)!(first_pc p) = Some(Istore (store_chunk p) (store_addr p) (store_args p) (first_src p) (second_pc p));
  pair_second: f.(fn_code)!(second_pc p) = Some(Istore (store_chunk p) (store_addr p) (store_args p) (second_src p) (after_pc p));
  pair_distinct: first_pc p <> second_pc p;
  pair_not_entry: second_pc p <> f.(fn_entrypoint);
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
  destruct i as [n|op args dst n|chunk addr args src n|chunk addr args r1 b|sg ros args dst n|sg ros args|ef args res n|cond args yes no|arg tbl|ret]; try discriminate.
  destruct (fn_code f)!b as [i|] eqn:S; try discriminate.
  destruct i as [n|op args2 dst n|chunk2 addr2 args2 src n|chunk2 addr2 args2 r2 s|sg ros args2 dst n|sg ros args2|ef args2 res n|cond args2 yes no|arg tbl|ret]; try discriminate.
  destruct (chunk_eq chunk chunk2); try discriminate; subst chunk2.
  destruct (eq_addressing addr addr2); try discriminate; subst addr2.
  destruct (list_eq_dec peq args args2); try discriminate; subst args2.
  destruct (negb (peq a b) && negb (peq b (fn_entrypoint f)) &&
     unique_predecessor f a b) eqn:CHECK; try discriminate.
  intro EQ. inv EQ. InvBooleans. constructor; simpl; auto.
  - destruct (peq a b); simpl in *; congruence.
  - destruct (peq b (fn_entrypoint f)); simpl in *; congruence.
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
Lemma nonstore_unchanged:
  forall f pc i, is_store i = false -> transf_instr f pc i = i.
Proof. intros. destruct i; simpl in *; try discriminate; unfold transf_instr; destruct (selected f); auto. Qed.
Lemma special_successor:
  forall f p pc i s, selected f = Some p -> (fn_code f)!pc = Some i ->
  In s (successors_instr i) -> s = second_pc p ->
  pc = first_pc p /\ i = Istore (store_chunk p) (store_addr p) (store_args p) (first_src p) (second_pc p).
Proof.
  intros. pose proof (selected_sound _ _ H) as V.
  assert (pc = first_pc p) by (eapply pair_unique; eauto; congruence).
  subst pc. split; auto. pose proof (pair_first _ _ V). congruence.
Qed.

Definition match_prog (p tp: RTL.program) :=
  match_program (fun ctx f tf => tf = transf_fundef f) eq p tp.
Global Instance TransfStoreElimLink : TransfLink match_prog := TransfTotalLink transf_function.
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

Definition not_second f pc := forall p, selected f = Some p -> pc <> second_pc p.
Definition not_first f pc := forall p, selected f = Some p -> pc <> first_pc p.
Lemma nonstore_successor:
  forall f pc i s, (fn_code f)!pc = Some i -> is_store i = false ->
  In s (successors_instr i) -> not_second f s.
Proof.
  unfold not_second; intros f pc i s CODE NON IN p SEL EQ.
  destruct (special_successor _ _ _ _ _ SEL CODE IN EQ) as [_ OP]. subst i; discriminate.
Qed.
Lemma successor_not_first:
  forall f pc i s, (fn_code f)!pc = Some i -> In s (successors_instr i) ->
  not_first f pc -> not_second f s.
Proof.
  unfold not_first, not_second; intros f pc i s CODE IN FIRST p SEL EQ.
  destruct (special_successor _ _ _ _ _ SEL CODE IN EQ) as [PC _].
  exact (FIRST p SEL PC).
Qed.
Lemma entry_not_second: forall f, not_second f (fn_entrypoint f).
Proof.
  unfold not_second; intros f p SEL EQ.
  pose proof (pair_not_entry _ _ (selected_sound _ _ SEL)); congruence.
Qed.
Lemma second_not_first:
  forall f p, selected f = Some p -> not_first f (second_pc p).
Proof.
  unfold not_first; intros f p SEL p' SEL'. rewrite SEL in SEL'. inv SEL'.
  pose proof (pair_distinct _ _ (selected_sound _ _ SEL)); congruence.
Qed.
Lemma lookup_nonstore:
  forall f pc i, (fn_code f)!pc = Some i -> is_store i = false ->
  (fn_code (transf_function f))!pc = Some i.
Proof. intros. rewrite (transformed_code _ _ _ H). rewrite nonstore_unchanged; auto. Qed.

Inductive match_frames: RTL.stackframe -> RTL.stackframe -> Prop :=
  | match_frames_intro: forall res f sp pc rs,
      not_second f pc ->
      match_frames (Stackframe res f sp pc rs) (Stackframe res (transf_function f) sp pc rs).
Inductive match_states: RTL.state -> RTL.state -> Prop :=
  | match_normal: forall stk stk' f sp pc rs m,
      list_forall2 match_frames stk stk' -> not_second f pc ->
      match_states (State stk f sp pc rs m) (State stk' (transf_function f) sp pc rs m)
  | match_special: forall stk stk' f sp rs m0 m1 p a,
      list_forall2 match_frames stk stk' -> selected f = Some p ->
      eval_addressing ge sp (store_addr p) rs##(store_args p) = Some a ->
      Mem.storev (store_chunk p) m0 a rs#(first_src p) = Some m1 ->
      match_states (State stk f sp (second_pc p) rs m1)
                   (State stk' (transf_function f) sp (second_pc p) rs m0)
  | match_call: forall stk stk' f args m,
      list_forall2 match_frames stk stk' ->
      match_states (Callstate stk f args m) (Callstate stk' (transf_fundef f) args m)
  | match_return: forall stk stk' v m,
      list_forall2 match_frames stk stk' ->
      match_states (Returnstate stk v m) (Returnstate stk' v m).

Lemma step_simulation:
  forall S1 t S2, RTL.step ge S1 t S2 ->
  forall S1', match_states S1 S1' ->
  exists S2', RTL.step tge S1' t S2' /\ match_states S2 S2'.
Proof.
  induction 1; intros S1' MS; inv MS;
  try match goal with SEL: selected ?f = Some ?p,
                      CODE: (fn_code ?f)!(second_pc ?p) = Some ?i |- _ =>
      pose proof (pair_second _ _ (selected_sound _ _ SEL)) as SECOND;
      rewrite CODE in SECOND; discriminate
  end;
  try match goal with CODE: (fn_code ?f)!?pc = Some ?i |- _ =>
      pose proof (lookup_nonstore _ _ _ CODE eq_refl) as TCODE
  end.
- (* nop *)
  econstructor; split. eapply exec_Inop; eauto.
  constructor; auto. eapply nonstore_successor; eauto; simpl; auto.
- (* op *)
  econstructor; split. eapply exec_Iop; eauto.
  rewrite <- H0. apply eval_operation_preserved. exact symbols_preserved.
  constructor; auto. eapply nonstore_successor; eauto; simpl; auto.
- (* load *)
  econstructor; split. eapply exec_Iload; eauto.
  rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
  constructor; auto. eapply nonstore_successor; eauto; simpl; auto.
- (* store from normal point *)
  pose proof (transformed_code _ _ _ H) as TCODE.
  unfold transf_instr in TCODE.
  destruct (selected f) as [p|] eqn:SEL.
  + destruct (peq pc (first_pc p)) as [EQ|NE].
    * subst pc. pose proof (pair_first _ _ (selected_sound _ _ SEL)) as FIRST.
      rewrite H in FIRST. inv FIRST.
      econstructor; split. eapply exec_Inop; eauto.
      eapply match_special; eauto.
    * econstructor; split. eapply exec_Istore; eauto.
      rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
      constructor; auto. eapply successor_not_first; eauto; simpl; auto.
      unfold not_first; intros p' EQ. rewrite SEL in EQ. inv EQ. auto.
  + econstructor; split. eapply exec_Istore; eauto.
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    constructor; auto. eapply successor_not_first; eauto; simpl; auto.
    unfold not_first; intros p EQ. congruence.
- (* store at second point collapses the two memories *)
  match goal with SEL: selected f = Some ?p |- _ =>
    pose proof (pair_second _ _ (selected_sound _ _ SEL)) as SECOND end.
  rewrite H in SECOND. inv SECOND.
  match goal with SEL: selected f = Some ?p |- _ =>
    pose proof (transformed_code _ _ _ H) as TCODE;
    unfold transf_instr in TCODE; rewrite SEL in TCODE;
    destruct (peq (second_pc p) (first_pc p)) as [BAD|GOOD]
  end.
  + exfalso. match goal with SEL: selected f = Some ?p |- _ =>
      pose proof (pair_distinct _ _ (selected_sound _ _ SEL)) end. congruence.
  + assert (a0 = a) by congruence. subst a0.
    econstructor; split. eapply exec_Istore; eauto.
    rewrite <- H0. apply eval_addressing_preserved. exact symbols_preserved.
    eapply storev_overwrite; eauto.
    constructor; auto. eapply successor_not_first; eauto; simpl; auto.
    eapply second_not_first; eauto.
- (* call *)
  econstructor; split. eapply exec_Icall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto. apply sig_preserved.
  constructor. constructor; auto. constructor.
  eapply nonstore_successor; eauto; simpl; auto.
- (* tailcall *)
  econstructor; split. eapply exec_Itailcall with (fd := transf_fundef fd); eauto.
  eapply find_function_translated; eauto. apply sig_preserved.
  rewrite (proj1 (proj2 (proj2 (transformed_fields f)))); eauto.
  constructor; auto.
- (* builtin *)
  econstructor; split. eapply exec_Ibuiltin; eauto.
  eapply eval_builtin_args_preserved with (ge1 := ge); eauto. exact symbols_preserved.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto. eapply nonstore_successor; eauto; simpl; auto.
- (* conditional *)
  econstructor; split. eapply exec_Icond; eauto.
  constructor; auto. eapply nonstore_successor; eauto; simpl; destruct b; auto.
- (* jump table *)
  econstructor; split. eapply exec_Ijumptable; eauto.
  constructor; auto. eapply nonstore_successor; eauto; simpl.
  eapply list_nth_z_in; eauto.
- (* return *)
  econstructor; split. eapply exec_Ireturn; eauto.
  rewrite (proj1 (proj2 (proj2 (transformed_fields f)))); eauto.
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
  constructor; auto. apply entry_not_second.
- (* external entry *)
  econstructor; split. eapply exec_function_external; eauto.
  eapply external_call_symbols_preserved; eauto. apply senv_preserved.
  constructor; auto.
- (* return into caller *)
  match goal with ST: list_forall2 _ _ _ |- _ => inv ST end.
  match goal with FR: match_frames _ _ |- _ => inv FR end.
  econstructor; split. eapply exec_return; eauto.
  constructor; auto.
Qed.

Lemma transf_initial_states:
  forall S1, RTL.initial_state prog S1 ->
  exists S2, RTL.initial_state tprog S2 /\ match_states S1 S2.
Proof.
  intros. inv H. econstructor; split. econstructor.
  - eapply (Genv.init_mem_transf TRANSL); eauto.
  - replace (prog_main tprog) with (prog_main prog).
    rewrite symbols_preserved. exact H1. symmetry. exact (match_program_main TRANSL).
  - eapply function_ptr_translated; eauto.
  - rewrite <- H3. apply sig_preserved.
  - constructor. constructor.
Qed.
Lemma transf_final_states:
  forall S1 S2 r, match_states S1 S2 -> RTL.final_state S1 r -> RTL.final_state S2 r.
Proof.
  intros. inv H0. inv H.
  match goal with ST: list_forall2 _ _ _ |- _ => inv ST end. constructor.
Qed.
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

Module Regression.
Definition base_addr := Aindexed Int64.zero.
Definition first := Istore Mint32 base_addr (1%positive::nil) 2%positive 2%positive.
Definition second := Istore Mint32 base_addr (1%positive::nil) 3%positive 3%positive.
Definition code0 := PTree.set 1%positive first
  (PTree.set 2%positive second
   (PTree.set 3%positive (Ireturn (Some 3%positive)) (PTree.empty instruction))).
Definition fixture := mkfunction signature_main nil 0%Z code0 1%positive.
Example valid_pair_detected: exists p, candidate_at fixture 1%positive = Some p.
Proof. vm_compute. eexists; reflexivity. Qed.
Example first_store_removed:
  (fn_code (transf_function fixture))!1%positive = Some (Inop 2%positive).
Proof. vm_compute. reflexivity. Qed.
Example second_store_retained:
  (fn_code (transf_function fixture))!2%positive = Some second.
Proof. vm_compute. reflexivity. Qed.
Definition other_pred := mkfunction signature_main nil 0%Z
  (PTree.set 4%positive (Inop 2%positive) code0) 1%positive.
Example multiple_predecessors_rejected: candidate_at other_pred 1%positive = None.
Proof. vm_compute. reflexivity. Qed.
Definition entry_second := mkfunction signature_main nil 0%Z code0 2%positive.
Example entry_target_rejected: candidate_at entry_second 1%positive = None.
Proof. vm_compute. reflexivity. Qed.
End Regression.

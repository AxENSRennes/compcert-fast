(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Replay the selected branch of the paired Clight loop. *)
Require Import Coqlib Maps AST Integers Values Memory Events Smallstep.
Require Import Ctypes Cop Clight ClightBigstep.
Require Import PointerNeonFacts ArrayPair ArrayPairBase ArrayPairReplay ArrayPairWide.

Local Open Scope Z_scope.

Definition lane_offset (p: plan) (ofs: ptrofs) (i: int) (lane: nat) : ptrofs :=
  match layout p with
  | Indexed _ =>
      let j := match lane with
               | O => i
               | S _ => Int.add i (Int.repr (Z.of_nat lane))
               end in
      Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_intu j))
  | _ =>
      match lane with
      | O => ofs
      | S _ => Ptrofs.add ofs
          (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr (Z.of_nat lane))))
      end
  end.

Definition index_value (p: plan) (le: temp_env) (i: int) : Prop :=
  match layout p with
  | Indexed id => le!id = Some (Vint i)
  | _ => True
  end.

Lemma eval_target_addr:
  forall ge p e le m b ofs i lane,
  pointer_value ge e p le b ofs ->
  index_value p le i ->
  eval_expr ge e le m (addr p lane) (Vptr b (lane_offset p ofs i lane)).
Proof.
  intros ge p e le m b ofs i lane PTR IDX.
  pose proof (pointer_value_eval ge e p le b ofs m PTR) as BASE.
  unfold index_value in IDX. unfold addr, lane_offset.
  destruct (layout p); destruct lane; cbn; try exact BASE.
  - eapply eval_Ebinop; [exact BASE|apply eval_Econst_int|].
    cbn [sem_binary_operation]. unfold sem_add, classify_add.
    rewrite pointer_expr_typeconv. reflexivity.
  - eapply eval_Ebinop; [exact BASE|apply eval_Econst_int|].
    cbn [sem_binary_operation]. unfold sem_add, classify_add.
    rewrite pointer_expr_typeconv. reflexivity.
  - eapply eval_Ebinop; [exact BASE|apply eval_Etempvar; exact IDX|].
    cbn [sem_binary_operation]. unfold sem_add, classify_add.
    rewrite pointer_expr_typeconv. reflexivity.
  - eapply eval_Ebinop.
    + exact BASE.
    + eapply eval_Ebinop; [apply eval_Etempvar; exact IDX|apply eval_Econst_int|reflexivity].
    + cbn [sem_binary_operation]. unfold sem_add, classify_add.
      rewrite pointer_expr_typeconv. reflexivity.
Qed.

Definition loop_flag (p: plan) (i n: int) : bool :=
  match layout p with
  | Indexed _ => Int.ltu i n
  | _ => negb (Int.eq n Int.zero)
  end.

Definition pair_flag (p: plan) (i n: int) : bool :=
  let rem := match layout p with Indexed _ => Int.sub n i | _ => n end in
  negb (Int.ltu rem (Int.repr 2)).

Definition base_ready (p: plan) (le: temp_env) : Prop :=
  pointer_wide p = true -> forall b ofs,
  le!(pointer p) = Some (Vptr b ofs) -> (8 | Ptrofs.unsigned ofs).

Lemma base_ready_set_other:
  forall p le id v, id <> pointer p ->
  (base_ready p (PTree.set id v le) <-> base_ready p le).
Proof. intros. unfold base_ready. rewrite PTree.gso by congruence. reflexivity. Qed.

(** The base is aligned and the index is even whenever a wide loop can take a turn.
    After a scalar tail the loop is exhausted, so its odd index is harmless. *)
Definition wide_ready (p: plan) (le: temp_env) : Prop :=
  forall i n,
    wide p = true ->
    le!(bound p) = Some (Vint n) ->
    index_value p le i ->
    loop_flag p i n = true ->
    (2 | Int.unsigned i) /\ base_ready p le.

Lemma wide_ready_narrow:
  forall p le, wide p = false -> wide_ready p le.
Proof. intros p le NARROW i n WIDE; congruence. Qed.

Lemma wide_indexed:
  forall p, wide p = true -> exists id, layout p = Indexed id.
Proof.
  intros p WIDE. unfold wide in WIDE.
  destruct (layout p); try discriminate. eauto.
Qed.

Lemma wide_ready_init:
  forall p le id,
  layout p = Indexed id ->
  base_ready p (PTree.set id (Vint Int.zero) le) ->
  wide_ready p (PTree.set id (Vint Int.zero) le).
Proof.
  intros p le id L BASE i n _ _ IDX _. split; [|exact BASE].
  unfold index_value in IDX. rewrite L, PTree.gss in IDX.
  injection IDX as <-. rewrite Int.unsigned_zero. apply Z.divide_0_r.
Qed.

Local Lemma test_bool:
  forall m b, bool_val (Val.of_bool b) tint m = Some b.
Proof. intros m []; reflexivity. Qed.

Lemma eval_target_loop_test:
  forall ge p e le m i n,
  le!(bound p) = Some (Vint n) ->
  index_value p le i ->
  exists v, eval_expr ge e le m (loop_test p) v /\
    bool_val v (typeof (loop_test p)) m = Some (loop_flag p i n).
Proof.
  intros ge p e le m i n COUNT IDX.
  unfold loop_test, loop_flag, index_value in *.
  destruct (layout p).
  - exists (Vint n). split; [apply eval_Etempvar; exact COUNT|reflexivity].
  - exists (Vint n). split; [apply eval_Etempvar; exact COUNT|reflexivity].
  - exists (Val.of_bool (Int.ltu i n)). split.
    + eapply eval_Ebinop; [apply eval_Etempvar; exact IDX|apply eval_Etempvar; exact COUNT|reflexivity].
    + apply test_bool.
Qed.

Lemma eval_target_pair_test:
  forall ge p e le m i n,
  le!(bound p) = Some (Vint n) ->
  index_value p le i ->
  eval_expr ge e le m (pair_test p) (Val.of_bool (pair_flag p i n)) /\
  bool_val (Val.of_bool (pair_flag p i n)) (typeof (pair_test p)) m = Some (pair_flag p i n).
Proof.
  intros ge p e le m i n COUNT IDX. split.
  - unfold pair_test, pair_flag, index_value in *.
    destruct (layout p).
    + eapply eval_Ebinop; [apply eval_Etempvar; exact COUNT|apply eval_Econst_int|reflexivity].
    + eapply eval_Ebinop; [apply eval_Etempvar; exact COUNT|apply eval_Econst_int|reflexivity].
    + eapply eval_Ebinop.
      * eapply eval_Ebinop; [apply eval_Etempvar; exact COUNT|apply eval_Etempvar; exact IDX|reflexivity].
      * apply eval_Econst_int.
      * reflexivity.
  - apply test_bool.
Qed.

Definition advanced_env (p: plan) (le: temp_env) (b: block) (ofs: ptrofs)
    (i n: int) (step: Z) : temp_env :=
  let delta := Int.repr step in
  match layout p with
  | Indexed id => PTree.set id (Vint (Int.add i delta)) le
  | _ =>
      let ofs' := Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints delta)) in
      PTree.set (bound p) (Vint (Int.sub n delta))
        (PTree.set (pointer p) (Vptr b ofs') le)
  end.

Local Lemma advance_pointer_exec:
  forall ge p e le m b ofs step,
  pointer_value ge e p le b ofs ->
  let ofs' := Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr step))) in
  Clight2.exec_stmt ge e le m (advance_pointer p step)
    E0 (PTree.set (pointer p) (Vptr b ofs') le) m Out_normal.
Proof.
  intros ge p e le m b ofs step PTR ofs'.
  apply ClightBigstep.exec_Sset.
  eapply eval_Ebinop.
  - eapply pointer_value_eval; exact PTR.
  - apply eval_Econst_int.
  - cbn [sem_binary_operation]. unfold sem_add, classify_add.
    rewrite pointer_expr_typeconv. reflexivity.
Qed.

Local Lemma decrease_count_exec:
  forall ge p e le m n step,
  le!(bound p) = Some (Vint n) ->
  Clight2.exec_stmt ge e le m (decrease_count p step)
    E0 (PTree.set (bound p) (Vint (Int.sub n (Int.repr step))) le) m Out_normal.
Proof.
  intros ge p e le m n step COUNT.
  apply ClightBigstep.exec_Sset.
  eapply eval_Ebinop; [apply eval_Etempvar; exact COUNT|apply eval_Econst_int|reflexivity].
Qed.

Lemma target_advance_exec:
  forall ge p e le m b ofs i n step,
  pointer p <> bound p ->
  pointer_value ge e p le b ofs ->
  le!(bound p) = Some (Vint n) ->
  index_value p le i ->
  Clight2.exec_stmt ge e le m (advance p step) E0
    (advanced_env p le b ofs i n step) m Out_normal.
Proof.
  intros ge p e le m b ofs i n step DISTINCT PTR COUNT IDX.
  unfold advance, advanced_env, index_value in *.
  destruct (layout p).
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + eapply advance_pointer_exec; exact PTR.
    + apply decrease_count_exec. rewrite PTree.gso by congruence. exact COUNT.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + eapply advance_pointer_exec; exact PTR.
    + apply decrease_count_exec. rewrite PTree.gso by congruence. exact COUNT.
  - apply ClightBigstep.exec_Sset.
    eapply eval_Ebinop; [apply eval_Etempvar; exact IDX|apply eval_Econst_int|reflexivity].
Qed.

Section LOOP.

Variable prog : Clight.program.
Let ge := Clight.globalenv prog.

Lemma target_loop_cycle:
  forall p f k e le m le' m' v0 v1 paired,
  eval_expr ge e le m (loop_test p) v0 ->
  bool_val v0 (typeof (loop_test p)) m = Some true ->
  eval_expr ge e le m (pair_test p) v1 ->
  bool_val v1 (typeof (pair_test p)) m = Some paired ->
  Clight2.exec_stmt ge e le m (if paired then pair_branch p else scalar_branch p)
    E0 le' m' Out_normal ->
  plus Clight.step2 ge (State f (target_loop p) k e le m)
    E0 (State f (target_loop p) k e le' m').
Proof.
  intros p f k e le m le' m' v0 v1 paired TEST GO TEST_PAIR PICK BRANCH.
  unfold target_loop.
  set (body := Ssequence (guard p) (Sifthenelse (pair_test p) (pair_branch p) (scalar_branch p))).
  assert (BODY: Clight2.exec_stmt ge e le m body E0 le' m' Out_normal).
  {
    unfold body, guard.
    eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m).
    - eapply ClightBigstep.exec_Sifthenelse with (b := true); eauto.
      apply ClightBigstep.exec_Sskip.
    - eapply ClightBigstep.exec_Sifthenelse with (b := paired); eauto.
  }
  destruct (ClightBigstep.exec_stmt_steps function_entry2 prog _ _ _ _ _ _ _ _
    BODY f (Kloop1 body Sskip k)) as [s [STEPS OUT]].
  inversion OUT; subst s.
  eapply plus_left with (t1 := E0) (t2 := E0).
  - apply Clight.step_loop.
  - eapply star_trans with (t1 := E0) (t2 := E0).
    + exact STEPS.
    + eapply star_two with (t1 := E0) (t2 := E0).
      * apply Clight.step_skip_or_continue_loop1. now left.
      * apply Clight.step_skip_loop2.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma target_loop_zero:
  forall p f k e le m v,
  eval_expr ge e le m (loop_test p) v ->
  bool_val v (typeof (loop_test p)) m = Some false ->
  plus Clight.step2 ge (State f (target_loop p) k e le m)
    E0 (State f Sskip k e le m).
Proof.
  intros p f k e le m v TEST STOP.
  unfold target_loop.
  set (body := Ssequence (guard p) (Sifthenelse (pair_test p) (pair_branch p) (scalar_branch p))).
  assert (BODY: Clight2.exec_stmt ge e le m body E0 le m Out_break).
  {
    unfold body, guard.
    eapply ClightBigstep.exec_Sseq_2.
    - eapply ClightBigstep.exec_Sifthenelse with (b := false); eauto.
      apply ClightBigstep.exec_Sbreak.
    - discriminate.
  }
  destruct (ClightBigstep.exec_stmt_steps function_entry2 prog _ _ _ _ _ _ _ _
    BODY f (Kloop1 body Sskip k)) as [s [STEPS OUT]].
  inversion OUT; subst s.
  eapply plus_left with (t1 := E0) (t2 := E0).
  - apply Clight.step_loop.
  - eapply star_right with (t1 := E0) (t2 := E0).
    + exact STEPS.
    + apply Clight.step_break_loop1.
    + reflexivity.
  - reflexivity.
Qed.

Lemma target_loop_pair:
  forall p f k e le m0 m1 m2 le' v0 v1 b0 ofs0 b1 ofs1 lo hi,
  let packed_env := PTree.set (scratch p)
    (packed_add_result lo hi (increment p) (increment p)) le in
  wide p = false ->
  eval_expr ge e le m0 (loop_test p) v0 ->
  bool_val v0 (typeof (loop_test p)) m0 = Some true ->
  eval_expr ge e le m0 (pair_test p) v1 ->
  bool_val v1 (typeof (pair_test p)) m0 = Some true ->
  eval_expr ge e le m0 (addr p 0) (Vptr b0 ofs0) ->
  eval_expr ge e le m0 (addr p 1) (Vptr b1 ofs1) ->
  eval_expr ge e packed_env m0 (addr p 0) (Vptr b0 ofs0) ->
  eval_expr ge e packed_env m1 (addr p 1) (Vptr b1 ofs1) ->
  Mem.loadv Mint32 m0 (Vptr b0 ofs0) = Some (Vint lo) ->
  Mem.loadv Mint32 m0 (Vptr b1 ofs1) = Some (Vint hi) ->
  Mem.storev Mint32 m0 (Vptr b0 ofs0) (Vint (Int.add lo (increment p))) = Some m1 ->
  Mem.storev Mint32 m1 (Vptr b1 ofs1) (Vint (Int.add hi (increment p))) = Some m2 ->
  Clight2.exec_stmt ge e packed_env m2 (packed_advance p) E0 le' m2 Out_normal ->
  plus Clight.step2 ge (State f (target_loop p) k e le m0)
    E0 (State f (target_loop p) k e le' m2).
Proof.
  intros p f k e le m0 m1 m2 le' v0 v1 b0 ofs0 b1 ofs1 lo hi packed_env
    NARROW TEST GO TEST_PAIR PICK ADDR0 ADDR1 STORE_ADDR0 STORE_ADDR1 LOAD0 LOAD1 STORE0 STORE1 ADVANCE.
  eapply target_loop_cycle with (paired := true); eauto.
  unfold pair_branch. rewrite NARROW.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := packed_env) (m1 := m2).
  - eapply packed_update_exec; eauto.
  - exact ADVANCE.
Qed.

Lemma target_loop_pair_wide:
  forall p f k e le m0 m1 m2 le' v0 v1 b ofs lo hi,
  let packed_env := PTree.set (scratch p)
    (packed_add_result lo hi (increment p) (increment p)) le in
  wide p = true ->
  eval_expr ge e le m0 (loop_test p) v0 ->
  bool_val v0 (typeof (loop_test p)) m0 = Some true ->
  eval_expr ge e le m0 (pair_test p) v1 ->
  bool_val v1 (typeof (pair_test p)) m0 = Some true ->
  eval_expr ge e le m0 (addr p 0) (Vptr b ofs) ->
  eval_expr ge e packed_env m0 (addr p 0) (Vptr b ofs) ->
  (8 | Ptrofs.unsigned ofs) ->
  Mem.loadv Mint32 m0 (Vptr b ofs) = Some (Vint lo) ->
  Mem.loadv Mint32 m0 (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint hi) ->
  Mem.storev Mint32 m0 (Vptr b ofs) (Vint (Int.add lo (increment p))) = Some m1 ->
  Mem.storev Mint32 m1 (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4)))
    (Vint (Int.add hi (increment p))) = Some m2 ->
  Clight2.exec_stmt ge e packed_env m2 (packed_advance p) E0 le' m2 Out_normal ->
  plus Clight.step2 ge (State f (target_loop p) k e le m0)
    E0 (State f (target_loop p) k e le' m2).
Proof.
  intros p f k e le m0 m1 m2 le' v0 v1 b ofs lo hi packed_env
    WIDE TEST GO TEST_PAIR PICK ADDR STORE_ADDR ALIGN LOAD0 LOAD1 STORE0 STORE1 ADVANCE.
  eapply target_loop_cycle with (paired := true); eauto.
  unfold pair_branch. rewrite WIDE.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := packed_env) (m1 := m2).
  - eapply wide_update_exec with (m1 := m1); eauto.
    destruct (wide_indexed _ WIDE) as [id L].
    unfold addr. rewrite L. reflexivity.
  - exact ADVANCE.
Qed.

Lemma target_loop_tail:
  forall p f k e le m m' le' v0 v1 b ofs v,
  eval_expr ge e le m (loop_test p) v0 ->
  bool_val v0 (typeof (loop_test p)) m = Some true ->
  eval_expr ge e le m (pair_test p) v1 ->
  bool_val v1 (typeof (pair_test p)) m = Some false ->
  eval_expr ge e le m (addr p 0) (Vptr b ofs) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint v) ->
  Mem.storev Mint32 m (Vptr b ofs) (Vint (Int.add v (increment p))) = Some m' ->
  Clight2.exec_stmt ge e le m' (scalar_advance p) E0 le' m' Out_normal ->
  plus Clight.step2 ge (State f (target_loop p) k e le m)
    E0 (State f (target_loop p) k e le' m').
Proof.
  intros p f k e le m m' le' v0 v1 b ofs v TEST GO TEST_PAIR PICK ADDR LOAD STORE ADVANCE.
  eapply target_loop_cycle with (paired := false); eauto.
  unfold scalar_branch.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m').
  - eapply scalar_update_exec; eauto.
  - exact ADVANCE.
Qed.

End LOOP.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Relate successful scalar turns to the corresponding target branch. *)
Require Import Coqlib Maps AST Integers Values Memory Events Smallstep.
Require Import Ctypes Cop Clight ClightBigstep.
Require Import PointerNeonFacts AutoPairMemory ArrayPair ArrayPairMatch.
Require Import ArrayPairLocalSource ArrayPairTarget.

Local Open Scope Z_scope.

Local Lemma eval_temp_inv:
  forall ge e le m id ty v,
  eval_expr ge e le m (Etempvar id ty) v -> le!id = Some v.
Proof.
  intros ge e le m id ty v EVAL. inversion EVAL; subst; auto.
  match goal with H: eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _ => inversion H end.
Qed.

Local Lemma eval_binop_inv:
  forall ge e le m op a b ty v,
  eval_expr ge e le m (Ebinop op a b ty) v ->
  exists va vb,
    eval_expr ge e le m a va /\ eval_expr ge e le m b vb /\
    sem_binary_operation ge op va (typeof a) vb (typeof b) m = Some v.
Proof.
  intros ge e le m op a b ty v EVAL. inversion EVAL; subst; eauto.
  match goal with H: eval_lvalue _ _ _ _ (Ebinop _ _ _ _) _ _ _ |- _ => inversion H end.
Qed.

Local Lemma exec_set_inv:
  forall ge e le m id a le' m',
  Clight2.exec_stmt ge e le m (Sset id a) E0 le' m' Out_normal ->
  exists v, eval_expr ge e le m a v /\ le' = PTree.set id v le /\ m' = m.
Proof. intros ge e le m id a le' m' EXEC. inversion EXEC; subst; eauto. Qed.

Local Lemma bool_of_flag_inv:
  forall b m flag,
  bool_val (Val.of_bool b) tint m = Some flag -> b = flag.
Proof. intros [] m flag BOOL; inversion BOOL; reflexivity. Qed.

Lemma loop_test_effect:
  forall ge p e le m v flag,
  eval_expr ge e le m (loop_test p) v ->
  bool_val v (typeof (loop_test p)) m = Some flag ->
  exists i n, le!(bound p) = Some (Vint n) /\
    index_value p le i /\ loop_flag p i n = flag.
Proof.
  intros ge p e le m v flag EVAL BOOL.
  unfold loop_test, count_expr, index_value, loop_flag in *.
  destruct (layout p) as [| |id].
  - apply eval_temp_inv in EVAL. destruct v; try discriminate.
    exists Int.zero, i; split; [exact EVAL|]. split; [exact I|].
    change (Some (negb (Int.eq i Int.zero)) = Some flag) in BOOL. congruence.
  - apply eval_temp_inv in EVAL. destruct v; try discriminate.
    exists Int.zero, i; split; [exact EVAL|]. split; [exact I|].
    change (Some (negb (Int.eq i Int.zero)) = Some flag) in BOOL. congruence.
  - apply eval_binop_inv in EVAL as (vi & vn & EI & EN & CMP).
    apply eval_temp_inv in EI, EN.
    destruct vi; try discriminate. destruct vn; try discriminate.
    cbn in CMP. inversion CMP; subst v.
    exists i, i0. split; [exact EN|]. split; [exact EI|].
    eapply bool_of_flag_inv. exact BOOL.
Qed.

Lemma addr0_effect:
  forall ge p e le m b ofs i,
  index_value p le i ->
  eval_expr ge e le m (addr p 0) (Vptr b ofs) ->
  exists base, le!(pointer p) = Some (Vptr b base) /\
    ofs = lane_offset p base i 0.
Proof.
  intros ge p e le m b ofs i IDX ADDR.
  unfold addr, pointer_expr, index_value, lane_offset in *.
  destruct (layout p) as [| |id].
  - apply eval_temp_inv in ADDR. exists ofs; auto.
  - apply eval_temp_inv in ADDR. exists ofs; auto.
  - apply eval_binop_inv in ADDR as (vp & vi & EP & EI & OP).
    apply eval_temp_inv in EP, EI.
    rewrite IDX in EI. inversion EI; subst vi.
    destruct vp; try discriminate.
    cbn in OP. inversion OP; subst.
    eexists; split; [exact EP|reflexivity].
Qed.

Local Lemma eval_sint_inv:
  forall ge e le m step v,
  eval_expr ge e le m (sint step) v -> v = Vint (Int.repr step).
Proof.
  intros ge e le m step v EVAL. unfold sint in EVAL. inversion EVAL; subst; auto.
  match goal with H: eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H end.
Qed.

Local Lemma advance_pointer_effect:
  forall ge p e le m b ofs le' m' step,
  le!(pointer p) = Some (Vptr b ofs) ->
  Clight2.exec_stmt ge e le m (advance_pointer p step) E0 le' m' Out_normal ->
  le' = PTree.set (pointer p)
    (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr step))))) le
  /\ m' = m.
Proof.
  intros ge p e le m b ofs le' m' step PTR EXEC.
  unfold advance_pointer in EXEC.
  apply exec_set_inv in EXEC as (v & EVAL & -> & ->).
  apply eval_binop_inv in EVAL as (vp & vn & EP & EN & OP).
  apply eval_temp_inv in EP. rewrite PTR in EP. inversion EP; subst vp.
  apply eval_sint_inv in EN. subst vn.
  cbn in OP. inversion OP. auto.
Qed.

Local Lemma decrease_count_effect:
  forall ge p e le m n le' m' step,
  le!(bound p) = Some (Vint n) ->
  Clight2.exec_stmt ge e le m (decrease_count p step) E0 le' m' Out_normal ->
  le' = PTree.set (bound p) (Vint (Int.sub n (Int.repr step))) le /\ m' = m.
Proof.
  intros ge p e le m n le' m' step COUNT EXEC.
  unfold decrease_count in EXEC.
  apply exec_set_inv in EXEC as (v & EVAL & -> & ->).
  apply eval_binop_inv in EVAL as (vn & vk & EN & EK & OP).
  apply eval_temp_inv in EN. rewrite COUNT in EN. inversion EN; subst vn.
  apply eval_sint_inv in EK. subst vk.
  cbn in OP. inversion OP. auto.
Qed.

Local Lemma advance_index_effect:
  forall ge e le m id i le' m' step,
  le!id = Some (Vint i) ->
  Clight2.exec_stmt ge e le m (advance_index id step) E0 le' m' Out_normal ->
  le' = PTree.set id (Vint (Int.add i (Int.repr step))) le /\ m' = m.
Proof.
  intros ge e le m id i le' m' step IDX EXEC.
  unfold advance_index in EXEC.
  apply exec_set_inv in EXEC as (v & EVAL & -> & ->).
  apply eval_binop_inv in EVAL as (vi & vk & EI & EK & OP).
  apply eval_temp_inv in EI. rewrite IDX in EI. inversion EI; subst vi.
  apply eval_sint_inv in EK. subst vk.
  cbn in OP. inversion OP. auto.
Qed.

Local Lemma advance_pointer_count_effect:
  forall ge p e le m b ofs n le' m' step,
  pointer p <> bound p ->
  le!(pointer p) = Some (Vptr b ofs) ->
  le!(bound p) = Some (Vint n) ->
  Clight2.exec_stmt ge e le m (Ssequence (advance_pointer p step) (decrease_count p step))
    E0 le' m' Out_normal ->
  le' = PTree.set (bound p) (Vint (Int.sub n (Int.repr step)))
    (PTree.set (pointer p)
      (Vptr b (Ptrofs.add ofs (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr step))))) le)
  /\ m' = m.
Proof.
  intros ge p e le m b ofs n le' m' step DISTINCT PTR COUNT EXEC.
  apply exec_sequence_normal in EXEC as (le1 & m1 & ADV & DEC).
  apply (advance_pointer_effect _ _ _ _ _ _ _ _ _ _ PTR) in ADV as [-> ->].
  eapply decrease_count_effect; [|exact DEC].
  rewrite PTree.gso by congruence. exact COUNT.
Qed.

Lemma advance_effect:
  forall ge p e le m b ofs i n le' m' step,
  pointer p <> bound p ->
  le!(pointer p) = Some (Vptr b ofs) ->
  le!(bound p) = Some (Vint n) ->
  index_value p le i ->
  Clight2.exec_stmt ge e le m (advance p step) E0 le' m' Out_normal ->
  le' = advanced_env p le b ofs i n step /\ m' = m.
Proof.
  intros ge p e le m b ofs i n le' m' step DISTINCT PTR COUNT IDX EXEC.
  unfold advance, advanced_env, index_value in *.
  destruct (layout p); eauto using advance_pointer_count_effect, advance_index_effect.
Qed.

Definition next_base (p: plan) (ofs: ptrofs) : ptrofs :=
  match layout p with Indexed _ => ofs | _ => Ptrofs.add ofs (Ptrofs.repr 4) end.
Definition next_index (p: plan) (i: int) : int :=
  match layout p with Indexed _ => Int.add i Int.one | _ => i end.
Definition next_count (p: plan) (n: int) : int :=
  match layout p with Indexed _ => n | _ => Int.sub n Int.one end.

Lemma advanced_env_one_values:
  forall p le b ofs i n,
  well_formed p ->
  le!(pointer p) = Some (Vptr b ofs) ->
  le!(bound p) = Some (Vint n) ->
  index_value p le i ->
  let le' := advanced_env p le b ofs i n 1 in
  le'!(pointer p) = Some (Vptr b (next_base p ofs)) /\
  le'!(bound p) = Some (Vint (next_count p n)) /\
  index_value p le' (next_index p i).
Proof.
  intros p le b ofs i n [DISTINCT W] PTR COUNT IDX.
  unfold advanced_env, next_base, next_count, next_index, index_value in *.
  destruct (layout p) as [| |id]; cbn zeta.
  - rewrite PTree.gso by congruence. rewrite !PTree.gss. repeat split; reflexivity.
  - rewrite PTree.gso by congruence. rewrite !PTree.gss. repeat split; reflexivity.
  - destruct W. rewrite !PTree.gso by congruence. rewrite PTree.gss.
    repeat split; assumption || reflexivity.
Qed.

Local Lemma set_commute:
  forall (le: temp_env) a b x y,
  a <> b -> PTree.set a x (PTree.set b y le) = PTree.set b y (PTree.set a x le).
Proof.
  intros le a b x y NE.
  apply PTree.extensionality; intros id; rewrite !PTree.gsspec.
  destruct (peq id a), (peq id b); congruence.
Qed.

Local Lemma set_twice:
  forall (le: temp_env) a x y, PTree.set a x (PTree.set a y le) = PTree.set a x le.
Proof.
  intros. apply PTree.extensionality; intros id; rewrite !PTree.gsspec.
  destruct (peq id a); reflexivity.
Qed.

Lemma advanced_env_scratch:
  forall p le b ofs i n step v,
  advanced_env p (PTree.set (scratch p) v le) b ofs i n step =
  PTree.set (scratch p) v (advanced_env p le b ofs i n step).
Proof.
  intros. unfold advanced_env.
  destruct (layout p) eqn:L.
  - rewrite (set_commute _ (pointer p)), (set_commute _ (bound p)) by
      (pose proof (scratch_pointer p); pose proof (scratch_bound p); congruence).
    reflexivity.
  - rewrite (set_commute _ (pointer p)), (set_commute _ (bound p)) by
      (pose proof (scratch_pointer p); pose proof (scratch_bound p); congruence).
    reflexivity.
  - apply set_commute. pose proof (scratch_index p index L). congruence.
Qed.

Local Lemma advanced_env_two_pointer:
  forall p le b ofs n,
  pointer p <> bound p ->
  PTree.set (bound p) (Vint (Int.sub (Int.sub n Int.one) Int.one))
    (PTree.set (pointer p) (Vptr b (Ptrofs.add (Ptrofs.add ofs (Ptrofs.repr 4)) (Ptrofs.repr 4)))
      (PTree.set (bound p) (Vint (Int.sub n Int.one))
        (PTree.set (pointer p) (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))) le))) =
  PTree.set (bound p) (Vint (Int.sub n (Int.repr 2)))
    (PTree.set (pointer p) (Vptr b (Ptrofs.add ofs (Ptrofs.repr 8))) le).
Proof.
  intros p le b ofs n DISTINCT.
  rewrite (set_commute _ (pointer p)) by exact DISTINCT.
  rewrite !set_twice, Ptrofs.add_assoc, !Int.sub_add_opp, Int.add_assoc. reflexivity.
Qed.

Lemma advanced_env_two:
  forall p le b ofs i n,
  well_formed p ->
  advanced_env p (advanced_env p le b ofs i n 1) b
    (next_base p ofs) (next_index p i) (next_count p n) 1 =
  advanced_env p le b ofs i n 2.
Proof.
  intros p le b ofs i n [DISTINCT W].
  unfold advanced_env, next_base, next_index, next_count.
  destruct (layout p).
  - apply advanced_env_two_pointer. exact DISTINCT.
  - apply advanced_env_two_pointer. exact DISTINCT.
  - rewrite set_twice, Int.add_assoc. reflexivity.
Qed.

Lemma lane_offset_next:
  forall p ofs i,
  lane_offset p (next_base p ofs) (next_index p i) 0 = lane_offset p ofs i 1.
Proof. intros; unfold lane_offset, next_base, next_index; destruct (layout p); reflexivity. Qed.

Local Definition remaining (p: plan) (i n: int) : Z :=
  Int.unsigned n - match layout p with Indexed _ => Int.unsigned i | _ => 0 end.

Local Lemma loop_flag_spec:
  forall p i n, loop_flag p i n = true <-> 0 < remaining p i n.
Proof.
  intros p i n. unfold loop_flag, remaining, Int.eq, Int.ltu.
  pose proof (Int.unsigned_range n).
  destruct (layout p).
  - rewrite Int.unsigned_zero. destruct (zeq (Int.unsigned n) 0); simpl; intuition lia || discriminate.
  - rewrite Int.unsigned_zero. destruct (zeq (Int.unsigned n) 0); simpl; intuition lia || discriminate.
  - destruct (zlt (Int.unsigned i) (Int.unsigned n)); intuition lia || discriminate.
Qed.

Local Lemma pair_flag_spec:
  forall p i n,
  loop_flag p i n = true -> pair_flag p i n = true <-> 2 <= remaining p i n.
Proof.
  intros p i n GO. apply loop_flag_spec in GO.
  unfold pair_flag, remaining in *. unfold Int.ltu.
  change (Int.unsigned (Int.repr 2)) with 2.
  pose proof (Int.unsigned_range_2 i).
  pose proof (Int.unsigned_range_2 n).
  destruct (layout p).
  - destruct (zlt (Int.unsigned n) 2); simpl; intuition lia || discriminate.
  - destruct (zlt (Int.unsigned n) 2); simpl; intuition lia || discriminate.
  - unfold Int.sub. rewrite Int.unsigned_repr by lia.
    destruct (zlt (Int.unsigned n - Int.unsigned i) 2); simpl; intuition lia || discriminate.
Qed.

Local Lemma remaining_next:
  forall p i n, loop_flag p i n = true ->
  remaining p (next_index p i) (next_count p n) = remaining p i n - 1.
Proof.
  intros p i n GO. apply loop_flag_spec in GO.
  unfold remaining, next_index, next_count in *.
  pose proof (Int.unsigned_range_2 i).
  pose proof (Int.unsigned_range_2 n).
  destruct (layout p); unfold Int.add, Int.sub; rewrite Int.unsigned_one;
    rewrite Int.unsigned_repr by lia; lia.
Qed.

Lemma pair_flag_next:
  forall p i n, loop_flag p i n = true ->
  pair_flag p i n = loop_flag p (next_index p i) (next_count p n).
Proof.
  intros p i n GO.
  pose proof (remaining_next _ _ _ GO) as NEXT.
  apply pair_flag_spec in GO.
  pose proof (loop_flag_spec p (next_index p i) (next_count p n)) as TEST.
  rewrite NEXT in TEST.
  destruct (pair_flag p i n), (loop_flag p (next_index p i) (next_count p n));
    reflexivity || exfalso; intuition lia || discriminate.
Qed.

Lemma lane_offset_adjacent:
  forall p ofs i n,
  loop_flag p i n = true ->
  lane_offset p ofs i 1 = Ptrofs.add (lane_offset p ofs i 0) (Ptrofs.repr 4).
Proof.
  intros p ofs i n GO. apply loop_flag_spec in GO.
  unfold remaining, lane_offset in *. destruct (layout p); try reflexivity.
  change (Int.repr (Z.of_nat 1)) with Int.one.
  assert (INDEX: Ptrofs.of_intu (Int.add i Int.one) = Ptrofs.add (Ptrofs.of_intu i) Ptrofs.one).
  {
    unfold Ptrofs.of_intu, Ptrofs.of_int, Int.add.
    rewrite Int.unsigned_one, Int.unsigned_repr by
      (pose proof (Int.unsigned_range_2 n); pose proof (Int.unsigned_range_2 i); lia).
    unfold Ptrofs.add. rewrite Ptrofs.unsigned_one.
    apply Ptrofs.eqm_samerepr. apply Ptrofs.eqm_add; auto with ints.
  }
  rewrite INDEX, Ptrofs.mul_add_distr_r, Ptrofs.mul_one, Ptrofs.add_assoc.
  reflexivity.
Qed.

Definition scratch_env (p: plan) (le tle: temp_env) : Prop :=
  exists v, tle = PTree.set (scratch p) v le.

Local Lemma scratch_ptr_value:
  forall p (le: temp_env) v,
  (PTree.set (scratch p) v le)!(pointer p) = le!(pointer p).
Proof. intros; apply PTree.gso; pose proof (scratch_pointer p); congruence. Qed.

Local Lemma scratch_count_value:
  forall p (le: temp_env) v,
  (PTree.set (scratch p) v le)!(bound p) = le!(bound p).
Proof. intros; apply PTree.gso; pose proof (scratch_bound p); congruence. Qed.

Local Lemma scratch_index_value:
  forall p le i v, index_value p le i -> index_value p (PTree.set (scratch p) v le) i.
Proof.
  intros p le i v IDX. unfold index_value in *.
  destruct (layout p) eqn:L; auto.
  rewrite PTree.gso by (pose proof (scratch_index p index L); congruence). exact IDX.
Qed.

Local Lemma test_loop_flag:
  forall ge p e le m i n flag,
  le!(bound p) = Some (Vint n) ->
  index_value p le i ->
  test_value ge e le m (loop_test p) flag ->
  loop_flag p i n = flag.
Proof.
  intros ge p e le m i n flag COUNT IDX (v & EVAL & BOOL).
  destruct (loop_test_effect _ _ _ _ _ _ _ EVAL BOOL) as (j & k & COUNT' & IDX' & FLAG).
  rewrite COUNT in COUNT'. inversion COUNT'; subst k.
  unfold index_value, loop_flag in *. destruct (layout p); auto.
  rewrite IDX in IDX'. inversion IDX'; subst j. exact FLAG.
Qed.

Local Lemma eval_uint_inv:
  forall ge e le m step v,
  eval_expr ge e le m (uint step) v -> v = Vint (Int.repr step).
Proof.
  intros ge e le m step v EVAL. unfold uint in EVAL. inversion EVAL; subst; auto.
  match goal with H: eval_lvalue _ _ _ _ (Econst_int _ _) _ _ _ |- _ => inversion H end.
Qed.

Local Lemma test_pair_flag:
  forall ge p e le m i n flag,
  le!(bound p) = Some (Vint n) ->
  index_value p le i ->
  test_value ge e le m (pair_test p) flag ->
  pair_flag p i n = flag.
Proof.
  intros ge p e le m i n flag COUNT IDX (v & EVAL & BOOL).
  unfold pair_test, pair_flag, index_value in *.
  destruct (layout p) as [| |id];
    apply eval_binop_inv in EVAL as (vr & vk & ER & EK & CMP);
    apply eval_uint_inv in EK; subst vk.
  - apply eval_temp_inv in ER. rewrite COUNT in ER. inversion ER; subst vr.
    change (Some (Val.of_bool (negb (Int.ltu n (Int.repr 2)))) = Some v) in CMP.
    injection CMP as <-. eapply bool_of_flag_inv. exact BOOL.
  - apply eval_temp_inv in ER. rewrite COUNT in ER. inversion ER; subst vr.
    change (Some (Val.of_bool (negb (Int.ltu n (Int.repr 2)))) = Some v) in CMP.
    injection CMP as <-. eapply bool_of_flag_inv. exact BOOL.
  - apply eval_binop_inv in ER as (vn & vi & EN & EI & SUB).
    apply eval_temp_inv in EN, EI.
    rewrite COUNT in EN. rewrite IDX in EI. inversion EN; inversion EI; subst vn vi.
    change (Some (Vint (Int.sub n i)) = Some vr) in SUB. injection SUB as <-.
    change (Some (Val.of_bool (negb (Int.ltu (Int.sub n i) (Int.repr 2)))) = Some v) in CMP.
    injection CMP as <-. eapply bool_of_flag_inv. exact BOOL.
Qed.

Local Lemma source_turn_effect:
  forall ge p e le m le' m',
  well_formed p ->
  source_turn ge p e le m le' m' ->
  exists b ofs i n lo,
    le!(pointer p) = Some (Vptr b ofs) /\
    le!(bound p) = Some (Vint n) /\
    index_value p le i /\
    loop_flag p i n = true /\
    Mem.loadv Mint32 m (Vptr b (lane_offset p ofs i 0)) = Some (Vint lo) /\
    Mem.storev Mint32 m (Vptr b (lane_offset p ofs i 0))
      (Vint (Int.add lo (increment p))) = Some m' /\
    le' = advanced_env p le b ofs i n 1.
Proof.
  intros ge p e le m le' m' [DISTINCT WF] ((v & EV & BOOL) & UPDATE & ADVANCE).
  destruct (loop_test_effect _ _ _ _ _ _ _ EV BOOL) as (i & n & COUNT & IDX & GO).
  destruct (exec_scalar_update_inv _ _ _ _ _ _ UPDATE) as (b & offs & lo & ADDR & LOAD & STORE).
  destruct (addr0_effect _ _ _ _ _ _ _ _ IDX ADDR) as (ofs & PTR & ->).
  exists b, ofs, i, n, lo. repeat split; auto.
  eapply advance_effect in ADVANCE as [A _]; eauto.
Qed.

Lemma source_turn_choice:
  forall ge p e le m le1 m1,
  well_formed p ->
  source_turn ge p e le m le1 m1 ->
  test_value ge e le m (pair_test p) false \/
  ~ test_value ge e le1 m1 (loop_test p) false.
Proof.
  intros ge p e le m le1 m1 WF TURN.
  destruct (source_turn_effect _ _ _ _ _ _ _ WF TURN)
    as (b & ofs & i & n & lo & PTR & COUNT & IDX & GO & LOAD & STORE & ->).
  destruct (pair_flag p i n) eqn:PAIR.
  - right. intros EXIT.
    destruct (advanced_env_one_values _ _ _ _ _ _ WF PTR COUNT IDX) as (PTR1 & COUNT1 & IDX1).
    pose proof (test_loop_flag _ _ _ _ _ _ _ _ COUNT1 IDX1 EXIT) as STOP.
    rewrite (pair_flag_next _ _ _ GO), STOP in PAIR. discriminate.
  - left. destruct (eval_target_pair_test ge p e le m i n COUNT IDX) as [EVAL BOOL].
    exists (Val.of_bool (pair_flag p i n)). split; [exact EVAL|].
    rewrite BOOL. now rewrite PAIR.
Qed.

Section TARGET.
Variables (ge: genv) (tprog: Clight.program).
Let tge := Clight.globalenv tprog.

Lemma target_turn_zero:
  forall p f k e le tle m,
  scratch_env p le tle ->
  test_value ge e le m (loop_test p) false ->
  plus Clight.step2 tge (State f (target_loop p) k e tle m)
    E0 (State f Sskip k e tle m).
Proof.
  intros p f k e le tle m (saved & ->) (v & EV & BOOL).
  destruct (loop_test_effect _ _ _ _ _ _ _ EV BOOL) as (i & n & COUNT & IDX & STOP).
  rewrite <- (scratch_count_value p le saved) in COUNT.
  apply (scratch_index_value _ _ _ saved) in IDX.
  destruct (eval_target_loop_test tge p e _ m i n COUNT IDX) as (tv & TEV & TBOOL).
  rewrite STOP in TBOOL. eapply target_loop_zero; eauto.
Qed.

Lemma target_turn_tail:
  forall p f k e le tle m le1 m1,
  well_formed p ->
  scratch_env p le tle ->
  source_turn ge p e le m le1 m1 ->
  test_value ge e le m (pair_test p) false ->
  exists tle1,
    plus Clight.step2 tge (State f (target_loop p) k e tle m)
      E0 (State f (target_loop p) k e tle1 m1) /\
    scratch_env p le1 tle1.
Proof.
  intros p f k e le tle m le1 m1 WF (saved & ->) TURN TAIL.
  destruct (source_turn_effect _ _ _ _ _ _ _ WF TURN)
    as (b & ofs & i & n & lo & PTR & COUNT & IDX & GO & LOAD & STORE & ->).
  pose proof (test_pair_flag _ _ _ _ _ _ _ _ COUNT IDX TAIL) as SINGLE.
  rewrite <- (scratch_ptr_value p le saved) in PTR.
  rewrite <- (scratch_count_value p le saved) in COUNT.
  apply (scratch_index_value _ _ _ saved) in IDX.
  destruct (eval_target_loop_test tge p e _ m i n COUNT IDX) as (v0 & TEST & BOOL0).
  destruct (eval_target_pair_test tge p e _ m i n COUNT IDX) as (PAIR & BOOL1).
  rewrite GO in BOOL0.
  assert (SINGLE_BOOL: bool_val (Val.of_bool (pair_flag p i n)) (typeof (pair_test p)) m = Some false).
  { now rewrite BOOL1, SINGLE. }
  exists (PTree.set (scratch p) saved (advanced_env p le b ofs i n 1)). split.
  - eapply target_loop_tail with (b := b) (ofs := lane_offset p ofs i 0) (v := lo); eauto.
    + apply eval_target_addr; auto.
    + rewrite <- advanced_env_scratch.
      apply target_advance_exec; auto. exact (proj1 WF).
  - now exists saved.
Qed.

Lemma target_turn_pair:
  forall p f k e le tle m le1 m1 le2 m2,
  well_formed p ->
  scratch_env p le tle ->
  source_turn ge p e le m le1 m1 ->
  source_turn ge p e le1 m1 le2 m2 ->
  exists tle2,
    plus Clight.step2 tge (State f (target_loop p) k e tle m)
      E0 (State f (target_loop p) k e tle2 m2) /\
    scratch_env p le2 tle2.
Proof.
  intros p f k e le tle m le1 m1 le2 m2 WF (saved & ->) TURN0 TURN1.
  destruct (source_turn_effect _ _ _ _ _ _ _ WF TURN0)
    as (b & ofs & i & n & lo & PTR & COUNT & IDX & GO & LOAD0 & STORE0 & ->).
  destruct (advanced_env_one_values _ _ _ _ _ _ WF PTR COUNT IDX) as (PTR1 & COUNT1 & IDX1).
  destruct TURN1 as (NEXT & UPDATE1 & ADVANCE1).
  pose proof (test_loop_flag _ _ _ _ _ _ _ _ COUNT1 IDX1 NEXT) as GO1.
  pose proof (eq_trans (pair_flag_next _ _ _ GO) GO1) as BOTH.
  destruct (exec_scalar_update_inv _ _ _ _ _ _ UPDATE1)
    as (b1 & ofs1 & hi & ADDR1 & LOAD1 & STORE1).
  destruct (addr0_effect _ _ _ _ _ _ _ _ IDX1 ADDR1) as (base1 & PTR1' & OFF1).
  rewrite PTR1 in PTR1'. inversion PTR1'; subst b1 base1.
  rewrite lane_offset_next in OFF1. subst ofs1.
  assert (EARLY_LOAD1: Mem.loadv Mint32 m (Vptr b (lane_offset p ofs i 1)) = Some (Vint hi)).
  {
    pose proof (load32_after_store32_next _ _ _ _ STORE0) as UNCHANGED.
    change (Mem.loadv Mint32 m1 (Vptr b (Ptrofs.add (lane_offset p ofs i 0) (Ptrofs.repr 4))) =
      Mem.loadv Mint32 m (Vptr b (Ptrofs.add (lane_offset p ofs i 0) (Ptrofs.repr 4)))) in UNCHANGED.
    rewrite <- (lane_offset_adjacent _ _ _ _ GO) in UNCHANGED.
    rewrite <- UNCHANGED. exact LOAD1.
  }
  destruct (advance_effect ge p e _ m2 b _ _ _ le2 m2 1 (proj1 WF) PTR1 COUNT1 IDX1 ADVANCE1)
    as [LE2 _].
  rewrite (advanced_env_two _ _ _ _ _ _ WF) in LE2. subst le2.
  set (packed := packed_add_result lo hi (increment p) (increment p)).
  exists (PTree.set (scratch p) packed (advanced_env p le b ofs i n 2)). split.
  - assert (TPTR: (PTree.set (scratch p) saved le)!(pointer p) = Some (Vptr b ofs)).
    { rewrite scratch_ptr_value. exact PTR. }
    assert (TCOUNT: (PTree.set (scratch p) saved le)!(bound p) = Some (Vint n)).
    { rewrite scratch_count_value. exact COUNT. }
    pose proof (scratch_index_value _ _ _ saved IDX) as TIDX.
    destruct (eval_target_loop_test tge p e _ m i n TCOUNT TIDX) as (v0 & TEST & BOOL0).
    destruct (eval_target_pair_test tge p e _ m i n TCOUNT TIDX) as (PAIR & BOOL1).
    rewrite GO in BOOL0.
    assert (BOTH_BOOL: bool_val (Val.of_bool (pair_flag p i n)) (typeof (pair_test p)) m = Some true).
    { now rewrite BOOL1, BOTH. }
    eapply target_loop_pair with (m1 := m1) (lo := lo) (hi := hi)
      (b0 := b) (ofs0 := lane_offset p ofs i 0) (b1 := b) (ofs1 := lane_offset p ofs i 1); eauto.
    + apply eval_target_addr; auto.
    + apply eval_target_addr; auto.
    + apply eval_target_addr; [rewrite scratch_ptr_value; exact TPTR|].
      apply scratch_index_value. exact TIDX.
    + apply eval_target_addr; [rewrite scratch_ptr_value; exact TPTR|].
      apply scratch_index_value. exact TIDX.
    + rewrite set_twice. rewrite <- advanced_env_scratch.
      apply target_advance_exec; [exact (proj1 WF)| | |].
      * rewrite scratch_ptr_value. exact PTR.
      * rewrite scratch_count_value. exact COUNT.
      * apply scratch_index_value. exact IDX.
  - now exists packed.
Qed.

End TARGET.

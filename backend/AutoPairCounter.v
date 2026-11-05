(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under    *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Exact unsigned countdown facts for grouping two scalar iterations.
    The countdown remains scalar; the pair test prevents decrement wrap. *)
Require Import Coqlib AST Integers Values Memory Op.

Definition decrement (n: int): int := Int.add n (Int.repr (-1)).
Definition decrement_pair (n: int): int := Int.add n (Int.repr (-2)).
Definition pair_guard (n: int): bool := Int.cmpu Cge n (Int.repr 2).

Lemma counter_condition_defined:
  forall c k v m b,
  eval_condition (Ccompuimm c k) (v :: nil) m = Some b ->
  exists n, v = Vint n.
Proof.
  intros c k v m b H. destruct v; simpl in H; try discriminate; eauto.
Qed.

Lemma decrement_as_sub:
  forall n, decrement n = Int.sub n Int.one.
Proof.
  intros. unfold decrement. rewrite Int.sub_add_opp.
  unfold Int.one. rewrite Int.neg_repr. reflexivity.
Qed.

Lemma decrement_pair_as_sub:
  forall n, decrement_pair n = Int.sub n (Int.repr 2).
Proof.
  intros. unfold decrement_pair. rewrite Int.sub_add_opp, Int.neg_repr. reflexivity.
Qed.

Lemma unsigned_nonzero:
  forall n, n <> Int.zero -> 0 < Int.unsigned n.
Proof.
  intros n NZ. generalize (Int.unsigned_range n); intros RANGE.
  assert (Int.unsigned n <> 0).
  { intros E. apply NZ. rewrite <- (Int.repr_unsigned n), E. reflexivity. }
  lia.
Qed.

Lemma decrement_unsigned:
  forall n, n <> Int.zero -> Int.unsigned (decrement n) = Int.unsigned n - 1.
Proof.
  intros n NZ. rewrite decrement_as_sub. unfold Int.sub.
  rewrite Int.unsigned_one. apply Int.unsigned_repr.
  generalize (unsigned_nonzero n NZ), (Int.unsigned_range_2 n); lia.
Qed.

Lemma pair_guard_true:
  forall n, pair_guard n = true <-> 2 <= Int.unsigned n.
Proof.
  intros n. unfold pair_guard, Int.cmpu, Int.ltu.
  rewrite (Int.unsigned_repr 2) by (vm_compute; split; discriminate).
  destruct (zlt (Int.unsigned n) 2); simpl; split; intros; try discriminate; lia.
Qed.

Lemma pair_guard_false:
  forall n, pair_guard n = false <-> Int.unsigned n < 2.
Proof.
  intros n. unfold pair_guard, Int.cmpu, Int.ltu.
  rewrite (Int.unsigned_repr 2) by (vm_compute; split; discriminate).
  destruct (zlt (Int.unsigned n) 2); simpl; split; intros; try discriminate; lia.
Qed.

Lemma decrement_pair_unsigned:
  forall n, pair_guard n = true ->
  Int.unsigned (decrement_pair n) = Int.unsigned n - 2.
Proof.
  intros n PAIR. apply pair_guard_true in PAIR.
  rewrite decrement_pair_as_sub. unfold Int.sub.
  rewrite (Int.unsigned_repr 2) by (vm_compute; split; discriminate).
  apply Int.unsigned_repr. generalize (Int.unsigned_range_2 n); lia.
Qed.

Lemma decrement_twice:
  forall n, decrement (decrement n) = decrement_pair n.
Proof.
  intros. unfold decrement, decrement_pair. rewrite Int.add_assoc.
  replace (Int.add (Int.repr (-1)) (Int.repr (-1))) with (Int.repr (-2))
    by (apply Int.same_if_eq; vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma decrement_twice_val:
  forall v,
  Val.add (Val.add v (Vint (Int.repr (-1)))) (Vint (Int.repr (-1))) =
  Val.add v (Vint (Int.repr (-2))).
Proof.
  intros v. destruct v; simpl; try reflexivity.
  f_equal. apply decrement_twice.
Qed.

Lemma pair_guard_nonzero:
  forall n, pair_guard n = true -> n <> Int.zero /\ decrement n <> Int.zero.
Proof.
  intros n PAIR. apply pair_guard_true in PAIR.
  assert (NZ: n <> Int.zero).
  { intro E; subst. rewrite Int.unsigned_zero in PAIR; lia. }
  split; auto. intro E.
  generalize (decrement_unsigned n NZ). rewrite E, Int.unsigned_zero. lia.
Qed.

Lemma pair_guard_after_nonzero:
  forall n, n <> Int.zero ->
  Int.cmpu Cne (decrement n) Int.zero = pair_guard n.
Proof.
  intros n NZ. unfold pair_guard, Int.cmpu, Int.eq, Int.ltu.
  rewrite Int.unsigned_zero, (decrement_unsigned n NZ).
  rewrite (Int.unsigned_repr 2) by (vm_compute; split; discriminate).
  generalize (unsigned_nonzero n NZ).
  destruct (zeq (Int.unsigned n - 1) 0), (zlt (Int.unsigned n) 2);
    simpl; intros; try reflexivity; lia.
Qed.

Lemma scalar_guards_pair:
  forall n,
  andb (Int.cmpu Cne n Int.zero) (Int.cmpu Cne (decrement n) Int.zero) =
  pair_guard n.
Proof.
  intros n. destruct (Int.eq_dec n Int.zero) as [E|NZ].
  - subst. reflexivity.
  - rewrite pair_guard_after_nonzero by auto.
    change (andb (negb (Int.eq n Int.zero)) (pair_guard n) = pair_guard n).
    rewrite Int.eq_false by auto. reflexivity.
Qed.

Lemma pair_false_tail:
  forall n, pair_guard n = false -> n = Int.zero \/ n = Int.one.
Proof.
  intros n PAIR. apply pair_guard_false in PAIR.
  generalize (Int.unsigned_range n); intros RANGE.
  assert (Int.unsigned n = 0 \/ Int.unsigned n = 1) by lia.
  destruct H as [E|E]; [left|right]; rewrite <- (Int.repr_unsigned n), E; reflexivity.
Qed.

Lemma pair_count_progress:
  forall n, pair_guard n = true -> Int.unsigned (decrement_pair n) < Int.unsigned n.
Proof. intros. rewrite decrement_pair_unsigned by auto. lia. Qed.

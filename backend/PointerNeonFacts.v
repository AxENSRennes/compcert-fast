(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under    *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Exact independent-lane facts for guarded pointer-based SIMD arithmetic.
    The scalar accesses themselves need no stronger alignment witness. *)
Require Import Coqlib AST Integers Values Memory Events Globalenvs.
Require Import Op Builtins0 Builtins1 Builtins MemoryNeon.

Lemma signed_condition_defined:
  forall c v0 v1 m b,
  eval_condition (Ccomp c) (v0 :: v1 :: nil) m = Some b ->
  exists lo hi, v0 = Vint lo /\ v1 = Vint hi.
Proof.
  intros c v0 v1 m b H.
  destruct v0, v1; simpl in H; try discriminate; eauto.
Qed.

Definition packed_add_result (lo hi nlo nhi: int): val :=
  Vlong (Int64.ofwords (Int.add hi nhi) (Int.add lo nlo)).

Lemma packed_add_low_high:
  forall lo hi nlo nhi,
  Val.loword (packed_add_result lo hi nlo nhi) = Val.add (Vint lo) (Vint nlo) /\
  Val.hiword (packed_add_result lo hi nlo nhi) = Val.add (Vint hi) (Vint nhi).
Proof.
  intros. unfold packed_add_result; simpl.
  rewrite Int64.lo_ofwords, Int64.hi_ofwords. split; reflexivity.
Qed.

Lemma packed_add_builtin:
  forall ge lo hi nlo nhi m,
  external_call MemoryNeon.packed_builtin ge
    (Vlong (Int64.ofwords hi lo) :: Vlong (Int64.ofwords nhi nlo) :: nil)
    m E0 (packed_add_result lo hi nlo nhi) m.
Proof.
  intros. change (known_builtin_sem (BI_platform BI_neon_add_u32x2) ge
    (Vlong (Int64.ofwords hi lo) :: Vlong (Int64.ofwords nhi nlo) :: nil)
    m E0 (packed_add_result lo hi nlo nhi) m).
  constructor. unfold packed_add_result; simpl.
  unfold packed_u32x2.
  rewrite !Int64.lo_ofwords, !Int64.hi_ofwords. reflexivity.
Qed.

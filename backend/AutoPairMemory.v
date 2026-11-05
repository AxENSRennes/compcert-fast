(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under    *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Memory facts for automatically grouping two scalar uint32 iterations.
    Adjacent scalar cells remain disjoint even when pointer arithmetic wraps.
    No wider access or additional alignment assumption is introduced. *)
Require Import Coqlib AST Integers Values Memory.

Lemma adjacent32_disjoint:
  forall ofs,
  Ptrofs.unsigned ofs + 4 <= Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4)) \/
  Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4)) + 4 <= Ptrofs.unsigned ofs.
Proof.
  intros ofs.
  destruct (Ptrofs.unsigned_add_either ofs (Ptrofs.repr 4)) as [ADD|ADD];
    change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4 in ADD;
    change Ptrofs.modulus with 18446744073709551616 in ADD;
    lia.
Qed.

Lemma load32_after_store32_next:
  forall m ptr v m',
  Mem.storev Mint32 m ptr v = Some m' ->
  Mem.loadv Mint32 m' (Val.offset_ptr ptr (Ptrofs.repr 4)) =
  Mem.loadv Mint32 m (Val.offset_ptr ptr (Ptrofs.repr 4)).
Proof.
  intros m ptr v m' STORE.
  destruct ptr as [|n|n|f|f|b ofs]; try discriminate.
  cbn [Mem.storev] in STORE.
  destruct (zle (Ptrofs.unsigned ofs + size_chunk Mint32) Ptrofs.modulus);
    try discriminate.
  cbn [Val.offset_ptr Mem.loadv].
  destruct (zle (Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4)) + size_chunk Mint32)
                 Ptrofs.modulus); auto.
  eapply Mem.load_store_other; eauto.
  generalize (adjacent32_disjoint ofs). simpl. tauto.
Qed.

Lemma offset_ptr_two_steps:
  forall ptr,
  Val.offset_ptr (Val.offset_ptr ptr (Ptrofs.repr 4)) (Ptrofs.repr 4) =
  Val.offset_ptr ptr (Ptrofs.repr 8).
Proof.
  intros. rewrite Val.offset_ptr_assoc. reflexivity.
Qed.

Lemma addl_four_pointer:
  forall b ofs,
  Val.addl (Vptr b ofs) (Vlong (Int64.repr 4)) =
  Val.offset_ptr (Vptr b ofs) (Ptrofs.repr 4).
Proof. intros; reflexivity. Qed.

Lemma addl_two_steps:
  forall ptr,
  Val.addl (Val.addl ptr (Vlong (Int64.repr 4))) (Vlong (Int64.repr 4)) =
  Val.addl ptr (Vlong (Int64.repr 8)).
Proof. intros. rewrite Val.addl_assoc. reflexivity. Qed.

Lemma load32_after_store32_addl:
  forall m ptr v m',
  Mem.storev Mint32 m ptr v = Some m' ->
  Mem.loadv Mint32 m' (Val.addl ptr (Vlong (Int64.repr 4))) =
  Mem.loadv Mint32 m (Val.addl ptr (Vlong (Int64.repr 4))).
Proof.
  intros m ptr v m' STORE.
  destruct ptr; try discriminate.
  rewrite addl_four_pointer. eapply load32_after_store32_next; exact STORE.
Qed.

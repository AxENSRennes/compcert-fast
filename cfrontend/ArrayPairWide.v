(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Widen adjacent, defined 32-bit lanes at an eight-byte-aligned offset. *)
Require Import Coqlib Maps AST Integers Values Memory Events.
Require Import Ctypes Cop Clight ClightBigstep.
Require Import MemoryLaneFacts PointerNeonFacts ArrayPair.

Local Open Scope Z_scope.

Local Lemma aligned_wide_bounds:
  forall ofs, (8 | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus.
Proof.
  intros ofs [q OFFSET].
  pose proof (Ptrofs.unsigned_range ofs).
  change Ptrofs.modulus with 18446744073709551616 in *.
  lia.
Qed.

Local Lemma unsigned_next_lane:
  forall ofs, Ptrofs.unsigned ofs + 8 <= Ptrofs.modulus ->
  Ptrofs.unsigned (Ptrofs.add ofs (Ptrofs.repr 4)) = Ptrofs.unsigned ofs + 4.
Proof.
  intros ofs BOUNDS.
  rewrite Ptrofs.add_unsigned.
  change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
  apply Ptrofs.unsigned_repr.
  unfold Ptrofs.max_unsigned.
  pose proof (Ptrofs.unsigned_range ofs). lia.
Qed.

Lemma loadv_two_int32:
  forall m b ofs lo hi,
  (8 | Ptrofs.unsigned ofs) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint lo) ->
  Mem.loadv Mint32 m (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint hi) ->
  Mem.loadv Mint64 m (Vptr b ofs) = Some (Vlong (Int64.ofwords hi lo)).
Proof.
  intros m b ofs lo hi ALIGN LOAD0 LOAD1.
  pose proof (aligned_wide_bounds _ ALIGN) as BOUNDS.
  pose proof (unsigned_next_lane _ BOUNDS) as NEXT.
  cbn [Mem.loadv size_chunk] in LOAD0, LOAD1 |- *.
  rewrite NEXT in LOAD1.
  rewrite !zle_true in LOAD0, LOAD1 |- * by lia.
  eapply load_two_int32; eauto.
Qed.

Lemma storev_two_int32:
  forall m0 m1 m2 b ofs lo hi,
  (8 | Ptrofs.unsigned ofs) ->
  Mem.storev Mint32 m0 (Vptr b ofs) (Vint lo) = Some m1 ->
  Mem.storev Mint32 m1 (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))) (Vint hi) = Some m2 ->
  Mem.storev Mint64 m0 (Vptr b ofs) (Vlong (Int64.ofwords hi lo)) = Some m2.
Proof.
  intros m0 m1 m2 b ofs lo hi ALIGN STORE0 STORE1.
  pose proof (aligned_wide_bounds _ ALIGN) as BOUNDS.
  pose proof (unsigned_next_lane _ BOUNDS) as NEXT.
  cbn [Mem.storev size_chunk] in STORE0, STORE1 |- *.
  rewrite NEXT in STORE1.
  rewrite !zle_true in STORE0, STORE1 |- * by lia.
  eapply store_two_int32; eauto.
Qed.

Local Lemma eval_wide_lvalue:
  forall ge e le m addr b ofs,
  typeof addr = tuint_ptr ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  eval_lvalue ge e le m (wide_cell addr) b ofs Full.
Proof.
  intros ge e le m addr b ofs TYPE ADDR.
  unfold wide_cell. apply eval_Ederef.
  eapply eval_Ecast; [exact ADDR|].
  rewrite TYPE. reflexivity.
Qed.

Local Lemma eval_wide_lane:
  forall ge e le m addr b ofs lo hi,
  typeof addr = tuint_ptr ->
  eval_expr ge e le m addr (Vptr b ofs) ->
  Mem.loadv Mint64 m (Vptr b ofs) = Some (Vlong (Int64.ofwords hi lo)) ->
  eval_expr ge e le m (wide_cell addr) (Vlong (Int64.ofwords hi lo)).
Proof.
  intros ge e le m addr b ofs lo hi TYPE ADDR LOAD.
  eapply eval_Elvalue.
  - eapply eval_wide_lvalue; eauto.
  - eapply deref_loc_value; [reflexivity|exact LOAD].
Qed.

Lemma wide_update_exec:
  forall ge e le m0 m1 m2 tmp addr b ofs lo hi k,
  let le' := PTree.set tmp (packed_add_result lo hi k k) le in
  typeof addr = tuint_ptr ->
  eval_expr ge e le m0 addr (Vptr b ofs) ->
  eval_expr ge e le' m0 addr (Vptr b ofs) ->
  (8 | Ptrofs.unsigned ofs) ->
  Mem.loadv Mint32 m0 (Vptr b ofs) = Some (Vint lo) ->
  Mem.loadv Mint32 m0 (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))) = Some (Vint hi) ->
  Mem.storev Mint32 m0 (Vptr b ofs) (Vint (Int.add lo k)) = Some m1 ->
  Mem.storev Mint32 m1 (Vptr b (Ptrofs.add ofs (Ptrofs.repr 4))) (Vint (Int.add hi k)) = Some m2 ->
  Clight2.exec_stmt ge e le m0 (wide_update tmp addr k) E0 le' m2 Out_normal.
Proof.
  intros ge e le m0 m1 m2 tmp addr b ofs lo hi k le'
    TYPE ADDR STORE_ADDR ALIGN LOAD0 LOAD1 STORE0 STORE1.
  pose proof (loadv_two_int32 _ _ _ _ _ ALIGN LOAD0 LOAD1) as LOAD.
  pose proof (storev_two_int32 _ _ _ _ _ _ _ ALIGN STORE0 STORE1) as STORE.
  unfold wide_update.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le') (m1 := m0).
  - eapply ClightBigstep.exec_Sbuiltin with
      (vargs := Vlong (Int64.ofwords hi lo) :: Vlong (Int64.ofwords k k) :: nil)
      (vres := packed_add_result lo hi k k).
    + econstructor.
      * eapply eval_wide_lane; eauto.
      * reflexivity.
      * econstructor.
        -- apply eval_Econst_long.
        -- reflexivity.
        -- constructor.
    + apply packed_add_builtin.
  - eapply ClightBigstep.exec_Sassign.
    + eapply eval_wide_lvalue; eauto.
    + apply eval_Etempvar. unfold le'. apply PTree.gss.
    + reflexivity.
    + eapply assign_loc_value; [reflexivity|exact STORE].
Qed.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Exact two-lane memory facts on the current little-endian ARM64 target.
    Independent lanes require explicit integer-definedness witnesses. *)
Require Import Coqlib Integers AST Values Memdata Memory.

Lemma encode_two_int32:
  forall lo hi,
  encode_val Mint64 (Vlong (Int64.ofwords hi lo)) =
  encode_val Mint32 (Vint lo) ++ encode_val Mint32 (Vint hi).
Proof.
  intros. change (map Byte (bytes_of_int 8 (Int64.unsigned (Int64.ofwords hi lo))) =
    map Byte (bytes_of_int 4 (Int.unsigned lo)) ++ map Byte (bytes_of_int 4 (Int.unsigned hi))).
  rewrite bytes_of_int64, Int64.lo_ofwords, Int64.hi_ofwords, map_app. reflexivity.
Qed.

Lemma store_two_int32:
  forall m b ofs lo hi m1 m2,
  Mem.store Mint32 m b ofs (Vint lo) = Some m1 ->
  Mem.store Mint32 m1 b (ofs + 4) (Vint hi) = Some m2 ->
  (align_chunk Mint64 | ofs) ->
  Mem.store Mint64 m b ofs (Vlong (Int64.ofwords hi lo)) = Some m2.
Proof.
  intros m b ofs lo hi m1 m2 S1 S2 ALIGN.
  apply Mem.store_storebytes in S1. apply Mem.store_storebytes in S2.
  apply Mem.storebytes_store; auto.
  rewrite encode_two_int32. eapply Mem.storebytes_concat; eauto.
Qed.

Lemma decode_two_int32:
  forall byteslo byteshi lo hi,
  length byteslo = 4%nat -> length byteshi = 4%nat ->
  decode_val Mint32 byteslo = Vint lo ->
  decode_val Mint32 byteshi = Vint hi ->
  decode_val Mint64 (byteslo ++ byteshi) = Vlong (Int64.ofwords hi lo).
Proof.
  intros byteslo byteshi lo hi LENLO LENHI LO HI.
  unfold decode_val in *.
  rewrite proj_bytes_append.
  destruct (proj_bytes byteslo) as [bl|] eqn:BL; try discriminate.
  destruct (proj_bytes byteshi) as [bh|] eqn:BH; try discriminate.
  inv LO. inv HI.
  assert (LLO: length bl = 4%nat).
  { rewrite (length_proj_bytes _ _ BL). exact LENLO. }
  assert (LHI: length bh = 4%nat).
  { rewrite (length_proj_bytes _ _ BH). exact LENHI. }
  assert (UR: forall l, length l = 4%nat ->
      Int.unsigned (Int.repr (int_of_bytes l)) = int_of_bytes l).
  { intros. apply Int.unsigned_repr.
    generalize (int_of_bytes_range l). rewrite H.
    change (two_p (Z.of_nat 4 * 8)) with (Int.max_unsigned + 1). lia. }
  unfold decode_int, rev_if_be. change Archi.big_endian with false.
  f_equal. rewrite Int64.ofwords_add. f_equal.
  rewrite !UR by auto. rewrite int_of_bytes_append, LLO.
  change (Z.of_nat 4 * 8) with 32. ring.
Qed.

Lemma load_two_int32:
  forall m b ofs lo hi,
  Mem.load Mint32 m b ofs = Some (Vint lo) ->
  Mem.load Mint32 m b (ofs + 4) = Some (Vint hi) ->
  (align_chunk Mint64 | ofs) ->
  Mem.load Mint64 m b ofs = Some (Vlong (Int64.ofwords hi lo)).
Proof.
  intros m b ofs lo hi LO HI ALIGN.
  destruct (Mem.load_loadbytes _ _ _ _ _ LO) as [byteslo [LBLO EQLO]].
  destruct (Mem.load_loadbytes _ _ _ _ _ HI) as [byteshi [LBHI EQHI]].
  assert (LENLO: length byteslo = 4%nat).
  { exact (Mem.loadbytes_length _ _ _ _ _ LBLO). }
  assert (LENHI: length byteshi = 4%nat).
  { exact (Mem.loadbytes_length _ _ _ _ _ LBHI). }
  assert (LB: Mem.loadbytes m b ofs 8 = Some (byteslo ++ byteshi)).
  { change 8 with (4 + 4). eapply Mem.loadbytes_concat; eauto; lia. }
  rewrite <- (decode_two_int32 byteslo byteshi lo hi LENLO LENHI) by congruence.
  eapply Mem.loadbytes_load; eauto.
Qed.

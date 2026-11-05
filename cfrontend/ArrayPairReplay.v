(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Execution of the packed Clight update on the two defined scalar lanes. *)
Require Import Coqlib Maps AST Integers Values Memory Events.
Require Import Ctypes Cop Clight ClightBigstep.
Require Import MemoryNeon PointerNeonFacts ArrayPair.

Local Open Scope Z_scope.

Local Lemma eval_lane:
  forall ge e le m addr b ofs v,
  eval_expr ge e le m addr (Vptr b ofs) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint v) ->
  eval_expr ge e le m (Ederef addr tuint) (Vint v).
Proof.
  intros ge e le m addr b ofs v ADDR LOAD.
  eapply eval_Elvalue.
  - apply eval_Ederef. exact ADDR.
  - eapply deref_loc_value.
    + reflexivity.
    + exact LOAD.
Qed.

Local Lemma eval_lane_cast:
  forall ge e le m addr b ofs v,
  eval_expr ge e le m addr (Vptr b ofs) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint v) ->
  eval_expr ge e le m (Ecast (Ederef addr tuint) tulong)
    (Vlong (Int64.repr (Int.unsigned v))).
Proof.
  intros ge e le m addr b ofs v ADDR LOAD.
  eapply eval_Ecast.
  - eapply eval_lane; eauto.
  - reflexivity.
Qed.

Local Lemma eval_pack:
  forall ge e le m addr0 addr1 b0 ofs0 b1 ofs1 lo hi,
  eval_expr ge e le m addr0 (Vptr b0 ofs0) ->
  eval_expr ge e le m addr1 (Vptr b1 ofs1) ->
  Mem.loadv Mint32 m (Vptr b0 ofs0) = Some (Vint lo) ->
  Mem.loadv Mint32 m (Vptr b1 ofs1) = Some (Vint hi) ->
  eval_expr ge e le m
    (Ebinop Oor (Ecast (Ederef addr0 tuint) tulong)
      (Ebinop Oshl (Ecast (Ederef addr1 tuint) tulong)
        (Econst_int (Int.repr 32) tint) tulong) tulong)
    (Vlong (Int64.ofwords hi lo)).
Proof.
  intros ge e le m addr0 addr1 b0 ofs0 b1 ofs1 lo hi ADDR0 ADDR1 LOAD0 LOAD1.
  eapply eval_Ebinop.
  - eapply eval_lane_cast; eauto.
  - eapply eval_Ebinop.
    + eapply eval_lane_cast; eauto.
    + apply eval_Econst_int.
    + reflexivity.
  - change (Some (Vlong (Int64.or (Int64.repr (Int.unsigned lo))
      (Int64.shl (Int64.repr (Int.unsigned hi)) (Int64.repr 32)))) =
      Some (Vlong (Int64.ofwords hi lo))).
    unfold Int64.ofwords. rewrite Int64.or_commut. reflexivity.
Qed.

Local Lemma store_lane:
  forall ge e le m addr rhs b ofs v m',
  eval_expr ge e le m addr (Vptr b ofs) ->
  typeof rhs = tuint ->
  eval_expr ge e le m rhs (Vint v) ->
  Mem.storev Mint32 m (Vptr b ofs) (Vint v) = Some m' ->
  Clight2.exec_stmt ge e le m (Sassign (Ederef addr tuint) rhs)
    E0 le m' Out_normal.
Proof.
  intros ge e le m addr rhs b ofs v m' ADDR TYPE RHS STORE.
  eapply ClightBigstep.exec_Sassign.
  - apply eval_Ederef. exact ADDR.
  - exact RHS.
  - rewrite TYPE. reflexivity.
  - eapply assign_loc_value.
    + reflexivity.
    + exact STORE.
Qed.

Lemma scalar_update_exec:
  forall ge e le m m' p b ofs v,
  eval_expr ge e le m (addr p 0) (Vptr b ofs) ->
  Mem.loadv Mint32 m (Vptr b ofs) = Some (Vint v) ->
  Mem.storev Mint32 m (Vptr b ofs) (Vint (Int.add v (increment p))) = Some m' ->
  Clight2.exec_stmt ge e le m (scalar_update p) E0 le m' Out_normal.
Proof.
  intros ge e le m m' p b ofs v ADDR LOAD STORE.
  unfold scalar_update.
  eapply store_lane; [exact ADDR | reflexivity | | exact STORE].
  eapply eval_Ebinop.
  - eapply eval_lane; eauto.
  - apply eval_Econst_int.
  - destruct (increment_signedness p); reflexivity.
Qed.

Lemma packed_update_exec:
  forall ge e le m0 m1 m2 tmp addr0 addr1 b0 ofs0 b1 ofs1 lo hi k,
  let le' := PTree.set tmp (packed_add_result lo hi k k) le in
  eval_expr ge e le m0 addr0 (Vptr b0 ofs0) ->
  eval_expr ge e le m0 addr1 (Vptr b1 ofs1) ->
  eval_expr ge e le' m0 addr0 (Vptr b0 ofs0) ->
  eval_expr ge e le' m1 addr1 (Vptr b1 ofs1) ->
  Mem.loadv Mint32 m0 (Vptr b0 ofs0) = Some (Vint lo) ->
  Mem.loadv Mint32 m0 (Vptr b1 ofs1) = Some (Vint hi) ->
  Mem.storev Mint32 m0 (Vptr b0 ofs0) (Vint (Int.add lo k)) = Some m1 ->
  Mem.storev Mint32 m1 (Vptr b1 ofs1) (Vint (Int.add hi k)) = Some m2 ->
  Clight2.exec_stmt ge e le m0 (packed_update tmp addr0 addr1 k)
    E0 le' m2 Out_normal.
Proof.
  intros ge e le m0 m1 m2 tmp addr0 addr1 b0 ofs0 b1 ofs1 lo hi k le'
    ADDR0 ADDR1 STORE_ADDR0 STORE_ADDR1 LOAD0 LOAD1 STORE0 STORE1.
  unfold packed_update.
  eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le') (m1 := m0).
  - eapply ClightBigstep.exec_Sbuiltin with
      (vargs := Vlong (Int64.ofwords hi lo) :: Vlong (Int64.ofwords k k) :: nil)
      (vres := packed_add_result lo hi k k).
    + econstructor.
      * eapply eval_pack; eauto.
      * reflexivity.
      * econstructor.
        -- apply eval_Econst_long.
        -- reflexivity.
        -- constructor.
    + apply packed_add_builtin.
  - eapply ClightBigstep.exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le') (m1 := m1).
    + eapply store_lane; [exact STORE_ADDR0 | reflexivity | | exact STORE0].
      eapply eval_Ecast.
      * apply eval_Etempvar. unfold le'. apply PTree.gss.
      * change (Some (Vint (Int64.loword (Int64.ofwords (Int.add hi k) (Int.add lo k)))) =
          Some (Vint (Int.add lo k))).
        rewrite Int64.lo_ofwords. reflexivity.
    + eapply store_lane; [exact STORE_ADDR1 | reflexivity | | exact STORE1].
      eapply eval_Ecast.
      * eapply eval_Ebinop.
        -- apply eval_Etempvar. unfold le'. apply PTree.gss.
        -- apply eval_Econst_int.
        -- reflexivity.
      * change (Some (Vint (Int64.hiword (Int64.ofwords (Int.add hi k) (Int.add lo k)))) =
          Some (Vint (Int.add hi k))).
        rewrite Int64.hi_ofwords. reflexivity.
Qed.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** The automatically formed pair computes both scalar updates, before
    the first retained guard and without changing any original register. *)
Require Import Coqlib Maps AST Integers Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL MemoryNeon PointerNeonFacts AutoPair.

Lemma run_pack:
  forall ge p sp stk rs m lo hi b,
  rs#(4%positive) = Vint lo -> rs#(3%positive) = Vint hi ->
  eval_condition (Ccomp Clt) (Vint lo::Vint hi::nil) m = Some b ->
  exists trs,
    plus RTL.step ge
      (State stk (target_template p) sp 71%positive rs m) E0
      (State stk (target_template p) sp (if b then 35%positive else 33%positive) trs m) /\
    (forall r, Ple r 6%positive -> trs#r = rs#r) /\
    Val.loword (trs#(9%positive)) = Val.add (Vint lo) (Vint (increment p)) /\
    Val.hiword (trs#(9%positive)) = Val.add (Vint hi) (Vint (increment p)).
Proof.
  intros ge p sp stk rs m lo hi b LOW HIGH COND.
  set (t0 := rs#(7%positive) <- (Vlong (Int64.ofwords hi lo))).
  set (t1 := t0#(8%positive) <- (Vlong (Int64.ofwords (increment p) (increment p)))).
  set (t2 := t1#(9%positive) <- (packed_add_result lo hi (increment p) (increment p))).
  assert (ORIGINAL: forall r, Ple r 6%positive -> t2#r = rs#r).
  { intros r BOUND. unfold t2,t1,t0. rewrite !Regmap.gso by extlia. reflexivity. }
  exists t2; split.
  - eapply plus_four with
      (s2 := State stk (target_template p) sp 72%positive t0 m)
      (s3 := State stk (target_template p) sp 73%positive t1 m)
      (s4 := State stk (target_template p) sp 36%positive t2 m)
      (t1 := E0) (t2 := E0) (t3 := E0) (t4 := E0).
    + eapply exec_Iop. reflexivity.
      simpl. rewrite HIGH, LOW. reflexivity.
    + eapply exec_Iop. reflexivity. reflexivity.
    + eapply exec_Ibuiltin with
        (ef:=MemoryNeon.packed_builtin)
        (args:=BA 7%positive::BA 8%positive::nil) (res:=BR 9%positive)
        (vargs:=Vlong(Int64.ofwords hi lo)::Vlong(Int64.ofwords(increment p)(increment p))::nil)
        (vres:=packed_add_result lo hi (increment p) (increment p)).
      * reflexivity.
      * assert (A0: t1#(7%positive)=Vlong(Int64.ofwords hi lo)).
        { unfold t1,t0. rewrite Regmap.gso by discriminate. apply Regmap.gss. }
        assert (A1: t1#(8%positive)=Vlong(Int64.ofwords(increment p)(increment p))).
        { unfold t1. apply Regmap.gss. }
        unfold eval_builtin_args. constructor. rewrite <-A0;constructor.
        constructor. rewrite <-A1;constructor. constructor.
      * apply packed_add_builtin.
    + eapply exec_Icond. reflexivity.
      simpl. rewrite !ORIGINAL by (unfold Ple; simpl; lia). rewrite LOW,HIGH. exact COND.
      reflexivity.
    + reflexivity.
  - split; auto. unfold t2. rewrite Regmap.gss. apply packed_add_low_high.
Qed.

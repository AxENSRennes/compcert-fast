(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                      *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)
Require Import Coqlib AST Smallstep Linking RTL LoopFusion LoopFusionproof LoopTile2D.
Definition match_prog := LoopFusionproof.match_prog_with LoopTile2D.candidate.
Lemma transf_program_match:
  forall p, match_prog p (LoopTile2D.transf_program p).
Proof. apply LoopFusionproof.transf_program_with_match. Qed.
Global Instance TransfLoopTile2DLink: TransfLink match_prog :=
  TransfTotalLink LoopTile2D.transf_function.
Theorem transf_program_correct:
  forall p tp, match_prog p tp ->
  forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof. intros; eapply LoopFusionproof.transf_program_with_correct; eauto. Qed.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Interchange correctness is discharged by the generic symbolic validator.
    The candidate generator is not trusted and rejected proposals use identity. *)
Require Import Coqlib AST Linking Smallstep RTL LoopFusion LoopFusionproof LoopInterchange.
Definition match_prog := LoopFusionproof.match_prog_with LoopInterchange.candidate.
Lemma transf_program_match: forall p, match_prog p (LoopInterchange.transf_program p).
Proof. apply LoopFusionproof.transf_program_with_match. Qed.
Global Instance TransfLoopInterchangeLink: TransfLink match_prog :=
  TransfTotalLink LoopInterchange.transf_function.
Theorem transf_program_correct:
  forall p tp, match_prog p tp -> forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof. intros; eapply LoopFusionproof.transf_program_with_correct; eauto. Qed.

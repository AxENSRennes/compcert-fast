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

(* Composition proof for additional cleanup rounds. Distributed under the
   repository's INRIA Non-Commercial License Agreement. *)
Require Import Coqlib Errors AST Linking Smallstep RTL.
Require Import Constprop Constpropproof CSE CSEproof Deadcode Deadcodeproof ExtraCleanup.
Local Open Scope linking_scope.

Definition round_pass :=
  pass_compose (mkpass Constpropproof.match_prog)
    (pass_compose (mkpass CSEproof.match_prog) (mkpass Deadcodeproof.match_prog)).

Definition cleanup_pass := pass_compose round_pass round_pass.
Definition match_prog := pass_match cleanup_pass.

Global Instance TransfLinkCleanup : TransfLink match_prog := pass_match_link cleanup_pass.

Lemma cleanup_round_match:
  forall p tp, cleanup_round p = OK tp -> pass_match round_pass p tp.
Proof.
  unfold cleanup_round; intros. monadInv H.
  exists (Constprop.transf_program p); split.
  apply Constpropproof.transf_program_match.
  exists x; split.
  eapply CSEproof.transf_program_match; eauto.
  eapply Deadcodeproof.transf_program_match; eauto.
Qed.

Lemma transf_program_match:
  forall p tp, ExtraCleanup.transf_program p = OK tp -> match_prog p tp.
Proof.
  unfold ExtraCleanup.transf_program; intros. monadInv H.
  exists x; split; eapply cleanup_round_match; eauto.
Qed.

Lemma cleanup_round_correct:
  forall p tp, pass_match round_pass p tp ->
  forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof.
  intros p tp (p1 & C & p2 & S & D).
  eapply compose_forward_simulations.
  eapply Constpropproof.transf_program_correct; eauto.
  eapply compose_forward_simulations.
  eapply CSEproof.transf_program_correct; eauto.
  eapply Deadcodeproof.transf_program_correct; eauto.
Qed.

Theorem transf_program_correct:
  forall p tp, match_prog p tp ->
  forward_simulation (RTL.semantics p) (RTL.semantics tp).
Proof.
  intros p tp (p1 & A & B).
  eapply compose_forward_simulations; eapply cleanup_round_correct; eauto.
Qed.

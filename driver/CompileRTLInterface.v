(* *********************************************************************)
(*                                                                     *)
(*              The CompCert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Preservation of the linker interface by RTL-to-RTL passes. *)
Require Import Coqlib Maps AST Linking Errors.
Require Import CompileLinkInterface.
Require RTL Tailcallproof Inlining Inliningproof Renumberproof Constpropproof.
Require CSE CSEproof Deadcode Deadcodeproof AutoPairProgram PointerNeonproof.
Require LowerLongproof PeelTwoproof MemoryNeonproof.
Require LoopFusion LoopFusionproof LoopTile2D LoopTile2Dproof.
Require LoopInterchange LoopInterchangeproof LoopTileproof Vectorizeproof.
Require LICMproof PreheaderLICMproof StrengthReduceproof LoopPeelproof.
Require HoistConstproof Scheduleproof LoadForwardproof StoreElimproof.
Require Unswitchproof Experimentalproof MemVectorproof.

Definition rtl_interface := fundef_interface RTL.fn_sig.

Ltac link_from_program_match H :=
  try unfold Linking.match_program in H;
  lazymatch type of H with
  | @match_program_gen ?C ?F ?V ?G ?W ?LC ?fm ?vm ?ctx ?p ?q =>
      refine (@match_prog_interface C F V G W LC _ _ fm vm _ ctx p q H)
  end.

Ltac link_by_signature SIG :=
  lazymatch type of SIG with ?dst = ?src =>
    change (AST.Internal src = AST.Internal dst); now rewrite SIG
  end.

Ltac link_total_interface lemma :=
  intros ctx f tf REL; subst tf;
  pose proof (lemma f) as SIG;
  destruct f; [link_by_signature SIG|reflexivity].

Ltac link_partial_interface wrapper lemma :=
  intros ctx f tf REL;
  pose proof REL as SIG; apply lemma in SIG;
  destruct f; unfold wrapper, AST.transf_partial_fundef in REL; monadInv REL;
  [link_by_signature SIG|reflexivity].

Local Ltac total_rtl_interface relation lemma :=
  intros p q MATCH; unfold relation in MATCH;
  try unfold LoopFusionproof.match_prog_with in MATCH;
  link_from_program_match MATCH; link_total_interface lemma.

Lemma inlining_link_interface: forall p q,
  Inliningproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof.
  intros p q MATCH. unfold Inliningproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface Inlining.transf_fundef Inliningproof.sig_function_translated.
Qed.

Lemma cse_link_interface: forall p q,
  CSEproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof.
  intros p q MATCH. unfold CSEproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface CSE.transf_fundef CSEproof.sig_preserved.
Qed.

Lemma deadcode_link_interface: forall p q,
  Deadcodeproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof.
  intros p q MATCH. unfold Deadcodeproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface Deadcode.transf_fundef Deadcodeproof.sig_function_translated.
Qed.

Lemma constprop_link_interface: forall p q,
  Constpropproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof.
  intros p q MATCH. unfold Constpropproof.match_prog in MATCH. link_from_program_match MATCH.
  intros cu f tf REL. subst tf.
  pose proof (Constpropproof.sig_function_translated (ValueAnalysis.romem_for cu) f) as SIG.
  destruct f; [link_by_signature SIG|reflexivity].
Qed.

Lemma tailcall_link_interface: forall p q,
  Tailcallproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface Tailcallproof.match_prog Tailcallproof.sig_preserved. Qed.

Lemma renumber_link_interface: forall p q,
  Renumberproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface Renumberproof.match_prog Renumberproof.sig_preserved. Qed.

Lemma autopair_link_interface: forall p q,
  AutoPairProgram.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface AutoPairProgram.match_prog AutoPairProgram.sig_preserved. Qed.

Lemma pointer_neon_link_interface: forall p q,
  PointerNeonproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface PointerNeonproof.match_prog PointerNeonproof.sig_preserved. Qed.

Lemma lower_long_link_interface: forall p q,
  LowerLongproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LowerLongproof.match_prog LowerLongproof.sig_preserved. Qed.

Lemma peel_two_link_interface: forall p q,
  PeelTwoproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface PeelTwoproof.match_prog PeelTwoproof.sig_preserved. Qed.

Lemma memory_neon_link_interface: forall p q,
  MemoryNeonproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface MemoryNeonproof.match_prog MemoryNeonproof.sig_preserved. Qed.

Lemma loop_fusion_link_interface: forall p q,
  LoopFusionproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LoopFusionproof.match_prog (LoopFusionproof.sig_preserved LoopFusion.candidate). Qed.

Lemma loop_tile2d_link_interface: forall p q,
  LoopTile2Dproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LoopTile2Dproof.match_prog (LoopFusionproof.sig_preserved LoopTile2D.candidate). Qed.

Lemma loop_interchange_link_interface: forall p q,
  LoopInterchangeproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LoopInterchangeproof.match_prog (LoopFusionproof.sig_preserved LoopInterchange.candidate). Qed.

Lemma loop_tile_link_interface: forall p q,
  LoopTileproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LoopTileproof.match_prog LoopTileproof.sig_preserved. Qed.

Lemma vectorize_link_interface: forall p q,
  Vectorizeproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface Vectorizeproof.match_prog Vectorizeproof.sig_preserved. Qed.

Lemma licm_link_interface: forall p q,
  LICMproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LICMproof.match_prog LICMproof.sig_preserved. Qed.

Lemma preheader_licm_link_interface: forall p q,
  PreheaderLICMproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface PreheaderLICMproof.match_prog PreheaderLICMproof.sig_preserved. Qed.

Lemma strength_reduce_link_interface: forall p q,
  StrengthReduceproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface StrengthReduceproof.match_prog StrengthReduceproof.sig_preserved. Qed.

Lemma loop_peel_link_interface: forall p q,
  LoopPeelproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LoopPeelproof.match_prog LoopPeelproof.sig_preserved. Qed.

Lemma hoist_const_link_interface: forall p q,
  HoistConstproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface HoistConstproof.match_prog HoistConstproof.sig_preserved. Qed.

Lemma schedule_link_interface: forall p q,
  Scheduleproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface Scheduleproof.match_prog Scheduleproof.sig_preserved. Qed.

Lemma load_forward_link_interface: forall p q,
  LoadForwardproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface LoadForwardproof.match_prog LoadForwardproof.sig_preserved. Qed.

Lemma store_elim_link_interface: forall p q,
  StoreElimproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface StoreElimproof.match_prog StoreElimproof.sig_preserved. Qed.

Lemma unswitch_link_interface: forall p q,
  Unswitchproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface Unswitchproof.match_prog Unswitchproof.sig_preserved. Qed.

Lemma memvector_link_interface: forall p q,
  MemVectorproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface MemVectorproof.match_prog MemVectorproof.sig_preserved. Qed.

Lemma memvector_indirect_link_interface: forall p q,
  MemVectorproof.IndirectProof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. total_rtl_interface MemVectorproof.IndirectProof.match_prog MemVectorproof.IndirectProof.sig_preserved. Qed.

Lemma experimental_link_interface: forall four p q,
  Experimentalproof.match_prog four p q -> preserves_interface rtl_interface rtl_interface p q.
Proof. intro four. total_rtl_interface Experimentalproof.match_prog (Experimentalproof.sig_preserved four). Qed.

Ltac rtl_link_step H :=
  lazymatch type of H with
  | Inliningproof.match_prog _ _ => exact (inlining_link_interface _ _ H)
  | CSEproof.match_prog _ _ => exact (cse_link_interface _ _ H)
  | Deadcodeproof.match_prog _ _ => exact (deadcode_link_interface _ _ H)
  | Constpropproof.match_prog _ _ => exact (constprop_link_interface _ _ H)
  | Tailcallproof.match_prog _ _ => exact (tailcall_link_interface _ _ H)
  | Renumberproof.match_prog _ _ => exact (renumber_link_interface _ _ H)
  | AutoPairProgram.match_prog _ _ => exact (autopair_link_interface _ _ H)
  | PointerNeonproof.match_prog _ _ => exact (pointer_neon_link_interface _ _ H)
  | LowerLongproof.match_prog _ _ => exact (lower_long_link_interface _ _ H)
  | PeelTwoproof.match_prog _ _ => exact (peel_two_link_interface _ _ H)
  | MemoryNeonproof.match_prog _ _ => exact (memory_neon_link_interface _ _ H)
  | LoopFusionproof.match_prog _ _ => exact (loop_fusion_link_interface _ _ H)
  | LoopTile2Dproof.match_prog _ _ => exact (loop_tile2d_link_interface _ _ H)
  | LoopInterchangeproof.match_prog _ _ => exact (loop_interchange_link_interface _ _ H)
  | LoopTileproof.match_prog _ _ => exact (loop_tile_link_interface _ _ H)
  | Vectorizeproof.match_prog _ _ => exact (vectorize_link_interface _ _ H)
  | LICMproof.match_prog _ _ => exact (licm_link_interface _ _ H)
  | PreheaderLICMproof.match_prog _ _ => exact (preheader_licm_link_interface _ _ H)
  | StrengthReduceproof.match_prog _ _ => exact (strength_reduce_link_interface _ _ H)
  | LoopPeelproof.match_prog _ _ => exact (loop_peel_link_interface _ _ H)
  | HoistConstproof.match_prog _ _ => exact (hoist_const_link_interface _ _ H)
  | Scheduleproof.match_prog _ _ => exact (schedule_link_interface _ _ H)
  | LoadForwardproof.match_prog _ _ => exact (load_forward_link_interface _ _ H)
  | StoreElimproof.match_prog _ _ => exact (store_elim_link_interface _ _ H)
  | Unswitchproof.match_prog _ _ => exact (unswitch_link_interface _ _ H)
  | MemVectorproof.match_prog _ _ => exact (memvector_link_interface _ _ H)
  | MemVectorproof.IndirectProof.match_prog _ _ => exact (memvector_indirect_link_interface _ _ H)
  | Experimentalproof.match_prog ?four _ _ => exact (experimental_link_interface four _ _ H)
  end.

(* *********************************************************************)
(*                                                                     *)
(*              The CompCert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** The link interface of every successful compilation, independent of
    which experimental options and validated oracle results were used. *)
Require Import Coqlib Maps Errors AST Linking Integers.
Require Import Compiler CompileLinkInterface CompileRTLInterface.
Require Ctypes Csyntax Clight Csharpminor Cminor CminorSel RTL LTL Linear Mach Asm.
Import Ctypes.

Require SimplExpr SimplExprspec SimplExprproof SimplLocals SimplLocalsproof.
Require ArrayPairContext ArrayPairProgram Cshmgen Cshmgenproof Cminorgen Cminorgenproof.
Require Selection Selectionproof RTLgen RTLgenproof ExtraCleanupproof.
Require Unusedglobproof Allocation Allocproof.
Require Tunnelingproof Linearize Linearizeproof CleanupLabelsproof Debugvar Debugvarproof.
Require Stacking Stackingproof Asmgen Asmgenproof.

Definition signature_of_function_type (t: Ctypes.type): signature :=
  match t with
  | Ctypes.Tfunction args res cc => Ctypes.signature_of_type args res cc
  | _ => signature_main
  end.

Definition c_interface := c_fundef_interface
  (fun f => signature_of_function_type (Csyntax.type_of_function f)).
Definition clight_interface := c_fundef_interface
  (fun f => signature_of_function_type (Clight.type_of_function f)).
Definition csharpminor_interface := fundef_interface Csharpminor.fn_sig.
Definition cminor_interface := fundef_interface Cminor.fn_sig.
Definition cminorsel_interface := fundef_interface CminorSel.fn_sig.
Definition ltl_interface := fundef_interface LTL.fn_sig.
Definition linear_interface := fundef_interface Linear.fn_sig.
Definition mach_interface := fundef_interface Mach.fn_sig.
Definition asm_interface := fundef_interface Asm.fn_sig.

Local Lemma simplify_expression_interface: forall p q,
  SimplExprproof.match_prog p q -> preserves_interface c_interface clight_interface p q.
Proof.
  intros p q [MATCH _]. link_from_program_match MATCH.
  intros ctx f tf REL.
  pose proof (SimplExprproof.type_of_fundef_preserved _ _ _ REL) as SIG.
  inv REL; cbn [c_interface clight_interface c_fundef_interface]; auto.

  cbn [Clight.type_of_fundef Csyntax.type_of_fundef ArrayPair.transf_fundef] in SIG. now rewrite SIG.
Qed.

Local Lemma simplify_locals_interface: forall p q,
  SimplLocalsproof.match_prog p q -> preserves_interface clight_interface clight_interface p q.
Proof.
  intros p q [MATCH _]. link_from_program_match MATCH.
  intros ctx f tf REL.
  pose proof (SimplLocalsproof.type_of_fundef_preserved _ _ REL) as SIG.
  destruct f; unfold SimplLocals.transf_fundef in REL; monadInv REL;
    cbn [clight_interface c_fundef_interface]; auto.
  cbn [Clight.type_of_fundef Csyntax.type_of_fundef ArrayPair.transf_fundef] in SIG. now rewrite SIG.
Qed.

Local Lemma array_pair_interface: forall p q,
  ArrayPairProgram.match_prog p q -> preserves_interface clight_interface clight_interface p q.
Proof.
  intros p q [MATCH _]. link_from_program_match MATCH.
  intros ctx f tf REL. unfold ArrayPairContext.match_fundef in REL; subst tf.
  pose proof (ArrayPairProgram.type_preserved ctx f) as SIG.
  destruct f; cbn [clight_interface c_fundef_interface ArrayPair.transf_fundef]; auto.
  cbn [Clight.type_of_fundef Csyntax.type_of_fundef ArrayPair.transf_fundef] in SIG. now rewrite SIG.
Qed.

Local Lemma csharpminor_link_interface: forall p q,
  Cshmgenproof.match_prog p q -> preserves_interface clight_interface csharpminor_interface p q.
Proof.
  intros p q MATCH. unfold Cshmgenproof.match_prog in MATCH. link_from_program_match MATCH.
  intros ctx f tf REL. inv REL; cbn [clight_interface csharpminor_interface c_fundef_interface fundef_interface]; auto.
  monadInv H. reflexivity.
Qed.

Local Lemma cminor_link_interface: forall p q,
  Cminorgenproof.match_prog p q -> preserves_interface csharpminor_interface cminor_interface p q.
Proof.
  intros p q MATCH. unfold Cminorgenproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface Cminorgen.transl_fundef Cminorgenproof.sig_preserved.
Qed.

Local Lemma selection_link_interface: forall p q,
  Selectionproof.match_prog p q -> preserves_interface cminor_interface cminorsel_interface p q.
Proof.
  intros p q MATCH. unfold Selectionproof.match_prog in MATCH. link_from_program_match MATCH.
  intros ctx f tf REL.
  pose proof (Selectionproof.sig_function_translated _ _ _ REL) as SIG.
  destruct REL as (hf & HELPERS & REL).
  destruct f; unfold Selection.sel_fundef, AST.transf_partial_fundef in REL; monadInv REL;
    [link_by_signature SIG|reflexivity].
Qed.

Local Lemma rtlgen_link_interface: forall p q,
  RTLgenproof.match_prog p q -> preserves_interface cminorsel_interface rtl_interface p q.
Proof.
  intros p q MATCH. unfold RTLgenproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface RTLgen.transl_fundef RTLgenproof.sig_transl_function.
Qed.


Local Lemma allocation_link_interface: forall p q,
  Allocproof.match_prog p q -> preserves_interface rtl_interface ltl_interface p q.
Proof.
  intros p q MATCH. unfold Allocproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface Allocation.transf_fundef Allocproof.sig_function_translated.
Qed.

Local Lemma tunneling_link_interface: forall p q,
  Tunnelingproof.match_prog p q -> preserves_interface ltl_interface ltl_interface p q.
Proof.
  intros p q MATCH. unfold Tunnelingproof.match_prog in MATCH. link_from_program_match MATCH.
  link_total_interface Tunnelingproof.sig_preserved.
Qed.

Local Lemma linearize_link_interface: forall p q,
  Linearizeproof.match_prog p q -> preserves_interface ltl_interface linear_interface p q.
Proof.
  intros p q MATCH. unfold Linearizeproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface Linearize.transf_fundef Linearizeproof.sig_preserved.
Qed.

Local Lemma cleanup_labels_link_interface: forall p q,
  CleanupLabelsproof.match_prog p q -> preserves_interface linear_interface linear_interface p q.
Proof.
  intros p q MATCH. unfold CleanupLabelsproof.match_prog in MATCH. link_from_program_match MATCH.
  link_total_interface CleanupLabelsproof.sig_function_translated.
Qed.

Local Lemma debugvar_link_interface: forall p q,
  Debugvarproof.match_prog p q -> preserves_interface linear_interface linear_interface p q.
Proof.
  intros p q MATCH. unfold Debugvarproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface Debugvar.transf_fundef Debugvarproof.sig_preserved.
Qed.

Local Lemma stacking_link_interface: forall p q,
  Stackingproof.match_prog p q -> preserves_interface linear_interface mach_interface p q.
Proof.
  intros p q MATCH. unfold Stackingproof.match_prog in MATCH. link_from_program_match MATCH.
  link_partial_interface Stacking.transf_fundef Stackingproof.sig_preserved.
Qed.

Local Lemma asmgen_link_interface: forall p q,
  Asmgenproof.match_prog p q -> preserves_interface mach_interface asm_interface p q.
Proof.
  intros p q MATCH. unfold Asmgenproof.match_prog in MATCH. link_from_program_match MATCH.
  intros ctx f tf REL.
  destruct f; unfold Asmgen.transf_fundef, AST.transf_partial_fundef in REL; monadInv REL;
    [|reflexivity].
  unfold Asmgen.transf_function in EQ.
  monadInv EQ.
  destruct (zlt Ptrofs.max_unsigned (list_length_z (Asm.fn_code x0))); inv EQ1.
  unfold Asmgen.transl_function in EQ0.
  monadInv EQ0. reflexivity.
Qed.

Local Lemma unusedglob_link_interface: forall p q,
  Unusedglobproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof.
  intros p q (used & VALID & [MAIN PUBLIC DEF UNIQUE]).
  constructor; try assumption.
  - intros id td TD. rewrite DEF in TD.
    destruct (Unusedglob.IS.mem id used); try discriminate.
    exists td; auto.
  - intros id d IN D. rewrite DEF.
    apply (Unusedglobproof.used_public _ _ VALID) in IN.
    apply Unusedglob.IS.mem_1 in IN.
    rewrite IN. intro ABS. discriminate (eq_trans (eq_sym D) ABS).
  - intros d D. rewrite DEF.
    change ((if Unusedglob.IS.mem (AST.prog_main q) used
             then (prog_defmap p)!(AST.prog_main q) else None) <> None).
    rewrite MAIN.
    pose proof (Unusedglob.IS.mem_1 (Unusedglobproof.used_main _ _ VALID)) as USED.
    rewrite USED. intro ABS. discriminate (eq_trans (eq_sym D) ABS).
Qed.

Local Lemma unusedglob_public_defined: forall p q,
  Unusedglobproof.match_prog p q -> public_defined p.
Proof.
  intros p q (used & VALID & _) id PUBLIC NOTMAIN.
  apply (Unusedglobproof.used_public _ _ VALID) in PUBLIC.
  apply (Unusedglobproof.used_defined _ _ VALID) in PUBLIC as [DEF|EQ]; [|contradiction].
  apply prog_defmap_dom in DEF as [d DEF].
  intro ABS. discriminate (eq_trans (eq_sym DEF) ABS).
Qed.

Local Lemma cleanup_round_link_interface: forall p q,
  pass_match ExtraCleanupproof.round_pass p q ->
  preserves_interface rtl_interface rtl_interface p q.
Proof.
  intros p q (p1 & CONST & p2 & CSE & DEAD).
  eapply interface_trans; [exact (constprop_link_interface _ _ CONST)|].
  eapply interface_trans; [exact (cse_link_interface _ _ CSE)|].
  exact (deadcode_link_interface _ _ DEAD).
Qed.

Local Lemma extra_cleanup_link_interface: forall p q,
  ExtraCleanupproof.match_prog p q -> preserves_interface rtl_interface rtl_interface p q.
Proof.
  intros p q (p1 & FIRST & SECOND).
  eapply interface_trans; eapply cleanup_round_link_interface; eassumption.
Qed.

Local Ltac direct_link_step REL :=
  lazymatch type of REL with
  | SimplExprproof.match_prog _ _ => exact (simplify_expression_interface _ _ REL)
  | SimplLocalsproof.match_prog _ _ => exact (simplify_locals_interface _ _ REL)
  | ArrayPairProgram.match_prog _ _ => exact (array_pair_interface _ _ REL)
  | Cshmgenproof.match_prog _ _ => exact (csharpminor_link_interface _ _ REL)
  | Cminorgenproof.match_prog _ _ => exact (cminor_link_interface _ _ REL)
  | Selectionproof.match_prog _ _ => exact (selection_link_interface _ _ REL)
  | RTLgenproof.match_prog _ _ => exact (rtlgen_link_interface _ _ REL)
  | ExtraCleanupproof.match_prog _ _ => exact (extra_cleanup_link_interface _ _ REL)
  | Unusedglobproof.match_prog _ _ => exact (unusedglob_link_interface _ _ REL)
  | Allocproof.match_prog _ _ => exact (allocation_link_interface _ _ REL)
  | Tunnelingproof.match_prog _ _ => exact (tunneling_link_interface _ _ REL)
  | Linearizeproof.match_prog _ _ => exact (linearize_link_interface _ _ REL)
  | CleanupLabelsproof.match_prog _ _ => exact (cleanup_labels_link_interface _ _ REL)
  | Debugvarproof.match_prog _ _ => exact (debugvar_link_interface _ _ REL)
  | Stackingproof.match_prog _ _ => exact (stacking_link_interface _ _ REL)
  | Asmgenproof.match_prog _ _ => exact (asmgen_link_interface _ _ REL)
  | _ => rtl_link_step REL
  end.

Local Ltac link_step REL :=
  lazymatch type of REL with
  | match_if ?flag _ _ _ =>
      unfold match_if in REL;
      destruct (flag tt); [direct_link_step REL | subst; apply interface_refl]
  | _ => direct_link_step REL
  end.

Local Ltac expose_passes REL :=
  cbn [Compiler.match_prog CompCert's_passes compose_passes pass_compose
       pass_identity pass_match] in REL.

Lemma compiler_match_preserves_interface: forall p q,
  Compiler.match_prog p q -> preserves_interface c_interface asm_interface p q.
Proof.
  intros p q REL. expose_passes REL.
  repeat lazymatch type of REL with
  | exists middle, _ /\ _ =>
      let MID := fresh "mid" in let STEP := fresh "STEP" in
      destruct REL as (MID & STEP & REL);
      eapply interface_trans; [link_step STEP|]
  end.
  subst. apply interface_refl.
Qed.

Lemma compiler_match_public_defined: forall p q,
  Compiler.match_prog p q -> public_defined p.
Proof.
  intros p q REL. expose_passes REL.
  repeat lazymatch type of REL with
  | exists middle, _ /\ _ =>
      let MID := fresh "mid" in let STEP := fresh "STEP" in
      destruct REL as (MID & STEP & REL);
      lazymatch type of STEP with
      | Unusedglobproof.match_prog _ _ => exact (unusedglob_public_defined _ _ STEP)
      | _ => eapply public_defined_source; [link_step STEP|]
      end
  end.
Qed.

(** The certificate does not mention any particular compiler options.
    Each successful invocation can establish it with its own options. *)
Definition compiled_link_interface (p: Csyntax.program) (q: Asm.program): Prop :=
  preserves_interface c_interface asm_interface p q /\ public_defined p.

Theorem transf_c_program_link_interface: forall p q,
  transf_c_program p = OK q -> compiled_link_interface p q.
Proof.
  intros p q SUCCESS. apply transf_c_program_match in SUCCESS.
  split; eauto using compiler_match_preserves_interface, compiler_match_public_defined.
Qed.

Theorem mixed_compilation_link_succeeds: forall sources targets p,
  nlist_forall2 compiled_link_interface sources targets ->
  link_list sources = Some p ->
  exists q, link_list targets = Some q /\ compiled_link_interface p q.
Proof.
  intros sources targets p CERT LINK.
  exact (link_mixed_interfaces _ _ _ _ _ _ _ CERT LINK).
Qed.

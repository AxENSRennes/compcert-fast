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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
From Coq Require Import String.
Require Import Coqlib Errors.
Require Import AST Linking Smallstep.
(** Languages (syntax and semantics). *)
Require Ctypes Csyntax Csem Cstrategy Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
Require Tailcall.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require PeelTwo.
Require LowerLong.
Require PreheaderLICM.
Require LoopFusion.
Require LoopTile2D.
Require MemVector.
Require MemoryNeon.
Require PointerNeon.
Require LoopInterchange.
Require LoopTile.
Require Vectorize.
Require LICM.
Require StrengthReduce.
Require LoopPeel.
Require HoistConst.
Require Schedule.
Require LoadForward.
Require StoreElim.
Require Unswitch.
Require Experimental.
Require ExtraCleanup.
Require Unusedglob.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Debugvar.
Require Stacking.
Require Asmgen.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
Require Tailcallproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require PeelTwoproof.
Require LowerLongproof.
Require PreheaderLICMproof.
Require LoopFusionproof.
Require LoopTile2Dproof.
Require MemVectorproof.
Require MemoryNeonproof.
Require PointerNeonproof.
Require LoopInterchangeproof.
Require LoopTileproof.
Require Vectorizeproof.
Require LICMproof.
Require StrengthReduceproof.
Require LoopPeelproof.
Require HoistConstproof.
Require Scheduleproof.
Require LoadForwardproof.
Require StoreElimproof.
Require Unswitchproof.
Require Experimentalproof.
Require ExtraCleanupproof.
Require Unusedglobproof.
Require Allocproof.
Require Tunnelingproof.
Require Linearizeproof.
Require CleanupLabelsproof.
Require Debugvarproof.
Require Stackingproof.
Require Asmgenproof.
(** Command-line flags. *)
Require Import Compopts.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_LTL: LTL.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Local Open Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res Asm.program :=
   OK f
   @@ print (print_RTL 0)
   @@ total_if Compopts.optim_tailcalls (time "Tail calls" Tailcall.transf_program)
   @@ print (print_RTL 1)
  @@@ time "Inlining" Inlining.transf_program
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 4)
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 7)
   @@ print (print_RTL 50)
   @@ total_if Compopts.experimental_memoryneon (time "Guarded pointer NEON" PointerNeon.transf_program)
   @@ print (print_RTL 78)
   @@ total_if Compopts.experimental_memoryneon (time "Pointer NEON packing lowering" LowerLong.transf_program)
   @@ print (print_RTL 79)
   @@ total_if Compopts.experimental_memoryneon (time "NEON peeling renumber" Renumber.transf_program)
   @@ total_if Compopts.experimental_memoryneon (time "NEON two-iteration peeling" PeelTwo.transf_program)
  @@@ partial_if Compopts.experimental_memoryneon (time "NEON peeled cleanup" ExtraCleanup.transf_program)
   @@ total_if Compopts.experimental_memoryneon (time "NEON peeled renumber" Renumber.transf_program)
   @@ print (print_RTL 77)
   @@ total_if Compopts.experimental_memoryneon (time "Guarded memory NEON" MemoryNeon.transf_program)
   @@ print (print_RTL 76)
   @@ total_if Compopts.experimental_fusion (time "Experimental LoopFusion" LoopFusion.transf_program)
   @@ print (print_RTL 71)
   @@ total_if Compopts.experimental_tile2d (time "Experimental LoopTile2D" LoopTile2D.transf_program)
   @@ print (print_RTL 75)
   @@ total_if Compopts.experimental_interchange (time "Experimental LoopInterchange" LoopInterchange.transf_program)
   @@ print (print_RTL 72)
   @@ total_if Compopts.experimental_tile (time "Experimental LoopTile" LoopTile.transf_program)
   @@ print (print_RTL 73)
   @@ total_if Compopts.experimental_vectorize
        (time "Experimental Vectorize" Vectorize.transf_program)
   @@ print (print_RTL 60)
   @@ total_if Compopts.experimental_vectorize
        (time "Experimental vector packing lowering" LowerLong.transf_program)
   @@ print (print_RTL 65)
   @@ total_if Compopts.experimental_licm
        (time "Experimental LICM" LICM.transf_program)
   @@ print (print_RTL 61)
   @@ total_if Compopts.experimental_preheader
        (time "Experimental preheader LICM" PreheaderLICM.transf_program)
   @@ print (print_RTL 64)
   @@ total_if Compopts.experimental_strength
        (time "Experimental StrengthReduce" StrengthReduce.transf_program)
   @@ print (print_RTL 62)
   @@ total_if Compopts.experimental_peel (time "Experimental peeling renumber" Renumber.transf_program)
   @@ print (print_RTL 66)
   @@ total_if Compopts.experimental_peel
        (time "Experimental LoopPeel" LoopPeel.transf_program)
   @@ print (print_RTL 63)
   @@ total_if Compopts.experimental_hoist
        (time "Experimental integer constant hoisting" HoistConst.transf_program)
   @@ print (print_RTL 51)
   @@ total_if Compopts.experimental_schedule
        (time "Experimental dependency scheduling" Schedule.transf_program)
   @@ print (print_RTL 52)
   @@ total_if Compopts.experimental_loadforward
        (time "Experimental load forwarding" LoadForward.transf_program)
   @@ print (print_RTL 53)
   @@ total_if Compopts.experimental_storeelim
        (time "Experimental overwritten-store elimination" StoreElim.transf_program)
   @@ print (print_RTL 54)
   @@ total_if Compopts.experimental_unswitch
        (time "Experimental delayed loop unswitching" Unswitch.transf_program)
   @@ print (print_RTL 55)
   @@ total_if Compopts.experimental_scalar
        (time "Experimental CFG covering"
          (Experimental.transf_program (Compopts.experimental_unroll4 tt)))
   @@ print (print_RTL 56)
  @@@ partial_if Compopts.experimental_cleanup
        (time "Experimental cleanup" ExtraCleanup.transf_program)
   @@ print (print_RTL 57)
   @@ total_if Compopts.experimental_memvector (time "Memory peeling renumber" Renumber.transf_program)
   @@ total_if Compopts.experimental_memvector (time "Two-iteration peeling" PeelTwo.transf_program)
  @@@ partial_if Compopts.experimental_memvector (time "Peeled memory cleanup" ExtraCleanup.transf_program)
   @@ total_if Compopts.experimental_memvector (time "Peeled memory renumber" Renumber.transf_program)
   @@ print (print_RTL 70)
   @@ total_if Compopts.experimental_memvector (time "Direct memory widening" MemVector.transf_program)
   @@ total_if Compopts.experimental_memvector (time "Producer-backed memory widening" MemVector.Indirect.transf_program)
   @@ total_if Compopts.experimental_memvector (time "Memory packing lowering" LowerLong.transf_program)
   @@ print (print_RTL 74)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 8)
  @@@ time "Register allocation" Allocation.transf_program
   @@ print print_LTL
   @@ time "Branch tunneling" Tunneling.tunnel_program
  @@@ time "CFG linearization" Linearize.transf_program
   @@ time "Label cleanup" CleanupLabels.transf_program
  @@@ partial_if Compopts.debug (time "Debugging info for local variables" Debugvar.transf_program)
  @@@ time "Mach generation" Stacking.transf_program
   @@ print print_Mach
  @@@ time "Asm generation" Asmgen.transf_program.

Definition transf_cminor_program (p: Cminor.program) : res Asm.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res Asm.program :=
  OK p
   @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  OK p
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program.

(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

(** * Relational specification of compilation *)

Definition match_if {A: Type} (flag: unit -> bool) (R: A -> A -> Prop): A -> A -> Prop :=
  if flag tt then R else eq.

Lemma total_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> A) (rel: A -> A -> Prop) (prog: A),
  (forall p, rel p (f p)) ->
  match_if flag rel prog (total_if flag f prog).
Proof.
  intros. unfold match_if, total_if. destruct (flag tt); auto.
Qed.

Lemma partial_if_match:
  forall (A: Type) (flag: unit -> bool) (f: A -> res A) (rel: A -> A -> Prop) (prog tprog: A),
  (forall p tp, f p = OK tp -> rel p tp) ->
  partial_if flag f prog = OK tprog ->
  match_if flag rel prog tprog.
Proof.
  intros. unfold match_if, partial_if in *. destruct (flag tt). auto. congruence.
Qed.

Global Instance TransfIfLink {A: Type} {LA: Linker A}
                      (flag: unit -> bool) (transf: A -> A -> Prop) (TL: TransfLink transf)
                      : TransfLink (match_if flag transf).
Proof.
  unfold match_if. destruct (flag tt).
- auto.
- red; intros. subst tp1 tp2. exists p; auto.
Qed.

(** This is the list of compilation passes of CompCert in relational style.
  Each pass is characterized by a [match_prog] relation between its
  input code and its output code.  The [mkpass] and [:::] combinators,
  defined in module [Linking], ensure that the passes are composable
  (the output language of a pass is the input language of the next pass)
  and that they commute with linking (property [TransfLink], inferred
  by the type class mechanism of Coq). *)

Local Open Scope linking_scope.

Definition CompCert's_passes :=
      mkpass SimplExprproof.match_prog
  ::: mkpass SimplLocalsproof.match_prog
  ::: mkpass Cshmgenproof.match_prog
  ::: mkpass Cminorgenproof.match_prog
  ::: mkpass Selectionproof.match_prog
  ::: mkpass RTLgenproof.match_prog
  ::: mkpass (match_if Compopts.optim_tailcalls Tailcallproof.match_prog)
  ::: mkpass Inliningproof.match_prog
  ::: mkpass Renumberproof.match_prog
  ::: mkpass (match_if Compopts.optim_constprop Constpropproof.match_prog)
  ::: mkpass (match_if Compopts.optim_constprop Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.optim_CSE CSEproof.match_prog)
  ::: mkpass (match_if Compopts.optim_redundancy Deadcodeproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memoryneon PointerNeonproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memoryneon LowerLongproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memoryneon Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memoryneon PeelTwoproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memoryneon ExtraCleanupproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memoryneon Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memoryneon MemoryNeonproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_fusion LoopFusionproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_tile2d LoopTile2Dproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_interchange LoopInterchangeproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_tile LoopTileproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_vectorize Vectorizeproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_vectorize LowerLongproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_licm LICMproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_preheader PreheaderLICMproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_strength StrengthReduceproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_peel Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_peel LoopPeelproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_hoist HoistConstproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_schedule Scheduleproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_loadforward LoadForwardproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_storeelim StoreElimproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_unswitch Unswitchproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_scalar
        (Experimentalproof.match_prog (Compopts.experimental_unroll4 tt)))
  ::: mkpass (match_if Compopts.experimental_cleanup ExtraCleanupproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memvector Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memvector PeelTwoproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memvector ExtraCleanupproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memvector Renumberproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memvector MemVectorproof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memvector MemVectorproof.IndirectProof.match_prog)
  ::: mkpass (match_if Compopts.experimental_memvector LowerLongproof.match_prog)
  ::: mkpass Unusedglobproof.match_prog
  ::: mkpass Allocproof.match_prog
  ::: mkpass Tunnelingproof.match_prog
  ::: mkpass Linearizeproof.match_prog
  ::: mkpass CleanupLabelsproof.match_prog
  ::: mkpass (match_if Compopts.debug Debugvarproof.match_prog)
  ::: mkpass Stackingproof.match_prog
  ::: mkpass Asmgenproof.match_prog
  ::: pass_nil _.

(** Composing the [match_prog] relations above, we obtain the relation
  between CompCert C sources and Asm code that characterize CompCert's
  compilation. *)

Definition match_prog: Csyntax.program -> Asm.program -> Prop :=
  pass_match (compose_passes CompCert's_passes).

(** The [transf_c_program] function, when successful, produces
  assembly code that is in the [match_prog] relation with the source C program. *)

Theorem transf_c_program_match:
  forall p tp,
  transf_c_program p = OK tp ->
  match_prog p tp.
Proof.
  intros p tp T.
  unfold transf_c_program, time in T. simpl in T.
  destruct (SimplExpr.transl_program p) as [p1|e] eqn:P1; simpl in T; try discriminate.
  unfold transf_clight_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (SimplLocals.transf_program p1) as [p2|e] eqn:P2; simpl in T; try discriminate.
  destruct (Cshmgen.transl_program p2) as [p3|e] eqn:P3; simpl in T; try discriminate.
  destruct (Cminorgen.transl_program p3) as [p4|e] eqn:P4; simpl in T; try discriminate.
  unfold transf_cminor_program, time in T. rewrite ! compose_print_identity in T. simpl in T.
  destruct (Selection.sel_program p4) as [p5|e] eqn:P5; simpl in T; try discriminate.
  destruct (RTLgen.transl_program p5) as [p6|e] eqn:P6; simpl in T; try discriminate.
  unfold transf_rtl_program, time in T. rewrite ! compose_print_identity in T.
  cbn [apply_total apply_partial] in T.
  set (p7 := total_if optim_tailcalls Tailcall.transf_program p6) in *.
  destruct (Inlining.transf_program p7) as [p8|e] eqn:P8; cbn [apply_total apply_partial] in T; try discriminate.
  set (p9 := Renumber.transf_program p8) in *.
  set (p10 := total_if optim_constprop Constprop.transf_program p9) in *.
  set (p11 := total_if optim_constprop Renumber.transf_program p10) in *.
  destruct (partial_if optim_CSE CSE.transf_program p11) as [p12|e] eqn:P12; cbn [apply_total apply_partial] in T; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p12) as [p13|e] eqn:P13; cbn [apply_total apply_partial] in T; try discriminate.
  set (p13ptr := total_if experimental_memoryneon PointerNeon.transf_program p13) in *.
  set (p13ptrL := total_if experimental_memoryneon LowerLong.transf_program p13ptr) in *.
  set (p13neN := total_if experimental_memoryneon Renumber.transf_program p13ptrL) in *.
  set (p13neP := total_if experimental_memoryneon PeelTwo.transf_program p13neN) in *.
  destruct (partial_if experimental_memoryneon ExtraCleanup.transf_program p13neP)
    as [p13neC|e] eqn:P13neC; cbn [apply_total apply_partial] in T; try discriminate.
  set (p13neR := total_if experimental_memoryneon Renumber.transf_program p13neC) in *.
  set (p13neV := total_if experimental_memoryneon MemoryNeon.transf_program p13neR) in *.
  set (p13f := total_if experimental_fusion LoopFusion.transf_program p13neV) in *.
  set (p13z := total_if experimental_tile2d LoopTile2D.transf_program p13f) in *.
  set (p13x := total_if experimental_interchange LoopInterchange.transf_program p13z) in *.
  set (p13t := total_if experimental_tile LoopTile.transf_program p13x) in *.
  set (p13v := total_if experimental_vectorize Vectorize.transf_program p13t) in *.
  set (p13w := total_if experimental_vectorize LowerLong.transf_program p13v) in *.
  set (p13i := total_if experimental_licm LICM.transf_program p13w) in *.
  set (p13q := total_if experimental_preheader PreheaderLICM.transf_program p13i) in *.
  set (p13r := total_if experimental_strength StrengthReduce.transf_program p13q) in *.
  set (p13n := total_if experimental_peel Renumber.transf_program p13r) in *.
  set (p13p := total_if experimental_peel LoopPeel.transf_program p13n) in *.
  set (p13h := total_if experimental_hoist HoistConst.transf_program p13p) in *.
  set (p13s := total_if experimental_schedule Schedule.transf_program p13h) in *.
  set (p13l := total_if experimental_loadforward LoadForward.transf_program p13s) in *.
  set (p13d := total_if experimental_storeelim StoreElim.transf_program p13l) in *.
  set (p13u := total_if experimental_unswitch Unswitch.transf_program p13d) in *.
  set (p13a := total_if experimental_scalar
    (Experimental.transf_program (experimental_unroll4 tt)) p13u) in *.
  destruct (partial_if experimental_cleanup ExtraCleanup.transf_program p13a)
    as [p13b|e] eqn:P13b; simpl in T; try discriminate.
  set (p13mn := total_if experimental_memvector Renumber.transf_program p13b) in *.
  set (p13mp := total_if experimental_memvector PeelTwo.transf_program p13mn) in *.
  destruct (partial_if experimental_memvector ExtraCleanup.transf_program p13mp)
    as [p13mc|e] eqn:P13mc; simpl in T; try discriminate.
  set (p13mr := total_if experimental_memvector Renumber.transf_program p13mc) in *.
  set (p13mv := total_if experimental_memvector MemVector.transf_program p13mr) in *.
  set (p13mi := total_if experimental_memvector MemVector.Indirect.transf_program p13mv) in *.
  set (p13ml := total_if experimental_memvector LowerLong.transf_program p13mi) in *.
  destruct (Unusedglob.transform_program p13ml) as [p14|e] eqn:P14; simpl in T; try discriminate.
  destruct (Allocation.transf_program p14) as [p15|e] eqn:P15; simpl in T; try discriminate.
  set (p16 := Tunneling.tunnel_program p15) in *.
  destruct (Linearize.transf_program p16) as [p17|e] eqn:P17; simpl in T; try discriminate.
  set (p18 := CleanupLabels.transf_program p17) in *.
  destruct (partial_if debug Debugvar.transf_program p18) as [p19|e] eqn:P19; simpl in T; try discriminate.
  destruct (Stacking.transf_program p19) as [p20|e] eqn:P20; simpl in T; try discriminate.
  unfold match_prog; simpl.
  exists p1; split. apply SimplExprproof.transf_program_match; auto.
  exists p2; split. apply SimplLocalsproof.match_transf_program; auto.
  exists p3; split. apply Cshmgenproof.transf_program_match; auto.
  exists p4; split. apply Cminorgenproof.transf_program_match; auto.
  exists p5; split. apply Selectionproof.transf_program_match; auto.
  exists p6; split. apply RTLgenproof.transf_program_match; auto.
  exists p7; split. apply total_if_match. apply Tailcallproof.transf_program_match.
  exists p8; split. apply Inliningproof.transf_program_match; auto.
  exists p9; split. apply Renumberproof.transf_program_match; auto.
  exists p10; split. apply total_if_match. apply Constpropproof.transf_program_match.
  exists p11; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p12; split. eapply partial_if_match; eauto. apply CSEproof.transf_program_match.
  exists p13; split. eapply partial_if_match; eauto. apply Deadcodeproof.transf_program_match.
  exists p13ptr; split. apply total_if_match. apply PointerNeonproof.transf_program_match.
  exists p13ptrL; split. apply total_if_match. apply LowerLongproof.transf_program_match.
  exists p13neN; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p13neP; split. apply total_if_match. apply PeelTwoproof.transf_program_match.
  exists p13neC; split. eapply partial_if_match; eauto. apply ExtraCleanupproof.transf_program_match.
  exists p13neR; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p13neV; split. apply total_if_match. apply MemoryNeonproof.transf_program_match.
  exists p13f; split. apply total_if_match. apply LoopFusionproof.transf_program_match.
  exists p13z; split. apply total_if_match. apply LoopTile2Dproof.transf_program_match.
  exists p13x; split. apply total_if_match. apply LoopInterchangeproof.transf_program_match.
  exists p13t; split. apply total_if_match. apply LoopTileproof.transf_program_match.
  exists p13v; split. apply total_if_match. apply Vectorizeproof.transf_program_match.
  exists p13w; split. apply total_if_match. apply LowerLongproof.transf_program_match.
  exists p13i; split. apply total_if_match. apply LICMproof.transf_program_match.
  exists p13q; split. apply total_if_match. apply PreheaderLICMproof.transf_program_match.
  exists p13r; split. apply total_if_match. apply StrengthReduceproof.transf_program_match.
  exists p13n; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p13p; split. apply total_if_match. apply LoopPeelproof.transf_program_match.
  exists p13h; split. apply total_if_match. apply HoistConstproof.transf_program_match.
  exists p13s; split. apply total_if_match. apply Scheduleproof.transf_program_match.
  exists p13l; split. apply total_if_match. apply LoadForwardproof.transf_program_match.
  exists p13d; split. apply total_if_match. apply StoreElimproof.transf_program_match.
  exists p13u; split. apply total_if_match. apply Unswitchproof.transf_program_match.
  exists p13a; split. apply total_if_match. apply Experimentalproof.transf_program_match.
  exists p13b; split. eapply partial_if_match; eauto. apply ExtraCleanupproof.transf_program_match.
  exists p13mn; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p13mp; split. apply total_if_match. apply PeelTwoproof.transf_program_match.
  exists p13mc; split. eapply partial_if_match; eauto. apply ExtraCleanupproof.transf_program_match.
  exists p13mr; split. apply total_if_match. apply Renumberproof.transf_program_match.
  exists p13mv; split. apply total_if_match. apply MemVectorproof.transf_program_match.
  exists p13mi; split. apply total_if_match. apply MemVectorproof.IndirectProof.transf_program_match.
  exists p13ml; split. apply total_if_match. apply LowerLongproof.transf_program_match.
  exists p14; split. apply Unusedglobproof.transf_program_match; auto.
  exists p15; split. apply Allocproof.transf_program_match; auto.
  exists p16; split. apply Tunnelingproof.transf_program_match.
  exists p17; split. apply Linearizeproof.transf_program_match; auto.
  exists p18; split. apply CleanupLabelsproof.transf_program_match; auto.
  exists p19; split. eapply partial_if_match; eauto. apply Debugvarproof.transf_program_match.
  exists p20; split. apply Stackingproof.transf_program_match; auto.
  exists tp; split. apply Asmgenproof.transf_program_match; auto.
  reflexivity.
Qed.

(** * Semantic preservation *)

(** We now prove that the whole CompCert compiler (as characterized by the
  [match_prog] relation) preserves semantics by constructing
  the following simulations:
- Forward simulations from [Cstrategy] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).
*)

Remark forward_simulation_identity:
  forall sem, forward_simulation sem sem.
Proof.
  intros. apply forward_simulation_step with (fun s1 s2 => s2 = s1); intros.
- auto.
- exists s1; auto.
- subst s2; auto.
- subst s2. exists s1'; auto.
Qed.

Lemma match_if_simulation:
  forall (A: Type) (sem: A -> semantics) (flag: unit -> bool) (transf: A -> A -> Prop) (prog tprog: A),
  match_if flag transf prog tprog ->
  (forall p tp, transf p tp -> forward_simulation (sem p) (sem tp)) ->
  forward_simulation (sem prog) (sem tprog).
Proof.
  intros. unfold match_if in *. destruct (flag tt). eauto. subst. apply forward_simulation_identity.
Qed.

Theorem cstrategy_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  forward_simulation (Cstrategy.semantics p) (Asm.semantics tp)
  /\ backward_simulation (atomic (Cstrategy.semantics p)) (Asm.semantics tp).
Proof.
  intros p tp M. unfold match_prog, pass_match in M; simpl in M.
Ltac DestructM :=
  match goal with
    [ H: exists p, _ /\ _ |- _ ] =>
      let p := fresh "p" in let M := fresh "M" in let MM := fresh "MM" in
      destruct H as (p & M & MM)
  end.
  repeat DestructM. subst tp.
  assert (F: forward_simulation (Cstrategy.semantics p) (Asm.semantics p53)).
  {
  eapply compose_forward_simulations.
    eapply SimplExprproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply SimplLocalsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cshmgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Cminorgenproof.transl_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Selectionproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply RTLgenproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Tailcallproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Inliningproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations. eapply Renumberproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Constpropproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact CSEproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Deadcodeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact PointerNeonproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LowerLongproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact PeelTwoproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact ExtraCleanupproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact MemoryNeonproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LoopFusionproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LoopTile2Dproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LoopInterchangeproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LoopTileproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Vectorizeproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LowerLongproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LICMproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact PreheaderLICMproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact StrengthReduceproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LoopPeelproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact HoistConstproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Scheduleproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LoadForwardproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact StoreElimproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Unswitchproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption.
    exact (Experimentalproof.transf_program_correct (experimental_unroll4 tt)).
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact ExtraCleanupproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact PeelTwoproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact ExtraCleanupproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Renumberproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact MemVectorproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact MemVectorproof.IndirectProof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact LowerLongproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Unusedglobproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Allocproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Tunnelingproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply Linearizeproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply CleanupLabelsproof.transf_program_correct; eassumption.
  eapply compose_forward_simulations.
    eapply match_if_simulation. eassumption. exact Debugvarproof.transf_program_correct.
  eapply compose_forward_simulations.
    eapply Stackingproof.transf_program_correct with (return_address_offset := Asmgenproof0.return_address_offset).
    exact Asmgenproof.return_address_exists.
    eassumption.
  eapply Asmgenproof.transf_program_correct; eassumption.
  }
  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Asm.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
Qed.

Theorem c_semantic_preservation:
  forall p tp,
  match_prog p tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply factor_backward_simulation.
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (proj2 (cstrategy_semantic_preservation _ _ H)).
Qed.

(** * Correctness of the CompCert compiler *)

(** Combining the results above, we obtain semantic preservation for two
  usage scenarios of CompCert: compilation of a single monolithic program,
  and separate compilation of multiple source files followed by linking.

  In the monolithic case, we have a whole C program [p] that is
  compiled in one run of CompCert to a whole Asm program [tp].
  Then, [tp] preserves the semantics of [p], in the sense that there
  exists a backward simulation of the dynamic semantics of [p]
  by the dynamic semantics of [tp]. *)

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (Asm.semantics tp).
Proof.
  intros. apply c_semantic_preservation. apply transf_c_program_match; auto.
Qed.

(** Here is the separate compilation case.  Consider a nonempty list [c_units]
  of C source files (compilation units), [C1 ,,, Cn].  Assume that every
  C compilation unit [Ci] is successfully compiled by CompCert, obtaining
  an Asm compilation unit [Ai].  Let [asm_unit] be the nonempty list
  [A1 ... An].  Further assume that the C units [C1 ... Cn] can be linked
  together to produce a whole C program [c_program].  Then, the generated
  Asm units can be linked together, producing a whole Asm program
  [asm_program].  Moreover, [asm_program] preserves the semantics of
  [c_program], in the sense that there exists a backward simulation of
  the dynamic semantics of [asm_program] by the dynamic semantics of [c_program].
*)

Theorem separate_transf_c_program_correct:
  forall c_units asm_units c_program,
  nlist_forall2 (fun cu tcu => transf_c_program cu = OK tcu) c_units asm_units ->
  link_list c_units = Some c_program ->
  exists asm_program,
      link_list asm_units = Some asm_program
   /\ backward_simulation (Csem.semantics c_program) (Asm.semantics asm_program).
Proof.
  intros.
  assert (nlist_forall2 match_prog c_units asm_units).
  { eapply nlist_forall2_imply. eauto. simpl; intros. apply transf_c_program_match; auto. }
  assert (exists asm_program, link_list asm_units = Some asm_program /\ match_prog c_program asm_program).
  { eapply link_list_compose_passes; eauto. }
  destruct H2 as (asm_program & P & Q).
  exists asm_program; split; auto. apply c_semantic_preservation; auto.
Qed.

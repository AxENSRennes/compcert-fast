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

(* Additional experimental cleanup rounds. Distributed under the repository's
   INRIA Non-Commercial License Agreement. Each constituent transformation is
   the existing, proved CompCert pass; this module introduces no memory oracle. *)
Require Import Coqlib Errors RTL Constprop CSE Deadcode.
Local Open Scope error_monad_scope.

Definition cleanup_round (p: RTL.program) : res RTL.program :=
  let p1 := Constprop.transf_program p in
  do p2 <- CSE.transf_program p1;
  Deadcode.transf_program p2.

Definition transf_program (p: RTL.program) : res RTL.program :=
  do p1 <- cleanup_round p;
  cleanup_round p1.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, Collège de France and Inria Paris            *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Platform-specific built-in functions *)

From Coq Require Import String.
Require Import Coqlib AST Integers Floats Values.
Require Import Builtins0.
Local Open Scope asttyp_scope.

Inductive platform_builtin : Type :=
  | BI_neon_add_u32x2
  | BI_neon_sub_u32x2
  | BI_neon_mul_u32x2.

Local Open Scope string_scope.

Definition platform_builtin_table : list (string * platform_builtin) :=
     ("__builtin_cc_neon_add_u32x2", BI_neon_add_u32x2)
  :: ("__builtin_cc_neon_sub_u32x2", BI_neon_sub_u32x2)
  :: ("__builtin_cc_neon_mul_u32x2", BI_neon_mul_u32x2)
  :: nil.

Definition platform_builtin_sig (b: platform_builtin) : signature :=
  [Xlong; Xlong ---> Xlong].

(** Explicit packed integer builtins.  Each 64-bit C integer contains two
    independent 32-bit lanes; lane arithmetic wraps modulo 2^32.  These
    numerical semantics are part of the platform builtin specification.
    Their four-instruction hardware expansion is printed by TargetPrinter,
    in the same trusted expansion boundary as other platform builtins.
    This does not model general NEON registers or vectorize C loops. *)
Definition packed_u32x2 (op: int -> int -> int) (a b: int64): int64 :=
  Int64.ofwords (op (Int64.hiword a) (Int64.hiword b))
                (op (Int64.loword a) (Int64.loword b)).

Definition platform_builtin_sem (b: platform_builtin) : builtin_sem (sig_res (platform_builtin_sig b)) :=
  match b with
  | BI_neon_add_u32x2 => mkbuiltin_n2t Tlong Tlong Xlong (packed_u32x2 Int.add)
  | BI_neon_sub_u32x2 => mkbuiltin_n2t Tlong Tlong Xlong (packed_u32x2 Int.sub)
  | BI_neon_mul_u32x2 => mkbuiltin_n2t Tlong Tlong Xlong (packed_u32x2 Int.mul)
  end.

Definition eq_platform_builtin: forall (x y: platform_builtin), {x=y} + {x<>y}.
Proof.
  decide equality.
Defined.

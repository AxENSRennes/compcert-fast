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

(** Lower generic word packing/extraction to existing ARM64 operations.
    No new instruction semantics or printer expansion is introduced. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Experimental.
Definition amount_zero: amount64.
Proof. refine {| a64_amount := Int.zero |}; reflexivity. Defined.
Definition amount_32: amount64.
Proof. refine {| a64_amount := Int.repr 32 |}; reflexivity. Defined.
Definition fresh_reg (f: function): reg := Pos.succ (max_reg_function f).
Definition base (pc: node): node := xO pc.
Definition after (pc: node): node := xI pc.
Definition first_instr (f: function) (pc: node) (i: instruction): instruction :=
  match i with
  | Iop Omakelong (hi :: lo :: nil) dst s =>
      Iop (Oextend Xuns32 amount_32) (hi :: nil) (fresh_reg f) (after pc)
  | Iop Ohighlong (r :: nil) dst s =>
      Iop (Oshiftl Slsr amount_32) (r :: nil) (fresh_reg f) (after pc)
  | Iop Omakelong _ _ s | Iop Ohighlong _ _ s => Inop (base s)
  | _ => Experimental.map_successors base i
  end.
Definition next_instr (f: function) (pc: node) (i: instruction): instruction :=
  match i with
  | Iop Omakelong (hi :: lo :: nil) dst s =>
      Iop (Oaddlext Xuns32 amount_zero) (fresh_reg f :: lo :: nil) dst (base s)
  | Iop Ohighlong (r :: nil) dst s =>
      Iop Olowlong (fresh_reg f :: nil) dst (base s)
  | _ => Inop (base pc)
  end.
(** Only instructions that expand get a suffix node. Unused suffixes would
    create artificial predecessors and consume other passes' size budgets. *)
Definition needs_second (i: instruction): bool :=
  match i with
  | Iop Omakelong (_ :: _ :: nil) _ _ | Iop Ohighlong (_ :: nil) _ _ => true
  | _ => false
  end.
Definition next_instr_option (f: function) (i: instruction): option instruction :=
  match i with
  | Iop Omakelong (hi :: lo :: nil) dst s =>
      Some (Iop (Oaddlext Xuns32 amount_zero) (fresh_reg f :: lo :: nil) dst (base s))
  | Iop Ohighlong (r :: nil) dst s =>
      Some (Iop Olowlong (fresh_reg f :: nil) dst (base s))
  | _ => None
  end.
Definition transf_function (f: function): function :=
  mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
    (PTree.Node (PTree.map (first_instr f) (fn_code f)) None
                (PTree.map_filter1 (next_instr_option f) (fn_code f)))
    (base (fn_entrypoint f)).
Definition transf_fundef (f: fundef): fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.

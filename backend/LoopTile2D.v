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

(** Two-dimensional 2x2 tiling of a 2x3 rectangular pure nest.  The last
    column tile is partial.  Unlike the counted strip-mining foundation,
    this proposal changes the order of iteration coordinates.  It has no
    semantic authority: the proved whole-function symbolic validator must
    accept the actual reordered return expression. *)
Require Import Coqlib Maps AST Integers Op Registers RTL LoopFusion LoopInterchange.

Definition tile_base (f: function): reg := Pos.succ(max_reg_function f).
Definition tile_end (f: function): reg := Pos.succ(tile_base f).
Definition end_pc (f: function): node := Pos.succ(max_pc_function f).
Definition row_pc (f: function): node := Pos.succ(end_pc f).
Definition update_pc (f: function): node := Pos.succ(row_pc f).
Definition bound_pc (f: function): node := Pos.succ(update_pc f).
Definition column_pc (f: function): node := Pos.succ(bound_pc f).
Definition fixed_bound (c: condition) (n: Z): bool :=
  match c with
  | Ccompimm Clt k | Ccompuimm Clt k => Int.eq k (Int.repr n)
  | _=>false end.
Definition copy_instr (f: function) (plan: LoopInterchange.rectangle)
    (pc: node) (i: instruction): instruction :=
  if peq pc (LoopInterchange.outer_init plan) then
    Iop (Ointconst Int.zero) nil (tile_base f) (end_pc f)
  else if peq pc (LoopInterchange.inner_init plan) then
    Iop Omove (tile_base f::nil) (LoopInterchange.inner_reg plan)
      (if LoopInterchange.post_tested plan then LoopInterchange.body_entry plan
       else LoopInterchange.inner_test plan)
  else if peq pc (LoopInterchange.outer_test plan) then
    Icond (LoopInterchange.outer_cond plan) (LoopInterchange.outer_reg plan::nil)
      (LoopInterchange.inner_init plan) (update_pc f)
  else if peq pc (LoopInterchange.inner_test plan) then
    Icond (LoopInterchange.inner_cond plan) (LoopInterchange.inner_reg plan::nil)
      (column_pc f) (LoopInterchange.outer_update plan)
  else i.
Definition tiled (f: function) (plan: LoopInterchange.rectangle): function :=
  mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
    (PTree.set (end_pc f)
      (Iop (Oaddimm(Int.repr 2)) (tile_base f::nil) (tile_end f) (row_pc f))
    (PTree.set (row_pc f)
      (Iop (Ointconst Int.zero) nil (LoopInterchange.outer_reg plan) (LoopInterchange.inner_init plan))
    (PTree.set (update_pc f)
      (Iop (Oaddimm(Int.repr 2)) (tile_base f::nil) (tile_base f) (bound_pc f))
    (PTree.set (bound_pc f)
      (Icond (Ccompimm Clt (Int.repr 3)) (tile_base f::nil) (end_pc f) (LoopInterchange.exit_node plan))
    (PTree.set (column_pc f)
      (Icond (Ccomp Clt) (LoopInterchange.inner_reg plan::tile_end f::nil)
        (LoopInterchange.body_entry plan) (LoopInterchange.outer_update plan))
      (PTree.map (copy_instr f plan) (fn_code f)))))))
    (fn_entrypoint f).
Definition candidate (f: function): function :=
  let items:=PTree.elements(fn_code f) in
  if Nat.leb(length items)512 then
    match LoopInterchange.choose f items with
    | Some plan =>
      if fixed_bound(LoopInterchange.outer_cond plan)2 &&
         fixed_bound(LoopInterchange.inner_cond plan)3
      then tiled f plan else f
    | None=>f end
  else f.
Definition accepted (f: function): bool := LoopFusion.validate_function f (candidate f).
Definition transf_function := LoopFusion.transf_function_with candidate.
Definition transf_fundef := LoopFusion.transf_fundef_with candidate.
Definition transf_program := LoopFusion.transf_program_with candidate.

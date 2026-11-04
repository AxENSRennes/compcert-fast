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

(** Counted one-dimensional strip mining with four-iteration tiles.
    A selected loop induction backedge is split by an inner countdown and an
    outer tile reset. Original loop tests and all memory/call effects retain
    their order, so partial tiles need no alias or divisibility assumption.
    This pass does not reorder iterations or implement multidimensional tiling. *)
Require Import Coqlib Maps AST Integers Op Registers RTL HoistConst.

Record tile := Tile {
  tile_pc: node;
  tile_reg: reg;
  tile_step: int;
  tile_header: node
}.
Definition fresh_reg (f: function): reg := Pos.succ (max_reg_function f).
Definition test_pc (f: function): node := Pos.succ (max_pc_function f).
Definition reset_pc (f: function): node := Pos.succ (test_pc f).
Definition advance_pc (f: function): node := Pos.succ (reset_pc f).
Definition entry_pc (f: function): node := Pos.succ (advance_pc f).
Definition header_test (f: function) (pc: node): bool :=
  match (fn_code f)!pc with Some (Icond _ _ _ _) => true | _ => false end.
Fixpoint choose_in (f: function) (fuel: nat) (items: list (node * instruction)) : option tile :=
  match fuel,items with
  | S remaining,(pc,Iop (Oaddimm n) (r :: nil) dst next) :: rest =>
      if peq r dst then
        if Pos.leb pc next && header_test f next && HoistConst.cyclic f pc (Iop (Oaddimm n) (r :: nil) dst next)
        then Some (Tile pc r n next) else choose_in f remaining rest
      else choose_in f remaining rest
  | S remaining,_ :: rest => choose_in f remaining rest
  | _,_ => None
  end.
Definition chosen (f: function): option tile :=
  let items := PTree.elements (fn_code f) in
  if Nat.leb (length items) 512 then choose_in f 128 items else None.
Definition rewrite_instr (f: function) (plan: tile) (pc: node) (i: instruction): instruction :=
  if peq pc (tile_pc plan) then
    Iop (Oaddimm (tile_step plan)) (tile_reg plan :: nil) (tile_reg plan) (test_pc f)
  else i.
Definition tiled (f: function) (plan: tile): function :=
  let temporary := fresh_reg f in
  mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
    (PTree.set (entry_pc f) (Iop (Ointconst (Int.repr 4)) nil temporary (fn_entrypoint f))
    (PTree.set (test_pc f) (Icond (Ccompimm Ceq Int.one) (temporary :: nil) (reset_pc f) (advance_pc f))
    (PTree.set (reset_pc f) (Iop (Ointconst (Int.repr 4)) nil temporary (tile_header plan))
    (PTree.set (advance_pc f) (Iop (Oaddimm (Int.repr (-1))) (temporary :: nil) temporary (tile_header plan))
      (PTree.map (rewrite_instr f plan) (fn_code f))))))
    (entry_pc f).
Definition transf_function (f: function): function :=
  match chosen f with Some plan => tiled f plan | None => f end.
Definition transf_fundef (f: fundef): fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.

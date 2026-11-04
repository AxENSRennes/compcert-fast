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

(** Guarded loop unswitching for one immutable signed integer condition.
    Learning is delayed until the original conditional actually executes. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Experimental HoistConst.

Inductive phase := Normal | Known (answer: bool).
Definition tag (mode: phase) (pc: node) : node :=
  match mode with
  | Normal => xO (xO pc)
  | Known true => xI (xO pc)
  | Known false => xO (xI pc)
  end.
Record branch := mkbranch {
  branch_pc: node;
  branch_cmp: comparison;
  branch_imm: int;
  branch_reg: reg;
  branch_yes: node;
  branch_no: node
}.
Definition immutable (f: function) (r: reg) : bool :=
  forallb (fun kv => match instr_defs (snd kv) with
                    | Some dst => if peq dst r then false else true
                    | None => true end) (PTree.elements f.(fn_code)).
Fixpoint choose_in (loops: bool) (f: function) (items: list (node * instruction)) : option branch :=
  match items with
  | nil => None
  | (pc, i) :: rest =>
      match i with
      | Icond (Ccompimm cmp n) (r :: nil) yes no =>
          if immutable f r && (negb loops || HoistConst.cyclic f pc i)
          then Some (mkbranch pc cmp n r yes no) else choose_in loops f rest
      | _ => choose_in loops f rest
      end
  end.
Definition chosen (f: function) : option branch :=
  match choose_in true f (PTree.elements f.(fn_code)) with
  | Some b => Some b
  | None => choose_in false f (PTree.elements f.(fn_code))
  end.
Definition copy_instr (b: branch) (mode: phase) (pc: node) (i: instruction) : instruction :=
  if peq pc b.(branch_pc) then
    match mode with
    | Normal => Icond (Ccompimm b.(branch_cmp) b.(branch_imm)) (b.(branch_reg) :: nil)
                       (tag (Known true) b.(branch_yes)) (tag (Known false) b.(branch_no))
    | Known answer => Inop (tag (Known answer) (if answer then b.(branch_yes) else b.(branch_no)))
    end
  else Experimental.map_successors (tag mode) i.
Definition copy_code (f: function) (b: branch) : code :=
  PTree.Node
    (PTree.Node (PTree.map (copy_instr b Normal) f.(fn_code)) None
                (PTree.map (copy_instr b (Known false)) f.(fn_code)))
    None
    (PTree.Node (PTree.map (copy_instr b (Known true)) f.(fn_code)) None (PTree.empty instruction)).
Definition specialized (f: function) (b: branch) : function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (copy_code f b) (tag Normal f.(fn_entrypoint)).
Definition transf_function (f: function) : function :=
  match chosen f with Some b => specialized f b | None => f end.
Definition label (f: function) (mode: phase) (pc: node) : node :=
  match chosen f with Some _ => tag mode pc | None => pc end.
Definition transf_fundef (f: fundef) : fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program) : program := AST.transform_program transf_fundef p.

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

(** Validated two-traversal peeling of postorder RTL control flow.
    The first two copies transfer to a stable copy after successive backedge hints;
    the stable copy never returns to the initial copy. The projection checker
    proves safety independently of this heuristic. Larger functions are kept. *)
Require Import Coqlib Maps AST RTL Experimental.

Inductive phase := First | Second | Stable.
Definition tag (mode: phase) (pc: node): node :=
  match mode with First => xO(xO pc) | Second => xI(xO pc) | Stable => xO(xI pc) end.
Definition project (pc: node): node := Experimental.project (Experimental.project pc).
Definition next_phase (mode: phase): phase :=
  match mode with First => Second | Second => Stable | Stable => Stable end.
Definition advance (mode: phase) (pc succ: node): node :=
  tag (if Pos.leb pc succ then next_phase mode else mode) succ.
Definition copy_instruction (mode: phase) (pc: node) (i: instruction): instruction :=
  map_successors (advance mode pc) i.
Definition peel_candidate (f: function): function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (PTree.Node
      (PTree.Node (PTree.map (copy_instruction First) f.(fn_code)) None
                  (PTree.map (copy_instruction Stable) f.(fn_code))) None
      (PTree.Node (PTree.map (copy_instruction Second) f.(fn_code)) None (PTree.empty instruction)))
    (tag First f.(fn_entrypoint)).
Definition has_backedge (items: list(node*instruction)): bool :=
  existsb (fun kv=>existsb(Pos.leb(fst kv))(successors_instr(snd kv))) items.
Definition candidate (f: function): function :=
  let items:=PTree.elements f.(fn_code) in
  if Nat.leb(length items)512 then if has_backedge items then peel_candidate f else f else f.
Definition accepted (f: function): bool := check_function f (candidate f) project.
Definition transf_function (f: function): function := if accepted f then candidate f else f.
Definition source_node (f: function): node -> node := if accepted f then project else fun pc=>pc.
Definition match_pc (f: function) (pc tpc: node): Prop :=
  source_node f tpc=pc /\
  (accepted f=true -> present(fn_code(transf_function f))tpc=true).
Definition transf_fundef (f: fundef): fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.

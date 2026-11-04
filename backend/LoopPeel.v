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

(** Validated first-traversal peeling of postorder RTL control flow.
    The initial copy transfers to a stable copy at its first backedge hint;
    the stable copy never returns to the initial copy. The projection checker
    proves safety independently of this heuristic. Larger functions are kept. *)
Require Import Coqlib Maps AST RTL Experimental.

Definition advance (stable: bool) (pc succ: node): node :=
  tagged (orb stable (Pos.leb pc succ)) succ.
Definition copy_instruction (stable: bool) (pc: node) (i: instruction): instruction :=
  map_successors (advance stable pc) i.
Definition copy_node (c: code) (pc: node) (i: instruction): code :=
  PTree.set (tagged false pc) (copy_instruction false pc i)
    (PTree.set (tagged true pc) (copy_instruction true pc i) c).
Definition peel_candidate (f: function): function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (PTree.fold copy_node f.(fn_code) (PTree.empty instruction))
    (tagged false f.(fn_entrypoint)).
Definition has_backedge (items: list (node * instruction)): bool :=
  existsb (fun kv => existsb (Pos.leb (fst kv)) (successors_instr (snd kv))) items.
Definition candidate (f: function): function :=
  let items := PTree.elements f.(fn_code) in
  if Nat.leb (length items) 512 then
    if has_backedge items then peel_candidate f else f
  else f.
Definition accepted (f: function): bool := check_function f (candidate f) project.
Definition transf_function (f: function): function :=
  if accepted f then candidate f else f.
Definition source_node (f: function): node -> node :=
  if accepted f then project else fun pc => pc.
Definition match_pc (f: function) (pc tpc: node): Prop :=
  source_node f tpc = pc /\
  (accepted f = true -> present (fn_code (transf_function f)) tpc = true).
Definition transf_fundef (f: fundef): fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.

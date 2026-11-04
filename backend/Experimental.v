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

(* Experimental CFG covering and bounded loop unrolling. Distributed under
   the INRIA Non-Commercial License Agreement of this repository. *)

Require Import Coqlib Maps Errors AST RTL Op.

Definition map_successors (rho: node -> node) (i: instruction) : instruction :=
  match i with
  | Inop s => Inop (rho s)
  | Iop op args dst s => Iop op args dst (rho s)
  | Iload chunk addr args dst s => Iload chunk addr args dst (rho s)
  | Istore chunk addr args src s => Istore chunk addr args src (rho s)
  | Icall sg ros args dst s => Icall sg ros args dst (rho s)
  | Itailcall sg ros args => Itailcall sg ros args
  | Ibuiltin ef args dst s => Ibuiltin ef args dst (rho s)
  | Icond cond args s1 s2 => Icond cond args (rho s1) (rho s2)
  | Ijumptable arg tbl => Ijumptable arg (List.map rho tbl)
  | Ireturn arg => Ireturn arg
  end.

Definition instruction_eq (i j: instruction) : {i=j} + {i<>j}.
Proof.
  generalize peq, Op.eq_operation, Op.eq_addressing, Op.eq_condition,
    chunk_eq, signature_eq, external_function_eq, list_eq_dec,
    (eq_builtin_arg peq), (eq_builtin_res peq); decide equality.
all: decide equality; apply peq.
Defined.

Definition present (c: code) (pc: node) : bool :=
  match c!pc with Some _ => true | None => false end.

Definition check_node (f tf: function) (project: node -> node)
                      (pc: node) (ti: instruction) : bool :=
  match f.(fn_code)!(project pc) with
  | None => false
  | Some si =>
      if instruction_eq (map_successors project ti) si
      then forallb (present tf.(fn_code)) (successors_instr ti)
      else false
  end.

Definition check_function (f tf: function) (project: node -> node) : bool :=
  if signature_eq f.(fn_sig) tf.(fn_sig) then
  if list_eq_dec peq f.(fn_params) tf.(fn_params) then
  if zeq f.(fn_stacksize) tf.(fn_stacksize) then
  if peq (project tf.(fn_entrypoint)) f.(fn_entrypoint) then
    present tf.(fn_code) tf.(fn_entrypoint) &&
    forallb (fun kv => check_node f tf project (fst kv) (snd kv))
            (PTree.elements tf.(fn_code))
  else false else false else false else false.

Definition project (pc: node) : node :=
  match pc with xO p | xI p => p | xH => xH end.

Definition tagged (phase: bool) (pc: node) : node :=
  if phase then xI pc else xO pc.

(* Postorder RTL numbering gives a convenient conservative backedge hint.
   Correctness does not depend on this hint: all edges retain their projected
   source target, and the validator checks the resulting finite graph. *)
Definition next_phase (phase: bool) (pc succ: node) : bool :=
  if Pos.leb pc succ then negb phase else phase.

Definition copy_instruction (phase: bool) (pc: node) (i: instruction) :=
  map_successors (fun succ => tagged (next_phase phase pc succ) succ) i.

Definition copy_node (c: code) (pc: node) (i: instruction) : code :=
  PTree.set (tagged true pc) (copy_instruction true pc i)
    (PTree.set (tagged false pc) (copy_instruction false pc i) c).

Definition unroll_candidate (f: function) : function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (PTree.fold copy_node f.(fn_code) (PTree.empty instruction))
    (tagged false f.(fn_entrypoint)).

Definition project_for (four: bool) : node -> node :=
  if four then fun pc => project (project pc) else project.

Definition tagged4 (a b: bool) (pc: node) := tagged a (tagged b pc).
Definition advance4 (a b: bool) (pc succ: node) : node :=
  if Pos.leb pc succ
  then tagged4 (negb a) (xorb a b) succ
  else tagged4 a b succ.
Definition copy_node4 (c: code) (pc: node) (i: instruction) : code :=
  PTree.set (tagged4 true true pc) (map_successors (advance4 true true pc) i)
  (PTree.set (tagged4 false true pc) (map_successors (advance4 false true pc) i)
  (PTree.set (tagged4 true false pc) (map_successors (advance4 true false pc) i)
  (PTree.set (tagged4 false false pc) (map_successors (advance4 false false pc) i) c))).
Definition unroll4_candidate (f: function) : function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (PTree.fold copy_node4 f.(fn_code) (PTree.empty instruction))
    (tagged4 false false f.(fn_entrypoint)).
Definition candidate (four: bool) (f: function) : function :=
  if four then unroll4_candidate f else unroll_candidate f.
Definition accepted (four: bool) (f: function) : bool :=
  check_function f (candidate four f) (project_for four).
Definition transf_function (four: bool) (f: function) : function :=
  if accepted four f then candidate four f else f.
Definition source_node (four: bool) (f: function) : node -> node :=
  if accepted four f then project_for four else fun pc => pc.
Definition match_pc (four: bool) (f: function) (pc tpc: node) : Prop :=
  source_node four f tpc = pc /\
  (accepted four f = true -> present (fn_code (transf_function four f)) tpc = true).
Definition transf_fundef (four: bool) (f: fundef) : fundef :=
  AST.transf_fundef (transf_function four) f.
Definition transf_program (four: bool) (p: program) : program :=
  AST.transform_program (transf_fundef four) p.

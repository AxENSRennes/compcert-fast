(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Locally validated independent uint32 lane arithmetic under a retained
    signed source guard. All original memory operations, loop edges and tails
    are retained; no alignment, alias or trip-count assumption is introduced. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Schedule MemoryNeon.
Record vector_pair := mkpair {
  guard_pc: node; guard_cond: comparison; false_pc: node;
  first_pc: node; second_pc: node; low_reg: reg; high_reg: reg;
  first_imm: int; second_imm: int; first_dst: reg; second_dst: reg; after_pc: node
}.
Definition input_reg (f: function): reg := Pos.succ(max_reg_function f).
Definition constant_reg (f: function): reg := Pos.succ(input_reg f).
Definition result_reg (f: function): reg := Pos.succ(constant_reg f).
Definition constant_pc (f: function): node := Pos.succ(max_pc_function f).
Definition builtin_pc (f: function): node := Pos.succ(constant_pc f).
Definition extract_pc (f: function): node := Pos.succ(builtin_pc f).
Definition packed_constant (p:vector_pair): int64 := Int64.ofwords(second_imm p)(first_imm p).
Definition packed_builtin := MemoryNeon.packed_builtin.
Definition validate_candidate (f:function)(g:node):option vector_pair :=
  match (fn_code f)!g with
  | Some(Icond(Ccomp c)(lo::hi::nil)a no) =>
    match (fn_code f)!a with
    | Some(Iop(Oaddimm nlo)(rlo::nil)dlo b) =>
      match (fn_code f)!b with
      | Some(Iop(Oaddimm nhi)(rhi::nil)dhi after) =>
        if peq lo rlo then if peq hi rhi then
        if peq g a then None else if peq g b then None else if peq a b then None else
        if peq no a then None else if peq no b then None else
        if peq(fn_entrypoint f)a then None else if peq(fn_entrypoint f)b then None else
        if peq dlo lo then None else if peq dlo hi then None else if peq dlo dhi then None else
        if Schedule.predecessor_check f g a then
        if Schedule.predecessor_check f a b then
          Some(mkpair g c no a b lo hi nlo nhi dlo dhi after)
        else None else None
        else None else None
      | _=>None end
    | _=>None end
  | _=>None end.
Fixpoint find_candidate(f:function)(items:list(node*instruction)):option vector_pair :=
  match items with
  | nil=>None
  | (pc,_)::rest=>match validate_candidate f pc with Some p=>Some p|None=>find_candidate f rest end
  end.
Definition selected_pair(f:function):option vector_pair :=
  let items:=PTree.elements(fn_code f) in
  if Nat.leb(length items)512 then find_candidate f items else None.
Definition apply_pair(f:function)(p:vector_pair):function :=
  mkfunction(fn_sig f)(fn_params f)(fn_stacksize f)
    (PTree.set(first_pc p)
      (Iop Omakelong(high_reg p::low_reg p::nil)(input_reg f)(constant_pc f))
    (PTree.set(constant_pc f)
      (Iop(Olongconst(packed_constant p))nil(constant_reg f)(builtin_pc f))
    (PTree.set(builtin_pc f)
      (Ibuiltin packed_builtin(BA(input_reg f)::BA(constant_reg f)::nil)(BR(result_reg f))(extract_pc f))
    (PTree.set(extract_pc f)
      (Iop Olowlong(result_reg f::nil)(first_dst p)(second_pc p))
    (PTree.set(second_pc p)
      (Iop Ohighlong(result_reg f::nil)(second_dst p)(after_pc p))(fn_code f))))))
    (fn_entrypoint f).
Definition transf_function(f:function):function :=
  match selected_pair f with Some p=>apply_pair f p|None=>f end.
Definition accepted(f:function):bool :=match selected_pair f with Some _=>true|None=>false end.
Definition transf_fundef := AST.transf_fundef transf_function.
Definition transf_program(p:program):program := AST.transform_program transf_fundef p.

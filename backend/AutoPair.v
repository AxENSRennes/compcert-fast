(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Automatically group two iterations of a scalar lookahead loop.
    The source already compares adjacent cells, so its first signed guard
    justifies independent packed arithmetic. Reads and conditional writes
    keep their original order. An untouched scalar loop handles zero/one
    remaining iterations; the original source requires n+1 readable cells. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Experimental MemoryNeon.
Local Open Scope asttyp_scope.

Record plan := Plan { increment: int }.
Definition scalar_sig := mksignature (Xptr::Xint::nil) Xvoid cc_default.
Definition source_code (p:plan): code := MemoryNeon.code_of
 ((10%positive,Inop 9%positive)::
  (9%positive,Icond(Ccompuimm Cne Int.zero)(1%positive::nil)8%positive 1%positive)::
  (8%positive,Iload Mint32(Aindexed Int64.zero)(2%positive::nil)4%positive 7%positive)::
  (7%positive,Iload Mint32(Aindexed(Int64.repr 4))(2%positive::nil)3%positive 6%positive)::
  (6%positive,Icond(Ccomp Clt)(4%positive::3%positive::nil)5%positive 3%positive)::
  (5%positive,Iop(Oaddimm(increment p))(4%positive::nil)6%positive 4%positive)::
  (4%positive,Istore Mint32(Aindexed Int64.zero)(2%positive::nil)6%positive 3%positive)::
  (3%positive,Iop(Oaddlimm(Int64.repr 4))(2%positive::nil)2%positive 2%positive)::
  (2%positive,Iop(Oaddimm(Int.repr(-1)))(1%positive::nil)1%positive 9%positive)::
  (1%positive,Ireturn None)::nil).
Definition target_code (p:plan): code :=
 PTree.set 10%positive (Inop 20%positive)
 (fold_right (fun item c=>PTree.set(fst item)(snd item)c) (source_code p)
 ((20%positive,Icond(Ccompuimm Cge(Int.repr 2))(1%positive::nil)38%positive 9%positive)::
  (38%positive,Iload Mint32(Aindexed Int64.zero)(2%positive::nil)4%positive 37%positive)::
  (37%positive,Iload Mint32(Aindexed(Int64.repr 4))(2%positive::nil)3%positive 71%positive)::
  (71%positive,Iop Omakelong(3%positive::4%positive::nil)7%positive 72%positive)::
  (72%positive,Iop(Olongconst(Int64.ofwords(increment p)(increment p)))nil 8%positive 73%positive)::
  (73%positive,Ibuiltin MemoryNeon.packed_builtin(BA 7%positive::BA 8%positive::nil)(BR 9%positive)36%positive)::
  (36%positive,Icond(Ccomp Clt)(4%positive::3%positive::nil)35%positive 33%positive)::
  (35%positive,Iop Olowlong(9%positive::nil)6%positive 34%positive)::
  (34%positive,Istore Mint32(Aindexed Int64.zero)(2%positive::nil)6%positive 33%positive)::
  (33%positive,Iop(Oaddlimm(Int64.repr 4))(2%positive::nil)2%positive 32%positive)::
  (32%positive,Iop(Oaddimm(Int.repr(-1)))(1%positive::nil)1%positive 49%positive)::
  (49%positive,Icond(Ccompuimm Cne Int.zero)(1%positive::nil)48%positive 1%positive)::
  (48%positive,Iload Mint32(Aindexed Int64.zero)(2%positive::nil)4%positive 47%positive)::
  (47%positive,Iload Mint32(Aindexed(Int64.repr 4))(2%positive::nil)3%positive 46%positive)::
  (46%positive,Icond(Ccomp Clt)(4%positive::3%positive::nil)45%positive 43%positive)::
  (45%positive,Iop Ohighlong(9%positive::nil)6%positive 44%positive)::
  (44%positive,Istore Mint32(Aindexed Int64.zero)(2%positive::nil)6%positive 43%positive)::
  (43%positive,Iop(Oaddlimm(Int64.repr 4))(2%positive::nil)2%positive 42%positive)::
  (42%positive,Iop(Oaddimm(Int.repr(-1)))(1%positive::nil)1%positive 20%positive)::nil)).
Definition source_template(p:plan):function := mkfunction scalar_sig (2%positive::1%positive::nil)0(source_code p)10%positive.
Definition target_template(p:plan):function := mkfunction scalar_sig (2%positive::1%positive::nil)0(target_code p)10%positive.
Definition selected(f:function):option plan :=
 match(fn_code f)!5%positive with
 | Some(Iop(Oaddimm k)_ _ _) =>
   let p:=Plan k in
   if signature_eq(fn_sig f)scalar_sig then
   if list_eq_dec peq(fn_params f)(2%positive::1%positive::nil) then
   if zeq(fn_stacksize f)0 then
   if peq(fn_entrypoint f)10%positive then
   if PTree.beq(fun a b=>if instruction_eq a b then true else false)(fn_code f)(source_code p)
   then Some p else None else None else None else None else None
 | _=>None end.
Definition accepted(f:function):bool := match selected f with Some _=>true|None=>false end.
Definition transf_function(f:function):function := match selected f with Some p=>target_template p|None=>f end.
Definition transf_fundef := AST.transf_fundef transf_function.
Definition transf_program(p:program):program := AST.transform_program transf_fundef p.

Definition first_pc(pc:node):node := if peq pc 6%positive then 71%positive else Pos.add pc 30%positive.
Definition second_pc(pc:node):node := Pos.add pc 40%positive.

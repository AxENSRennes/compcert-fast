(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** A deliberately bounded memory-vectorization certificate for a guarded
    two-iteration uint32 update. The retained signed comparison witnesses
    integer-definedness of both loaded lanes. No new target semantics. *)
From Coq Require Import String.
Require Import Coqlib Maps AST Integers Values Memory Op Registers RTL Builtins1 Experimental.
Local Open Scope string_scope.
Local Open Scope asttyp_scope.

Record plan := Plan { global_id: ident; low_add: int; high_add: int }.
Definition packed_builtin : external_function :=
  EF_builtin "__builtin_cc_neon_add_u32x2" [Xlong; Xlong ---> Xlong].
Definition packed_eval (a b: val): val :=
  match a,b with Vlong x,Vlong y => Vlong(packed_u32x2 Int.add x y) | _,_ => Vundef end.
Definition void_sig := mksignature nil Xvoid cc_default.
Definition code_of (items: list(node * instruction)): code :=
  fold_right (fun item code => PTree.set (fst item) (snd item) code) (PTree.empty instruction) items.
Definition source_code (p: plan): code := code_of
  ((22%positive,Iop(Oaddrsymbol(global_id p)Ptrofs.zero)nil 12%positive 21%positive)::
   (21%positive,Iload Mint32(Aindexed Int64.zero)(12%positive::nil)3%positive 20%positive)::
   (20%positive,Iop Omove(12%positive::nil)11%positive 19%positive)::
   (19%positive,Iload Mint32(Aindexed(Int64.repr 4))(11%positive::nil)2%positive 18%positive)::
   (18%positive,Icond(Ccomp Clt)(3%positive::2%positive::nil)17%positive 1%positive)::
   (17%positive,Inop 16%positive)::
   (16%positive,Iop Omove(11%positive::nil)5%positive 15%positive)::
   (15%positive,Iop Omove(3%positive::nil)8%positive 14%positive)::
   (14%positive,Iop Omove(8%positive::nil)7%positive 13%positive)::
   (13%positive,Iop(Oaddimm(low_add p))(7%positive::nil)6%positive 12%positive)::
   (12%positive,Istore Mint32(Aindexed Int64.zero)(5%positive::nil)6%positive 11%positive)::
   (11%positive,Inop 10%positive)::
   (10%positive,Iop(Oaddrsymbol(global_id p)Ptrofs.zero)nil 5%positive 9%positive)::
   (9%positive,Iop Omove(5%positive::nil)10%positive 8%positive)::
   (8%positive,Iload Mint32(Aindexed(Int64.repr 4))(10%positive::nil)8%positive 7%positive)::
   (7%positive,Inop 6%positive)::(6%positive,Inop 5%positive)::
   (5%positive,Iop(Oaddimm(high_add p))(8%positive::nil)6%positive 4%positive)::
   (4%positive,Istore Mint32(Aindexed(Int64.repr 4))(5%positive::nil)6%positive 3%positive)::
   (3%positive,Inop 2%positive)::(2%positive,Ireturn None)::(1%positive,Ireturn None)::nil).
Definition target_code (p: plan): code := code_of
  ((7%positive,Iop(Oaddrsymbol(global_id p)Ptrofs.zero)nil 1%positive 6%positive)::
   (6%positive,Iload Mint32(Aindexed Int64.zero)(1%positive::nil)2%positive 5%positive)::
   (5%positive,Iload Mint32(Aindexed(Int64.repr 4))(1%positive::nil)3%positive 4%positive)::
   (4%positive,Icond(Ccomp Clt)(2%positive::3%positive::nil)3%positive 1%positive)::
   (3%positive,Iload Mint64(Aindexed Int64.zero)(1%positive::nil)4%positive 8%positive)::
   (8%positive,Iop(Olongconst(Int64.ofwords(high_add p)(low_add p)))nil 5%positive 9%positive)::
   (9%positive,Ibuiltin packed_builtin(BA 4%positive::BA 5%positive::nil)(BR 6%positive)10%positive)::
   (10%positive,Istore Mint64(Aindexed Int64.zero)(1%positive::nil)6%positive 1%positive)::
   (1%positive,Ireturn None)::nil).
Definition source_template (p: plan): function := mkfunction void_sig nil 0 (source_code p)22%positive.
Definition target_template (p: plan): function := mkfunction void_sig nil 0 (target_code p)7%positive.
Definition selected (f: function): option plan :=
  match (fn_code f)!22%positive,(fn_code f)!13%positive,(fn_code f)!5%positive with
  | Some(Iop(Oaddrsymbol id _) _ _ _),Some(Iop(Oaddimm lo) _ _ _),Some(Iop(Oaddimm hi) _ _ _) =>
    let p:=Plan id lo hi in
    if signature_eq(fn_sig f)void_sig then
    if list_eq_dec peq(fn_params f)nil then
    if zeq(fn_stacksize f)0 then
    if peq(fn_entrypoint f)22%positive then
    if PTree.beq (fun a b=>if instruction_eq a b then true else false)(fn_code f)(source_code p) then Some p else None
    else None else None else None else None
  | _,_,_=>None end.
Definition accepted (f: function): bool := match selected f with Some _=>true|None=>false end.
Definition transf_function (f: function): function :=
  match selected f with Some p=>target_template p|None=>f end.
Definition transf_fundef := AST.transf_fundef transf_function.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.

(** The checker executes only ordinary silent RTL operations and the already
    specified packed-add builtin. It introduces no oracle or memory semantics. *)
Definition transfer (ge: genv) (f: function) (sp: val) (pc: node) (rs: regset) (m: mem)
  : option(node * regset * mem) :=
  match (fn_code f)!pc with
  | Some(Inop next)=>Some(next,rs,m)
  | Some(Iop op args dst next)=>
      match eval_operation ge sp op rs##args m with
      | Some v=>Some(next,rs#dst<-v,m)|None=>None end
  | Some(Iload chunk addr args dst next)=>
      match eval_addressing ge sp addr rs##args with
      | Some a=>match Mem.loadv chunk m a with Some v=>Some(next,rs#dst<-v,m)|None=>None end
      | None=>None end
  | Some(Istore chunk addr args src next)=>
      match eval_addressing ge sp addr rs##args with
      | Some a=>match Mem.storev chunk m a rs#src with Some m'=>Some(next,rs,m')|None=>None end
      | None=>None end
  | Some(Icond cond args yes no)=>
      match eval_condition cond rs##args m with Some b=>Some((if b then yes else no),rs,m)|None=>None end
  | Some(Ibuiltin ef (BA a::BA b::nil)(BR dst)next)=>
      if external_function_eq ef packed_builtin then Some(next,rs#dst<-(packed_eval rs#a rs#b),m) else None
  | _=>None end.
Fixpoint execute (ge: genv) (f: function) (sp: val) (fuel: nat) (pc: node) (rs: regset) (m: mem): option mem :=
  match fuel with
  | O=>None
  | S rest=>
    match (fn_code f)!pc with
    | Some(Ireturn None)=>Some m
    | _=>match transfer ge f sp pc rs m with
         | Some(next,rs',m')=>execute ge f sp rest next rs' m'|None=>None end end
  end.

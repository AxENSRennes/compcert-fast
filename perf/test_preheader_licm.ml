(* Native checks of preheader-aware invariant operation motion.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Op
let p=Camlcoq.P.of_int
let int n=Int.repr(Camlcoq.Z.of_sint n)
let long n=Int64.repr(Camlcoq.Z.of_sint n)
let passed=ref []
let cases=ref 0
let check name b=if not b then failwith name else passed:=name::!passed
let tree xs=List.fold_left(fun m(k,v)->PTree.set(p k)v m)PTree.empty xs
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let fixture prefix1 prefix2 op args : RTL.coq_function=
 {fn_sig={sig_args=[Xint;Xany64;Xany64];sig_res=Xany64;sig_cc=cc_default};
  fn_params=List.map p[1;2;3];fn_stacksize=Camlcoq.Z.of_sint 32;fn_entrypoint=p 1;
  fn_code=tree[1,RTL.Iop(fst prefix1,snd prefix1,p 7,p 2);
   2,RTL.Iop(fst prefix2,snd prefix2,p 8,p 3);
   3,RTL.Iop(Ointconst(int 7),[],p 5,p 4);
   4,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 5,p 8);
   5,RTL.Iop(op,args,p 5,p 6);
   6,RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 4);
   8,RTL.Ireturn(Some(p 5))]}
let execute f selected values=
 let ge=Globalenvs.Genv.globalenv(program f) in
 let sp=Values.Vptr(p 77,Ptrofs.zero) in
 let rec run fuel pc rs count=
  if fuel=0 then failwith "preheader LICM fixture fuel exhausted";
  match PTree.get pc f.RTL.fn_code with
  | Some(RTL.Inop s)->run(fuel-1)s rs count
  | Some(RTL.Iop(op,args,dst,s))->
   let count=if (op,args)=selected then count+1 else count in
   begin match Op.eval_operation ge sp op(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   | None->None,count
   | Some v->run(fuel-1)s(PMap.set dst v rs)count end
  | Some(RTL.Icond(c,args,yes,no))->
   begin match Op.eval_condition c(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
   | None->None,count
   | Some b->run(fuel-1)(if b then yes else no)rs count end
  | Some(RTL.Ireturn(Some r))->Some(PMap.get r rs),count
  | _->failwith "unsupported preheader LICM fixture instruction" in
 run 10000 f.RTL.fn_entrypoint(RTL.init_regs values f.RTL.fn_params)0
let edge_values=[Values.Vundef;Values.Vint(int 0);Values.Vint(int 1);Values.Vint(int(-1));
 Values.Vint(int 2147483647);Values.Vlong(long 0);Values.Vlong(long(-1));
 Values.Vfloat Floats.Float.zero;Values.Vfloat(Floats.Float.of_int(int 1));
 Values.Vfloat Floats.default_nan_64;Values.Vsingle Floats.Float32.zero;
 Values.Vsingle Floats.default_nan_32;Values.Vptr(p 9,Ptrofs.zero)]
(* Memory and calls below use actual extracted allocation, addressing,
   load/store, symbol lookup and operation semantics. The interpreter executes
   the helper's RTL body; no function or memory result is mocked. *)
let execute_memory prog f selected values initial_mem=
 let ge=Globalenvs.Genv.globalenv prog in
 let fuel=ref 10000 and evaluations=ref 0 and calls=ref 0 in
 let read regs args=List.map(fun r->PMap.get r regs)args in
 let rec invoke f values mem=
  let mem,block=Memory.Mem.alloc mem Z0 f.RTL.fn_stacksize in
  let result,mem=run f (Values.Vptr(block,Ptrofs.zero)) f.RTL.fn_entrypoint
   (RTL.init_regs values f.RTL.fn_params)mem in
  match result with
  | None->None,mem
  | Some v->begin match Memory.Mem.free mem block Z0 f.RTL.fn_stacksize with
    | None->None,mem|Some mem->Some v,mem end
 and run f sp pc regs mem=
  decr fuel;if !fuel<0 then failwith "memory/call LICM fixture fuel exhausted";
  match PTree.get pc f.RTL.fn_code with
  | Some(RTL.Inop next)->run f sp next regs mem
  | Some(RTL.Iop(op,args,dst,next))->
   if (op,args)=selected then incr evaluations;
   begin match Op.eval_operation ge sp op(read regs args)mem with
   | None->None,mem|Some v->run f sp next(PMap.set dst v regs)mem end
  | Some(RTL.Iload(chunk,address,args,dst,next))->
   begin match Op.eval_addressing ge sp address(read regs args)with
   | None->None,mem
   | Some loc->begin match Memory.Mem.loadv chunk mem loc with
    | None->None,mem|Some v->run f sp next(PMap.set dst v regs)mem end end
  | Some(RTL.Istore(chunk,address,args,src,next))->
   begin match Op.eval_addressing ge sp address(read regs args)with
   | None->None,mem
   | Some loc->begin match Memory.Mem.storev chunk mem loc(PMap.get src regs)with
    | None->None,mem|Some mem->run f sp next regs mem end end
  | Some(RTL.Icall(_,ros,args,dst,next))->
   let target=match ros with
    | Datatypes.Coq_inl r->Globalenvs.Genv.find_funct ge(PMap.get r regs)
    | Datatypes.Coq_inr id->begin match Globalenvs.Genv.find_symbol ge id with
      |None->None|Some block->Globalenvs.Genv.find_funct_ptr ge block end in
   begin match target with
   | Some(Internal callee)->incr calls;
     let result,mem=invoke callee(read regs args)mem in
     begin match result with None->None,mem|Some v->run f sp next(PMap.set dst v regs)mem end
   | _->failwith "unsupported external call in LICM fixture" end
  | Some(RTL.Icond(cond,args,yes,no))->
   begin match Op.eval_condition cond(read regs args)mem with
   | None->None,mem|Some b->run f sp(if b then yes else no)regs mem end
  | Some(RTL.Ireturn(Some r))->Some(PMap.get r regs),mem
  | _->failwith "unsupported memory/call fixture instruction" in
 let value,mem=invoke f values initial_mem in value,mem,!evaluations,!calls
let require label=function Some x->x|None->failwith label
let initial_mem prog=require "global memory initialization"(Globalenvs.Genv.init_mem prog)
let variants=["integer-chain",(Oaddimm(int 9),[p 2]),(Omul,[p 7;p 3]),Omul,[p 8;p 7];
 "integer-chain-add",(Oaddimm(int 9),[p 2]),(Omul,[p 7;p 3]),Oadd,[p 8;p 7];
 "long-chain",(Oaddlimm(long 9),[p 2]),(Omull,[p 7;p 3]),Omull,[p 8;p 7];
 "float-chain",(Oaddf,[p 2;p 3]),(Omulf,[p 7;p 2]),Osubf,[p 8;p 7];
 "stack-address-chain",(Oaddrstack Ptrofs.zero,[]),(Oaddlimm(long 8),[p 7]),Oaddlimm(long 8),[p 8]]
let ()=
 List.iter(fun(name,a,b,op,args)->
  let f=fixture a b op args in let tf=PreheaderLICM.transf_function f in
  let region=match PreheaderLICM.chosen f with Some r->r|None->failwith(name^": not selected") in
  check(name^": base immutable-only LICM cannot move this operation") (LICM.chosen f=None);
  check(name^": operands were computed by a retained expression chain")
   (region.PreheaderLICM.region_op=op && region.PreheaderLICM.region_args=args);
  check(name^": prefix exit is the original loop condition")
   (region.PreheaderLICM.region_prefix.PreheaderLICM.prefix_exit=p 4);
  check(name^": all prefix definitions are retained")
   (List.sort compare region.PreheaderLICM.region_prefix.PreheaderLICM.prefix_nodes=List.sort compare(List.map p[1;2;3]));
  check(name^": actual cold/warm CFG copies")
   (List.length(PTree.elements tf.RTL.fn_code)=2*List.length(PTree.elements f.RTL.fn_code));
  check(name^": cache is computed after the prefix")
   (PTree.get(PreheaderLICM.tag false(p 4))tf.RTL.fn_code=
    Some(RTL.Iop(op,args,LICM.fresh_reg f,PreheaderLICM.tag true(p 4))));
  check(name^": loop operation becomes a cache move")
   (PTree.get(PreheaderLICM.tag true(p 5))tf.RTL.fn_code=
    Some(RTL.Iop(Omove,[LICM.fresh_reg f],p 5,PreheaderLICM.tag true(p 6))));
  List.iteri(fun i x->List.iteri(fun j y->List.iter(fun n->
   incr cases;
   let values=[Values.Vint(int n);x;y] in
   let before,old_count=execute f(op,args)values in
   let after,new_count=execute tf(op,args)values in
   check(Printf.sprintf "%s values%d/%d trip%d" name i j n)(before=after);
   check(Printf.sprintf "%s counts%d/%d trip%d" name i j n)(old_count=max 0 n && new_count=1))
   [-1;0;1;2;7])edge_values)edge_values)variants;
 let f=fixture(Oaddimm(int 9),[p 2])(Omul,[p 7;p 3])Omul[p 8;p 7] in
 let writeback={f with RTL.fn_code=PTree.set(p 99)(RTL.Iop(Ointconst(int 0),[],p 7,p 8))f.RTL.fn_code} in
 check "a closed suffix safely excludes unreachable operand assignments"
  (PreheaderLICM.chosen writeback<>None);
 List.iter(fun n->let values=[Values.Vint(int n);Values.Vint(int 4);Values.Vint(int 3)] in
  check(Printf.sprintf "unreachable assignment suffix result/trip%d" n)
   (fst(execute writeback(Omul,[p 8;p 7])values)=
    fst(execute(PreheaderLICM.transf_function writeback)(Omul,[p 8;p 7])values)))[0;1;7];
 let reachable_write={f with RTL.fn_code=PTree.set(p 6)(RTL.Iop(Oaddimm(int 1),[p 7],p 7,p 4))f.RTL.fn_code} in
 check "reachable loop-variant operand assignments reject motion"
  (PreheaderLICM.chosen reachable_write=None && PreheaderLICM.transf_function reachable_write=reachable_write);
 let backedge={f with RTL.fn_code=PTree.set(p 6)(RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 2))f.RTL.fn_code} in
 let bad_prefix=PreheaderLICM.find_prefix (List.fold_left(fun n _->Datatypes.S n)Datatypes.O(List.init 16(fun x->x))) backedge backedge.RTL.fn_entrypoint [] in
 check "a backedge into the eager preheader rejects that cut"
  (not(PreheaderLICM.prefix_closed backedge bad_prefix));
 List.iter(fun n->let values=[Values.Vint(int n);Values.Vint(int 4);Values.Vint(int 3)] in
  check(Printf.sprintf "different validated suffix with preheader backedge/trip%d" n)
   (fst(execute backedge(Omul,[p 8;p 7])values)=
    fst(execute(PreheaderLICM.transf_function backedge)(Omul,[p 8;p 7])values)))[0;1;7];
 let prefix_cycle={f with RTL.fn_code=PTree.set(p 1)(RTL.Inop(p 1))f.RTL.fn_code} in
 let cycle_tf=PreheaderLICM.transf_function prefix_cycle in
 let cycle_entry=cycle_tf.RTL.fn_entrypoint in
 check "a cyclic entry prefix remains an unchanged cold self-loop"
  (PTree.get cycle_entry cycle_tf.RTL.fn_code=Some(RTL.Inop cycle_entry));
 List.iter(fun(name,op,args)->
  let bad=fixture(Oaddimm(int 9),[p 2])(Omul,[p 7;p 3])op args in
  check(name^": non-total or memory-sensitive selected operation rejected")
   (PreheaderLICM.chosen bad=None && PreheaderLICM.transf_function bad=bad))
 ["pointer-comparison",Ocmp(Ccomplu Ceq),[p 8;p 7];"wrong-arity",Omul,[p 8]];
 let partial_prefix=fixture(Odiv,[p 2;p 3])(Omul,[p 7;p 3])Omul[p 8;p 7] in
 check "a partial prefix operation is retained before cache initialization"
  (PreheaderLICM.chosen partial_prefix<>None);
 let tf=PreheaderLICM.transf_function partial_prefix in
 List.iter(fun count->
  let values=[Values.Vint(int count);Values.Vint(int 7);Values.Vint(int 0)] in
  check(Printf.sprintf "prefix division fault remains before cache for trip%d" count)
   (execute partial_prefix(Omul,[p 8;p 7])values=(None,0) &&
    execute tf(Omul,[p 8;p 7])values=(None,0)))[0;1;7];
 let oversized={f with RTL.fn_code=List.fold_left(fun m n->PTree.set(p(n+100))(RTL.Inop(p 8))m)f.RTL.fn_code(List.init 600(fun x->x))} in
 check "large functions are retained exactly"(PreheaderLICM.chosen oversized=None && PreheaderLICM.transf_function oversized=oversized);
 check "whole-program wrapper transforms actual code"
  (match List.assoc(p 1)(PreheaderLICM.transf_program(program f)).prog_defs with
   Gfun(Internal actual)->actual=PreheaderLICM.transf_function f|_->false);
 (* A branching preheader defines one invariant along either path.
    The validated suffix fallback caches it at its first actual use. *)
 let branch_fixture op args : RTL.coq_function=
  {fn_sig={sig_args=[Xint;Xany64;Xany64;Xint];sig_res=Xany64;sig_cc=cc_default};
   fn_params=List.map p[1;2;3;4];fn_stacksize=Z0;fn_entrypoint=p 1;
   fn_code=tree[
    1,RTL.Icond(Ccompimm(Cge,int 0),[p 4],p 2,p 3);
    2,RTL.Iop(Oaddimm(int 9),[p 2],p 7,p 4);
    3,RTL.Iop(Oaddimm(int 17),[p 2],p 7,p 4);
    4,RTL.Iop(Ointconst(int 7),[],p 5,p 5);
    5,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 6,p 8);
    6,RTL.Iop(op,args,p 5,p 7);
    7,RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 5);
    8,RTL.Ireturn(Some(p 5))]} in
 let branching=branch_fixture Omul[p 7;p 3] in
 let bregion=match PreheaderLICM.chosen branching with Some b->b|None->failwith "branching prefix was not selected" in
 check "branching preheaders use a cache at the first actual operation"
  (bregion.PreheaderLICM.region_prefix.PreheaderLICM.prefix_exit=p 6);
 check "a validated suffix includes both incoming operand definitions"
  (List.for_all(fun pc->List.mem(p pc)bregion.PreheaderLICM.region_prefix.PreheaderLICM.prefix_nodes)[1;2;3;4]);
 List.iter(fun selector->List.iter(fun x->List.iter(fun n->incr cases;
  let values=[Values.Vint(int n);Values.Vint(int x);Values.Vint(int 3);Values.Vint(int selector)] in
  let before,bc=execute branching(Omul,[p 7;p 3])values in
  let after,ac=execute(PreheaderLICM.transf_function branching)(Omul,[p 7;p 3])values in
  check(Printf.sprintf "branching preheader selector%d x%d trip%d" selector x n)
   (before=after && bc=max 0 n && ac=(if n>0 then 1 else 0))) [-1;0;1;3;9])[-17;-9;0;4;2147483647])[-1;0;5];
 List.iter(fun(name,a,b,op,args,inputs)->
  let lazy_f=fixture a b op args in
  let lazy_region=match PreheaderLICM.chosen lazy_f with Some b->b|None->failwith(name^": lazy operation rejected") in
  check(name^": partial operation is anchored at its original first use")
   (lazy_region.PreheaderLICM.region_prefix.PreheaderLICM.prefix_exit=p 5);
  List.iteri(fun i(x,y)->List.iter(fun n->incr cases;
   let values=[Values.Vint(int n);x;y] in
   let before,bc=execute lazy_f(op,args)values in
   let after,ac=execute(PreheaderLICM.transf_function lazy_f)(op,args)values in
   check(Printf.sprintf "%s input%d trip%d" name i n)
    (before=after && bc=(if before=None && n>0 then 1 else max 0 n) &&
     ac=(if n>0 then 1 else 0))) [-1;0;1;2;7])inputs)
 ["lazy-integer-division",(Oaddimm(int 9),[p 2]),(Omul,[p 7;p 3]),Odiv,[p 8;p 7],
   [Values.Vint(int(-9)),Values.Vint(int 0);Values.Vint(int(-10)),Values.Vint(int(-2147483648));
    Values.Vint(int 0),Values.Vint(int 7);Values.Vundef,Values.Vint(int 1)];
  "lazy-float-conversion",(Oaddf,[p 2;p 3]),(Oabsf,[p 7]),Ointoffloat,[p 8],
   [Values.Vfloat Floats.default_nan_64,Values.Vfloat Floats.Float.zero;
    Values.Vfloat(Floats.Float.of_int(int 1)),Values.Vfloat Floats.Float.zero;
    Values.Vundef,Values.Vfloat Floats.Float.zero]];
 (* A load before a loop defines an invariant arithmetic operand. It
    remains at its original position, including its possible failure. *)
 let memory_fixture={f with RTL.fn_sig={f.RTL.fn_sig with sig_args=[Xint;Xptr;Xint]};
  fn_code=tree[
   1,RTL.Iload(Mint32,Aindexed Int64.zero,[p 2],p 7,p 2);
   2,RTL.Iop(Oaddimm(int 9),[p 7],p 8,p 3);
   3,RTL.Iop(Ointconst(int 7),[],p 5,p 4);
   4,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 5,p 8);
   5,RTL.Iop(Omul,[p 8;p 7],p 5,p 6);
   6,RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 4);8,RTL.Ireturn(Some(p 5))]} in
 check "a retained prefix load permits arithmetic on its loaded value"
  (PreheaderLICM.chosen memory_fixture<>None);
 let mem,block=Memory.Mem.alloc(initial_mem(program memory_fixture))Z0(Camlcoq.Z.of_sint 16) in
 let pointer=Values.Vptr(block,Ptrofs.zero) in
 List.iter(fun value->
  let value=Values.Vint(int value) in
  let mem=require "initial heap store"(Memory.Mem.storev Mint32 mem pointer value) in
  List.iter(fun n->incr cases;
   let values=[Values.Vint(int n);pointer;Values.Vint(int 0)] in
   let before,bmem,bc,callb=execute_memory(program memory_fixture)memory_fixture(Omul,[p 8;p 7])values mem in
   let tf=PreheaderLICM.transf_function memory_fixture in
   let after,amem,ac,calla=execute_memory(program tf)tf(Omul,[p 8;p 7])values mem in
   check(Printf.sprintf "retained load value/trip%d" n)(before=after && bc=max 0 n && ac=1 && callb=calla);
   check(Printf.sprintf "retained load leaves heap/trip%d" n)
    (Memory.Mem.loadv Mint32 bmem pointer=Some value && Memory.Mem.loadv Mint32 amem pointer=Some value))
   [0;1;2;9]) [0;1;-1;7;2147483647];
 let freed=require "free heap block"(Memory.Mem.free mem block Z0(Camlcoq.Z.of_sint 16)) in
 List.iter(fun n->
  let values=[Values.Vint(int n);pointer;Values.Vint(int 0)] in
  let before,_,bc,_=execute_memory(program memory_fixture)memory_fixture(Omul,[p 8;p 7])values freed in
  let tf=PreheaderLICM.transf_function memory_fixture in
  let after,_,ac,_=execute_memory(program tf)tf(Omul,[p 8;p 7])values freed in
  check(Printf.sprintf "prefix load fault stays before cache/trip%d" n)(before=None && after=None && bc=0 && ac=0)) [0;1;9];
 let volatile_prefix={memory_fixture with RTL.fn_code=PTree.set(p 1)
  (RTL.Ibuiltin(EF_vload Mint32,[BA(p 2)],BR(p 7),p 2))memory_fixture.RTL.fn_code} in
 check "a volatile builtin in the retained prefix permits pure motion after it"
  (PreheaderLICM.chosen volatile_prefix<>None);
 let volatile_tf=PreheaderLICM.transf_function volatile_prefix in
 check "the volatile builtin remains before the cold cache initialization"
  (PTree.get(PreheaderLICM.tag false(p 1))volatile_tf.RTL.fn_code=
   Some(RTL.Ibuiltin(EF_vload Mint32,[BA(p 2)],BR(p 7),PreheaderLICM.tag false(p 2))));
 let stored={memory_fixture with RTL.fn_code=tree[
   1,RTL.Istore(Mint32,Aindexed Int64.zero,[p 2],p 3,p 2);
   2,RTL.Iload(Mint32,Aindexed Int64.zero,[p 2],p 7,p 3);
   3,RTL.Iop(Oaddimm(int 9),[p 7],p 8,p 9);
   9,RTL.Iop(Ointconst(int 7),[],p 5,p 4);
   4,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 5,p 8);
   5,RTL.Iop(Omul,[p 8;p 7],p 5,p 6);
   6,RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 4);8,RTL.Ireturn(Some(p 5))]} in
 check "a prefix store and load stay before pure motion"(PreheaderLICM.chosen stored<>None);
 List.iter(fun n->
  let values=[Values.Vint(int n);pointer;Values.Vint(int 42)] in
  let before,bmem,bc,_=execute_memory(program stored)stored(Omul,[p 8;p 7])values mem in
  let tf=PreheaderLICM.transf_function stored in
  let after,amem,ac,_=execute_memory(program tf)tf(Omul,[p 8;p 7])values mem in
  check(Printf.sprintf "prefix store effect and value/trip%d" n)
   (before=after && bc=max 0 n && ac=1 &&
    Memory.Mem.loadv Mint32 bmem pointer=Some(Values.Vint(int 42)) &&
    Memory.Mem.loadv Mint32 amem pointer=Some(Values.Vint(int 42)))) [0;1;9];
 let helper : RTL.coq_function={fn_sig={sig_args=[Xint];sig_res=Xint;sig_cc=cc_default};
  fn_params=[p 1];fn_stacksize=Z0;fn_entrypoint=p 1;
  fn_code=tree[1,RTL.Iop(Oaddimm(int 13),[p 1],p 4,p 2);2,RTL.Ireturn(Some(p 4))]} in
 let called={f with RTL.fn_code=PTree.set(p 1)
  (RTL.Icall(helper.fn_sig,Datatypes.Coq_inr(p 2),[p 2],p 7,p 2))f.RTL.fn_code} in
 let call_program f={prog_defs=[p 1,Gfun(Internal f);p 2,Gfun(Internal helper)];prog_public=[p 1];prog_main=p 1} in
 check "a retained prefix call defines a usable invariant operand" (PreheaderLICM.chosen called<>None);
 List.iter(fun x->List.iter(fun n->incr cases;
  let values=[Values.Vint(int n);Values.Vint(int x);Values.Vint(int 3)] in
  let before,_,bc,bcall=execute_memory(call_program called)called(Omul,[p 8;p 7])values(initial_mem(call_program called)) in
  let tf=PreheaderLICM.transf_function called in
  let after,_,ac,acall=execute_memory(call_program tf)tf(Omul,[p 8;p 7])values(initial_mem(call_program tf)) in
  check(Printf.sprintf "prefix RTL call/trip%d input%d" n x)
   (before=after && bc=max 0 n && ac=1 && bcall=1 && acall=1)) [0;1;9]) [-1;0;1;42];
 Printf.printf "{\"success\":true,\"execution_cases\":%d,\"checks\":[%s]}\n" !cases
 (String.concat ","(List.map(Printf.sprintf "%S")(List.rev !passed)))

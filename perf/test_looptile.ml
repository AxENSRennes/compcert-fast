(* Counted tile tests against the actual extracted transformation/evaluators.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Op
let p=Camlcoq.P.of_int
let int n=Int.repr(Camlcoq.Z.of_sint n)
let passed=ref [] and executions=ref 0
let check n b=if not b then failwith n else passed:=n::!passed
let tree xs=List.fold_left(fun t(k,v)->PTree.set(p k)v t)PTree.empty xs
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let counter=p 1 and bound=p 2 and sum=p 3
let loop():RTL.coq_function={
 fn_sig={sig_args=[Xint;Xint;Xint];sig_res=Xint;sig_cc=cc_default};fn_params=[counter;bound;sum];
 fn_stacksize=Z0;fn_entrypoint=p 5;
 fn_code=tree[5,RTL.Icond(Ccompimm(Cgt,int 0),[bound],p 4,p 1);
              4,RTL.Iop(Oadd,[sum;counter],sum,p 2);
              2,RTL.Iop(Oaddimm(int(-1)),[bound],bound,p 3);
              3,RTL.Iop(Oaddimm(int 7),[counter],counter,p 5);
              1,RTL.Ireturn(Some sum)]}
let execute source f inputs=
 let ge=Globalenvs.Genv.globalenv(program f) in
 let rec walk fuel pc rs resets backedges =
  if fuel=0 then failwith "tile fixture exhausted fuel";
  let resets=resets+(if pc=LoopTile.reset_pc source then 1 else 0) in
  let backedges=backedges+(if pc=p 3 then 1 else 0) in
  match PTree.get pc f.RTL.fn_code with
  |Some(RTL.Inop next)->walk(fuel-1)next rs resets backedges
  |Some(RTL.Iop(op,args,dst,next))->begin
    match Op.eval_operation ge Values.Vundef op(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
    |Some v->walk(fuel-1)next(PMap.set dst v rs)resets backedges
    |None->None,rs,resets,backedges end
  |Some(RTL.Icond(cond,args,yes,no))->begin
    match Op.eval_condition cond(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
    |Some b->walk(fuel-1)(if b then yes else no)rs resets backedges
    |None->None,rs,resets,backedges end
  |Some(RTL.Ireturn(Some r))->Some(PMap.get r rs),rs,resets,backedges
  |_ -> failwith "unsupported tile fixture instruction"
 in walk 20000 f.RTL.fn_entrypoint(RTL.init_regs inputs f.RTL.fn_params)0 0
let differential f inputs=
 let tf=LoopTile.transf_function f in
 let old,rs,_,steps=execute f f inputs in
 let current,trs,resets,newsteps=execute f tf inputs in
 incr executions;
 if old<>current then failwith "tile output mismatch";
 List.iter(fun r->if PMap.get r rs<>PMap.get r trs then failwith "original register changed")
  [counter;bound;sum];
 if steps<>newsteps then failwith "iteration order changed";
 old,resets,steps
let ()=
 let f=loop() in
 let plan=match LoopTile.chosen f with Some t->t|None->failwith "no counted backedge" in
 check "loop backedge selected"(plan.LoopTile.tile_pc=p 3&&plan.LoopTile.tile_header=p 5);
 let tf=LoopTile.transf_function f in
 check "actual transformation changes code"(tf<>f);
 check "original exit condition retained at its location"(PTree.get(p 5)f.RTL.fn_code=PTree.get(p 5)tf.RTL.fn_code);
 check "actual countdown branch selects outer reset or inner continuation"
  (PTree.get(LoopTile.test_pc f)tf.RTL.fn_code=Some(RTL.Icond(Ccompimm(Ceq,Int.one),[LoopTile.fresh_reg f],LoopTile.reset_pc f,LoopTile.advance_pc f)));
 check "only four maintenance nodes are added"
  (List.length(PTree.elements tf.RTL.fn_code)=4+List.length(PTree.elements f.RTL.fn_code));
 let seeds=[0;1;(-1);2147483647;(-2147483648);4294967295] in
 List.iter(fun start->List.iter(fun seed->List.iter(fun n->
  let _,resets,steps=differential f[Values.Vint(int start);Values.Vint(int n);Values.Vint(int seed)] in
  if steps<>max 0 n||resets<>(max 0 n)/4 then failwith "tile boundary/count-tail mismatch")
  [-2;0;1;2;3;4;5;7;8;9;15;16;17;31;32;33])seeds)seeds;
 check "tile boundaries, wrapping inputs and every scalar tail preserved"(!executions=576);
 let tags=[Values.Vundef;Values.Vptr(p 42,Ptrofs.zero);Values.Vlong(Int64.repr(Camlcoq.Z.of_sint 99));Values.Vint(int 7)] in
 List.iter(fun start->List.iter(fun seed->List.iter(fun n->
  ignore(differential f[start;Values.Vint(int n);seed]))[0;1;4;9])tags)tags;
 check "undefined and noninteger data preserve exact results/registers"true;
 List.iter(fun n->ignore(differential f[Values.Vint(int 7);n;Values.Vundef]))tags;
 check "undefined/noninteger loop condition preserves faults"true;
 let no_loop={f with RTL.fn_entrypoint=p 1;fn_code=tree[1,RTL.Ireturn(Some sum)]} in
 check "acyclic function retained exactly"(LoopTile.transf_function no_loop=no_loop);
 let large={f with RTL.fn_code=tree(List.init 600(fun i->i+1,RTL.Inop(p 1)))} in
 check "size budget retains large function exactly"(LoopTile.transf_function large=large);
 let malformed={f with RTL.fn_code=PTree.set(p 3)(RTL.Iop(Oaddimm(int 1),[],counter,p 5))f.RTL.fn_code} in
 check "wrong-arity recurrence ignored"(LoopTile.chosen malformed=None);
 let zero_trip,_resets,_=differential f[Values.Vundef;Values.Vint(int 0);Values.Vint(int 123)] in
 check "zero-trip retains original accumulator"(zero_trip=Some(Values.Vint(int 123)));
 Printf.printf "{\"success\":true,\"execution_cases\":%d,\"checks\":[%s]}\n"!executions
  (String.concat ","(List.map(Printf.sprintf "%S")(List.rev !passed)))

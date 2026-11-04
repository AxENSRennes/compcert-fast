(* Production pure-loop interchange validation and actual order tests.
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
let accepted f=LoopFusion.validate_function f(LoopInterchange.candidate f)
let transform f=LoopFusion.transf_function_with LoopInterchange.candidate f
let x=p 1 and y=p 2 and a=p 3 and b=p 4 and i=p 5 and j=p 6 and out=p 7
let rectangle post inner_bound:RTL.coq_function={
 fn_sig={sig_args=[Xint;Xint;Xint;Xint];sig_res=Xint;sig_cc=cc_default};
 fn_params=[x;y;a;b];fn_stacksize=Z0;fn_entrypoint=p 100;
 fn_code=tree[
  100,RTL.Iop(Ointconst Int.zero,[],i,p(if post then 80 else 90));
  90,RTL.Icond(Ccompuimm(Clt,int 2),[i],p 80,p 1);
  80,RTL.Iop(Ointconst Int.zero,[],j,p(if post then 60 else 70));
  70,RTL.Icond(Ccompuimm(Clt,int inner_bound),[j],p 60,p 20);
  60,RTL.Icond(Ccompimm(Ceq,Int.zero),[i],p 50,p 40);
  50,RTL.Iop(Omul,[a;x],a,p 45);45,RTL.Iop(Oadd,[a;j],a,p 30);
  40,RTL.Iop(Omul,[b;y],b,p 35);35,RTL.Iop(Oadd,[b;j],b,p 30);
  30,RTL.Iop(Oaddimm Int.one,[j],j,p 70);
  20,RTL.Iop(Oaddimm Int.one,[i],i,p 90);
  1,RTL.Iop(Oxor,[a;b],out,p 2);2,RTL.Ireturn(Some out)]}
let execute f values=
 let ge=Globalenvs.Genv.globalenv(program f) in
 let rec walk fuel pc rs order=
  if fuel=0 then failwith "interchange fixture fuel";
  let order=if pc=p 60 then (PMap.get i rs,PMap.get j rs)::order else order in
  match PTree.get pc f.RTL.fn_code with
  |Some(RTL.Inop next)->walk(fuel-1)next rs order
  |Some(RTL.Iop(op,args,dst,next))->begin
    match Op.eval_operation ge Values.Vundef op(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
    |Some v->walk(fuel-1)next(PMap.set dst v rs)order|None->None,List.rev order end
  |Some(RTL.Icond(cond,args,yes,no))->begin
    match Op.eval_condition cond(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
    |Some take->walk(fuel-1)(if take then yes else no)rs order|None->None,List.rev order end
  |Some(RTL.Ireturn(Some r))->Some(PMap.get r rs),List.rev order
  |_->failwith "unsupported interchange fixture instruction"
 in walk 10000 f.RTL.fn_entrypoint(RTL.init_regs values f.RTL.fn_params)[]
let ()=
 List.iter(fun post->
  let name=if post then "post-tested" else "pre-tested" in
  let f=rectangle post 3 in
  let plan=match LoopInterchange.choose f(PTree.elements f.RTL.fn_code) with
    Some plan->plan|None->failwith(name^": no rectangle proposed") in
  check(name^": correct loop form recognized")(plan.LoopInterchange.post_tested=post);
  check(name^": pure symbolic validator accepts actual interchange")(accepted f);
  let tf=transform f in
  check(name^": actual code is changed")(tf<>f);
  let values=List.map(fun n->Values.Vint(int n))[7;11;3;5] in
  let old,oldorder=execute f values and current,neworder=execute tf values in
  let pair u v=Values.Vint(int u),Values.Vint(int v) in
  check(name^": source iteration order is i-major")
   (oldorder=List.map(fun(u,v)->pair u v)[0,0;0,1;0,2;1,0;1,1;1,2]);
  check(name^": target iteration order is j-major")
   (neworder=List.map(fun(u,v)->pair u v)[0,0;1,0;0,1;1,1;0,2;1,2]);
  check(name^": exact observable return preserved")(old=current);
  let tags=[Values.Vundef;Values.Vint Int.zero;Values.Vint Int.one;Values.Vint(int(-1));
            Values.Vint(int 2147483647);Values.Vptr(p 42,Ptrofs.zero);Values.Vlong(Int64.repr(Camlcoq.Z.of_sint 99))] in
  List.iter(fun vx->List.iter(fun vy->List.iter(fun va->List.iter(fun vb->
    let inputs=[vx;vy;va;vb] in
    let old,_=execute f inputs and current,_=execute tf inputs in
    incr executions;if old<>current then failwith "interchange all-tag result mismatch")tags)tags)tags)tags;
  let dependent={f with RTL.fn_code=PTree.set(p 40)(RTL.Iop(Omul,[a;y],a,p 35))
      (PTree.set(p 35)(RTL.Iop(Oadd,[a;j],a,p 30))f.RTL.fn_code)} in
  check(name^": dependent schedule proposal is actually different")
   (LoopInterchange.candidate dependent<>dependent);
  check(name^": real cross-stream dependency rejected")(not(accepted dependent));
  check(name^": rejection retains original function exactly")(transform dependent=dependent);
  let source,_=execute dependent values and unsafe,_=execute(LoopInterchange.candidate dependent)values in
  check(name^": negative control has different real outputs")(source<>unsafe)) [false;true];
 let zero=rectangle false 0 in
 check "zero-trip inner loop retains exact return"(accepted zero &&
  fst(execute zero[Values.Vundef;Values.Vundef;Values.Vint(int 7);Values.Vint(int 9)])=
  fst(execute(transform zero)[Values.Vundef;Values.Vundef;Values.Vint(int 7);Values.Vint(int 9)]));
 let observable_counter={zero with RTL.fn_code=PTree.set(p 1)(RTL.Ireturn(Some i))zero.RTL.fn_code} in
 check "observable zero-trip counter difference is rejected"(not(accepted observable_counter));
 let memory={(rectangle false 3) with RTL.fn_code=PTree.set(p 50)
    (RTL.Iload(Mint32,Aindexed Int64.zero,[x],a,p 45))(rectangle false 3).RTL.fn_code} in
 check "memory effects cannot pass the pure reordering validator"(not(accepted memory));
 let mutation={(rectangle false 3) with RTL.fn_code=PTree.set(p 60)
    (RTL.Icond(Ccompimm(Ceq,Int.zero),[x],p 50,p 40))(rectangle false 3).RTL.fn_code} in
 check "input-dependent control is rejected"(not(accepted mutation));
 let partial={(rectangle false 3) with RTL.fn_code=PTree.set(p 50)
    (RTL.Iop(Odivu,[a;x],a,p 45))(rectangle false 3).RTL.fn_code} in
 check "partial operations are not silently reordered"(not(accepted partial));
 Printf.printf "{\"success\":true,\"execution_cases\":%d,\"checks\":[%s]}\n"!executions
  (String.concat ","(List.map(Printf.sprintf "%S")(List.rev !passed)))

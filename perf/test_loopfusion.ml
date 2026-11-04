(* Native checks of production symbolic validation and bounded loop fusion.
   Distributed under the INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Op
let p=Camlcoq.P.of_int
let int n=Int.repr(Camlcoq.Z.of_sint n)
let passed=ref []
let checks=ref 0
let check name condition=if not condition then failwith name; incr checks; passed:=name::!passed
let tree xs=List.fold_left(fun t(k,v)->PTree.set(p k)v t)PTree.empty xs
let sig2={sig_args=[Xint;Xint];sig_res=Xint;sig_cc=cc_default}
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let fixture ?(shared=false) ?(dependent=false) n : RTL.coq_function =
 let j=if shared then p 5 else p 6 in
 {fn_sig=sig2;fn_params=[p 1;p 2];fn_stacksize=Z0;fn_entrypoint=p 20;
  fn_code=tree[
  20,RTL.Iop(Ointconst(int 0),[],p 3,p 19);
  19,RTL.Iop(Ointconst(int 0),[],p 5,p 18);
  18,RTL.Icond(Ccompuimm(Clt,int n),[p 5],p 17,p 14);
  17,RTL.Iop(Oadd,[p 3;p 1],p 3,p 16);
  16,RTL.Iop(Oaddimm(int 1),[p 5],p 5,p 18);
  14,RTL.Iop(Ointconst(int 0),[],p 4,p 13);
  13,RTL.Iop(Ointconst(int 0),[],j,p 12);
  12,RTL.Icond(Ccompuimm(Clt,int n),[j],p 11,p 8);
  11,RTL.Iop(Oadd,[p 4;(if dependent then p 3 else p 2)],p 4,p 10);
  10,RTL.Iop(Oaddimm(int 1),[j],j,p 12);
  8,RTL.Iop(Oxor,[p 3;p 4],p 7,p 7);
  7,RTL.Ireturn(Some(p 7))]}
let execute f a b =
 let ge=Globalenvs.Genv.globalenv(program f)in
 let rec step fuel pc rs conditions operations =
  if fuel=0 then failwith "loop fusion execution fuel";
  match PTree.get pc f.RTL.fn_code with
  | Some(RTL.Inop next)->step(fuel-1)next rs conditions operations
  | Some(RTL.Iop(op,args,dst,next))->
    begin match Op.eval_operation ge Values.Vundef op (List.map(fun r->PMap.get r rs)args) Memory.Mem.empty with
    | Some v->step(fuel-1)next(PMap.set dst v rs)conditions(operations+1)
    | None->None end
  | Some(RTL.Icond(cond,args,yes,no))->
    begin match Op.eval_condition cond(List.map(fun r->PMap.get r rs)args)Memory.Mem.empty with
    | Some take->step(fuel-1)(if take then yes else no)rs(conditions+1)operations
    | None->None end
  | Some(RTL.Ireturn r)->Some((match r with Some r->PMap.get r rs|None->Values.Vundef),conditions,operations)
  | _->None
 in step 1024 f.RTL.fn_entrypoint(RTL.init_regs[a;b]f.RTL.fn_params)0 0
let values=[Values.Vundef;Values.Vint(int 0);Values.Vint(int 1);Values.Vint(int(-1));
 Values.Vint(int 0x7fffffff);Values.Vint(int(-2147483648));
 Values.Vlong(Int64.repr(Camlcoq.Z.of_sint 7));
 Values.Vptr(p 7,Ptrofs.zero);Values.Vptr(p 9,Ptrofs.repr(Camlcoq.Z.of_sint 4));
 Values.Vfloat Floats.Float.zero;Values.Vsingle Floats.Float32.zero]
let executions=ref 0
let transform=LoopFusion.transf_function_with LoopFusion.candidate
let () =
 List.iter(fun shared->List.iter(fun n->
  let f=fixture ~shared n in let tf=transform f in
  check(Printf.sprintf "bound%d/shared%b candidate changes CFG" n shared)(tf<>f);
  check "production validator accepts actual fusion" (LoopFusion.validate_function f tf);
  check "fusion preserves original function metadata" (tf.RTL.fn_sig=f.RTL.fn_sig && tf.RTL.fn_params=f.RTL.fn_params && tf.RTL.fn_stacksize=f.RTL.fn_stacksize);
  List.iter(fun a->List.iter(fun b->
   match execute f a b,execute tf a b with
   | Some(v,c,_),Some(v',c',_)->
       if v<>v' then failwith "fusion changed arbitrary-value-tag result";
       if c'<>(n+1) || c<>2*(n+1) then failwith "fusion did not reduce two loop tests to one";
       incr executions
   | _->failwith "total pure fusion fixture did not complete")values)values)
 [0;1;2;3;4;8;16]) [false;true];
 let dependent=fixture ~dependent:true 2 in
 check "dependency rejects fusion" (transform dependent=dependent);
 let f=fixture 2 in let tf=LoopFusion.candidate f in
 check "wrong signature is rejected" (not(LoopFusion.validate_function f {tf with RTL.fn_sig={sig2 with sig_args=[]}}));
 check "wrong parameters are rejected" (not(LoopFusion.validate_function f {tf with RTL.fn_params=[]}));
 check "wrong stack size is rejected" (not(LoopFusion.validate_function f {tf with RTL.fn_stacksize=Camlcoq.Z.of_sint 8}));
 let corrupt={tf with RTL.fn_code=PTree.set(p 7)(RTL.Ireturn(Some(p 1)))tf.RTL.fn_code}in
 check "return-expression corruption is rejected" (not(LoopFusion.validate_function f corrupt));
 let partial={tf with RTL.fn_entrypoint=p 100;
  fn_code=PTree.set(p 100)(RTL.Iop(Odivu,[p 1;p 2],p 99,tf.RTL.fn_entrypoint))tf.RTL.fn_code}in
 check "new reachable dead partial operation is rejected" (not(LoopFusion.validate_function f partial));
 let memory={f with RTL.fn_code=PTree.set(p 17)(RTL.Iload(Mint32,Aindexed Int64.zero,[p 1],p 3,p 16))f.RTL.fn_code}in
 check "memory-effect loop is retained" (transform memory=memory);
 let dynamic={f with RTL.fn_code=PTree.set(p 18)(RTL.Icond(Ccompu Clt,[p 5;p 2],p 17,p 14))f.RTL.fn_code}in
 check "dynamic trip condition is conservatively retained" (transform dynamic=dynamic);
 let excessive=fixture 64 in
 check "symbolic execution fuel limit retains function" (transform excessive=excessive);
 let oversized={f with RTL.fn_code=List.fold_left(fun c i->PTree.set(p(100+i))(RTL.Inop(p 7))c)f.RTL.fn_code(List.init 100(fun i->i))}in
 check "size budget retains large function exactly" (transform oversized=oversized);
 check "source symbolic return is nonconstant" (match LoopFusion.run_function f with Some(LoopFusion.Intval _)|None->false|_->true);
 check "symbolic output same after actual fusion" (LoopFusion.run_function f=LoopFusion.run_function tf);
 let stackop=Oaddrstack Ptrofs.zero in
 let symbolop=Oaddrsymbol(p 1,Ptrofs.zero)in
 check "stack address is not constant-folded in empty context" (LoopFusion.make_expr stackop []=Some(LoopFusion.Op0 stackop));
 check "symbol address is not constant-folded in empty environment" (LoopFusion.make_expr symbolop []=Some(LoopFusion.Op0 symbolop));
 let contextual op={f with RTL.fn_entrypoint=p 100;
   fn_code=tree[100,RTL.Iop(op,[],p 3,p 101);101,RTL.Ireturn(Some(p 3))]}in
 List.iter(fun op->let original=contextual op in
   let erased={original with RTL.fn_code=PTree.set(p 101)(RTL.Ireturn None)original.RTL.fn_code}in
   check "contextual address cannot be erased as undefined" (not(LoopFusion.validate_function original erased))) [stackop;symbolop];
 Printf.printf "{\"success\":true,\"checks\":[%s],\"check_count\":%d,\"differential_cases\":%d}\n"
  (String.concat ","(List.map(Printf.sprintf "%S")(List.rev !passed)))!checks !executions

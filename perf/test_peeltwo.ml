(* Tests of the production extracted two-traversal CFG covering.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Maps
open Integers
open Op
let p=Camlcoq.P.of_int
let int n=Int.repr(Camlcoq.Z.of_sint n)
let z=Camlcoq.Z.of_sint
let passed=ref [] and cases=ref 0
let check name b=if not b then failwith name else passed:=name::!passed
let tree xs=List.fold_left(fun t(k,v)->PTree.set(p k)v t)PTree.empty xs
let sig3={sig_args=[Xint;Xint;Xint];sig_res=Xint;sig_cc=cc_default}
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let nodes f=List.length(PTree.elements f.RTL.fn_code)
let phases=[PeelTwo.First;PeelTwo.Second;PeelTwo.Stable]
type event=Load of Values.coq_val|Store of Values.coq_val|Fault
let memory_snapshot memory block=
 let permissions=List.concat_map(fun offset->List.concat_map(fun kind->
  List.map(fun permission->Memory.Mem.perm_dec memory block(z offset)kind permission)
   [Memtype.Nonempty;Memtype.Readable;Memtype.Writable;Memtype.Freeable])
  [Memtype.Cur;Memtype.Max])(List.init 18(fun i->i-1)) in
 Memory.Mem.mem_contents memory,Memory.Mem.nextblock memory,permissions
let loop():RTL.coq_function={
 fn_sig=sig3;fn_params=List.map p[1;2;3];fn_stacksize=Z0;fn_entrypoint=p 9;
 fn_code=tree[
  9,RTL.Icond(Ccompimm(Cgt,int 0),[p 1],p 8,p 1);
  8,RTL.Istore(Mint32,Aindexed(Ptrofs.zero),[p 4],p 2,p 7);
  7,RTL.Iload(Mint32,Aindexed(Ptrofs.zero),[p 4],p 5,p 6);
  6,RTL.Iop(Oadd,[p 3;p 5],p 3,p 5);
  5,RTL.Iop(Oaddimm(int 7),[p 2],p 2,p 4);
  4,RTL.Iop(Oaddimm(int(-1)),[p 1],p 1,p 9);
  1,RTL.Ireturn(Some(p 3))]}
(* Real extracted evaluators and memory operations. Preserve a sequence of memory
   observations, including failure, instead of checking only the final return. *)
let execute source f args valid_address=
 let ge=Globalenvs.Genv.globalenv(program f) in
 let memory,block=Memory.Mem.alloc Memory.Mem.empty Z0(z 16) in
 let address=if valid_address then Values.Vptr(block,Ptrofs.zero) else Values.Vundef in
 let rs=PMap.set(p 4)address(RTL.init_regs args f.RTL.fn_params) in
 let phase_node mode pc=pc=PeelTwo.tag mode(p 8) in
 let rec walk fuel pc rs memory trace visits=
  if fuel=0 then failwith "peeltwo execution fuel";
  let visits=List.map2(fun count mode->count+(if phase_node mode pc then 1 else 0))visits phases in
  let next n rs m trace=walk(fuel-1)n rs m trace visits in
  let values regs=List.map(fun r->PMap.get r rs)regs in
  let fault= None,memory_snapshot memory block,List.rev(Fault::trace),visits in
  match PTree.get pc f.RTL.fn_code with
  |Some(RTL.Inop n)->next n rs memory trace
  |Some(RTL.Iop(op,args,dst,n))->begin match Op.eval_operation ge Values.Vundef op(values args)memory with
    |Some value->next n(PMap.set dst value rs)memory trace|None->fault end
  |Some(RTL.Icond(cond,args,yes,no))->begin match Op.eval_condition cond(values args)memory with
    |Some take->next(if take then yes else no)rs memory trace|None->fault end
  |Some(RTL.Iload(chunk,addr,args,dst,n))->begin
    match Op.eval_addressing ge Values.Vundef addr(values args) with
    |Some address->begin match Memory.Mem.loadv chunk memory address with
      |Some value->next n(PMap.set dst value rs)memory(Load value::trace)
      |None->fault end
    |None->fault end
  |Some(RTL.Istore(chunk,addr,args,src,n))->begin
    match Op.eval_addressing ge Values.Vundef addr(values args) with
    |Some address->begin match Memory.Mem.storev chunk memory address(PMap.get src rs) with
      |Some m->next n rs m(Store(PMap.get src rs)::trace)|None->fault end
    |None->fault end
  |Some(RTL.Ireturn(Some r))->Some(PMap.get r rs),memory_snapshot memory block,List.rev trace,visits
  |_ ->failwith "unsupported differential fixture instruction"
 in ignore source;walk 10000 f.RTL.fn_entrypoint rs memory [] [0;0;0]
let differential f args valid=
 let tf=PeelTwo.transf_function f in
 let result,memory,trace,_=execute f f args valid in
 let tresult,tmemory,ttrace,visits=execute f tf args valid in
 incr cases;
 if result<>tresult||memory<>tmemory||trace<>ttrace then failwith "result/memory/effect-order/fault mismatch";
 visits
let ()=
 let f=loop() in let tf=PeelTwo.transf_function f in
 check "production projection validator accepts two traversals"(PeelTwo.accepted f);
 check "actual code contains three disjoint copies"(nodes tf=3*nodes f);
 List.iter(fun mode->List.iter(fun(pc,instruction)->
  let copied=PTree.get(PeelTwo.tag mode pc)tf.RTL.fn_code in
  if copied<>Some(PeelTwo.copy_instruction mode pc instruction) then failwith "copy mismatch")
  (PTree.elements f.RTL.fn_code))phases;
 check "every tagged instruction is the production successor mapping"true;
 let seeds=[0;1;(-1);2147483647;(-2147483648);4294967295] in
 List.iter(fun input->List.iter(fun acc->List.iter(fun n->
  let visits=differential f[Values.Vint(int n);Values.Vint(int input);Values.Vint(int acc)]true in
  let expected=[(if n>0 then 1 else 0);(if n>1 then 1 else 0);max 0(n-2)] in
  if visits<>expected then failwith "first/second/stable traversal mismatch")
  [-2;0;1;2;3;4;7;8;31;100])seeds)seeds;
 check "first two iterations and stable remainder preserve arithmetic and memory order"(!cases=360);
 let tags=[Values.Vundef;Values.Vint(int 17);Values.Vlong(Int64.repr(z 99));Values.Vptr(p 42,Ptrofs.zero);
           Values.Vsingle(Floats.Float32.zero);Values.Vfloat(Floats.Float.zero)] in
 List.iter(fun input->List.iter(fun acc->List.iter(fun n->
  ignore(differential f[Values.Vint(int n);input;acc]true))[0;1;2;3;7])tags)tags;
 check "all value tags retain byte memory and return results"true;
 List.iter(fun input->ignore(differential f[input;Values.Vint(int 1);Values.Vundef]true))tags;
 List.iter(fun n->ignore(differential f[Values.Vint(int n);Values.Vint(int 7);Values.Vint(int 9)]false))[0;1;2;7];
 check "undefined condition and invalid memory address retain faults and preceding effects"true;
 let acyclic={f with RTL.fn_entrypoint=p 2;fn_code=tree[2,RTL.Inop(p 1);1,RTL.Ireturn(Some(p 1))]} in
 check "acyclic function retained exactly"(PeelTwo.transf_function acyclic=acyclic);
 let broken={f with RTL.fn_code=tree[9,RTL.Inop(p 999)]} in
 check "missing successor rejected"(not(PeelTwo.accepted broken));
 check "rejected graph falls back exactly"(PeelTwo.transf_function broken=broken);
 let oversized={f with RTL.fn_code=tree(List.init 600(fun i->i+1,RTL.Inop(p 1)))} in
 check "size budget retains original graph exactly"(PeelTwo.transf_function oversized=oversized);
 let reject name altered=check name(not(Experimental.check_function f altered PeelTwo.project)) in
 reject "entry corruption rejected"{tf with RTL.fn_code=PTree.remove tf.RTL.fn_entrypoint tf.RTL.fn_code};
 reject "signature corruption rejected"{tf with RTL.fn_sig={sig3 with sig_args=[]}};
 reject "parameter corruption rejected"{tf with RTL.fn_params=[]};
 reject "stack size corruption rejected"{tf with RTL.fn_stacksize=z 4};
 let mem_pc=PeelTwo.tag PeelTwo.First(p 8) in
 reject "store width corruption rejected"{tf with RTL.fn_code=PTree.set mem_pc(RTL.Istore(Mint64,Aindexed(Ptrofs.zero),[p 4],p 2,PeelTwo.tag PeelTwo.First(p 7)))tf.RTL.fn_code};
 (* Calls, builtins and terminators do not occur in the executable fixture;
    check their full payload and successor preservation separately. *)
 let instructions=[RTL.Inop(p 3);RTL.Iop(Oadd,[p 2;p 3],p 4,p 3);
  RTL.Iload(Mint32,Aindexed Ptrofs.zero,[p 2],p 4,p 3);
  RTL.Istore(Mint32,Aindexed Ptrofs.zero,[p 2],p 4,p 3);
  RTL.Icall(sig3,Datatypes.Coq_inl(p 2),[p 2;p 3],p 4,p 3);
  RTL.Itailcall(sig3,Datatypes.Coq_inr(p 77),[p 2;p 3]);
  RTL.Ibuiltin(EF_debug(p 1,p 77,[]),[],BR_none,p 3);
  RTL.Icond(Ccomp Ceq,[p 2;p 3],p 3,p 9);
  RTL.Ijumptable(p 2,List.map p[1;3;9]);RTL.Ireturn(Some(p 2))] in
 List.iter(fun instruction->
  let effects={f with RTL.fn_entrypoint=p 7;fn_code=tree[7,instruction;
    1,RTL.Ireturn None;3,RTL.Ireturn None;9,RTL.Ireturn None]} in
  let candidate=PeelTwo.peel_candidate effects in
  if not(Experimental.check_function effects candidate PeelTwo.project) then failwith "effect candidate rejected";
  List.iter(fun mode->
   let copied=PeelTwo.copy_instruction mode(p 7)instruction in
   if Experimental.map_successors PeelTwo.project copied<>instruction then failwith "effect payload changed";
   if PTree.get(PeelTwo.tag mode(p 7))candidate.RTL.fn_code<>Some copied then failwith "effect copy misplaced")phases)instructions;
 check "all ten RTL instruction constructors pass production validator and preserve effect payloads"true;
 Printf.printf "{\"success\":true,\"execution_cases\":%d,\"checks\":[%s]}\n"!cases
  (String.concat ","(List.map(Printf.sprintf "%S")(List.rev !passed)))

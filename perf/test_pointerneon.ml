(* Production-extracted local NEON checks for variable pointer loops.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Integers
open Maps
open Values
open Op
open RTL

let p=Camlcoq.P.of_int
let z=Camlcoq.Z.of_sint
let vi n=Vint(Int.repr(z n))
let checks=ref [] and cases=ref 0
let check name value=if not value then failwith name else checks:=name::!checks
let require name=function Some x->x|None->failwith(name^": None")
let tree items=List.fold_left(fun t(pc,i)->PTree.set(p pc)i t)PTree.empty items
let signature={sig_args=[Xptr;Xint];sig_res=Xvoid;sig_cc=cc_default}
let fixture={fn_sig=signature;fn_params=[p 2;p 1];fn_stacksize=Z0;fn_entrypoint=p 16;
 fn_code=tree[
  16,Inop(p 15);
  15,Icond(Ccompuimm(Cge,Int.repr(z 2)),[p 1],p 14,p 5);
  14,Iload(Mint32,Aindexed Int64.zero,[p 2],p 6,p 13);
  13,Iload(Mint32,Aindexed(Int64.repr(z 4)),[p 2],p 5,p 12);
  12,Icond(Ccomp Clt,[p 6;p 5],p 11,p 7);
  11,Iop(Oaddimm(Int.repr(z 3)),[p 6],p 4,p 10);
  10,Iop(Oaddimm(Int.repr(z 7)),[p 5],p 3,p 9);
  9,Istore(Mint32,Aindexed Int64.zero,[p 2],p 4,p 8);
  8,Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 2],p 3,p 7);
  7,Iop(Oaddlimm(Int64.repr(z 8)),[p 2],p 2,p 6);
  6,Iop(Oaddimm(Int.repr(z(-2))),[p 1],p 1,p 15);
  5,Icond(Ccompuimm(Cne,Int.zero),[p 1],p 4,p 1);
  4,Iload(Mint32,Aindexed Int64.zero,[p 2],p 9,p 3);
  3,Iop(Oaddimm(Int.repr(z 3)),[p 9],p 8,p 2);
  2,Istore(Mint32,Aindexed Int64.zero,[p 2],p 8,p 1);
  1,Ireturn None]}
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let ge=Globalenvs.Genv.globalenv(program fixture)
let replace pc i f={f with fn_code=PTree.set(p pc)i f.fn_code}
let count predicate f=PTree.fold(fun n _ i->if predicate i then n+1 else n)f.fn_code 0
let packed=function Ibuiltin(EF_builtin(name,_),_,_,_)->name="__builtin_cc_neon_add_u32x2"|_->false
let memory=function Iload _|Istore _->true|_->false
let wide_memory=function Iload(Mint64,_,_,_,_)|Istore(Mint64,_,_,_,_)->true|_->false
let unsupported_pack=function Iop((Omakelong|Ohighlong),_,_,_)->true|_->false
let memory_code f=PTree.fold(fun items pc i->if memory i then(pc,i)::items else items)f.fn_code []
let same_mem a b=a.Memory.Mem.mem_contents=b.Memory.Mem.mem_contents &&
 a.Memory.Mem.mem_access==b.Memory.Mem.mem_access && a.Memory.Mem.nextblock=b.Memory.Mem.nextblock
type event=Read of memory_chunk*Values.coq_val*Values.coq_val|Write of memory_chunk*Values.coq_val*Values.coq_val
type result=Done of Values.coq_val*Memory.Mem.mem*event list*int*RTL.regset
 |Fault of string*Memory.Mem.mem*event list
let run f pointer n initial=
 let rec step fuel pc rs m events vectors=
  if fuel=0 then failwith "pointer NEON fixture exceeded semantic step budget";
  let args registers=List.map(fun r->PMap.get r rs)registers in
  let fault category=Fault(category,m,List.rev events)in
  match PTree.get pc f.fn_code with
  |Some(Inop next)->step(fuel-1)next rs m events vectors
  |Some(Iop(op,registers,dst,next))->begin match Op.eval_operation ge Vundef op(args registers)m with
    |Some v->step(fuel-1)next(PMap.set dst v rs)m events vectors|None->fault "operation"end
  |Some(Iload(chunk,addr,registers,dst,next))->begin match Op.eval_addressing ge Vundef addr(args registers)with
    |Some address->begin match Memory.Mem.loadv chunk m address with
      |Some v->step(fuel-1)next(PMap.set dst v rs)m(Read(chunk,address,v)::events)vectors
      |None->fault "load"end|None->fault "address"end
  |Some(Istore(chunk,addr,registers,src,next))->begin match Op.eval_addressing ge Vundef addr(args registers)with
    |Some address->let v=PMap.get src rs in begin match Memory.Mem.storev chunk m address v with
      |Some memory->step(fuel-1)next rs memory(Write(chunk,address,v)::events)vectors
      |None->fault "store"end|None->fault "address"end
  |Some(Icond(cond,registers,yes,no))->begin match Op.eval_condition cond(args registers)m with
    |Some take->step(fuel-1)(if take then yes else no)rs m events vectors|None->fault "condition"end
  |Some(Ibuiltin(EF_builtin(name,sg),registers,BR dst,next))->
    let values=List.map(function BA r->PMap.get r rs|_->failwith "unexpected vector argument")registers in
    begin match Builtins.lookup_builtin_function name sg with
    |Some builtin->begin match Builtins.builtin_function_sem builtin values with
      |Some value->step(fuel-1)next(PMap.set dst value rs)m events(vectors+1)
      |None->fault "builtin"end|None->failwith "unknown emitted builtin"end
  |Some(Ireturn result)->Done((match result with Some r->PMap.get r rs|None->Vundef),m,List.rev events,vectors,rs)
  |_->failwith "unsupported native pointer fixture instruction"
 in step 100000 f.fn_entrypoint(RTL.init_regs[pointer;n]f.fn_params)initial [] 0

let allocated,block=Memory.Mem.alloc Memory.Mem.empty Z0(z 256)
let address offset=Vptr(block,Ptrofs.repr(z offset))
let fill values=
 List.fold_left(fun (m,offset)value->
  (require "initial scalar memory store"(Memory.Mem.storev Mint32 m(address offset)value),offset+4))
  (allocated,0)values|>fst
let initial=fill(List.init 64(fun i->vi(i*17+9)))
let initial_pair lo hi=
 let m=require "initialize low pair lane"(Memory.Mem.storev Mint32 initial(address 4)lo)in
 require "initialize high pair lane"(Memory.Mem.storev Mint32 m(address 8)hi)
let compare f ptr n m=
 let transformed=PointerNeon.transf_function f in
 let lowered=LowerLong.transf_function transformed in
 let source=run f ptr n m in
 let compare_result label target=
  match source,target with
  |Done(sv,sm,se,_,sr),Done(tv,tm,te,_,tr)->
    if sv<>tv||not(same_mem sm tm)||se<>te then failwith(label^": completed value/memory/access order mismatch");
    (* All original registers, including dead destinations, must agree. *)
    let bound=Camlcoq.P.to_int(RTL.max_reg_function f)in
    for register=1 to bound do
     if PMap.get(p register)sr<>PMap.get(p register)tr then failwith(label^": original register changed")done
  |Fault(sk,sm,se),Fault(tk,tm,te)->
    if sk<>tk||not(same_mem sm tm)||se<>te then failwith(label^": fault prefix memory or access order changed")
  |_->failwith(label^": completion/fault behavior changed")
 in
 let target=run transformed ptr n m and low=run lowered ptr n m in
 compare_result "production PointerNeon" target;compare_result "production LowerLong" low;
 incr cases;source,target,low
let reject name f=check(name^": fallback retains original function")(PointerNeon.transf_function f=f)

let ()=
 let tf=PointerNeon.transf_function fixture in
 check "real variable pointer loop changes"(tf<>fixture);
 check "one local window creates one real NEON builtin"(count packed tf=1);
 check "all scalar memory instructions and order retained"(memory_code tf=memory_code fixture);
 check "no speculative or alignment-dependent wide memory access"(count wide_memory tf=0);
 check "pointer/count ABI and stack metadata preserved"(tf.fn_sig=fixture.fn_sig &&tf.fn_params=fixture.fn_params&&tf.fn_stacksize=fixture.fn_stacksize);
 check "mandatory LowerLong removes unsupported generic packing"
  (count unsupported_pack(LowerLong.transf_function tf)=0);
 for offset=0 to 3 do for n=0 to 31 do
  ignore(compare fixture(address(4*offset))(vi n)initial)done done;
 check "variable zero/even/odd counts and pointer offsets preserve exact accesses"true;
 let _,target,_=compare fixture(address 4)(vi 3)(fill(List.init 64(fun i->vi(i*7))))in
 check "alignment-four pointer really runs NEON"
  (match target with Done(_,_,_,vectors,_)->vectors=1|_->false);
 check "native fixture does not assume alignment-eight"
  (Memory.Mem.loadv Mint32 initial(address 4)<>None &&Memory.Mem.loadv Mint64 initial(address 4)=None);
 let null=Vlong Int64.zero in
 let _,zero,_=compare fixture null(vi 0)initial in
 check "null pointer with zero count performs no memory access"
  (match zero with Done(_,_,[],0,_)->true|_->false);
 let _,one,_=compare fixture(address 4)(vi 1)initial in
 check "odd scalar tail performs exactly one read and one write and no NEON"
  (match one with Done(_,_,[Read(Mint32,a,_);Write(Mint32,b,_)],0,_)->a=address 4&&b=a|_->false);
 let edges=[0;1;2;3;-1;0x7fffffff;0x80000000;0xaaaaaaaa;0x55555555]in
 List.iter(fun low_const->List.iter(fun high_const->
  let f=replace 11(Iop(Oaddimm(Int.repr(z low_const)),[p 6],p 4,p 10))
    (replace 10(Iop(Oaddimm(Int.repr(z high_const)),[p 5],p 3,p 9))fixture)in
  check "independent lane constants remain vectorized"(count packed(PointerNeon.transf_function f)=1);
  List.iter(fun lo->List.iter(fun hi->
   let m=initial_pair(vi lo)(vi hi)in
   ignore(compare f(address 4)(vi 3)m))edges)edges)edges)edges;
 check "boundary inputs and constants preserve independent modular lanes"true;
 let random=Random.State.make[|2026;11;5;0x3402|]in
 let rand32()=(Random.State.bits random lsl 2)lor(Random.State.bits random land 3)in
 for _=1 to 2000 do
  let m=fill(List.init 64(fun _->vi(rand32())))in
  let offset=4*(Random.State.int random 4)and n=Random.State.int random 32 in
  ignore(compare fixture(address offset)(vi n)m)
 done;
 check "random independent arrays/counts/offsets preserve memory and load/store trace"true;
 let tags=[Vundef;vi 0;vi 17;vi(-1);Vlong Int64.zero;
  Vsingle(Floats.Float32.of_bits Int.zero);Vfloat(Floats.Float.of_bits Int64.zero);address 0]in
 List.iter(fun lo->List.iter(fun hi->
  let m=initial_pair lo hi in
  ignore(compare fixture(address 4)(vi 3)m))tags)tags;
 check "all six value constructors and partial undefined pairs preserve fault prefixes"true;
 List.iter(fun ptr->List.iter(fun n->ignore(compare fixture ptr n initial))tags)tags;
 check "malformed pointer/count value tags preserve completion and faults"true;
 ignore(compare fixture(Vptr(block,Ptrofs.repr(z(-4))))(vi 2)initial);
 ignore(compare fixture(Vptr(block,Ptrofs.repr(z(-1))))(vi 2)initial);
 ignore(compare fixture(address 2)(vi 2)initial);
 ignore(compare fixture(address 252)(vi 2)initial);
 let short,shortblock=Memory.Mem.alloc Memory.Mem.empty Z0(z 4)in
 ignore(compare fixture(Vptr(shortblock,Ptrofs.zero))(vi 2)short);
 let freed=require "free allocated memory"(Memory.Mem.free initial block Z0(z 256))in
 ignore(compare fixture(address 4)(vi 2)freed);
 check "out-of-range/misaligned/freed memory faults retain the same prefix"true;
 let partial=fill(List.init 64(fun i->if i=0 then vi 1 else if i=1 then vi 9 else vi i))in
 let partial=require "make only second lane read-only"
  (Memory.Mem.drop_perm partial block(z 4)(z 8)Memtype.Readable)in
 let source,_,_=compare fixture(address 0)(vi 2)partial in
 check "second store fault preserves the successful first scalar write"
  (match source with Fault("store",m,[Read _;Read _;Write(Mint32,a,_)])->
     a=address 0&&Memory.Mem.loadv Mint32 m(address 0)=Some(vi 4)|_->false);
 let alias=replace 8(Istore(Mint32,Aindexed Int64.zero,[p 2],p 3,p 7))fixture in
 check "overlapping output addresses are accepted when loads precede guard"
  (count packed(PointerNeon.transf_function alias)=1);
 ignore(compare alias(address 4)(vi 19)initial);
 let live=replace 1(Ireturn(Some(p 4))){fixture with fn_sig={signature with sig_res=Xint}}in
 check "non-void return and arbitrary live-out registers are supported"
  (count packed(PointerNeon.transf_function live)=1);
 for n=0 to 13 do ignore(compare live(address 4)(vi n)initial)done;
 reject "guard removed"(replace 12(Inop(p 11))fixture);
 reject "unsigned guard lacks the signed integer witness"(replace 12(Icond(Ccompu Clt,[p 6;p 5],p 11,p 7))fixture);
 reject "guard false edge enters first addition"(replace 12(Icond(Ccomp Clt,[p 6;p 5],p 11,p 11))fixture);
 reject "guard false edge enters second addition"(replace 12(Icond(Ccomp Clt,[p 6;p 5],p 11,p 10))fixture);
 reject "function entry skips guard"{fixture with fn_entrypoint=p 11};
 reject "function entry enters second addition"{fixture with fn_entrypoint=p 10};
 reject "first destination overwrites low input"(replace 11(Iop(Oaddimm(Int.repr(z 3)),[p 6],p 6,p 10))fixture);
 reject "first destination overwrites high input"(replace 11(Iop(Oaddimm(Int.repr(z 3)),[p 6],p 5,p 10))fixture);
 reject "destinations alias"(replace 10(Iop(Oaddimm(Int.repr(z 7)),[p 5],p 4,p 9))fixture);
 reject "first addition uses another register"(replace 11(Iop(Oaddimm(Int.repr(z 3)),[p 5],p 4,p 10))fixture);
 reject "second addition uses another register"(replace 10(Iop(Oaddimm(Int.repr(z 7)),[p 6],p 3,p 9))fixture);
 reject "unrelated instruction interrupts the pair"(replace 11(Iop(Oaddimm(Int.repr(z 3)),[p 6],p 4,p 9))fixture);
 reject "extra predecessor of first addition"(replace 30(Inop(p 11))fixture);
 reject "extra predecessor of second addition"(replace 30(Inop(p 10))fixture);
 reject "observable store interrupts the additions"
  (replace 11(Istore(Mint32,Aindexed Int64.zero,[p 2],p 6,p 10))fixture);
 let large={fixture with fn_code=List.fold_left(fun t n->PTree.set(p(n+100))(Ireturn None)t)
   fixture.fn_code(List.init 600 Fun.id)}in
 reject "oversized local search"large;
 let renamed={fixture with fn_code=PTree.fold(fun out pc instruction->
   PTree.set(p(Camlcoq.P.to_int pc+100))(Experimental.map_successors(fun next->p(Camlcoq.P.to_int next+100))instruction)out)
   fixture.fn_code PTree.empty;fn_entrypoint=p 116}in
 check "arbitrary PC numbering is supported"(count packed(PointerNeon.transf_function renamed)=1);
 ignore(compare renamed(address 4)(vi 9)initial);
 let tp=PointerNeon.transf_program(program fixture)in
 check "whole-program production transformation uses the checked function"
  (match List.assoc(p 1)tp.prog_defs with Gfun(Internal f)->f=tf|_->false);
 Printf.printf "{\"success\":true,\"performance_measured\":false,\"execution_cases\":%d,\"checks\":[%s]}\n"
  !cases(String.concat ","(List.map(Printf.sprintf "%S")(List.rev !checks)))

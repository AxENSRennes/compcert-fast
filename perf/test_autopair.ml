(* Production-extracted automatic pairing checks for a scalar step-one loop.
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
let fixture={fn_sig=signature;fn_params=[p 2;p 1];fn_stacksize=Z0;fn_entrypoint=p 10;
 fn_code=tree[
  10,Inop(p 9);
  9,Icond(Ccompuimm(Cne,Int.zero),[p 1],p 8,p 1);
  8,Iload(Mint32,Aindexed Int64.zero,[p 2],p 4,p 7);
  7,Iload(Mint32,Aindexed(Int64.repr(z 4)),[p 2],p 3,p 6);
  6,Icond(Ccomp Clt,[p 4;p 3],p 5,p 3);
  5,Iop(Oaddimm(Int.repr(z 3)),[p 4],p 6,p 4);
  4,Istore(Mint32,Aindexed Int64.zero,[p 2],p 6,p 3);
  3,Iop(Oaddlimm(Int64.repr(z 4)),[p 2],p 2,p 2);
  2,Iop(Oaddimm(Int.repr(z(-1))),[p 1],p 1,p 9);
  1,Ireturn None]}
let program f={prog_defs=[p 1,Gfun(Internal f)];prog_public=[p 1];prog_main=p 1}
let ge=Globalenvs.Genv.globalenv(program fixture)
let replace pc i f={f with fn_code=PTree.set(p pc)i f.fn_code}
let count predicate f=PTree.fold(fun n _ i->if predicate i then n+1 else n)f.fn_code 0
let packed=function Ibuiltin(EF_builtin(name,_),_,_,_)->name="__builtin_cc_neon_add_u32x2"|_->false
let wide_memory=function Iload(Mint64,_,_,_,_)|Istore(Mint64,_,_,_,_)->true|_->false
let unsupported_pack=function Iop((Omakelong|Ohighlong),_,_,_)->true|_->false
let same_mem a b=a.Memory.Mem.mem_contents=b.Memory.Mem.mem_contents &&
 a.Memory.Mem.mem_access==b.Memory.Mem.mem_access && a.Memory.Mem.nextblock=b.Memory.Mem.nextblock
type event=Read of memory_chunk*Values.coq_val*Values.coq_val|Write of memory_chunk*Values.coq_val*Values.coq_val
type stats={vectors:int;scalar_data_adds:int;pair_dispatches:int}
let empty_stats={vectors=0;scalar_data_adds=0;pair_dispatches=0}
type result=Done of Values.coq_val*Memory.Mem.mem*event list*stats*RTL.regset
 |Fault of string*Memory.Mem.mem*event list*RTL.regset

let run f pointer n initial=
 let rec step fuel pc rs m events stats=
  if fuel=0 then failwith "automatic pairing exceeded semantic step budget";
  let args registers=List.map(fun r->PMap.get r rs)registers in
  let fault category=Fault(category,m,List.rev events,rs)in
  let builtin_arg=function BA r->PMap.get r rs|BA_int n->Vint n|BA_long n->Vlong n
   |_->failwith "unexpected generated builtin argument"in
  match PTree.get pc f.fn_code with
  |Some(Inop next)->step(fuel-1)next rs m events stats
  |Some(Iop(op,registers,dst,next))->begin match Op.eval_operation ge Vundef op(args registers)m with
    |Some v->let data=match op with Oaddimm _ when dst<>p 1->1|_->0 in
      step(fuel-1)next(PMap.set dst v rs)m events
        {stats with scalar_data_adds=stats.scalar_data_adds+data}
    |None->fault "operation"end
  |Some(Iload(chunk,addr,registers,dst,next))->begin match Op.eval_addressing ge Vundef addr(args registers)with
    |Some address->begin match Memory.Mem.loadv chunk m address with
      |Some v->step(fuel-1)next(PMap.set dst v rs)m(Read(chunk,address,v)::events)stats
      |None->fault "load"end|None->fault "address"end
  |Some(Istore(chunk,addr,registers,src,next))->begin match Op.eval_addressing ge Vundef addr(args registers)with
    |Some address->let v=PMap.get src rs in begin match Memory.Mem.storev chunk m address v with
      |Some memory->step(fuel-1)next rs memory(Write(chunk,address,v)::events)stats
      |None->fault "store"end|None->fault "address"end
  |Some(Icond(cond,registers,yes,no))->begin match Op.eval_condition cond(args registers)m with
    |Some take->let pair=match cond with Ccompuimm(Cge,k)when k=Int.repr(z 2)&&take->1|_->0 in
      step(fuel-1)(if take then yes else no)rs m events
        {stats with pair_dispatches=stats.pair_dispatches+pair}
    |None->fault "condition"end
  |Some(Ibuiltin(EF_builtin(name,sg),registers,BR dst,next))->
    begin match Builtins.lookup_builtin_function name sg with
    |Some builtin->begin match Builtins.builtin_function_sem builtin(List.map builtin_arg registers)with
      |Some value->step(fuel-1)next(PMap.set dst value rs)m events {stats with vectors=stats.vectors+1}
      |None->fault "builtin"end|None->failwith "unknown emitted builtin"end
  |Some(Ireturn result)->Done((match result with Some r->PMap.get r rs|None->Vundef),m,List.rev events,stats,rs)
  |_->failwith "unsupported automatic pairing fixture instruction"
 in step 100000 f.fn_entrypoint(RTL.init_regs[pointer;n]f.fn_params)initial [] empty_stats

let allocated,block=Memory.Mem.alloc Memory.Mem.empty Z0(z 256)
let address offset=Vptr(block,Ptrofs.repr(z offset))
let fill values=
 List.fold_left(fun (m,offset)value->
  (require "initialize scalar cell"(Memory.Mem.storev Mint32 m(address offset)value),offset+4))
  (allocated,0)values|>fst
let initial=fill(List.init 64(fun i->vi(i*7+1)))
let initialized_three a b c=
 List.fold_left(fun m(offset,value)->require "initialize input lane"(Memory.Mem.storev Mint32 m(address offset)value))
  initial[4,a;8,b;12,c]
let compare f ptr n m=
 let transformed=AutoPair.transf_function f in
 let lowered=LowerLong.transf_function transformed in
 let source=run f ptr n m in
 let regs_same label source target=
  let bound=Camlcoq.P.to_int(RTL.max_reg_function f)in
  for register=1 to bound do
   if PMap.get(p register)source<>PMap.get(p register)target then
    failwith(label^": original register changed")done in
 let compare_result label target=
  match source,target with
  |Done(sv,sm,se,_,sr),Done(tv,tm,te,_,tr)->
    if sv<>tv||not(same_mem sm tm)||se<>te then failwith(label^": complete value/memory/access order mismatch");
    regs_same label sr tr
  |Fault(sk,sm,se,sr),Fault(tk,tm,te,tr)->
    if sk<>tk||not(same_mem sm tm)||se<>te then failwith(label^": fault prefix memory or access order changed");
    regs_same label sr tr
  |_->failwith(label^": completion/fault behavior changed")
 in
 let target=run transformed ptr n m and low=run lowered ptr n m in
 compare_result "production AutoPair" target;compare_result "production LowerLong" low;
 incr cases;source,target,low
let reject name f=check(name^": original function retained")(AutoPair.transf_function f=f)

let ()=
 let tf=AutoPair.transf_function fixture in
 check "scalar step-one loop is automatically transformed"(tf<>fixture);
 check "one real NEON builtin is generated"(count packed tf=1);
 check "automatic grouping introduces no wide memory access"(count wide_memory tf=0);
 check "signature/parameters/stack preserved"
  (tf.fn_sig=fixture.fn_sig&&tf.fn_params=fixture.fn_params&&tf.fn_stacksize=fixture.fn_stacksize);
 check "mandatory lowering removes generic packing"
  (count unsupported_pack(LowerLong.transf_function tf)=0);
 let source,target,_=compare fixture(address 4)(vi 2)(initialized_three(vi 1)(vi 9)(vi 17))in
 check "two source scalar additions are genuinely replaced by one NEON operation"
  (match source,target with Done(_,_,_,s,_),Done(_,_,_,t,_)->
   s.scalar_data_adds=2&&t.scalar_data_adds=0&&t.vectors=1&&t.pair_dispatches=1|_->false);
 check "pairing preserves the source read-write-read sequence"
  (match target with Done(_,_,[Read _;Read _;Write _;Read _;Read _;Write _],_,_)->true|_->false);
 let _,zero,_=compare fixture(Vlong Int64.zero)(vi 0)initial in
 check "null pointer with zero iterations has no memory access or NEON"
  (match zero with Done(_,_,[],s,_)->s.vectors=0&&s.pair_dispatches=0|_->false);
 let _,tail,_=compare fixture(address 4)(vi 1)(initialized_three(vi 1)(vi 9)(vi 17))in
 check "single remaining iteration uses the original scalar tail"
  (match tail with Done(_,_,[Read _;Read _;Write _],s,_)->
   s.vectors=0&&s.scalar_data_adds=1&&s.pair_dispatches=0|_->false);
 for offset=0 to 3 do for n=0 to 31 do
  let source,target,_=compare fixture(address(4*offset))(vi n)initial in
  check "paired dispatch count is floor of the source iteration count"
   (match source,target with Done _,Done(_,_,_,s,_)->s.vectors=n/2&&s.pair_dispatches=n/2|_->false)
 done done;
 check "zero/even/odd counts and four-byte pointer alignment preserve exact events"true;
 check "pointer four-mod-eight does not permit a wide load"
  (Memory.Mem.loadv Mint32 initial(address 4)<>None&&Memory.Mem.loadv Mint64 initial(address 4)=None);
 List.iter(fun(a,b,c)->ignore(compare fixture(address 4)(vi 2)(initialized_three(vi a)(vi b)(vi c))))
  [1,9,17;1,9,2;9,1,17;9,1,0];
 check "all four conditional-store combinations are preserved"true;
 let edges=[0;1;2;3;-1;0x7fffffff;0x80000000;0xaaaaaaaa;0x55555555]in
 List.iter(fun k->
  let f=replace 5(Iop(Oaddimm(Int.repr(z k)),[p 4],p 6,p 4))fixture in
  check "arbitrary modular increment is recognized"(count packed(AutoPair.transf_function f)=1);
  List.iter(fun a->List.iter(fun b->List.iter(fun c->
   ignore(compare f(address 4)(vi 2)(initialized_three(vi a)(vi b)(vi c))))edges)edges)edges)edges;
 check "boundary values and constants preserve lane-local uint32 arithmetic"true;
 let random=Random.State.make[|2026;11;5;0x2a11|]in
 let rand32()=(Random.State.bits random lsl 2)lor(Random.State.bits random land 3)in
 for _=1 to 2000 do
  let m=fill(List.init 64(fun _->vi(rand32())))in
  let offset=4*(Random.State.int random 4)and n=Random.State.int random 32 in
  ignore(compare fixture(address offset)(vi n)m)
 done;
 check "random scalar arrays are paired without changing the access trace"true;
 let tags=[Vundef;vi 0;vi 17;vi(-1);Vlong Int64.zero;
  Vsingle(Floats.Float32.of_bits Int.zero);Vfloat(Floats.Float.of_bits Int64.zero);address 0]in
 List.iter(fun a->List.iter(fun b->List.iter(fun c->
  ignore(compare fixture(address 4)(vi 2)(initialized_three a b c)))tags)tags)tags;
 check "all value tags and partially undefined lookahead cells preserve fault prefixes"true;
 List.iter(fun ptr->List.iter(fun n->ignore(compare fixture ptr n initial))tags)tags;
 List.iter(fun n->ignore(compare fixture(address 0)(vi n)initial))[-1;0x7fffffff;0x80000000];
 check "large unsigned counts and malformed values are checked without an unbounded execution"true;
 List.iter(fun ptr->ignore(compare fixture ptr(vi 2)initial))
  [address 2;address 252;Vptr(block,Ptrofs.repr(z(-4)));Vptr(block,Ptrofs.repr(z(-1)))];
 let short,b=Memory.Mem.alloc Memory.Mem.empty Z0(z 8)in
 let ptr=Vptr(b,Ptrofs.zero)in
 let short=require "short low"(Memory.Mem.storev Mint32 short ptr(vi 1))in
 let short=require "short high"(Memory.Mem.storev Mint32 short(Val.offset_ptr ptr(Ptrofs.repr(z 4)))(vi 9))in
 let source,_,_=compare fixture ptr(vi 2)short in
 check "missing third cell preserves the successful first write before the load fault"
  (match source with Fault("load",m,[Read _;Read _;Write _;Read _],_)->
   Memory.Mem.loadv Mint32 m ptr=Some(vi 4)|_->false);
 let partial=initialized_three(vi 1)(vi 9)(vi 17)in
 let partial=require "second cell read-only"(Memory.Mem.drop_perm partial block(z 8)(z 12)Memtype.Readable)in
 let source,_,_=compare fixture(address 4)(vi 2)partial in
 check "second-store permission failure retains the first scalar update"
  (match source with Fault("store",m,[Read _;Read _;Write _;Read _;Read _],_)->
   Memory.Mem.loadv Mint32 m(address 4)=Some(vi 4)|_->false);
 let freed=require "free allocation"(Memory.Mem.free initial block Z0(z 256))in
 ignore(compare fixture(address 4)(vi 2)freed);
 check "freed/misaligned/out-of-range accesses retain the source fault prefix"true;
 (* Alloc is a symbolic permission map, not a physical allocation of 2^64
    bytes. Three stores exercise the actual wrapped offsets in constant space. *)
 let wrapped,wrapped_block=Memory.Mem.alloc Memory.Mem.empty Z0 Ptrofs.modulus in
 let wrapped_ptr=Vptr(wrapped_block,Ptrofs.repr(z(-4)))in
 let wrapped_zero=Vptr(wrapped_block,Ptrofs.zero)in
 let wrapped_four=Vptr(wrapped_block,Ptrofs.repr(z 4))in
 let wrapped=require "wrapped low cell"(Memory.Mem.storev Mint32 wrapped wrapped_ptr(vi 1))in
 let wrapped=require "wrapped high cell"(Memory.Mem.storev Mint32 wrapped wrapped_zero(vi 9))in
 let wrapped=require "wrapped lookahead cell"(Memory.Mem.storev Mint32 wrapped wrapped_four(vi 17))in
 let source,target,_=compare fixture wrapped_ptr(vi 2)wrapped in
 check "wrapped pointer arithmetic preserves the two writes and original read order"
  (match source,target with Done(_,m,_,_,_),Done(_,_,_,s,_)->
   s.vectors=1&&Memory.Mem.loadv Mint32 m wrapped_ptr=Some(vi 4)&&
   Memory.Mem.loadv Mint32 m wrapped_zero=Some(vi 12)|_->false);
 reject "unguarded scalar update"(replace 6(Inop(p 5))fixture);
 reject "unsigned data guard"(replace 6(Icond(Ccompu Clt,[p 4;p 3],p 5,p 3))fixture);
 reject "changed lookahead distance"(replace 7(Iload(Mint32,Aindexed(Int64.repr(z 8)),[p 2],p 3,p 6))fixture);
 reject "changed pointer stride"(replace 3(Iop(Oaddlimm(Int64.repr(z 8)),[p 2],p 2,p 2))fixture);
 reject "changed count stride"(replace 2(Iop(Oaddimm(Int.repr(z(-2))),[p 1],p 1,p 9))fixture);
 reject "different written cell"(replace 4(Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 2],p 6,p 3))fixture);
 reject "volatile source access"(replace 8(Ibuiltin(EF_vload Mint32,[BA(p 2)],BR(p 4),p 7))fixture);
 reject "observable call in the scalar body"(replace 10(Icall(signature_main,Datatypes.Coq_inr(p 99),[],p 6,p 9))fixture);
 reject "observable return value"(replace 1(Ireturn(Some(p 6))){fixture with fn_sig={signature with sig_res=Xint}});
 reject "different function entry"{fixture with fn_entrypoint=p 9};
 reject "different parameter mapping"{fixture with fn_params=[p 1;p 2]};
 reject "nonzero stack storage"{fixture with fn_stacksize=z 8};
 reject "extra code outside the scalar template"(replace 11(Inop(p 1))fixture);
 let transformed=AutoPair.transf_program(program fixture)in
 check "whole-program transformation uses the tested production function"
  (match List.assoc(p 1)transformed.prog_defs with Gfun(Internal f)->f=tf|_->false);
 Printf.printf "{\"success\":true,\"performance_measured\":false,\"execution_cases\":%d,\"checks\":[%s]}\n"
  !cases(String.concat ","(List.map(Printf.sprintf "%S")(List.rev !checks)))

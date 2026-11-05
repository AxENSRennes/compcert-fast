(* Production-extracted guarded two-lane memory NEON checks.
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
let int n=Vint(Int.repr(z n))
let checks=ref [] and cases=ref 0
let check name truth=if not truth then failwith name else checks:=name::!checks
let tree items=List.fold_left(fun t(pc,i)->PTree.set(p pc)i t)PTree.empty items
let g=p 2
let signature={sig_args=[];sig_res=Xvoid;sig_cc=cc_default}
let fixture={fn_sig=signature;fn_params=[];fn_stacksize=Z0;fn_entrypoint=p 22;
 fn_code=tree[
  22,Iop(Oaddrsymbol(g,Ptrofs.zero),[],p 12,p 21);
  21,Iload(Mint32,Aindexed Int64.zero,[p 12],p 3,p 20);
  20,Iop(Omove,[p 12],p 11,p 19);
  19,Iload(Mint32,Aindexed(Int64.repr(z 4)),[p 11],p 2,p 18);
  18,Icond(Ccomp Clt,[p 3;p 2],p 17,p 1);
  17,Inop(p 16);16,Iop(Omove,[p 11],p 5,p 15);
  15,Iop(Omove,[p 3],p 8,p 14);14,Iop(Omove,[p 8],p 7,p 13);
  13,Iop(Oaddimm(Int.repr(z 3)),[p 7],p 6,p 12);
  12,Istore(Mint32,Aindexed Int64.zero,[p 5],p 6,p 11);
  11,Inop(p 10);10,Iop(Oaddrsymbol(g,Ptrofs.zero),[],p 5,p 9);
  9,Iop(Omove,[p 5],p 10,p 8);
  8,Iload(Mint32,Aindexed(Int64.repr(z 4)),[p 10],p 8,p 7);
  7,Inop(p 6);6,Inop(p 5);
  5,Iop(Oaddimm(Int.repr(z 7)),[p 8],p 6,p 4);
  4,Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 5],p 6,p 3);
  3,Inop(p 2);2,Ireturn None;1,Ireturn None]}
let global={gvar_info=();gvar_init=[Init_int32 Int.zero;Init_int32 Int.zero;
 Init_int32(Int.repr(z 0x13579bdf));Init_int32(Int.repr(z 0x2468ace0))];
 gvar_readonly=false;gvar_volatile=false}
let program f={prog_defs=[p 1,Gfun(Internal f);g,Gvar global];prog_public=[p 1;g];prog_main=p 1}
let ge=Globalenvs.Genv.globalenv(program fixture)
let require label=function Some x->x|None->failwith(label^": None")
let initial=require "global init"(Globalenvs.Genv.init_mem(program fixture))
let ptr=Globalenvs.Genv.symbol_address ge g Ptrofs.zero
let block=match ptr with Vptr(b,_)->b|_->failwith "missing symbol"
let offset n=Val.offset_ptr ptr(Ptrofs.repr(z n))
let same_mem a b=a.Memory.Mem.mem_contents=b.Memory.Mem.mem_contents &&
 a.Memory.Mem.mem_access==b.Memory.Mem.mem_access && a.Memory.Mem.nextblock=b.Memory.Mem.nextblock
let count pred f=PTree.fold(fun n _ i->if pred i then n+1 else n)f.fn_code 0
let packed=function Ibuiltin(EF_builtin(name,_),_,_,_)->name="__builtin_cc_neon_add_u32x2"|_->false
let wide_load=function Iload(Mint64,_,_,_,_)->true|_->false
let wide_store=function Istore(Mint64,_,_,_,_)->true|_->false
let replace pc i f={f with fn_code=PTree.set(p pc)i f.fn_code}
type stats={loads32:int;loads64:int;stores32:int;stores64:int;vectors:int}
let empty_stats={loads32=0;loads64=0;stores32=0;stores64=0;vectors=0}
let run f memory=
 let rec step fuel pc rs m stats=
  if fuel=0 then failwith "memory NEON fixture fuel";
  let args rl=List.map(fun r->PMap.get r rs)rl in
  match PTree.get pc f.fn_code with
  |Some(Inop next)->step(fuel-1)next rs m stats
  |Some(Iop(op,rl,dst,next))->begin match Op.eval_operation ge Vundef op(args rl)m with
    |Some v->step(fuel-1)next(PMap.set dst v rs)m stats|None->None end
  |Some(Iload(chunk,addr,rl,dst,next))->begin match Op.eval_addressing ge Vundef addr(args rl)with
    |Some address->begin match Memory.Mem.loadv chunk m address with
      |Some v->let stats={stats with loads32=stats.loads32+(if chunk=Mint32 then 1 else 0);
                         loads64=stats.loads64+(if chunk=Mint64 then 1 else 0)}in
        step(fuel-1)next(PMap.set dst v rs)m stats|None->None end
    |None->None end
  |Some(Istore(chunk,addr,rl,src,next))->begin match Op.eval_addressing ge Vundef addr(args rl)with
    |Some address->begin match Memory.Mem.storev chunk m address(PMap.get src rs)with
      |Some memory->let stats={stats with stores32=stats.stores32+(if chunk=Mint32 then 1 else 0);
                               stores64=stats.stores64+(if chunk=Mint64 then 1 else 0)}in
        step(fuel-1)next rs memory stats|None->None end
    |None->None end
  |Some(Icond(cond,rl,yes,no))->begin match Op.eval_condition cond(args rl)m with
    |Some take->step(fuel-1)(if take then yes else no)rs m stats|None->None end
  |Some(Ibuiltin(EF_builtin(name,sg),rl,BR dst,next))->
    let values=List.map(function BA r->PMap.get r rs|_->failwith "unsupported numeric argument")rl in
    begin match Builtins.lookup_builtin_function name sg with
    |Some bf->begin match Builtins.builtin_function_sem bf values with
      |Some v->step(fuel-1)next(PMap.set dst v rs)m {stats with vectors=stats.vectors+1}
      |None->None end|None->failwith "unknown generated builtin"end
  |Some(Ireturn None)->Some(m,stats)
  |_->failwith "unsupported memory NEON fixture instruction"
 in step 10000 f.fn_entrypoint(RTL.init_regs [] f.fn_params)memory empty_stats
let initialized a b=
 let m=require "lane zero store"(Memory.Mem.storev Mint32 initial ptr a)in
 require "lane one store"(Memory.Mem.storev Mint32 m(offset 4)b)
let compare f memory=
 let tf=MemoryNeon.transf_function f in
 let source=run f memory and target=run tf memory in
 incr cases;
 match source,target with
 |None,None->None
 |Some(sm,ss),Some(tm,ts)->
   if not(same_mem sm tm)then failwith "memory NEON exact memory mismatch";
   for n=8 to 15 do
    if Memory.Mem.loadv Mint8unsigned sm(offset n)<>Memory.Mem.loadv Mint8unsigned initial(offset n)
      then failwith "memory NEON overwrote surrounding sentinel"done;
   Some(ss,ts)
 |_->failwith "memory NEON changed source completion/fault behavior"
let reject name f=
 check(name^": original function retained")(MemoryNeon.transf_function f=f)

let ()=
 let tf=MemoryNeon.transf_function fixture in
 check "real scalar memory region changes"(tf<>fixture);
 check "target contains one real packed NEON builtin"(count packed tf=1);
 check "target contains one 64-bit memory load"(count wide_load tf=1);
 check "target contains one 64-bit memory store"(count wide_store tf=1);
 check "signature/params/stack preserved"(tf.fn_sig=fixture.fn_sig && tf.fn_params=fixture.fn_params && tf.fn_stacksize=fixture.fn_stacksize);
 let ss,ts=require "true guard"(compare fixture(initialized(int 1)(int 9)))in
 check "true guard performs one packed operation and wide memory write"
   (ts.loads64=1 && ts.stores64=1 && ts.vectors=1 && ts.stores32=0 && ss.stores32=2);
 let _,ts=require "false guard"(compare fixture(initialized(int 9)(int 1)))in
 check "false guard performs no speculative wide access or vector operation"
   (ts.loads64=0 && ts.stores64=0 && ts.vectors=0 && ts.stores32=0);
 let edges=[0;1;2;3;-1;0x7fffffff;0x80000000;0xaaaaaaaa;0x55555555]in
 List.iter(fun a->List.iter(fun b->ignore(compare fixture(initialized(int a)(int b))))edges)edges;
 check "81 independent boundary lane combinations preserve exact memory"true;
 List.iter(fun lo->List.iter(fun hi->
  let f=replace 13(Iop(Oaddimm(Int.repr(z lo)),[p 7],p 6,p 12))
    (replace 5(Iop(Oaddimm(Int.repr(z hi)),[p 8],p 6,p 4))fixture)in
  check "independent lane constants are actually vectorized"(count packed(MemoryNeon.transf_function f)=1);
  List.iter(fun a->List.iter(fun b->ignore(compare f(initialized(int a)(int b))))edges)edges)edges)edges;
 check "6561 boundary input/constant combinations preserve lane-local wrapping arithmetic"true;
 let random=Random.State.make[|0x2e0f;2026;11|]in
 let rand32()=(Random.State.bits random lsl 2)lor(Random.State.bits random land 3)in
 for _=1 to 10000 do let a=rand32()and b=rand32()in
  ignore(compare fixture(initialized(int a)(int b)))done;
 check "10000 deterministic independent random lane pairs preserve exact memory"true;
 let tags=[Vundef;int 0;int 17;int(-1);Vlong Int64.zero;
  Vsingle(Floats.Float32.of_bits Int.zero);Vfloat(Floats.Float.of_bits Int64.zero);ptr]in
 List.iter(fun a->List.iter(fun b->ignore(compare fixture(initialized a b)))tags)tags;
 check "all six Val constructors and mixed undefined lanes preserve completion"true;
 let mixed=initialized(int 17)Vundef in
 check "partial undefined lane blocks the original signed guard"(run fixture mixed=None);
 let unsafely_widened=require "mixed wide read"(Memory.Mem.loadv Mint64 mixed ptr)in
 check "negative control: naive widening would lose the defined lane"
  (unsafely_widened=Vundef && Memory.Mem.loadv Mint32 mixed ptr=Some(int 17));
 let no_guard=replace 18(Inop(p 17))fixture in
 let scalar_partial,_=require "unguarded partial scalar update"(run no_guard mixed)in
 let wrong_partial=require "wrong unguarded packed update"(Memory.Mem.storev Mint64 mixed ptr Vundef)in
 check "unguarded source preserves a defined updated lane that unsafe NEON packing loses"
  (Memory.Mem.loadv Mint32 scalar_partial ptr=Some(int 20) &&
   Memory.Mem.loadv Mint32 wrong_partial ptr=Some Vundef);
 check "two scalar-aligned readable lanes alone do not justify a wide read"
  (Memory.Mem.loadv Mint32 initial(offset 4)<>None && Memory.Mem.loadv Mint32 initial(offset 8)<>None &&
   Memory.Mem.loadv Mint64 initial(offset 4)=None);
 reject "guard removed"(replace 18(Inop(p 17))fixture);
 reject "unsigned guard is outside the supported source pattern"
  (replace 18(Icond(Ccompu Clt,[p 3;p 2],p 17,p 1))fixture);
 reject "reversed lane store offsets"(replace 4(Istore(Mint32,Aindexed Int64.zero,[p 5],p 6,p 3))fixture);
 reject "source alias changes after first store"
  (replace 8(Iload(Mint32,Aindexed Int64.zero,[p 10],p 8,p 7))fixture);
 reject "second load extends past the checked pair"
  (replace 19(Iload(Mint32,Aindexed(Int64.repr(z 8)),[p 11],p 2,p 18))fixture);
 reject "different store chunk"
  (replace 4(Istore(Mint16unsigned,Aindexed(Int64.repr(z 4)),[p 5],p 6,p 3))fixture);
 reject "different second-store source"
  (replace 4(Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 5],p 2,p 3))fixture);
 reject "intervening observable external call"
  (replace 11(Icall(signature_main,Datatypes.Coq_inr(p 99),[],p 6,p 10))fixture);
 reject "nonzero global producer lacks alignment witness"
  (replace 22(Iop(Oaddrsymbol(g,Ptrofs.repr(z 4)),[],p 12,p 21))fixture);
 reject "volatile source access"(replace 21(Ibuiltin(EF_vload Mint32,[BA(p 12)],BR(p 3),p 20))fixture);
 reject "second global producer changes symbol"
  (replace 10(Iop(Oaddrsymbol(p 3,Ptrofs.zero),[],p 5,p 9))fixture);
 reject "branch returns before the second store"
  (replace 18(Icond(Ccomp Clt,[p 3;p 2],p 17,p 4))fixture);
 reject "function entry does not establish both loaded lanes"{fixture with fn_entrypoint=p 17};
 reject "observable scalar return register"(replace 2(Ireturn(Some(p 6))){fixture with fn_sig={signature with sig_res=Xint}});
 let large={fixture with fn_code=List.fold_left(fun t n->PTree.set(p(n+100))(Ireturn None)t)
   fixture.fn_code(List.init 600 Fun.id)}in
 reject "oversized function"large;
 let mfn,_=Memory.Mem.alloc Memory.Mem.empty Z0(z 1)in
 let short,shortblock=Memory.Mem.alloc mfn Z0(z 4)in
 check "short-block fault control uses same symbol block"(shortblock=block);
 check "one readable lane does not justify a vector memory access"(compare fixture short=None);
 let allocated,allocatedblock=Memory.Mem.alloc mfn Z0(z 16)in
 let freed=require "free"(Memory.Mem.free allocated allocatedblock Z0(z 16))in
 check "freed memory faults identically"(compare fixture freed=None);
 let transformed_program=MemoryNeon.transf_program(program fixture)in
 check "whole-program transformation uses the tested production function"
  (match List.assoc(p 1)transformed_program.prog_defs with Gfun(Internal f)->f=tf|_->false);
 Printf.printf "{\"success\":true,\"performance_measured\":false,\"execution_cases\":%d,\"checks\":[%s]}\n"
 !cases(String.concat ","(List.map(Printf.sprintf "%S")(List.rev !checks)))

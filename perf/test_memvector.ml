(* Production-extracted correlated-lane store-widening checks.
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
let check_names=ref []
let cases=ref 0
let check name truth=if not truth then failwith name else check_names:=name::!check_names
let tree items=List.fold_left(fun t(pc,i)->PTree.set(p pc)i t)PTree.empty items
let g=p 2
let global= {gvar_info=();gvar_init=[Init_space(z 16)];gvar_readonly=false;gvar_volatile=false}
let signature={sig_args=[Xint];sig_res=Xint;sig_cc=cc_default}
let store ofs r next=Istore(Mint32,Aglobal(g,Ptrofs.repr(z ofs)),[],p r,p next)
let fixture={fn_sig=signature;fn_params=[p 1];fn_stacksize=Z0;fn_entrypoint=p 1;
             fn_code=tree[1,store 0 1 2;2,store 4 1 3;3,Ireturn(Some(p 1))]}
let program={prog_defs=[p 1,Gfun(Internal fixture);g,Gvar global];prog_public=[p 1;g];prog_main=p 1}
let ge=Globalenvs.Genv.globalenv program
let require label=function Some x->x|None->failwith(label^": None")
let initial=require "global init" (Globalenvs.Genv.init_mem program)
let pointer=Globalenvs.Genv.symbol_address ge g Ptrofs.zero
let block=match pointer with Vptr(b,_)->b|_->failwith"symbol missing"
let count_store f=PTree.fold(fun n _->function Istore _->n+1|_->n)f.fn_code 0
let replace pc i f={f with fn_code=PTree.set(p pc)i f.fn_code}
let same_mem a b=a.Memory.Mem.mem_contents=b.Memory.Mem.mem_contents &&
  a.Memory.Mem.mem_access==b.Memory.Mem.mem_access && a.Memory.Mem.nextblock=b.Memory.Mem.nextblock
let run f inputs memory =
  let rec step fuel pc rs m stores =
    if fuel=0 then failwith"memory fixture fuel";
    match PTree.get pc f.fn_code with
    | Some(Inop next)->step(fuel-1)next rs m stores
    | Some(Iop(op,args,dst,next))->
      begin match Op.eval_operation ge Vundef op (List.map(fun r->PMap.get r rs)args)m with
      | Some v->step(fuel-1)next(PMap.set dst v rs)m stores|None->None end
    | Some(Istore(chunk,addr,args,src,next))->
      begin match Op.eval_addressing ge Vundef addr(List.map(fun r->PMap.get r rs)args)with
      | Some address->begin match Memory.Mem.storev chunk m address(PMap.get src rs)with
        |Some nextmem->step(fuel-1)next rs nextmem(stores+1)|None->None end
      |None->None end
    | Some(Ireturn(Some r))->Some(PMap.get r rs,rs,m,stores)
    | _->failwith"unexpected memory fixture instruction"
  in step 10000 f.fn_entrypoint(RTL.init_regs inputs f.fn_params)memory 0
let compare_with transform f inputs memory =
  let source,rs,sm,sc=require "source execution"(run f inputs memory)in
  let tf=transform f in
  let target,trs,tm,tc=require "wide execution"(run tf inputs memory)in
  let lowered,lrs,lm,lc=require "lowered execution"(run(LowerLong.transf_function tf)inputs memory)in
  incr cases;
  if source<>target || source<>lowered || not(same_mem sm tm && same_mem tm lm)then
    failwith"correlated wide store changed value or exact memory";
  for r=1 to Camlcoq.P.to_int(RTL.max_reg_function f)do
    if PMap.get(p r)rs<>PMap.get(p r)trs || PMap.get(p r)rs<>PMap.get(p r)lrs then
      failwith"wide store changed an original register" done;
  sc,tc,lc
let compare=compare_with MemVector.transf_function
let indirect_compare=compare_with MemVector.Indirect.transf_function
let indirect_fixture={fixture with fn_code=tree[
  1,Iop(Oaddrsymbol(g,Ptrofs.zero),[],p 4,p 2);
  2,Istore(Mint32,Aindexed Int64.zero,[p 4],p 1,p 3);
  3,Inop(p 4);
  4,Iop(Oaddrsymbol(g,Ptrofs.zero),[],p 4,p 5);
  5,Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 4],p 1,p 6);
  6,Ireturn(Some(p 1))]}
let indirect_reject name f =
  check(name^": refused")(MemVector.Indirect.selected f=None);
  check(name^": unchanged")(MemVector.Indirect.transf_function f=f)
let reject name f =
  check(name^": refused")(MemVector.selected f=None);
  check(name^": unchanged")(MemVector.transf_function f=f)
let () =
  let tf=MemVector.transf_function fixture in
  check "ordinary same-input stores selected"(MemVector.selected fixture<>None);
  check "two 32-bit stores become one 64-bit store"(count_store fixture=2 && count_store tf=1);
  check "fresh register above every source use/definition"(Camlcoq.P.to_int(MemVector.fresh_reg fixture)>Camlcoq.P.to_int(RTL.max_reg_function fixture));
  check "first store becomes correlated packing"(PTree.get(p 1)tf.fn_code=Some(Iop(Omakelong,[p 1;p 1],MemVector.fresh_reg fixture,p 2)));
  check "second store is widened at original base"(PTree.get(p 2)tf.fn_code=Some(Istore(Mint64,Aglobal(g,Ptrofs.zero),[],MemVector.fresh_reg fixture,p 3)));
  check "function signature/stack/entry preserved"(fixture.fn_sig=tf.fn_sig && fixture.fn_params=tf.fn_params && fixture.fn_stacksize=tf.fn_stacksize && fixture.fn_entrypoint=tf.fn_entrypoint);
  let random=Random.State.make[|0x571de;2026|]in
  let numbers=[0;1;-1;0x7fffffff;0x80000000;0xffffffff;0xaaaaaaaa;0x55555555]@
      List.init 4096(fun _->(Random.State.bits random lsl 2)lor(Random.State.bits random land 3))in
  let values=List.map int numbers@[Vundef;Vlong Int64.zero;Vlong(Int64.repr(z(-1)));pointer;
        Vfloat(Floats.Float.of_bits(Int64.repr(z(-1))));Vsingle(Floats.Float32.of_bits(Int.repr(z 0x7fc00001)))]in
  List.iter(fun value->let sc,tc,lc=compare fixture[value]initial in
    if sc<>2 || tc<>1 || lc<>1 then failwith"incorrect memory-access coalescence")values;
  check "all value tags and full-width random integers preserve exact memory"true;
  let itf=MemVector.Indirect.transf_function indirect_fixture in
  check "executed global producer and repeated address reload selected"
    (MemVector.Indirect.selected indirect_fixture<>None);
  check "separated indirect scalar stores become one native indexed wide store"
    (count_store indirect_fixture=2 && count_store itf=1);
  check "indirect wide store retains native base-register addressing"
    (PTree.get(p 5)itf.fn_code=Some(Istore(Mint64,Aindexed Int64.zero,[p 4],MemVector.fresh_reg indirect_fixture,p 6)));
  List.iter(fun value->let sc,tc,lc=indirect_compare indirect_fixture[value]initial in
    if sc<>2 || tc<>1 || lc<>1 then failwith"indirect store coalescence")values;
  check "indirect producer, reload and all value tags preserve exact memory"true;
  let selfmoves=replace 3(Iop(Omove,[p 1],p 1,p 4))indirect_fixture in
  List.iter(fun value->ignore(indirect_compare selfmoves[value]initial))values;
  check "self moves preserve source correlation through every value tag"true;
  let samebase={indirect_fixture with fn_code=tree[
    1,Iop(Oaddrsymbol(g,Ptrofs.zero),[],p 4,p 2);
    2,Istore(Mint32,Aindexed Int64.zero,[p 4],p 4,p 3);
    3,Inop(p 4);4,Iop(Oaddrsymbol(g,Ptrofs.zero),[],p 4,p 5);
    5,Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 4],p 4,p 6);
    6,Ireturn(Some(p 4))]}in
  ignore(indirect_compare samebase[int 9]initial);
  check "same source/base register remains valid through correlated pointer reload"true;
  indirect_reject "indirect unrelated source register"(replace 5(Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 4],p 2,p 6))indirect_fixture);
  indirect_reject "indirect unrelated base register"(replace 5(Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 3],p 1,p 6))indirect_fixture);
  indirect_reject "indirect first point is entry"{indirect_fixture with fn_entrypoint=p 2};
  indirect_reject "indirect first point has extra predecessor"(replace 7(Inop(p 2))indirect_fixture);
  indirect_reject "indirect intermediate point has extra predecessor"(replace 7(Inop(p 4))indirect_fixture);
  indirect_reject "indirect last point has extra predecessor"(replace 7(Inop(p 5))indirect_fixture);
  indirect_reject "indirect source-modifying move"(replace 3(Iop(Omove,[p 2],p 1,p 4))indirect_fixture);
  indirect_reject "indirect base-modifying arithmetic"(replace 3(Iop(Oaddlimm(Int64.repr(z 8)),[p 4],p 4,p 4))indirect_fixture);
  indirect_reject "indirect intervening volatile write"(replace 3(Ibuiltin(EF_vstore Mint32,[BA(p 4);BA(p 1)],BR_none,p 4))indirect_fixture);
  indirect_reject "indirect reload changes global"(replace 4(Iop(Oaddrsymbol(p 3,Ptrofs.zero),[],p 4,p 5))indirect_fixture);
  indirect_reject "indirect reload changes offset"(replace 4(Iop(Oaddrsymbol(g,Ptrofs.repr(z 8)),[],p 4,p 5))indirect_fixture);
  indirect_reject "indirect producer lacks zero alignment witness"(replace 1(Iop(Oaddrsymbol(g,Ptrofs.repr(z 4)),[],p 4,p 2))indirect_fixture);
  indirect_reject "indirect endpoint returns into pending first store"(replace 5(Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 4],p 1,p 2))indirect_fixture);
  let long_path={indirect_fixture with fn_code=tree(
    [1,Iop(Oaddrsymbol(g,Ptrofs.zero),[],p 4,p 2);
     2,Istore(Mint32,Aindexed Int64.zero,[p 4],p 1,p 10);
     100,Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 4],p 1,p 101);101,Ireturn(Some(p 1))]@
    List.init 90(fun n->n+10,Inop(p(n+11)) ))}in
  indirect_reject "indirect scan is finitely bounded"long_path;

  let cyc=replace 2(store 4 1 1)fixture in
  let tcyc=MemVector.transf_function cyc in
  check "two-store backedge accepted"(MemVector.selected cyc<>None && count_store tcyc=1);
  reject "unrelated source registers"(replace 2(store 4 2 3)fixture);
  reject "misaligned source pair"{fixture with fn_code=tree[1,store 4 1 2;2,store 8 1 3;3,Ireturn(Some(p 1))]};
  reject "different target global"(replace 2(Istore(Mint32,Aglobal(p 3,Ptrofs.repr(z 4)),[],p 1,p 3))fixture);
  reject "different memory chunk"(replace 2(Istore(Mint16unsigned,Aglobal(g,Ptrofs.repr(z 4)),[],p 1,p 3))fixture);
  reject "dynamic address lacks alignment witness"{fixture with fn_code=tree[
    1,Istore(Mint32,Aindexed Int64.zero,[p 2],p 1,p 2);
    2,Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 2],p 1,p 3);3,Ireturn(Some(p 1))]};
  reject "second point is entry"{fixture with fn_entrypoint=p 2};
  reject "extra predecessor"(replace 4(Inop(p 2))fixture);
  reject "call-return predecessor"(replace 4(Icall(signature_main,Datatypes.Coq_inr(p 9),[],p 3,p 2))fixture);
  reject "second point self edge"(replace 2(store 4 1 2)fixture);
  reject "first volatile access"(replace 1(Ibuiltin(EF_vstore Mint32,[BA(p 2);BA(p 1)],BR_none,p 2))fixture);
  reject "second volatile access"(replace 2(Ibuiltin(EF_vstore Mint32,[BA(p 2);BA(p 1)],BR_none,p 3))fixture);
  reject "undefined successor"(replace 1(store 0 1 99)fixture);
  let large={fixture with fn_code=tree(List.init 600(fun i->i+1,Inop(p 1))@[601,store 0 1 602;602,store 4 1 603;603,Ireturn(Some(p 1))])}in
  reject "oversized function"large;
  (* A mixed defined/undefined pair cannot be represented by one all-or-nothing
     Vlong. The actual byte difference is a negative semantic control. *)
  let mixed={fixture with fn_params=[p 1;p 2];fn_sig={signature with sig_args=[Xint;Xint]};
     fn_code=tree[1,store 0 1 2;2,store 4 2 3;3,Ireturn(Some(p 2))]}in
  let _,_,sm,_=require "mixed pair"(run mixed[Vundef;int 17]initial)in
  let wrong=require "wrong all-undefined word"(Memory.Mem.storev Mint64 initial pointer Vundef)in
  check "mixed undefined lane rejection avoids losing a defined second word"
    (MemVector.selected mixed=None && Memory.Mem.loadv Mint32 sm (Values.Val.offset_ptr pointer(Ptrofs.repr(z 4)))=Some(int 17) &&
     Memory.Mem.loadv Mint32 wrong (Values.Val.offset_ptr pointer(Ptrofs.repr(z 4)))=Some Vundef);
  let misaligned=Globalenvs.Genv.symbol_address ge g(Ptrofs.repr(z 4))in
  let m1=require "first aligned32"(Memory.Mem.storev Mint32 initial misaligned(int 7))in
  ignore(require "second aligned32"(Memory.Mem.storev Mint32 m1(Val.offset_ptr misaligned(Ptrofs.repr(z 4)))(int 7)));
  check "32-bit alignment alone does not justify a wide store"(Memory.Mem.storev Mint64 initial misaligned(Vlong Int64.zero)=None);
  (* Globals retain Writable rather than Freeable permission. Use an allocated
     block at the same symbol block number for the deallocation control. *)
  let mfn,_=Memory.Mem.alloc Memory.Mem.empty Z0(z 1)in
  let allocated,allocatedblock=Memory.Mem.alloc mfn Z0(z 16)in
  check "deallocation control preserves the symbol block"(allocatedblock=block);
  let freed=require "free"(Memory.Mem.free allocated allocatedblock Z0(z 16))in
  check "faulting memory cannot complete source or widened pair"(run fixture[int 4]freed=None && run tf[int 4]freed=None);
  let short,shortblock=Memory.Mem.alloc mfn Z0(z 4)in
  check "short allocation has the tested global symbol's block"(shortblock=block);
  check "one valid scalar word does not justify a complete wide access"
    (run fixture[int 7]short=None && run tf[int 7]short=None);
  let huge,hblock=Memory.Mem.alloc mfn Z0 Ptrofs.modulus in
  check "symbolic huge allocation preserves target block"(hblock=block);
  let lastword=Ptrofs.repr(Camlcoq.Z.sub Ptrofs.modulus(z 4))in
  let wrapping={fixture with fn_code=tree[
    1,Istore(Mint32,Aglobal(g,lastword),[],p 1,p 2);
    2,store 0 1 3;3,Ireturn(Some(p 1))]}in
  check "wrapping source pair can complete"
    (run wrapping[int 7]huge<>None);
  check "widening must not silently cross the pointer modulus"
    (MemVector.selected wrapping=None && Memory.Mem.storev Mint64 huge
      (Globalenvs.Genv.symbol_address ge g lastword)(Vlong Int64.zero)=None);
  Printf.printf "{\"success\":true,\"performance_measured\":false,\"memory_cases\":%d,\"checks\":[%s]}\n"
    !cases(String.concat ","(List.map(Printf.sprintf"%S")(List.rev !check_names)))

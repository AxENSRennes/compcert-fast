(* Tests of production extracted overwritten-store elimination and real Mem.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open BinNums
open Datatypes
open Integers
open Maps
open Op
open RTL
open Registers
open Values

let checks = ref []
let check name condition =
  if not condition then failwith ("store elimination: " ^ name);
  checks := name :: !checks
let p = Camlcoq.P.of_int
let z = Camlcoq.Z.of_sint
let addr = Aindexed Int64.zero
let store src next = Istore(Mint32,addr,[p 1],p src,p next)
let tree entries = List.fold_left(fun t (key,value) -> PTree.set(p key)value t) PTree.empty entries
let base_code = tree [1,store 2 2;2,store 3 3;3,Ireturn(Some(p 3))]
let fixture = {fn_sig={sig_args=[Xptr;Xint;Xint];sig_res=Xint;sig_cc=cc_default};
               fn_params=List.map p [1;2;3];fn_stacksize=Z0;fn_entrypoint=p 1;fn_code=base_code}
let replace node instr f = {f with fn_code=PTree.set(p node)instr f.fn_code}
let stores f = PTree.fold(fun n _ -> function Istore _ -> n+1 | _ -> n) f.fn_code 0
let get node f = PTree.get(p node)f.fn_code
let reject name f =
  check (name ^ ": refused") (StoreElim.selected f=None);
  check (name ^ ": original retained") (StoreElim.transf_function f=f)
let require label = function Some x -> x | None -> failwith(label ^ " returned None")
let program : RTL.program = {prog_defs=[];prog_public=[];prog_main=p 1}
let ge = Globalenvs.Genv.globalenv program
let step f (pc,rs,m) =
  match PTree.get pc f.fn_code with
  | Some(Inop next) -> (next,rs,m),0
  | Some(Istore(chunk,address,args,src,next)) ->
      let loc=require "address" (Op.eval_addressing ge Vundef address (List.map(fun r -> Regmap.get r rs)args)) in
      let mem=require "store" (Memory.Mem.storev chunk m loc (Regmap.get src rs)) in
      (next,rs,mem),1
  | _ -> failwith "unexpected instruction in tested store fragment"
let execute_two f rs m =
  let s,n1=step f (f.fn_entrypoint,rs,m) in
  let (pc,rs',mem),n2=step f s in
  match PTree.get pc f.fn_code with
  | Some(Ireturn(Some r)) -> Regmap.get r rs',mem,n1+n2
  | _ -> failwith "expected return after store pair"
(* mem_access contains functions, so test exact contents and nextblock plus
   physically shared unchanged permission maps, not polymorphic equality. *)
let same_memory a b =
  a.Memory.Mem.mem_contents=b.Memory.Mem.mem_contents &&
  a.Memory.Mem.mem_access==b.Memory.Mem.mem_access &&
  a.Memory.Mem.nextblock=b.Memory.Mem.nextblock
let make_regs pointer first last =
  List.fold_left(fun rs (r,v) -> Regmap.set(p r)v rs) (Regmap.init Vundef)
    [1,pointer;2,first;3,last]
let int v = Vint(Int.repr(z v))

let () =
  let transformed=StoreElim.transf_function fixture in
  check "valid pair is selected" (StoreElim.selected fixture<>None);
  check "two stores become one actual store" (stores fixture=2 && stores transformed=1);
  check "first store is replaced by a no-op" (get 1 transformed=Some(Inop(p 2)));
  check "second store is retained exactly" (get 2 transformed=get 2 fixture);
  check "function metadata retained" (fixture.fn_sig=transformed.fn_sig && fixture.fn_params=transformed.fn_params && fixture.fn_entrypoint=transformed.fn_entrypoint && fixture.fn_stacksize=transformed.fn_stacksize);
  check "source-value register may also be an address register"
    (StoreElim.selected (replace 1 (store 1 2) fixture)<>None);
  reject "different address offset" (replace 2 (Istore(Mint32,Aindexed(Int64.repr(z 4)),[p 1],p 3,p 3)) fixture);
  reject "different memory chunk" (replace 2 (Istore(Mint64,addr,[p 1],p 3,p 3)) fixture);
  reject "different address register" (replace 2 (Istore(Mint32,addr,[p 4],p 3,p 3)) fixture);
  reject "second point is entry" {fixture with fn_entrypoint=p 2};
  reject "extra predecessor" (replace 4 (Inop(p 2)) fixture);
  reject "call-return predecessor" (replace 4 (Icall(signature_main,Coq_inr(p 9),[],p 5,p 2)) fixture);
  reject "second point self edge" (replace 2 (store 3 2) fixture);
  reject "coincident first and second points"
    {fixture with fn_entrypoint=p 3;fn_code=tree[1,store 2 1;3,Ireturn(Some(p 3))]};
  reject "undefined second point" (replace 1 (store 2 99) fixture);
  reject "intervening address change"
    {fixture with fn_code=tree[1,store 2 2;2,Iop(Oaddlimm(Int64.repr(z 4)),[p 1],p 1,p 4);4,store 3 3;3,Ireturn(Some(p 3))]};
  reject "first access is volatile"
    (replace 1 (Ibuiltin(EF_vstore Mint32,[BA(p 1);BA(p 2)],BR_none,p 2)) fixture);
  reject "second access is volatile"
    (replace 2 (Ibuiltin(EF_vstore Mint32,[BA(p 1);BA(p 3)],BR_none,p 3)) fixture);
  let m,block=Memory.Mem.alloc Memory.Mem.empty Z0 (z 16) in
  let pointer=Vptr(block,Ptrofs.zero) in
  let initial=require "initial memory" (Memory.Mem.storev Mint64 m pointer (Vlong Int64.zero)) in
  (* A shorter second write does not overwrite the first write's upper bytes.
     The guard must prevent a concrete wrong transformation. *)
  let different_size={fixture with fn_sig={fixture.fn_sig with sig_args=[Xptr;Xlong;Xint]};
      fn_code=tree[1,Istore(Mint64,addr,[p 1],p 2,p 2);2,store 3 3;3,Ireturn(Some(p 3))]} in
  let regs=make_regs pointer (Vlong(Int64.repr(z (-1)))) (int 17) in
  let _,original,lines=execute_two different_size regs initial in
  let _,checked,_=execute_two (StoreElim.transf_function different_size) regs initial in
  let _,wrong,_=execute_two (replace 1 (Inop(p 2)) different_size) regs initial in
  check "different-size guard prevents a real lost-byte semantic difference"
    (lines=2 && same_memory original checked &&
     Memory.Mem.loadv Mint64 original pointer<>Memory.Mem.loadv Mint64 wrong pointer &&
     StoreElim.selected different_size=None);
  let random=Random.State.make[|0x5354;2026|] in
  let values=[0;1;-1;127;128;255;256;32767;32768;-2147483647;2147483647] @
     List.init 2000 (fun _ -> Random.State.bits random - (1 lsl 29)) in
  List.iteri(fun index value ->
    let last=int value and first=int (value lxor 0x55555555) in
    let regs=make_regs pointer first last in
    let rv,sm,sc=execute_two fixture regs initial in
    let rv',tm,tc=execute_two transformed regs initial in
    check (Printf.sprintf "memory case %d same returned value" index) (rv=rv' && rv'=last);
    check (Printf.sprintf "memory case %d exact final contents/permissions" index) (same_memory sm tm);
    check (Printf.sprintf "memory case %d only final value remains" index) (Memory.Mem.loadv Mint32 tm pointer=Some last);
    check (Printf.sprintf "memory case %d eliminates one physical store" index) (sc=2 && tc=1)) values;
  (* Cover every chunk, including pointer fragments, NaN payloads and undefined
     encodings. The direct final store is the overwrite lemma's executable
     oracle; comparing only loaded values could miss byte-fragment differences. *)
  let chunks=[Mbool;Mint8signed;Mint8unsigned;Mint16signed;Mint16unsigned;
              Mint32;Mint64;Mfloat32;Mfloat64;Many32;Many64] in
  let stored_values=[Vundef;int (-1);int 1;Vlong(Int64.repr(z (-1)));
                     Vlong Int64.zero;pointer;
                     Vsingle(Floats.Float32.of_bits(Int.repr(z 0x7fc00001)));
                     Vfloat(Floats.Float.of_bits(Int64.repr(z (-1))))] in
  let chunk_cases=ref 0 in
  List.iteri(fun chunk_index chunk ->
    let source={fixture with fn_code=tree
      [1,Istore(chunk,addr,[p 1],p 2,p 2);
       2,Istore(chunk,addr,[p 1],p 3,p 3);3,Ireturn(Some(p 3))]} in
    let target=StoreElim.transf_function source in
    check (Printf.sprintf "chunk %d is accepted" chunk_index) (stores target=1);
    List.iteri(fun first_index first -> List.iteri(fun last_index last ->
      incr chunk_cases;
      let label=Printf.sprintf "chunk %d values %d/%d" chunk_index first_index last_index in
      let rs=make_regs pointer first last in
      let rv,sm,sc=execute_two source rs initial in
      let rv',tm,tc=execute_two target rs initial in
      let direct=require "direct final store" (Memory.Mem.storev chunk initial pointer last) in
      check (label^": exact memory equals direct final store")
        (same_memory sm tm && same_memory tm direct);
      check (label^": returned register preserved") (rv=last && rv'=last);
      check (label^": exactly one store removed") (sc=2 && tc=1)
    ) stored_values) stored_values) chunks;
  let cycle=replace 2 (store 3 1) fixture in
  let target_cycle=StoreElim.transf_function cycle in
  check "two-node store cycle transformed" (stores target_cycle=1);
  let regs=make_regs pointer (int 77) (int 123) in
  let rec prefix index source target =
    if index=200 then () else
    let ((pc,rs,mem)as source),_=step cycle source in
    let ((pc',rs',mem')as target),_=step target_cycle target in
    check (Printf.sprintf "cycle step %d preserves PC/registers" index)
      (pc=pc' && List.for_all(fun r -> Regmap.get(p r)rs=Regmap.get(p r)rs')[1;2;3]);
    if index mod 2=1 then
      check (Printf.sprintf "cycle step %d collapses memories after final store" index) (same_memory mem mem');
    prefix (index+1) source target
  in prefix 0 (p 1,regs,initial) (p 1,regs,initial);
  let freed=require "free" (Memory.Mem.free initial block Z0(z 16)) in
  let fails f=try ignore(execute_two f regs freed);false with Failure _ -> true in
  check "invalid memory cannot complete either source or target pair" (fails fixture && fails transformed);
  let names=List.rev !checks in
  Printf.printf "{\"success\":true,\"performance_measured\":false,\"memory_cases\":%d,\"all_chunk_cases\":%d,\"cycle_steps\":200,\"checks\":[%s]}\n"
    (List.length values) !chunk_cases (String.concat "," (List.map(Printf.sprintf "%S")names))

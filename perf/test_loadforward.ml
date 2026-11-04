(* Tests of the production extracted adjacent ordinary-load forwarding pass.
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
  if not condition then failwith ("load forwarding: " ^ name);
  checks := name :: !checks
let p = Camlcoq.P.of_int
let z = Camlcoq.Z.of_sint
let addr = Aindexed Int64.zero
let load dst next = Iload (Mint32, addr, [p 1], p dst, p next)
let tree entries = List.fold_left (fun t (key,value) -> PTree.set (p key) value t) PTree.empty entries
let base_code = tree [1,load 2 2; 2,load 3 3; 3,Ireturn (Some (p 3))]
let fixture = { fn_sig = { sig_args=[Xptr]; sig_res=Xint; sig_cc=cc_default };
                fn_params=[p 1]; fn_stacksize=Z0; fn_entrypoint=p 1; fn_code=base_code }
let replace node instr f = { f with fn_code=PTree.set (p node) instr f.fn_code }
let ordinary_loads f = PTree.fold (fun n _ -> function Iload _ -> n+1 | _ -> n) f.fn_code 0
let moves f = PTree.fold (fun n _ -> function Iop(Omove,_,_,_) -> n+1 | _ -> n) f.fn_code 0
let get node f = PTree.get (p node) f.fn_code
let reject name f =
  check (name ^ ": candidate refused") (LoadForward.selected f = None);
  check (name ^ ": original function retained") (LoadForward.transf_function f = f)

let require label = function Some x -> x | None -> failwith (label ^ " returned None")
let program : RTL.program = { prog_defs=[]; prog_public=[]; prog_main=p 1 }
let ge = Globalenvs.Genv.globalenv program

(* Execute exactly the tested RTL fragment, delegating all values/addresses/
   operations/memory to production CompCert modules. No host-C memory oracle. *)
let step f (pc,rs,m) =
  match PTree.get pc f.fn_code with
  | Some(Inop next) -> (next,rs,m),0,0
  | Some(Iload(chunk,address,args,dst,next)) ->
      let loc = require "address evaluation" (Op.eval_addressing ge Vundef address (List.map (fun r -> Regmap.get r rs) args)) in
      let value = require "memory load" (Memory.Mem.loadv chunk m loc) in
      (next,Regmap.set dst value rs,m),1,0
  | Some(Iop(op,args,dst,next)) ->
      let value = require "operation evaluation" (Op.eval_operation ge Vundef op (List.map (fun r -> Regmap.get r rs) args) m) in
      (next,Regmap.set dst value rs,m),0,(if op=Omove then 1 else 0)
  | _ -> failwith "unexpected instruction in tested execution fragment"

let execute_two f rs m =
  let state,l1,m1 = step f (f.fn_entrypoint,rs,m) in
  let (pc,rs',mem),l2,m2 = step f state in
  match PTree.get pc f.fn_code with
  | Some(Ireturn(Some r)) -> Regmap.get r rs',mem,l1+l2,m1+m2
  | _ -> failwith "expected return after the two ordinary instructions"

let () =
  let transformed = LoadForward.transf_function fixture in
  check "valid repeated load is selected" (LoadForward.selected fixture <> None);
  check "two source loads become one actual target load" (ordinary_loads fixture=2 && ordinary_loads transformed=1);
  check "target contains the introduced register move" (moves fixture=0 && moves transformed=1);
  check "first load is retained" (get 1 fixture=get 1 transformed);
  check "second load becomes the exact cached register move"
    (get 2 transformed=Some(Iop(Omove,[p 2],p 3,p 3)));
  check "function signature/entry/parameters/stack size are retained"
    (fixture.fn_sig=transformed.fn_sig && fixture.fn_params=transformed.fn_params &&
     fixture.fn_entrypoint=transformed.fn_entrypoint && fixture.fn_stacksize=transformed.fn_stacksize);
  reject "different address offset" (replace 2 (Iload(Mint32,Aindexed(Int64.repr(z 4)),[p 1],p 3,p 3)) fixture);
  reject "different load chunk" (replace 2 (Iload(Mint64,addr,[p 1],p 3,p 3)) fixture);
  reject "different address registers" (replace 2 (Iload(Mint32,addr,[p 4],p 3,p 3)) fixture);
  reject "first load overwrites an address register" (replace 1 (load 1 2) fixture);
  reject "target is a function entry" {fixture with fn_entrypoint=p 2};
  reject "extra ordinary predecessor" (replace 4 (Inop(p 2)) fixture);
  reject "extra call-return predecessor" (replace 4 (Icall(signature_main,Coq_inr(p 9),[],p 5,p 2)) fixture);
  reject "second load has a self edge" (replace 2 (load 3 2) fixture);
  reject "first and second program counters coincide"
    {fixture with fn_entrypoint=p 3; fn_code=tree [1,load 2 1;3,Ireturn(Some(p 2))]};
  reject "undefined second block" (replace 1 (load 2 99) fixture);
  reject "intervening store"
    {fixture with fn_code=tree [1,load 2 2;2,Istore(Mint32,addr,[p 1],p 2,p 4);4,load 3 3;3,Ireturn(Some(p 3))]};
  reject "second access is volatile builtin"
    (replace 2 (Ibuiltin(EF_vload Mint32,[BA(p 1)],BR(p 3),p 3)) fixture);
  reject "first access is volatile builtin"
    (replace 1 (Ibuiltin(EF_vload Mint32,[BA(p 1)],BR(p 2),p 2)) fixture);
  let m,block = Memory.Mem.alloc Memory.Mem.empty Z0 (z 16) in
  let pointer = Vptr(block,Ptrofs.zero) in
  let rs = Regmap.set (p 1) pointer (Regmap.init Vundef) in
  (* Negative semantic control: forwarding across a signedness change is
     observably wrong, even though the address and physical byte are equal. *)
  let signedness = { fixture with fn_code=tree
      [1,Iload(Mint8signed,addr,[p 1],p 2,p 2);
       2,Iload(Mint8unsigned,addr,[p 1],p 3,p 3);
       3,Ireturn(Some(p 3))] } in
  let byte_mem = require "byte store" (Memory.Mem.storev Mint8unsigned m pointer (Vint(Int.repr(z 255)))) in
  let correct,_,_,_ = execute_two signedness rs byte_mem in
  let checked,_,_,_ = execute_two (LoadForward.transf_function signedness) rs byte_mem in
  let forged = replace 2 (Iop(Omove,[p 2],p 3,p 3)) signedness in
  let wrong,_,_,_ = execute_two forged rs byte_mem in
  check "signed/unsigned same-address guard prevents a real semantic difference"
    (correct=Vint(Int.repr(z 255)) && checked=correct && wrong<>correct &&
     LoadForward.selected signedness=None);
  let values = [0;1;-1;127;128;255;256;32767;32768;-2147483647;2147483647] in
  let random = Random.State.make [|0x4c46;2026|] in
  let values = values @ List.init 2000 (fun _ -> Random.State.bits random - (1 lsl 29)) in
  List.iteri (fun index integer ->
    let input = Vint(Int.repr(z integer)) in
    let mem = require "initial store" (Memory.Mem.storev Mint32 m pointer input) in
    let sv,sm,sl,so = execute_two fixture rs mem in
    let tv,tm,tl,to_ = execute_two transformed rs mem in
    check (Printf.sprintf "real memory execution %d preserves returned value" index) (sv=tv && tv=input);
    check (Printf.sprintf "real memory execution %d preserves memory" index) (sm==tm && sm==mem);
    check (Printf.sprintf "real memory execution %d eliminates exactly one load" index) (sl=2 && tl=1 && so=0 && to_=1)) values;
  let chunks=[Mbool;Mint8signed;Mint8unsigned;Mint16signed;Mint16unsigned;
              Mint32;Mint64;Mfloat32;Mfloat64;Many32;Many64] in
  let stored_values=[Vundef;Vint(Int.repr(z (-1)));Vint Int.one;
                     Vlong(Int64.repr(z (-1)));Vlong Int64.zero;pointer;
                     Vsingle(Floats.Float32.of_bits(Int.repr(z 0x7fc00001)));
                     Vfloat(Floats.Float.of_bits(Int64.repr(z (-1))))] in
  let chunk_cases=ref 0 in
  List.iteri(fun chunk_index chunk ->
    let source={fixture with fn_code=tree
      [1,Iload(chunk,addr,[p 1],p 2,p 2);
       2,Iload(chunk,addr,[p 1],p 3,p 3);3,Ireturn(Some(p 3))]} in
    let target=LoadForward.transf_function source in
    check (Printf.sprintf "chunk %d is forwarded" chunk_index)
      (ordinary_loads target=1 && moves target=1);
    List.iteri(fun value_index stored ->
      incr chunk_cases;
      let label=Printf.sprintf "chunk %d stored value %d" chunk_index value_index in
      let mem=require "all-chunk initial store" (Memory.Mem.storev chunk m pointer stored) in
      let expected=require "all-chunk direct load" (Memory.Mem.loadv chunk mem pointer) in
      let sv,sm,sl,so=execute_two source rs mem in
      let tv,tm,tl,to_=execute_two target rs mem in
      check (label^": returns the direct memory result") (sv=expected && tv=expected);
      check (label^": exact memory retained") (sm==mem && tm==mem);
      check (label^": exactly one load becomes a move") (sl=2 && so=0 && tl=1 && to_=1)
    ) stored_values) chunks;
  let cycle = replace 2 (load 3 1) fixture in
  let target_cycle = LoadForward.transf_function cycle in
  check "two-node load cycle is transformed" (ordinary_loads target_cycle=1 && moves target_cycle=1);
  let mem = require "cycle store" (Memory.Mem.storev Mint32 m pointer (Vint(Int.repr(z 77)))) in
  let rec prefix n source target =
    if n=0 then () else
    let ((pc,rs,mem) as source),_,_ = step cycle source in
    let ((pc',rs',mem') as target),_,_ = step target_cycle target in
    check (Printf.sprintf "cyclic execution step %d preserves PC/value/memory" n)
      (pc=pc' && mem==mem' && List.for_all(fun r -> Regmap.get(p r)rs=Regmap.get(p r)rs') [1;2;3]);
    prefix (n-1) source target
  in prefix 200 (p 1,rs,mem) (p 1,rs,mem);
  let freed = require "free block" (Memory.Mem.free mem block Z0 (z 16)) in
  let fails f = try ignore(step f (p 1,rs,freed));false with Failure _ -> true in
  check "invalid first load fails in source and target" (fails fixture && fails transformed);
  let passed = List.rev !checks in
  Printf.printf "{\"success\":true,\"performance_measured\":false,\"memory_cases\":%d,\"all_chunk_cases\":%d,\"cycle_steps\":200,\"checks\":[%s]}\n"
    (List.length values) !chunk_cases (String.concat "," (List.map (Printf.sprintf "%S") passed))

(* Observe actual compiler RTL states; tracing has no authority over validation.
   Distributed under the repository's INRIA Non-Commercial License Agreement. *)
open AST
open Maps

let previous : RTL.program option ref = ref None

let functions program =
  List.filter_map (function id, Gfun (Internal f) -> Some(id,f) | _ -> None) program.prog_defs

let count predicate fn =
  PTree.fold (fun n _ instruction -> if predicate instruction then n+1 else n) fn.RTL.fn_code 0

let nodes = count (fun _ -> true)
let loads = count (function RTL.Iload _ -> true | _ -> false)
let narrow_stores = count (function RTL.Istore (Mint32,_,_,_,_) -> true | _ -> false)
let wide_stores = count (function RTL.Istore (Mint64,_,_,_,_) -> true | _ -> false)
let multiplies = count (function RTL.Iop ((Op.Omul | Op.Omull),_,_,_) -> true | _ -> false)
let vectors = count (function RTL.Ibuiltin (EF_builtin (name,_),_,_,_) ->
  List.mem name ["__builtin_cc_neon_add_u32x2"; "__builtin_cc_neon_sub_u32x2"; "__builtin_cc_neon_mul_u32x2"] | _ -> false)
let stores = count (function RTL.Istore _ -> true | _ -> false)

let loop_multiplies fn =
  let graph=PTree.fold (fun acc pc instr ->
    (Camlcoq.P.to_int pc, List.map Camlcoq.P.to_int (RTL.successors_instr instr))::acc) fn.RTL.fn_code [] in
  let members=Hashtbl.create (List.length graph) in
  List.iter (fun pc->Hashtbl.replace members pc ()) (ExperimentalOptions.cyclic_nodes graph);
  PTree.fold (fun n pc instr -> match instr with
    | RTL.Iop ((Op.Omul | Op.Omull),_,_,_) when Hashtbl.mem members (Camlcoq.P.to_int pc) -> n+1
    | _ -> n) fn.RTL.fn_code 0

let record pass before after =
  if ExperimentalOptions.enabled pass then begin
    let old_functions=functions before and new_functions=functions after in
    let changed=ref 0 and retained=ref 0 and old_nodes=ref 0 and new_nodes=ref 0 in
    let old_loads=ref 0 and new_loads=ref 0 and old_stores=ref 0 and new_stores=ref 0 in
    let old_narrow=ref 0 and new_narrow=ref 0 and old_wide=ref 0 and new_wide=ref 0 in
    let old_loop_multiplies=ref 0 and new_loop_multiplies=ref 0 in
    let old_multiplies=ref 0 and new_multiplies=ref 0 and old_vectors=ref 0 and new_vectors=ref 0 in
    List.iter (fun (id, old) ->
      match List.assoc_opt id new_functions with
      | None -> ()
      | Some current ->
          (* Mandatory LowerLong also renumbers unchanged functions. For the
             memory pass, count actual widening, not that renumbering. *)
          let transformed = if pass="memory-vector" then
            wide_stores current > wide_stores old && narrow_stores current < narrow_stores old
            else old<>current in
          if transformed then incr changed else incr retained;
          old_nodes:= !old_nodes + nodes old; new_nodes:= !new_nodes + nodes current;
          old_loads:= !old_loads + loads old; new_loads:= !new_loads + loads current;
          old_stores:= !old_stores + stores old; new_stores:= !new_stores + stores current;
          old_narrow:= !old_narrow + narrow_stores old; new_narrow:= !new_narrow + narrow_stores current;
          old_wide:= !old_wide + wide_stores old; new_wide:= !new_wide + wide_stores current;
          if pass="strength-reduce" then begin
            old_loop_multiplies:= !old_loop_multiplies + loop_multiplies old;
            new_loop_multiplies:= !new_loop_multiplies + loop_multiplies current end;
          old_multiplies:= !old_multiplies + multiplies old; new_multiplies:= !new_multiplies + multiplies current;
          old_vectors:= !old_vectors + vectors old; new_vectors:= !new_vectors + vectors current)
      old_functions;
    let note event value=ExperimentalOptions.note ~pass ~event value in
    if pass="strength-reduce" then begin
      note "loop-multiplies-before" !old_loop_multiplies; note "loop-multiplies-after" !new_loop_multiplies end;
    note "integer-multiplies-before" !old_multiplies; note "integer-multiplies-after" !new_multiplies;
    note "packed-builtins-before" !old_vectors; note "packed-builtins-after" !new_vectors;
    note "int32-stores-before" !old_narrow; note "int32-stores-after" !new_narrow;
    note "int64-stores-before" !old_wide; note "int64-stores-after" !new_wide;
    note "changed-functions" !changed; note "retained-functions" !retained;
    note "nodes-before" !old_nodes; note "nodes-after" !new_nodes;
    note "loads-removed" (max 0 (!old_loads - !new_loads));
    note "stores-removed" (max 0 (!old_stores - !new_stores));
    if pass="rtl-unroll2" || pass="rtl-unroll4" then begin
      let four=pass="rtl-unroll4" in
      let accepted=List.fold_left (fun n (_,f) -> if Experimental.accepted four f then n+1 else n) 0 old_functions in
      note "candidate-accepted" accepted;
      note "candidate-rejected-fallback" (List.length old_functions - accepted)
    end
  end

let observe passno program =
  if ExperimentalOptions.flags <> [] then begin
    let stage=Camlcoq.Z.to_int passno in
    if stage >= 50 && stage <= 75 then begin
      begin match !previous with
      | None -> ()
      | Some before ->
          begin match stage with
          | 75 -> record "loop-tile2d" before program
          | 74 -> record "memory-vector" before program
          | 71 -> record "loop-fusion" before program
          | 72 -> record "loop-interchange" before program
          | 73 -> record "loop-tile" before program
          | 64 -> record "licm-preheader" before program
          | 60 -> record "auto-neon" before program
          | 61 -> record "licm-pure" before program
          | 62 -> record "strength-reduce" before program
          | 63 -> record "loop-peel" before program
          | 51 -> record "hoist-constant" before program
          | 52 -> record "schedule-pure" before program
          | 53 -> record "load-forward" before program
          | 54 -> record "store-elim" before program
          | 55 -> record "loop-unswitch" before program
          | 56 -> record "rtl-unroll2" before program; record "rtl-unroll4" before program
          | 57 -> record "memory-cleanup" before program
          | _ -> () end
      end;
      previous:=Some program
    end
  end

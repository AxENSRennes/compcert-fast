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
let stores = count (function RTL.Istore _ -> true | _ -> false)

let record pass before after =
  if ExperimentalOptions.enabled pass then begin
    let old_functions=functions before and new_functions=functions after in
    let changed=ref 0 and retained=ref 0 and old_nodes=ref 0 and new_nodes=ref 0 in
    let old_loads=ref 0 and new_loads=ref 0 and old_stores=ref 0 and new_stores=ref 0 in
    List.iter (fun (id, old) ->
      match List.assoc_opt id new_functions with
      | None -> ()
      | Some current ->
          if old=current then incr retained else incr changed;
          old_nodes:= !old_nodes + nodes old; new_nodes:= !new_nodes + nodes current;
          old_loads:= !old_loads + loads old; new_loads:= !new_loads + loads current;
          old_stores:= !old_stores + stores old; new_stores:= !new_stores + stores current)
      old_functions;
    let note event value=ExperimentalOptions.note ~pass ~event value in
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
    if stage >= 50 && stage <= 57 then begin
      begin match !previous with
      | None -> ()
      | Some before ->
          begin match stage with
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

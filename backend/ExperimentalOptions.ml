(* Experimental, untrusted heuristic controls. Distributed under the
   repository's INRIA Non-Commercial License Agreement. The compiler's
   proved transformations and validators remain responsible for correctness. *)

let known_flags = ["small-inline"; "loop-spill"; "trace-layout";
                   "rtl-unroll2"; "rtl-unroll4"; "memory-cleanup";
                   "schedule-pure"; "hoist-constant"; "load-forward";
                   "arm64-combine"; "loop-unswitch"; "store-elim";
                   "neon-packed"; "licm-pure"; "strength-reduce"; "loop-peel"; "auto-neon"; "licm-preheader"; "memory-vector"; "loop-fusion"; "loop-interchange"; "loop-tile"; "loop-tile2d"]

let getenv name = try Sys.getenv name with Not_found -> ""

let flags =
  let raw = String.trim (getenv "COMPCERT_EXPERIMENTS") in
  if raw = "" then [] else begin
    let items = List.map String.trim (String.split_on_char ',' raw) in
    List.iter (fun name ->
      if not (List.mem name known_flags) then
        invalid_arg ("COMPCERT_EXPERIMENTS: unknown experiment '" ^ name ^
                     "'; supported: " ^ String.concat "," known_flags)) items;
    if List.mem "rtl-unroll2" items && List.mem "rtl-unroll4" items then
      invalid_arg "COMPCERT_EXPERIMENTS: rtl-unroll2 and rtl-unroll4 are mutually exclusive";
    List.sort_uniq String.compare items
  end

let enabled name = List.mem name flags

let scalar_enabled () = enabled "rtl-unroll2" || enabled "rtl-unroll4"
let unroll4_enabled () = enabled "rtl-unroll4"
let cleanup_enabled () = enabled "memory-cleanup"
let schedule_enabled () = enabled "schedule-pure"
let hoist_enabled () = enabled "hoist-constant"
let loadforward_enabled () = enabled "load-forward"
let select_enabled () = enabled "arm64-combine"
let unswitch_enabled () = enabled "loop-unswitch"
let storeelim_enabled () = enabled "store-elim"
let packed_neon_enabled () = enabled "neon-packed"

let counters : ((string * string), int) Hashtbl.t = Hashtbl.create 17

let trace =
  let path = getenv "COMPCERT_EXPERIMENT_TRACE" in
  if flags = [] || path = "" then None
  else Some (open_out_gen [Open_creat; Open_append; Open_text] 0o600 path)

let emit pass event count =
  match trace with
  | None -> ()
  | Some channel ->
      (* These names are fixed ASCII identifiers, so OCaml's quoted spelling
         is also valid JSON. No source strings or file paths are emitted. *)
      Printf.fprintf channel "{\"pass\":%S,\"event\":%S,\"count\":%d}\n%!"
        pass event count

let note ~pass ~event count =
  if enabled pass then begin
    let key = (pass, event) in
    let before = try Hashtbl.find counters key with Not_found -> 0 in
    let after = if count > max_int - before then max_int else before + count in
    Hashtbl.replace counters key after;
    emit pass event count
  end

let summary () =
  Hashtbl.fold (fun (pass, event) count acc -> (pass, event, count) :: acc)
    counters [] |> List.sort compare

let () = List.iter (fun pass -> emit pass "enabled" 1) flags

(* A nonrecursive SCC analysis, shared by loop-aware cost and layout oracles.
   Undefined targets are ignored. It has no semantic authority: a mistake can
   change heuristic quality, while the existing Coq validators still decide
   whether the resulting allocation/layout is safe. *)
let cyclic_nodes graph =
  let edges = Hashtbl.create (List.length graph) in
  let reverse = Hashtbl.create (List.length graph) in
  List.iter (fun (node, _) ->
    Hashtbl.replace edges node [];
    Hashtbl.replace reverse node []) graph;
  List.iter (fun (node, succs) ->
    let succs = List.filter (fun s -> Hashtbl.mem edges s) succs in
    Hashtbl.replace edges node succs;
    List.iter (fun s ->
      Hashtbl.replace reverse s (node :: Hashtbl.find reverse s)) succs) graph;
  let seen = Hashtbl.create (List.length graph) in
  let order = ref [] in
  List.iter (fun (start, _) ->
    let work = ref [start, false] in
    while !work <> [] do
      match !work with
      | [] -> ()
      | (node, finish) :: rest ->
          work := rest;
          if finish then order := node :: !order
          else if not (Hashtbl.mem seen node) then begin
            Hashtbl.add seen node ();
            work := List.fold_right (fun s acc -> (s, false) :: acc)
              (Hashtbl.find edges node) ((node, true) :: !work)
          end
    done) graph;
  Hashtbl.clear seen;
  let cyclic = ref [] in
  List.iter (fun start ->
    if not (Hashtbl.mem seen start) then begin
      let component = ref [] and work = ref [start] in
      while !work <> [] do
        match !work with
        | [] -> ()
        | node :: rest ->
            work := rest;
            if not (Hashtbl.mem seen node) then begin
              Hashtbl.add seen node ();
              component := node :: !component;
              work := Hashtbl.find reverse node @ !work
            end
      done;
      match !component with
      | [node] when not (List.mem node (Hashtbl.find edges node)) -> ()
      | nodes -> cyclic := nodes @ !cyclic
    end) !order;
  List.sort_uniq compare !cyclic

let vectorize_enabled () = enabled "auto-neon"
let licm_enabled () = enabled "licm-pure"
let strength_enabled () = enabled "strength-reduce"
let peel_enabled () = enabled "loop-peel"
let preheader_enabled () = enabled "licm-preheader"
let memvector_enabled () = enabled "memory-vector"
let fusion_enabled () = enabled "loop-fusion"
let interchange_enabled () = enabled "loop-interchange"
let tile_enabled () = enabled "loop-tile"
let tile2d_enabled () = enabled "loop-tile2d"

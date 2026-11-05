(* Experimental, untrusted heuristic controls. Distributed under the
   repository's INRIA Non-Commercial License Agreement. The compiler's
   proved transformations and validators remain responsible for correctness. *)

let known_flags = ["small-inline"; "loop-spill"; "trace-layout";
                   "memory-neon";
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

let enabled name =
  (* Internal trace labels for paths of the public memory-neon option. *)
  List.mem (if name="pointer-neon" || name="auto-pairs" then "memory-neon" else name) flags

let memoryneon_enabled () = enabled "memory-neon"

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

let packed_neon_names =
  ["__builtin_cc_neon_add_u32x2"; "__builtin_cc_neon_sub_u32x2";
   "__builtin_cc_neon_mul_u32x2"]

let counters : ((string * string), int) Hashtbl.t = Hashtbl.create 17

let write_event channel pass event count =
  (* Names are fixed ASCII identifiers. No source strings are emitted. *)
  Printf.fprintf channel "{\"pass\":%S,\"event\":%S,\"count\":%d}\n%!"
    pass event count

let trace_disabled = ref false
let disable_trace () = trace_disabled := true

let trace = lazy (
  let path = getenv "COMPCERT_EXPERIMENT_TRACE" in
  if !trace_disabled || flags = [] || path = "" then None
  else
    try
      let fd = Unix.openfile path
        [Unix.O_WRONLY; Unix.O_CREAT; Unix.O_APPEND; Unix.O_NONBLOCK; Unix.O_CLOEXEC]
        0o600 in
      let channel = Unix.out_channel_of_descr fd in
      try
        if (Unix.fstat fd).Unix.st_kind = Unix.S_REG then begin
          List.iter (fun pass -> write_event channel pass "enabled" 1) flags;
          Some channel
        end else begin
          close_out_noerr channel;
          None
        end
      with Sys_error _ | Unix.Unix_error _ -> close_out_noerr channel; None
    with Unix.Unix_error _ -> None)

let start_trace () = ignore (Lazy.force trace)

let emit pass event count =
  match Lazy.force trace with
  | None -> ()
  | Some channel ->
      try write_event channel pass event count with Sys_error _ -> ()

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

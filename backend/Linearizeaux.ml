(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open LTL
open Maps
open Camlcoq

(* Trivial enumeration, in decreasing order of PC *)

(***
let enumerate_aux f reach =
  positive_rec
    Coq_nil
    (fun pc nodes ->
      if PMap.get pc reach
      then Coq_cons (pc, nodes)
      else nodes)
    f.fn_nextpc
***)

(* More clever enumeration that flattens basic blocks *)

module IntSet = Set.Make(struct type t = int let compare = compare end)

(* Determine join points: reachable nodes that have > 1 predecessor *)

let join_points f =
  let reached = ref IntSet.empty in
  let reached_twice = ref IntSet.empty in
  let rec traverse pc =
    let npc = P.to_int pc in
    if IntSet.mem npc !reached then begin
      if not (IntSet.mem npc !reached_twice) then
        reached_twice := IntSet.add npc !reached_twice
    end else begin
      reached := IntSet.add npc !reached;
      match PTree.get pc f.fn_code with
      | None -> ()
      | Some b -> traverse_succs (successors_block b)
    end
  and traverse_succs = function
    | [] -> ()
    | [pc] -> traverse pc
    | pc :: l -> traverse pc; traverse_succs l
  in traverse f.fn_entrypoint; !reached_twice

(* Cut into reachable basic blocks, annotated with the min value of the PC *)

let basic_blocks f joins =
  let blocks = ref [] in
  let visited = ref IntSet.empty in
  (* start_block:
       pc is the function entry point
          or a join point
          or the successor of a conditional test *)
  let rec start_block pc =
    let npc = P.to_int pc in
    if not (IntSet.mem npc !visited) then begin
      visited := IntSet.add npc !visited;
      in_block [] max_int pc
    end
  (* in_block: add pc to block and check successors *)
  and in_block blk minpc pc =
    let npc = P.to_int pc in
    let blk = pc :: blk in
    let minpc = min npc minpc in
    match PTree.get pc f.fn_code with
    | None -> assert false
    | Some b ->
       let rec do_instr_list = function
       | [] -> assert false
       | Lbranch s :: _ -> next_in_block blk minpc s
       | Ltailcall (sig0, ros) :: _ -> end_block blk minpc
       | Lcond (cond, args, ifso, ifnot) :: _ ->
             end_block blk minpc; start_block ifso; start_block ifnot
       | Ljumptable(arg, tbl) :: _ ->
             end_block blk minpc; List.iter start_block tbl
       | Lreturn :: _ -> end_block blk minpc
       | instr :: b' -> do_instr_list b' in
       do_instr_list b
  (* next_in_block: check if join point and either extend block
     or start block *)
  and next_in_block blk minpc pc =
    let npc = P.to_int pc in
    if IntSet.mem npc joins
    then (end_block blk minpc; start_block pc)
    else in_block blk minpc pc
  (* end_block: record block that we just discovered *)
  and end_block blk minpc =
    blocks := (minpc, List.rev blk) :: !blocks
  in
    start_block f.fn_entrypoint; !blocks

(* Flatten basic blocks in decreasing order of minpc *)

let flatten_blocks blks =
  let cmp_minpc (mpc1, _) (mpc2, _) =
    if mpc1 = mpc2 then 0 else if mpc1 > mpc2 then -1 else 1
  in
    List.flatten (List.map snd (List.sort cmp_minpc blks))

(* Build the enumeration *)

let trace_blocks f blocks =
  let owner = Hashtbl.create (List.length blocks) in
  let table = Hashtbl.create (List.length blocks) in
  List.iter (fun (minpc, nodes) -> match nodes with
    | [] -> ()
    | head :: _ ->
        let key = P.to_int head in
        Hashtbl.replace table key (minpc, nodes);
        List.iter (fun pc -> Hashtbl.replace owner (P.to_int pc) key) nodes) blocks;
  let successors nodes =
    match List.rev nodes with
    | [] -> []
    | last :: _ ->
        match PTree.get last f.fn_code with
        | None -> []
        | Some block ->
            successors_block block
            |> List.filter_map (fun pc ->
                try Some (Hashtbl.find owner (P.to_int pc)) with Not_found -> None) in
  let graph = Hashtbl.fold
    (fun key (_, nodes) acc -> (key, successors nodes) :: acc) table [] in
  let cyclic = ExperimentalOptions.cyclic_nodes graph in
  let used = Hashtbl.create (List.length blocks) in
  let result = ref [] in
  let append_trace start =
    let current = ref (Some start) in
    while !current <> None do
      match !current with
      | None -> ()
      | Some key ->
          current := None;
          if not (Hashtbl.mem used key) then begin
            Hashtbl.add used key ();
            let _, nodes = Hashtbl.find table key in
            result := nodes :: !result;
            let available = List.filter (fun pc -> not (Hashtbl.mem used pc)) (successors nodes) in
            (* Prefer a cyclic successor before an acyclic exit. Otherwise
               prefer the false/fall-through edge supplied last by LTL. *)
            let preferred =
              List.filter (fun pc -> List.mem key cyclic && List.mem pc cyclic) available in
            match List.rev (if preferred = [] then available else preferred) with
            | next :: _ -> current := Some next
            | [] -> ()
          end
    done in
  (try append_trace (Hashtbl.find owner (P.to_int f.fn_entrypoint)) with Not_found -> ());
  let ordered = List.sort (fun (x, _) (y, _) -> compare y x) blocks in
  List.iter (fun (_, nodes) -> match nodes with
    | [] -> ()
    | head :: _ -> append_trace (P.to_int head)) ordered;
  List.flatten (List.rev !result)

let enumerate_aux f reach =
  let blocks = basic_blocks f (join_points f) in
  let baseline = flatten_blocks blocks in
  if not (ExperimentalOptions.enabled "trace-layout") then baseline
  else begin
    let candidate = trace_blocks f blocks in
    ExperimentalOptions.note ~pass:"trace-layout" ~event:"candidate" 1;
    if candidate <> baseline then
      ExperimentalOptions.note ~pass:"trace-layout" ~event:"changed-order" 1;
    candidate
  end

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

(** Coalesce adjacent ordinary 32-bit stores into one 64-bit memory write.
    Both lanes share their source, so undefined lanes remain correlated.
    Global offsets zero/four provide a checked alignment/no-wrap witness.
    This is a widening building block, not a loop-trip-count transformation. *)
Require Import Coqlib Maps AST Integers Registers Op RTL Schedule.
Record store_pair := Pair {
  first_pc: node; second_pc: node; global_id: ident;
  source_reg: reg; after_pc: node
}.
Definition fresh_reg (f: function): reg := Pos.succ (max_reg_function f).
Definition candidate_at (f: function) (a: node): option store_pair :=
  match f.(fn_code)!a with
  | Some(Istore Mint32 (Aglobal id ofs) nil r b) =>
      match f.(fn_code)!b with
      | Some(Istore Mint32 (Aglobal id2 ofs2) nil r2 s) =>
          if peq id id2 then if peq r r2 then
          if Ptrofs.eq ofs Ptrofs.zero then
          if Ptrofs.eq ofs2 (Ptrofs.repr 4) then
          if peq a b then None else
          if peq b f.(fn_entrypoint) then None else
          if Schedule.predecessor_check f a b then Some(Pair a b id r s) else None
          else None else None else None else None
      | _ => None end
  | _ => None end.
Fixpoint find_candidate (f: function) (items: list(node*instruction)): option store_pair :=
  match items with
  | nil => None
  | (pc,_)::rest => match candidate_at f pc with Some p => Some p | None => find_candidate f rest end
  end.
Definition selected (f: function): option store_pair :=
  let items:=PTree.elements f.(fn_code) in
  if Nat.leb(length items)512 then find_candidate f items else None.
Definition transf_instr_cached (f: function) (p: store_pair) (pc: node) (i: instruction): instruction :=
  if peq pc p.(first_pc) then
    Iop Omakelong (p.(source_reg)::p.(source_reg)::nil) (fresh_reg f) p.(second_pc)
  else if peq pc p.(second_pc) then
    Istore Mint64 (Aglobal p.(global_id) Ptrofs.zero) nil (fresh_reg f) p.(after_pc)
  else i.
Definition transf_instr (f: function) (pc: node) (i: instruction): instruction :=
  match selected f with Some p => transf_instr_cached f p pc i | None => i end.
Definition transf_function (f: function): function :=
  match selected f with
  | Some p => RTL.transf_function (transf_instr_cached f p) f
  | None => f end.
Definition transf_fundef := AST.transf_fundef transf_function.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.

Module Indirect.
(** Retain a global-address producer, then widen stores separated only by
    no-ops, self moves or the identical global-address reload. Its finite
    certificate proves alignment from the
    executed producer; no assumption is made about arbitrary pointer inputs. *)
Record region := Region {
  producer_pc: node; first_pc: node; path: list node; second_pc: node;
  after_pc: node; global_id: ident; base_reg: reg; source_reg: reg
}.
Definition transparent (id: ident) (base: reg) (i: instruction): option node :=
  match i with
  | Inop next => Some next
  | Iop Omove (r::nil) dst next => if peq r dst then Some next else None
  | Iop (Oaddrsymbol id2 ofs) nil dst next =>
      if peq id id2 then if peq base dst then if Ptrofs.eq ofs Ptrofs.zero
      then Some next else None else None else None
  | _ => None end.
Fixpoint scan_tail (f: function) (fuel: nat) (previous pc: node) (id: ident) (base src: reg)
    : option (list node * node * node) :=
  match fuel with
  | O => None
  | S rest =>
      if peq pc f.(fn_entrypoint) then None else
      if Schedule.predecessor_check f previous pc then
        match f.(fn_code)!pc with
        | None => None
        | Some i =>
          match transparent id base i with
          | Some next =>
              match scan_tail f rest pc next id base src with
              | Some(nodes,last,exit) => Some(pc::nodes,last,exit)
              | None => None end
          | None =>
              match i with
              | Istore Mint32 (Aindexed ofs) (r::nil) src2 next =>
                  if Int64.eq ofs (Int64.repr 4) then
                  if peq r base then if peq src src2 then Some(pc::nil,pc,next)
                  else None else None else None
              | _ => None end
          end
        end
      else None
  end.
Definition candidate_at (f: function) (producer: node): option region :=
  match f.(fn_code)!producer with
  | Some(Iop (Oaddrsymbol id ofs) nil base first) =>
      if Ptrofs.eq ofs Ptrofs.zero then
      if peq first f.(fn_entrypoint) then None else
      if Schedule.predecessor_check f producer first then
        match f.(fn_code)!first with
        | Some(Istore Mint32 (Aindexed delta) (r::nil) src next) =>
            if Int64.eq delta Int64.zero then if peq r base then
              match scan_tail f 32 first next id base src with
              | Some(nodes,last,exit) =>
                  if peq exit first then None else
                  if in_dec peq exit nodes then None else
                  Some(Region producer first nodes last exit id base src)
              | None => None end
            else None else None
        | _ => None end
      else None else None
  | _ => None end.
Fixpoint find_candidate (f: function) (items: list(node*instruction)): option region :=
  match items with
  | nil => None
  | (pc,_)::rest => match candidate_at f pc with Some p=>Some p|None=>find_candidate f rest end
  end.
Definition selected (f: function): option region :=
  let items:=PTree.elements f.(fn_code) in
  if Nat.leb(length items)512 then find_candidate f items else None.
Definition transf_instr_cached (f: function) (p: region) (pc: node) (i: instruction): instruction :=
  if peq pc p.(first_pc) then
    Iop Omakelong (p.(source_reg)::p.(source_reg)::nil) (fresh_reg f)
      (match p.(path) with hd::_=>hd|_=>p.(second_pc) end)
  else if peq pc p.(second_pc) then
    Istore Mint64(Aindexed Int64.zero)(p.(base_reg)::nil)(fresh_reg f)p.(after_pc)
  else i.
Definition transf_instr (f: function) (pc: node) (i: instruction): instruction :=
  match selected f with Some p=>transf_instr_cached f p pc i|None=>i end.
Definition transf_function (f: function): function :=
  match selected f with Some p=>RTL.transf_function(transf_instr_cached f p)f|None=>f end.
Definition transf_fundef := AST.transf_fundef transf_function.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.
End Indirect.

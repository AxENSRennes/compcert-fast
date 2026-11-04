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

(** Hoist one pure integer constant into a fresh entry temporary.
    This transformation never speculates a load, call, division or FP op. *)
Require Import Coqlib Maps AST Integers Op Registers RTL.

Definition fresh_reg (f: function) : reg := Pos.succ (max_reg_function f).
Definition fresh_node (f: function) : node := Pos.succ (max_pc_function f).

Fixpoint choose_in (items: list (node * instruction)) : option int :=
  match items with
  | nil => None
  | (_, Iop (Ointconst n) nil _ _) :: _ => Some n
  | _ :: rest => choose_in rest
  end.
(* Bounded cycle discovery is a profitability hint only. Safety is independent
   of its precision: every selected value is a pure integer constant. *)
Definition search_fuel (f: function) : nat :=
  S (PTree.fold (fun n _ i => S (length (successors_instr i) + n)) f.(fn_code) 1%nat).
Fixpoint reaches (fuel: nat) (f: function) (goal: node)
                 (todo visited: list node) : bool :=
  match fuel, todo with
  | S fuel', pc :: rest =>
      if peq pc goal then true else
      if in_dec peq pc visited then reaches fuel' f goal rest visited else
      match f.(fn_code)!pc with
      | Some i => reaches fuel' f goal (successors_instr i ++ rest) (pc :: visited)
      | None => reaches fuel' f goal rest (pc :: visited)
      end
  | _, _ => false
  end.
Definition cyclic (f: function) (pc: node) (i: instruction) : bool :=
  reaches (Nat.min 128 (search_fuel f)) f pc (successors_instr i) nil.
(* Cycle discovery is a bounded profitability hint, independent of semantic
   preservation. Scan at most 32 integer literals and visit at most 128 work
   items for each. Cache the graph-derived fuel once for the entire scan.
   If no cyclic literal is found, [chosen] safely selects the first literal. *)
Fixpoint choose_cyclic_bounded (f: function) (graph_fuel candidates: nat)
    (items: list (node * instruction)) {struct items} : option int :=
  match items with
  | nil => None
  | (pc, i) :: rest =>
      match i with
      | Iop (Ointconst n) nil _ _ =>
          match candidates with
          | O => None
          | S remaining =>
              if reaches graph_fuel f pc (successors_instr i) nil
              then Some n else choose_cyclic_bounded f graph_fuel remaining rest
          end
      | _ => choose_cyclic_bounded f graph_fuel candidates rest
      end
  end.
Definition choose_cyclic (f: function) (items: list (node * instruction)) : option int :=
  choose_cyclic_bounded f (Nat.min 128 (search_fuel f)) 32 items.
Definition chosen (f: function) : option int :=
  let items := PTree.elements f.(fn_code) in
  (* A function-wide temporary can make allocation expensive in large CFGs.
     This conservative compilability guard leaves those functions unchanged. *)
  if Nat.leb (length items) 512 then
    match choose_cyclic f items with
    | Some n => Some n
    | None => choose_in items
    end
  else None.

Definition transf_instr (f: function) (i: instruction) : instruction :=
  match i with
  | Iop (Ointconst m) nil r s =>
      match chosen f with
      | Some n => if Int.eq n m then Iop Omove (fresh_reg f :: nil) r s else i
      | None => i
      end
  | _ => i
  end.

(* The executable map receives cached values: selecting a literal and finding
   a fresh register traverse the whole function and must not run per node. *)
Definition transf_instr_cached (n: int) (temporary: reg) (i: instruction) : instruction :=
  match i with
  | Iop (Ointconst m) nil r s =>
      if Int.eq n m then Iop Omove (temporary :: nil) r s else i
  | _ => i
  end.

Definition hoisted (f: function) (n: int) : function :=
  let temporary := fresh_reg f in
  let entry := fresh_node f in
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (PTree.set entry (Iop (Ointconst n) nil temporary f.(fn_entrypoint))
      (PTree.map1 (transf_instr_cached n temporary) f.(fn_code)))
    entry.
Definition transf_function (f: function) : function :=
  match chosen f with Some n => hoisted f n | None => f end.
Definition transf_fundef (f: fundef) : fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program) : program := AST.transform_program transf_fundef p.

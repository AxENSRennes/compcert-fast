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

(** Adjacent overwritten ordinary-store elimination, guarded by a finite CFG check. *)
Require Import Coqlib Maps AST Registers Op RTL.

Record store_pair := Store_pair {
  first_pc: node; second_pc: node; store_chunk: memory_chunk;
  store_addr: addressing; store_args: list reg;
  first_src: reg; second_src: reg; after_pc: node
}.

Definition unique_predecessor (f: function) (a b: node) :=
  forallb (fun entry =>
    if existsb (peq b) (successors_instr (snd entry))
    then peq (fst entry) a else true) (PTree.elements f.(fn_code)).

Definition candidate_at (f: function) (a: node) : option store_pair :=
  match f.(fn_code)!a with
  | Some (Istore chunk addr args r1 b) =>
      match f.(fn_code)!b with
      | Some (Istore chunk2 addr2 args2 r2 s) =>
          if chunk_eq chunk chunk2 then
          if eq_addressing addr addr2 then
          if list_eq_dec peq args args2 then
          if negb (peq a b) && negb (peq b f.(fn_entrypoint)) &&
             unique_predecessor f a b
          then Some (Store_pair a b chunk addr args r1 r2 s)
          else None else None else None else None
      | _ => None
      end
  | _ => None
  end.

Fixpoint find_candidate (f: function) (entries: list (node * instruction)) :=
  match entries with
  | nil => None
  | (a, _) :: tail =>
      match candidate_at f a with
      | Some p => Some p
      | None => find_candidate f tail
      end
  end.
Definition selected f := find_candidate f (PTree.elements f.(fn_code)).
Definition is_store i := match i with Istore _ _ _ _ _ => true | _ => false end.
Definition transf_instr f pc i :=
  match selected f, i with
  | Some p, Istore _ _ _ _ _ =>
      if peq pc p.(first_pc)
      then Inop p.(second_pc)
      else i
  | _, _ => i
  end.
Definition transf_function f :=
  match selected f with
  | None => f
  | Some _ => RTL.transf_function (transf_instr f) f
  end.
Definition transf_fundef := AST.transf_fundef transf_function.
Definition transf_program (p: program) := AST.transform_program transf_fundef p.

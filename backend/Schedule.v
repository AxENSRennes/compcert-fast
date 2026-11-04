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

(* Experimental scheduling of one independent adjacent RTL operation pair.
   Distributed under the INRIA Non-Commercial License Agreement. *)
Require Import Coqlib Maps AST Integers Op Registers RTL.

Record scheduled_pair : Type := mkpair {
  first_pc : node;
  second_pc : node;
  first_op : operation;
  first_args : list reg;
  first_dst : reg;
  second_op : operation;
  second_args : list reg;
  second_dst : reg;
  after_pc : node
}.

Definition predecessor_check (f: function) (a b: node) : bool :=
  forallb (fun item =>
    if in_dec peq b (successors_instr (snd item))
    then if peq (fst item) a then true else false
    else true) (PTree.elements (fn_code f)).

Definition validate_candidate (f: function) (a b: node) : option scheduled_pair :=
  match (fn_code f)!a, (fn_code f)!b with
  | Some (Iop op1 args1 dst1 next), Some (Iop op2 args2 dst2 after) =>
      if peq next b then
      if peq a b then None else
      if peq (fn_entrypoint f) b then None else
      if peq dst1 dst2 then None else
      if in_dec peq dst1 args2 then None else
      if in_dec peq dst2 args1 then None else
      if predecessor_check f a b
      then Some (mkpair a b op1 args1 dst1 op2 args2 dst2 after)
      else None
      else None
  | _, _ => None
  end.

Fixpoint find_candidate (f: function) (nodes: list node) : option scheduled_pair :=
  match nodes with
  | nil => None
  | pc :: tail =>
      match (fn_code f)!pc with
      | Some (Iop _ _ _ next) =>
          match validate_candidate f pc next with
          | Some plan => Some plan
          | None => find_candidate f tail
          end
      | _ => find_candidate f tail
      end
  end.

Definition selected_pair (f: function) :=
  find_candidate f (List.map (@fst node instruction) (PTree.elements (fn_code f))).

Definition apply_pair (f: function) (pair: scheduled_pair) : function :=
  mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
    (PTree.set (first_pc pair)
       (Iop (second_op pair) (second_args pair) (second_dst pair) (second_pc pair))
       (PTree.set (second_pc pair)
         (Iop (first_op pair) (first_args pair) (first_dst pair) (after_pc pair))
         (fn_code f)))
    (fn_entrypoint f).

Definition transf_function (f: function) : function :=
  match selected_pair f with Some plan => apply_pair f plan | None => f end.

Definition transf_fundef (fd: fundef) : fundef := AST.transf_fundef transf_function fd.
Definition transf_program (p: program) : program := transform_program transf_fundef p.

(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Automatic two-lane SLP for correlated 32-bit affine expressions.
    The shared input is essential: both scalar lanes are defined together,
    so packing cannot lose a defined lane when the other lane is undefined.
    No source builtin, load speculation, alias assumption or new instruction
    specification is used. This is not a general memory-loop vectorizer. *)
From Coq Require Import String.
Require Import Coqlib Maps AST Integers Op Registers RTL Schedule.
Local Open Scope string_scope.
Local Open Scope asttyp_scope.

Record vector_pair : Type := mkpair {
  first_pc: node;
  second_pc: node;
  source_reg: reg;
  first_imm: int;
  second_imm: int;
  first_dst: reg;
  second_dst: reg;
  after_pc: node
}.

Definition input_reg (f: function): reg := Pos.succ (max_reg_function f).
Definition constant_reg (f: function): reg := Pos.succ (input_reg f).
Definition result_reg (f: function): reg := Pos.succ (constant_reg f).
Definition constant_pc (f: function): node := Pos.succ (max_pc_function f).
Definition builtin_pc (f: function): node := Pos.succ (constant_pc f).
Definition extract_pc (f: function): node := Pos.succ (builtin_pc f).

Definition packed_constant (plan: vector_pair): int64 :=
  Int64.ofwords plan.(second_imm) plan.(first_imm).
Definition packed_builtin : external_function :=
  EF_builtin "__builtin_cc_neon_add_u32x2" [Xlong; Xlong ---> Xlong].

Definition validate_candidate (f: function) (a b: node): option vector_pair :=
  match f.(fn_code)!a, f.(fn_code)!b with
  | Some (Iop (Oaddimm n1) (r1 :: nil) d1 next),
    Some (Iop (Oaddimm n2) (r2 :: nil) d2 after) =>
      if peq next b then
      if peq r1 r2 then
      if peq a b then None else
      if peq f.(fn_entrypoint) b then None else
      if peq d1 r1 then None else
      if peq d1 d2 then None else
      if Schedule.predecessor_check f a b
      then Some (mkpair a b r1 n1 n2 d1 d2 after)
      else None
      else None else None
  | _, _ => None
  end.

Fixpoint find_candidate (f: function) (items: list (node * instruction)) : option vector_pair :=
  match items with
  | nil => None
  | (pc, Iop (Oaddimm _) (_ :: nil) _ next) :: rest =>
      match validate_candidate f pc next with
      | Some plan => Some plan
      | None => find_candidate f rest
      end
  | _ :: rest => find_candidate f rest
  end.

Definition selected_pair (f: function) :=
  let items := PTree.elements f.(fn_code) in
  if Nat.leb (length items) 512 then find_candidate f items else None.

Definition apply_pair (f: function) (plan: vector_pair): function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (PTree.set plan.(first_pc)
      (Iop Omakelong (plan.(source_reg) :: plan.(source_reg) :: nil)
           (input_reg f) (constant_pc f))
    (PTree.set (constant_pc f)
      (Iop (Olongconst (packed_constant plan)) nil (constant_reg f) (builtin_pc f))
    (PTree.set (builtin_pc f)
      (Ibuiltin packed_builtin (BA (input_reg f) :: BA (constant_reg f) :: nil)
                (BR (result_reg f)) (extract_pc f))
    (PTree.set (extract_pc f)
      (Iop Olowlong (result_reg f :: nil) plan.(first_dst) plan.(second_pc))
    (PTree.set plan.(second_pc)
      (Iop Ohighlong (result_reg f :: nil) plan.(second_dst) plan.(after_pc))
      f.(fn_code))))))
    f.(fn_entrypoint).

Definition transf_function (f: function): function :=
  match selected_pair f with Some plan => apply_pair f plan | None => f end.
Definition transf_fundef (fd: fundef): fundef := AST.transf_fundef transf_function fd.
Definition transf_program (p: program): program := transform_program transf_fundef p.

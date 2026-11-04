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

(** Eager motion of total, memory-independent loop-invariant operations.
    Operands must never be assigned in the function. Operations are evaluated
    once into a fresh entry temporary; original destinations remain untouched
    until the corresponding original instruction executes. *)
Require Import Coqlib Maps AST Integers Op Registers RTL HoistConst.

Definition fresh_reg (f: function) : reg := Pos.succ (max_reg_function f).
Definition fresh_node (f: function) : node := Pos.succ (max_pc_function f).

(** Totality includes undefined input values. Partial integer division,
    float-to-integer conversions and rounded shifts are deliberately absent. *)
Definition total_arity (op: operation) (n: nat) : bool :=
  match op with
  | Ointconst _ | Olongconst _ | Ofloatconst _ | Osingleconst _
  | Oaddrsymbol _ _ | Oaddrstack _ => Nat.eqb n 0
  | Omove | Oshift _ _ | Oaddimm _ | Oneg | Onegshift _ _
  | Oandimm _ | Oorimm _ | Oxorimm _ | Onot | Onotshift _ _
  | Ozext _ | Osext _ | Oshlzext _ _ | Oshlsext _ _ | Ozextshr _ _ | Osextshr _ _
  | Oshiftl _ _ | Oextend _ _ | Olowlong | Ohighlong | Oaddlimm _ | Onegl
  | Oneglshift _ _ | Oandlimm _ | Oorlimm _ | Oxorlimm _ | Onotl | Onotlshift _ _
  | Ozextl _ | Osextl _ | Oshllzext _ _ | Oshllsext _ _ | Ozextshrl _ _ | Osextshrl _ _
  | Onegf | Oabsf | Onegfs | Oabsfs | Osingleoffloat | Ofloatofsingle => Nat.eqb n 1
  | Oadd | Oaddshift _ _ | Osub | Osubshift _ _ | Omul
  | Oand | Oandshift _ _ | Oor | Oorshift _ _ | Oxor | Oxorshift _ _
  | Obic | Obicshift _ _ | Oorn | Oornshift _ _ | Oeqv | Oeqvshift _ _
  | Oshl | Oshr | Oshru | Omakelong | Oaddl | Oaddlshift _ _ | Oaddlext _ _
  | Osubl | Osublshift _ _ | Osublext _ _ | Omull | Omullhs | Omullhu
  | Oandl | Oandlshift _ _ | Oorl | Oorlshift _ _ | Oxorl | Oxorlshift _ _
  | Obicl | Obiclshift _ _ | Oornl | Oornlshift _ _ | Oeqvl | Oeqvlshift _ _
  | Oshll | Oshrl | Oshrlu | Oaddf | Osubf | Omulf | Odivf
  | Oaddfs | Osubfs | Omulfs | Odivfs => Nat.eqb n 2
  | Omuladd | Omulsub | Omulladd | Omullsub => Nat.eqb n 3
  | Ocmp _ => true
  | Osel _ _ => Nat.leb 2 n
  | _ => false
  end.
Definition worth_hoisting (op: operation) : bool :=
  match op with Omove | Ointconst _ | Olongconst _ | Ofloatconst _ | Osingleconst _ => false | _ => true end.
Definition immutable (f: function) (r: reg) : bool :=
  forallb (fun kv => match instr_defs (snd kv) with
                    | Some dst => if peq dst r then false else true
                    | None => true end) (PTree.elements f.(fn_code)).
Record invariant := mkinvariant { invariant_op: operation; invariant_args: list reg }.
Definition eligible (f: function) (op: operation) (args: list reg) : bool :=
  negb (op_depends_on_memory op) && total_arity op (length args) &&
  forallb (immutable f) args && worth_hoisting op.
Fixpoint choose_in (f: function) (fuel: nat) (items: list (node * instruction)) {struct items}
  : option invariant :=
  match items with
  | nil => None
  | (pc,i) :: rest =>
      match i with
      | Iop op args dst next =>
          match fuel with
          | O => None
          | S remaining =>
              if eligible f op args && HoistConst.cyclic f pc i
              then Some (mkinvariant op args) else choose_in f remaining rest
          end
      | _ => choose_in f fuel rest
      end
  end.
Definition chosen (f: function) : option invariant :=
  let items := PTree.elements f.(fn_code) in
  if Nat.leb (length items) 512 then choose_in f 32 items else None.
Definition transf_instr_cached (b: invariant) (temporary: reg) (i: instruction) : instruction :=
  match i with
  | Iop op args dst next =>
      if Op.eq_operation op b.(invariant_op) then
      if list_eq_dec peq args b.(invariant_args) then Iop Omove (temporary :: nil) dst next else i
      else i
  | _ => i
  end.
Definition transf_instr (f: function) (i: instruction) : instruction :=
  match i with
  | Iop op args dst next =>
      match chosen f with Some b => transf_instr_cached b (fresh_reg f) i | None => i end
  | _ => i
  end.
Definition hoisted (f: function) (b: invariant) : function :=
  let temporary := fresh_reg f in let entry := fresh_node f in
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize)
    (PTree.set entry (Iop b.(invariant_op) b.(invariant_args) temporary f.(fn_entrypoint))
      (PTree.map1 (transf_instr_cached b temporary) f.(fn_code))) entry.
Definition transf_function (f: function) : function :=
  match chosen f with Some b => hoisted f b | None => f end.
Definition transf_fundef (f: fundef) : fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program) : program := AST.transform_program transf_fundef p.

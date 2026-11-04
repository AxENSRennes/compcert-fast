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

(** Strength reduction for modular integer induction recurrences.
    A fresh accumulator tracks [induction * factor], including literal resets
    of either input. Only fixed-step updates of the induction are accepted. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Experimental HoistConst.

Record recurrence := mkrecurrence {
  induction_reg: reg;
  factor_reg: reg;
  induction_step: int
}.
Definition fresh_acc (f: function): reg := Pos.succ (max_reg_function f).
Definition fresh_delta (f: function): reg := Pos.succ (fresh_acc f).
Definition allowed_definition (c: recurrence) (i: instruction): bool :=
  match instr_defs i with
  | None => true
  | Some dst =>
      if peq dst (induction_reg c) then
        match i with
        | Iop (Ointconst _) nil _ _ => true
        | Iop (Oaddimm n) (r :: nil) _ _ =>
            if peq r (induction_reg c) then Int.eq n (induction_step c) else false
        | _ => false
        end
      else if peq dst (factor_reg c) then
        match i with Iop (Ointconst _) nil _ _ => true | _ => false end
      else true
  end.
Definition valid (f: function) (c: recurrence): bool :=
  if peq (induction_reg c) (factor_reg c) then false else
  if plt (induction_reg c) (fresh_acc f) then
  if plt (factor_reg c) (fresh_acc f) then
    forallb (fun kv => allowed_definition c (snd kv)) (PTree.elements f.(fn_code))
  else false else false.
Fixpoint choose_factor (f: function) (ind: reg) (step: int)
    (items: list (node * instruction)): option recurrence :=
  match items with
  | nil => None
  | (_, Iop Omul (r :: k :: nil) _ _) :: rest =>
      if peq r ind then
        let c := mkrecurrence ind k step in
        if valid f c then Some c else choose_factor f ind step rest
      else choose_factor f ind step rest
  | _ :: rest => choose_factor f ind step rest
  end.
Fixpoint choose_update (f: function) (fuel: nat)
    (items: list (node * instruction)): option recurrence :=
  match fuel, items with
  | S remaining, (pc, Iop (Oaddimm n) (r :: nil) dst s) :: rest =>
      if peq r dst then
        if HoistConst.cyclic f pc (Iop (Oaddimm n) (r :: nil) dst s) then
          match choose_factor f r n (PTree.elements f.(fn_code)) with
          | Some c => Some c
          | None => choose_update f remaining rest
          end
        else choose_update f remaining rest
      else choose_update f remaining rest
  | S remaining, _ :: rest => choose_update f remaining rest
  | _, _ => None
  end.
Definition chosen (f: function): option recurrence :=
  let items := PTree.elements f.(fn_code) in
  if Nat.leb (length items) 512 then choose_update f 128 items else None.

Definition base (pc: node): node := xO (xO pc).
Definition after1 (pc: node): node := xI (xO pc).
Definition after2 (pc: node): node := xO (xI pc).
Inductive action := Default | Multiply | Advance | ResetInd | ResetFactor.
Definition classify (c: recurrence) (i: instruction): action :=
  match i with
  | Iop op args dst _ =>
      if peq dst (induction_reg c) then
        match op,args with
        | Oaddimm _, _ :: nil => Advance
        | Ointconst _, nil => ResetInd
        | _,_ => Default
        end
      else if peq dst (factor_reg c) then
        match op,args with Ointconst _, nil => ResetFactor | _,_ => Default end
      else
        match op,args with
        | Omul,r :: k :: nil =>
            if peq r (induction_reg c) then
            if peq k (factor_reg c) then Multiply else Default else Default
        | _,_ => Default
        end
  | _ => Default
  end.
Definition first_instr (f: function) (c: recurrence) (pc: node) (i: instruction): instruction :=
  match classify c i,i with
  | Multiply,Iop _ _ dst s => Iop Omove (fresh_acc f :: nil) dst (base s)
  | Advance,Iop op args dst _ | ResetInd,Iop op args dst _ | ResetFactor,Iop op args dst _ =>
      Iop op args dst (after1 pc)
  | _,_ => Experimental.map_successors base i
  end.
Definition next_instr (f: function) (c: recurrence) (pc: node) (i: instruction): instruction :=
  match classify c i,i with
  | Advance,Iop _ _ _ s => Iop Oadd (fresh_acc f :: fresh_delta f :: nil) (fresh_acc f) (base s)
  | ResetInd,Iop _ _ _ s => Iop Omul (induction_reg c :: factor_reg c :: nil) (fresh_acc f) (base s)
  | ResetFactor,Iop (Ointconst n) _ _ _ =>
      Iop (Ointconst (Int.mul (induction_step c) n)) nil (fresh_delta f) (after2 pc)
  | _,_ => Inop (base pc)
  end.
Definition last_instr (f: function) (c: recurrence) (pc: node) (i: instruction): instruction :=
  match classify c i,i with
  | ResetFactor,Iop _ _ _ s => Iop Omul (induction_reg c :: factor_reg c :: nil) (fresh_acc f) (base s)
  | _,_ => Inop (base pc)
  end.
Definition reduced (f: function) (c: recurrence): function :=
  let code := fn_code f in
  let init1 := Iop (Ointconst (induction_step c)) nil (fresh_delta f) 2%positive in
  let init2 := Iop Omul (fresh_delta f :: factor_reg c :: nil) (fresh_delta f) 3%positive in
  let init3 := Iop Omul (induction_reg c :: factor_reg c :: nil) (fresh_acc f) (base (fn_entrypoint f)) in
  mkfunction (fn_sig f) (fn_params f) (fn_stacksize f)
    (PTree.Node
      (PTree.Node (PTree.map (first_instr f c) code) (Some init2) (PTree.map (last_instr f c) code))
      (Some init1)
      (PTree.Node (PTree.map (next_instr f c) code) (Some init3) (PTree.empty instruction))) 1%positive.
Definition transf_function (f: function): function :=
  match chosen f with Some c => reduced f c | None => f end.
Definition label (f: function) (pc: node): node :=
  match chosen f with Some _ => base pc | None => pc end.
Definition transf_fundef (f: fundef): fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program): program := AST.transform_program transf_fundef p.

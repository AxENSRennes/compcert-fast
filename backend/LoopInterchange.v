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

(** Proposed interchange of two constant-counter rectangular pure loops.
    This generator has no semantic authority: LoopFusion.validate_function
    symbolically checks both entire functions and rejects unsafe schedules.
    Both loops remain loops; the nesting and induction-update edges change. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Experimental LoopFusion.
Record rectangle := Rectangle {
  outer_init: node; outer_test: node; inner_init: node; inner_test: node;
  outer_update: node; inner_update: node; body_entry: node; exit_node: node;
  outer_reg: reg; inner_reg: reg; outer_cond: condition; inner_cond: condition;
  post_tested: bool
}.
Definition immediate_condition (c: condition): bool :=
  match c with Ccompimm _ _ | Ccompuimm _ _ => true | _ => false end.
Fixpoint find_update (f: function) (r: reg) (header: node)
    (items: list(node * instruction)): option node :=
  match items with
  | nil => None
  | (pc,Iop (Oaddimm n) (rin :: nil) dst next)::rest =>
      if peq r rin then if peq r dst then if peq next header then
        if Int.eq n Int.one then Some pc else find_update f r header rest
      else find_update f r header rest else find_update f r header rest else find_update f r header rest
  | _::rest => find_update f r header rest
  end.
Definition detect (f: function) (init: node): option rectangle :=
  match (fn_code f)!init with
  | Some(Iop (Ointconst z) nil ri hi) =>
    if Int.eq z Int.zero then
    match (fn_code f)!hi with
    | Some(Icond ci (rin::nil) ij exit) =>
      if peq ri rin then if immediate_condition ci then
      match (fn_code f)!ij with
      | Some(Iop (Ointconst zinner) nil rj hj) =>
        if Int.eq zinner Int.zero then if peq ri rj then None else
        match (fn_code f)!hj with
        | Some(Icond cj (rjin::nil) body ui) =>
          if peq rj rjin then if immediate_condition cj then
          match (fn_code f)!ui with
          | Some(Iop (Oaddimm one) (risrc::nil) ridst hiout) =>
            if peq ri risrc then if peq ri ridst then if peq hi hiout then if Int.eq one Int.one then
            match find_update f rj hj (PTree.elements(fn_code f)) with
            | Some uj => Some(Rectangle init hi ij hj ui uj body exit ri rj ci cj false)
            | None => None end
            else None else None else None else None
          | _ => None end
          else None else None
        | _ => None end
        else None
      | _ => None end
      else None else None
    | _ => None end
    else None
  | _ => None end.
(** Constant propagation normally rotates statically nonempty C for-loops.
    Recognize that post-tested form too; both schedules retain their own tests. *)
Definition post_update (f: function) (oi ij: node) (ri rj: reg) (body: node)
    (uj: node) (i: instruction): option rectangle :=
  match i with
  | Iop (Oaddimm onej) (rjin::nil) rjout hj =>
    if peq rj rjin then if peq rj rjout then if Int.eq onej Int.one then
    match (fn_code f)!hj with
    | Some(Icond cj (rjtest::nil) bodytest ui) =>
      if peq rj rjtest then if peq body bodytest then if immediate_condition cj then
      match (fn_code f)!ui with
      | Some(Iop (Oaddimm onei) (riin::nil) riout hi) =>
        if peq ri riin then if peq ri riout then if Int.eq onei Int.one then
        match (fn_code f)!hi with
        | Some(Icond ci (ritest::nil) ijtest exit) =>
          if peq ri ritest then if peq ij ijtest then if immediate_condition ci
          then Some(Rectangle oi hi ij hj ui uj body exit ri rj ci cj true)
          else None else None else None
        | _=>None end
        else None else None else None
      | _=>None end
      else None else None else None
    | _=>None end
    else None else None else None
  | _=>None end.
Fixpoint find_post_update (f: function) (oi ij: node) (ri rj: reg) (body: node)
    (items: list(node*instruction)): option rectangle :=
  match items with
  | nil=>None
  | (pc,i)::rest=>match post_update f oi ij ri rj body pc i with
                 Some b=>Some b|None=>find_post_update f oi ij ri rj body rest end
  end.
Definition detect_post (f: function) (oi: node): option rectangle :=
  match (fn_code f)!oi with
  | Some(Iop (Ointconst zi) nil ri ij) =>
    if Int.eq zi Int.zero then
    match (fn_code f)!ij with
    | Some(Iop (Ointconst zj) nil rj body) =>
      if Int.eq zj Int.zero then if peq ri rj then None else
        find_post_update f oi ij ri rj body (PTree.elements(fn_code f))
      else None
    | _=>None end
    else None
  | _=>None end.
Fixpoint choose (f: function) (items: list(node * instruction)): option rectangle :=
  match items with
  | nil => None
  | (pc,_)::rest => match detect f pc with Some b=>Some b|None=>
                    match detect_post f pc with Some b=>Some b|None=>choose f rest end end
  end.
Definition retarget (plan: rectangle) (pc: node): node :=
  if peq pc (inner_update plan) then outer_update plan else pc.
Definition copy_instr (plan: rectangle) (pc: node) (i: instruction): instruction :=
  if peq pc (outer_init plan) then
    Iop (Ointconst Int.zero) nil (inner_reg plan)
      (if post_tested plan then inner_init plan else inner_test plan)
  else if peq pc (inner_init plan) then
    Iop (Ointconst Int.zero) nil (outer_reg plan)
      (if post_tested plan then body_entry plan else outer_test plan)
  else if peq pc (outer_test plan) then
    Icond (outer_cond plan) (outer_reg plan::nil) (body_entry plan) (inner_update plan)
  else if peq pc (inner_test plan) then
    Icond (inner_cond plan) (inner_reg plan::nil) (inner_init plan) (exit_node plan)
  else Experimental.map_successors (retarget plan) i.
Definition candidate (f: function): function :=
  let items:=PTree.elements(fn_code f) in
  if Nat.leb(length items)512 then
    match choose f items with
    | Some plan=>mkfunction(fn_sig f)(fn_params f)(fn_stacksize f)
                   (PTree.map(copy_instr plan)(fn_code f))(fn_entrypoint f)
    | None=>f end
  else f.
Definition accepted (f: function): bool := LoopFusion.validate_function f (candidate f).
Definition transf_function := LoopFusion.transf_function_with candidate.
Definition transf_fundef := LoopFusion.transf_fundef_with candidate.
Definition transf_program := LoopFusion.transf_program_with candidate.

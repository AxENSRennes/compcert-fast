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

(** Motion after a retained entry preheader. Prefix operations execute in their
    original order, including loads, stores, builtins and returning calls. No
    memory operation is speculated or hoisted. The total invariant is cached only when the prefix exits;
    loop operands may therefore be values computed by prefix expressions.
    A validated closed suffix also supports branching preheaders. Its cache is
    initialized at the first actual selected operation, so partial operations
    such as integer division are never speculated on a zero-trip path. *)
Require Import Coqlib Maps AST Integers Op Registers RTL Experimental HoistConst LICM.

Definition tag (warm: bool) (pc: node) : node := if warm then xI pc else xO pc.
Record prefix := mkprefix { prefix_nodes: list node; prefix_exit: node }.
Fixpoint find_prefix (fuel: nat) (f: function) (pc: node) (seen: list node) : prefix :=
  match fuel with
  | O => mkprefix seen pc
  | S fuel' =>
      if in_dec peq pc seen then mkprefix seen pc else
      match f.(fn_code)!pc with
      | Some (Inop next) | Some (Iop _ _ _ next)
      | Some (Iload _ _ _ _ next) | Some (Istore _ _ _ _ next)
      | Some (Ibuiltin _ _ _ next) | Some (Icall _ _ _ _ next) =>
          find_prefix fuel' f next (pc :: seen)
      | _ => mkprefix seen pc
      end
  end.
Definition outsideb (pre: prefix) (pc: node) : bool :=
  if in_dec peq pc pre.(prefix_nodes) then false else true.
Definition prefix_closed (f: function) (pre: prefix) : bool :=
  forallb (fun kv => if outsideb pre (fst kv)
                    then forallb (outsideb pre) (successors_instr (snd kv)) else true)
          (PTree.elements f.(fn_code)).
Definition stable_after (f: function) (pre: prefix) (r: reg) : bool :=
  forallb (fun kv => if outsideb pre (fst kv) then
                    match instr_defs (snd kv) with
                    | Some dst => if peq dst r then false else true
                    | None => true end else true) (PTree.elements f.(fn_code)).
Record region := mkregion { region_prefix: prefix; region_op: operation; region_args: list reg }.
Definition eligible (f: function) (pre: prefix) (op: operation) (args: list reg) : bool :=
  negb (op_depends_on_memory op) && LICM.total_arity op (length args) &&
  forallb (stable_after f pre) args && LICM.worth_hoisting op.
Fixpoint choose_in (f: function) (pre: prefix) (fuel: nat)
    (items: list (node * instruction)) {struct items} : option region :=
  match items with
  | nil => None
  | (pc,i) :: rest =>
      match i with
      | Iop op args dst next =>
          match fuel with
          | O => None
          | S remaining =>
              if outsideb pre pc && eligible f pre op args && HoistConst.cyclic f pc i
              then Some (mkregion pre op args) else choose_in f pre remaining rest
          end
      | _ => choose_in f pre fuel rest
      end
  end.
(** A conservative suffix search is only a proposal generator. The closed-cut
    and stable-register checks below validate it before any code changes. *)
Fixpoint reachable (fuel: nat) (f: function) (work: list node) (seen: PTree.t unit) : PTree.t unit :=
  match fuel,work with
  | S remaining, pc :: rest =>
      match seen!pc with
      | Some _ => reachable remaining f rest seen
      | None =>
          let seen := PTree.set pc tt seen in
          match f.(fn_code)!pc with
          | Some i => reachable remaining f (successors_instr i ++ rest) seen
          | None => reachable remaining f rest seen
          end
      end
  | _,_ => seen
  end.
Definition suffix_prefix (f: function) (anchor: node) : prefix :=
  let seen := reachable 2048 f (anchor :: nil) (PTree.empty unit) in
  mkprefix (map fst (filter (fun kv => match seen!(fst kv) with None => true | Some _ => false end)
                           (PTree.elements f.(fn_code)))) anchor.
Definition lazy_eligible (f: function) (pre: prefix) (op: operation) (args: list reg) : bool :=
  negb (op_depends_on_memory op) &&
  Nat.eqb (length args) (length (fst (type_of_operation op))) &&
  forallb (stable_after f pre) args && LICM.worth_hoisting op.
Fixpoint choose_suffix (f: function) (fuel: nat) (items: list (node * instruction)) {struct items}
    : option region :=
  match items with
  | nil => None
  | (pc,i) :: rest =>
      match i with
      | Iop op args dst next =>
          match fuel with
          | O => None
          | S remaining =>
              if HoistConst.cyclic f pc i then
                let pre := suffix_prefix f pc in
                if outsideb pre pc && prefix_closed f pre && lazy_eligible f pre op args
                then Some (mkregion pre op args) else choose_suffix f remaining rest
              else choose_suffix f remaining rest
          end
      | _ => choose_suffix f fuel rest
      end
  end.
Definition chosen (f: function) : option region :=
  let items := PTree.elements f.(fn_code) in
  if Nat.leb (length items) 512 then
    let pre := find_prefix 16 f f.(fn_entrypoint) nil in
    let eager := if outsideb pre pre.(prefix_exit) && prefix_closed f pre
                 then choose_in f pre 32 items else None in
    match eager with Some b => Some b | None => choose_suffix f 32 items end
  else None.
Definition cached (b: region) (temporary: reg) (i: instruction) : instruction :=
  LICM.transf_instr_cached (LICM.mkinvariant b.(region_op) b.(region_args)) temporary i.
Definition copy_instr (f: function) (b: region) (warm: bool) (i: instruction) : instruction :=
  Experimental.map_successors (tag warm) (if warm then cached b (LICM.fresh_reg f) i else i).
Definition copy_code (f: function) (b: region) : code :=
  PTree.set (tag false b.(region_prefix).(prefix_exit))
    (Iop b.(region_op) b.(region_args) (LICM.fresh_reg f) (tag true b.(region_prefix).(prefix_exit)))
    (PTree.Node (PTree.map1 (copy_instr f b false) f.(fn_code)) None
                (PTree.map1 (copy_instr f b true) f.(fn_code))).
Definition hoisted (f: function) (b: region) : function :=
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize) (copy_code f b) (tag false f.(fn_entrypoint)).
Definition transf_function (f: function) : function :=
  match chosen f with Some b => hoisted f b | None => f end.
Definition label (f: function) (warm: bool) (pc: node) : node :=
  match chosen f with Some _ => tag warm pc | None => pc end.
Definition transf_fundef (f: fundef) : fundef := AST.transf_fundef transf_function f.
Definition transf_program (p: program) : program := AST.transform_program transf_fundef p.

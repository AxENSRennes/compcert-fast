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

(** Bounded symbolic validation of pure finite loop schedules.  Every
    executed operation is total and memory-independent.  Reordered schedules
    must return the identical symbolic value for arbitrary input value tags.
    This validates bounded fusion without algebraic or alias assumptions. *)
Require Import Coqlib Maps AST Integers Values Memory Globalenvs Op Registers RTL LICM Experimental.

Inductive expr : Type :=
| Input (r: reg)
| Intval (n: int)
| Undef
| Op0 (op: operation)
| Op1 (op: operation) (a: expr)
| Op2 (op: operation) (a b: expr)
| Op3 (op: operation) (a b c: expr).

Definition expr_eq: forall (a b: expr), {a=b}+{a<>b}.
Proof.
  decide equality; auto using peq, Int.eq_dec, Op.eq_operation.
Defined.

Fixpoint denote {F V: Type} (ge: Genv.t F V) (sp: val) (rs: regset) (e: expr): val :=
  match e with
  | Input r => rs#r
  | Intval n => Vint n
  | Undef => Vundef
  | Op0 op => Val.maketotal (eval_operation ge sp op nil Mem.empty)
  | Op1 op a => Val.maketotal (eval_operation ge sp op (denote ge sp rs a :: nil) Mem.empty)
  | Op2 op a b => Val.maketotal (eval_operation ge sp op (denote ge sp rs a :: denote ge sp rs b :: nil) Mem.empty)
  | Op3 op a b c => Val.maketotal (eval_operation ge sp op (denote ge sp rs a :: denote ge sp rs b :: denote ge sp rs c :: nil) Mem.empty)
  end.

Fixpoint bounded (fuel: nat) (e: expr) {struct e}: option nat :=
  match fuel with
  | O => None
  | S n =>
      match e with
      | Input _ | Intval _ | Undef | Op0 _ => Some n
      | Op1 _ a => bounded n a
      | Op2 _ a b => match bounded n a with Some n1 => bounded n1 b | None => None end
      | Op3 _ a b c => match bounded n a with
                      | Some n1 => match bounded n1 b with Some n2 => bounded n2 c | None => None end
                      | None => None end
      end
  end.
Definition small (e: expr): bool := match bounded 128 e with Some _ => true | None => false end.
Definition raw_expr (op: operation) (args: list expr): option expr :=
  match args with
  | nil => Some (Op0 op)
  | a :: nil => Some (Op1 op a)
  | a :: b :: nil => Some (Op2 op a b)
  | a :: b :: c :: nil => Some (Op3 op a b c)
  | _ => None
  end.
Fixpoint constant_args (args: list expr): option (list val) :=
  match args with
  | nil => Some nil
  | Intval n :: rest => match constant_args rest with Some vs => Some (Vint n :: vs) | None => None end
  | _ => None
  end.
Definition no_context (op: operation): bool :=
  match op with Oaddrstack _ | Oaddrsymbol _ _ => false | _ => true end.
Definition empty_program: RTL.program := mkprogram nil nil 1%positive.
Definition empty_ge := Genv.globalenv empty_program.
Definition make_expr (op: operation) (args: list expr): option expr :=
  let e := if no_context op then
    match constant_args args with
    | Some vs => match eval_operation empty_ge Vundef op vs Mem.empty with
                 | Some (Vint n) => Some (Intval n)
                 | _ => raw_expr op args end
    | None => raw_expr op args end
    else raw_expr op args in
  match e with Some e => if small e then Some e else None | None => None end.

Definition symregs := PTree.t expr.
Definition symget (ss: symregs) (r: reg): expr :=
  match ss!r with Some e => e | None => Input r end.
Definition symargs (ss: symregs) (args: list reg): list expr := map (symget ss) args.
Definition safe_operation (op: operation) (args: list reg): bool :=
  negb (op_depends_on_memory op) && LICM.total_arity op (length args) && Nat.leb (length args) 3.
Definition known_condition (cond: condition) (args: list expr): option bool :=
  if negb (op_depends_on_memory (Ocmp cond)) then
    match constant_args args with Some vs => eval_condition cond vs Mem.empty | None => None end
  else None.
Fixpoint run (f: function) (fuel: nat) (pc: node) (ss: symregs): option expr :=
  match fuel with
  | O => None
  | S remaining =>
      match f.(fn_code)!pc with
      | Some (Inop next) => run f remaining next ss
      | Some (Iop op args dst next) =>
          if safe_operation op args then
            match make_expr op (symargs ss args) with
            | Some e => run f remaining next (PTree.set dst e ss)
            | None => None end
          else None
      | Some (Icond cond args yes no) =>
          match known_condition cond (symargs ss args) with
          | Some b => run f remaining (if b then yes else no) ss
          | None => None end
      | Some (Ireturn r) => Some (match r with Some r => symget ss r | None => Undef end)
      | _ => None
      end
  end.
Definition run_function (f: function): option expr := run f 128 f.(fn_entrypoint) (PTree.empty expr).
Definition validate_function (f tf: function): bool :=
  if signature_eq f.(fn_sig) tf.(fn_sig) then
  if list_eq_dec peq f.(fn_params) tf.(fn_params) then
  if zeq f.(fn_stacksize) tf.(fn_stacksize) then
    match run_function f, run_function tf with
    | Some a, Some b => if expr_eq a b then true else false
    | _,_ => false end
  else false else false else false.
Definition transf_function_with (proposal: function -> function) (f: function): function :=
  let tf := proposal f in if validate_function f tf then tf else f.
Definition transf_fundef_with (proposal: function -> function) (f: fundef): fundef :=
  AST.transf_fundef (transf_function_with proposal) f.
Definition transf_program_with (proposal: function -> function) (p: program): program :=
  AST.transform_program (transf_fundef_with proposal) p.

(** Candidate construction is a proposal only; the checker above is the sole
    authority for accepting its finite reordering. *)
Fixpoint chain_to (f: function) (fuel: nat) (stop pc: node): option (list (node * instruction)) :=
  if peq pc stop then Some nil else
  match fuel with
  | O => None
  | S remaining =>
      match f.(fn_code)!pc with
      | Some (Inop next) => match chain_to f remaining stop next with
                          | Some rest => Some ((pc,Inop next)::rest) | None => None end
      | Some (Iop op args dst next) => match chain_to f remaining stop next with
                          | Some rest => Some ((pc,Iop op args dst next)::rest) | None => None end
      | _ => None
      end
  end.
Record loop := mkloop { loop_header: node; loop_cond: condition; loop_args: list reg;
  loop_body: node; loop_exit: node; loop_true: bool; loop_chain: list (node * instruction) }.
Definition try_loop (f: function) (pc: node) (cond: condition) (args: list reg)
    (body exit: node) (truth: bool): option loop :=
  match chain_to f 24 pc body with
  | Some (_ :: _ as items) => Some (mkloop pc cond args body exit truth items)
  | _ => None
  end.
Definition get_loop (f: function) (pc: node): option loop :=
  match f.(fn_code)!pc with
  | Some (Icond cond args yes no) =>
      match try_loop f pc cond args yes no true with
      | Some loop => Some loop
      | None => try_loop f pc cond args no yes false
      end
  | _ => None
  end.
Fixpoint before_loop (f: function) (fuel: nat) (pc: node): option (list instruction * loop) :=
  match fuel with
  | O => None
  | S remaining =>
      match get_loop f pc with
      | Some lp => Some (nil,lp)
      | None =>
          match f.(fn_code)!pc with
          | Some (Inop next) => match before_loop f remaining next with
                              | Some (items,lp) => Some (Inop next::items,lp) | None => None end
          | Some (Iop op args dst next) => match before_loop f remaining next with
                              | Some (items,lp) => Some (Iop op args dst next::items,lp) | None => None end
          | _ => None
          end
      end
  end.
Fixpoint prepend (items: list instruction) (fresh dest: node) (code: code): node * RTL.code :=
  match items with
  | nil => (dest,code)
  | i :: rest =>
      let (entry,code) := prepend rest (Pos.succ fresh) dest code in
      (fresh,PTree.set fresh (map_successors (fun _ => entry) i) code)
  end.
Definition last_instr (lp: loop): node * instruction :=
  List.last lp.(loop_chain) (lp.(loop_body),Inop lp.(loop_header)).
Definition same_increment (a b: instruction): bool :=
  match a,b with
  | Iop (Oaddimm x) (r::nil) d _, Iop (Oaddimm y) (r'::nil) d' _ =>
      if peq r d then if peq r' d' then if peq r r' then Int.eq x y else false else false else false
  | _ , _ => false
  end.
Definition fuse (f: function) (first second: loop) (prefix: list instruction): function :=
  let (last1,i1) := last_instr first in
  let (last2,i2) := last_instr second in
  let code := PTree.set first.(loop_header)
    (Icond first.(loop_cond) first.(loop_args)
      (if first.(loop_true) then first.(loop_body) else second.(loop_exit))
      (if first.(loop_true) then second.(loop_exit) else first.(loop_body)))
    (PTree.set last1 (if same_increment i1 i2 then Inop second.(loop_body)
                    else map_successors (fun _ => second.(loop_body)) i1)
    (PTree.set last2 (map_successors (fun _ => first.(loop_header)) i2) f.(fn_code))) in
  let (entry,code) := prepend prefix (Pos.succ (max_pc_function f)) f.(fn_entrypoint) code in
  mkfunction f.(fn_sig) f.(fn_params) f.(fn_stacksize) code entry.
Fixpoint find_fusion (f: function) (fuel: nat) (items: list (node * instruction)): option function :=
  match fuel,items with
  | S remaining,(pc,_)::rest =>
      match get_loop f pc with
      | Some first =>
          match before_loop f 24 first.(loop_exit) with
          | Some (prefix,second) =>
              if peq first.(loop_header) second.(loop_header) then find_fusion f remaining rest else
              let tf := fuse f first second prefix in
              if validate_function f tf then Some tf else find_fusion f remaining rest
          | None => find_fusion f remaining rest
          end
      | None => find_fusion f remaining rest
      end
  | _,_ => None
  end.
Definition candidate (f: function): function :=
  let items := PTree.elements f.(fn_code) in
  if Nat.leb (length items) 96 then
    match find_fusion f 64 items with Some tf => tf | None => f end
  else f.
Definition transf_function := transf_function_with candidate.
Definition transf_fundef := transf_fundef_with candidate.
Definition transf_program := transf_program_with candidate.

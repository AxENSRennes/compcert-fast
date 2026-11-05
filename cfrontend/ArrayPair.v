(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Pair adjacent unsigned additions at Clight, where evaluating each
    scalar addition requires an integer operand. *)
Require Import Coqlib AST Integers Ctypes Cop Clight MemoryNeon.

Definition tuint := Tint I32 Unsigned noattr.
Definition tint := Tint I32 Signed noattr.
Definition tulong := Tlong Unsigned noattr.
Definition tuint_ptr := Tpointer tuint noattr.

Inductive traversal := WhilePointer | ForPointer | Indexed (index: ident).

Record plan := Plan {
  pointer: ident;
  bound: ident;
  layout: traversal;
  increment: int;
  increment_signedness: signedness;
  anchor: option (Z * N)
}.

Definition array_anchor (p: plan) : option (Z * N) :=
  match layout p with Indexed _ => anchor p | _ => None end.

Definition wide (p: plan) : bool :=
  match array_anchor p with Some _ => true | None => false end.

Definition scratch (p: plan) : ident :=
  Pos.succ (Pos.max (pointer p) (Pos.max (bound p)
    (match layout p with Indexed i => i | _ => xH end))).

Definition array_type (len: Z) (log_alignment: N) : type :=
  Tarray tuint len (mk_attr false (Some log_alignment)).
Definition pointer_expr (p: plan) :=
  match array_anchor p with
  | Some (len, log_alignment) => Evar (pointer p) (array_type len log_alignment)
  | None => Etempvar (pointer p) tuint_ptr
  end.
Definition count_expr (p: plan) := Etempvar (bound p) tuint.
Definition sint (n: Z) := Econst_int (Int.repr n) tint.
Definition uint (n: Z) := Econst_int (Int.repr n) tuint.

Definition addr (p: plan) (lane: nat) : expr :=
  match layout p with
  | Indexed i =>
      let idx := Etempvar i tuint in
      let off := match lane with O => idx
                  | S _ => Ebinop Oadd idx (sint (Z.of_nat lane)) tuint end in
      Ebinop Oadd (pointer_expr p) off tuint_ptr
  | _ => match lane with O => pointer_expr p
          | S _ => Ebinop Oadd (pointer_expr p) (sint (Z.of_nat lane)) tuint_ptr end
  end.

Definition loop_test (p: plan) : expr :=
  match layout p with
  | Indexed i => Ebinop Olt (Etempvar i tuint) (count_expr p) tint
  | _ => count_expr p
  end.

Definition pair_test (p: plan) : expr :=
  let remaining := match layout p with
                   | Indexed i => Ebinop Osub (count_expr p) (Etempvar i tuint) tuint
                   | _ => count_expr p end in
  Ebinop Oge remaining (uint 2) tint.

Definition scalar_update (p: plan) : statement :=
  let cell := Ederef (addr p 0) tuint in
  let literal := Econst_int (increment p) (Tint I32 (increment_signedness p) noattr) in
  Sassign cell (Ebinop Oadd cell literal tuint).

Definition advance_pointer (p: plan) (n: Z) :=
  Sset (pointer p) (Ebinop Oadd (pointer_expr p) (sint n) tuint_ptr).
Definition decrease_count (p: plan) (n: Z) :=
  Sset (bound p) (Ebinop Osub (count_expr p) (sint n) tuint).
Definition advance_index (i: ident) (n: Z) :=
  Sset i (Ebinop Oadd (Etempvar i tuint) (sint n) tuint).
Definition advance (p: plan) (n: Z) : statement :=
  match layout p with
  | Indexed i => advance_index i n
  | _ => Ssequence (advance_pointer p n) (decrease_count p n)
  end.
Definition scalar_advance (p: plan) := advance p 1.
Definition packed_advance (p: plan) := advance p 2.

Definition with_skip (s: statement) := Ssequence Sskip s.
Definition guard (p: plan) := Sifthenelse (loop_test p) Sskip Sbreak.

Definition source_loop (p: plan) : statement :=
  let check := with_skip (guard p) in
  let update := with_skip (scalar_update p) in
  match layout p with
  | WhilePointer =>
      Sloop (Ssequence check (Ssequence update
        (Ssequence (with_skip (advance_pointer p 1)) (with_skip (decrease_count p 1))))) Sskip
  | ForPointer =>
      Sloop (Ssequence check update)
        (Ssequence (with_skip (advance_pointer p 1)) (decrease_count p 1))
  | Indexed i => Sloop (Ssequence check update) (with_skip (advance_index i 1))
  end.

Definition with_init (p: plan) (s: statement) : statement :=
  match layout p with
  | Indexed i => Ssequence (with_skip (Sset i (sint 0))) s
  | _ => s
  end.
Definition source_body (p: plan) := with_init p (source_loop p).

Definition packed_update (tmp: ident) (addr0 addr1: expr) (k: int) : statement :=
  let lo := Ederef addr0 tuint in
  let hi := Ederef addr1 tuint in
  let shift := sint 32 in
  let packed := Ebinop Oor (Ecast lo tulong)
    (Ebinop Oshl (Ecast hi tulong) shift tulong) tulong in
  let res := Etempvar tmp tulong in
  Ssequence
    (Sbuiltin (Some tmp) MemoryNeon.packed_builtin (tulong :: tulong :: nil)
      (packed :: Econst_long (Int64.ofwords k k) tulong :: nil))
    (Ssequence (Sassign lo (Ecast res tuint))
      (Sassign hi (Ecast (Ebinop Oshr res shift tulong) tuint))).

Definition wide_cell (a: expr) : expr :=
  Ederef (Ecast a (Tpointer tulong noattr)) tulong.

Definition wide_update (tmp: ident) (a: expr) (k: int) : statement :=
  Ssequence
    (Sbuiltin (Some tmp) MemoryNeon.packed_builtin (tulong :: tulong :: nil)
      (wide_cell a :: Econst_long (Int64.ofwords k k) tulong :: nil))
    (Sassign (wide_cell a) (Etempvar tmp tulong)).

Definition pair_branch (p: plan) := Ssequence
  (if wide p then wide_update (scratch p) (addr p 0) (increment p)
   else packed_update (scratch p) (addr p 0) (addr p 1) (increment p))
  (packed_advance p).
Definition scalar_branch (p: plan) := Ssequence (scalar_update p) (scalar_advance p).
Definition target_loop (p: plan) := Sloop
  (Ssequence (guard p) (Sifthenelse (pair_test p) (pair_branch p) (scalar_branch p))) Sskip.
Definition target_body (p: plan) := with_init p (target_loop p).

Definition parameters (p: plan) :=
  if wide p then (bound p, tuint) :: nil
  else (pointer p, tuint_ptr) :: (bound p, tuint) :: nil.
Definition scalar_temps (p: plan) := match layout p with Indexed i => (i, tuint) :: nil | _ => nil end.
Definition source_template (p: plan) :=
  mkfunction Tvoid cc_default (parameters p) nil (scalar_temps p) (source_body p).
Definition target_template (p: plan) :=
  mkfunction Tvoid cc_default (parameters p) nil ((scratch p, tulong) :: scalar_temps p) (target_body p).

Definition binop_eq (a b: binary_operation) : {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Only the expression and statement constructors of the recognised
    loops need to be compared. Every other constructor fails the check. *)
Fixpoint same_expr (a b: expr) : bool :=
  match a, b with
  | Econst_int v t, Econst_int v' t' => Int.eq_dec v v' && type_eq t t'
  | Etempvar id t, Etempvar id' t' | Evar id t, Evar id' t' => peq id id' && type_eq t t'
  | Ederef x t, Ederef x' t' => same_expr x x' && type_eq t t'
  | Ebinop op x y t, Ebinop op' x' y' t' =>
      binop_eq op op' && same_expr x x' && same_expr y y' && type_eq t t'
  | _, _ => false
  end.

Fixpoint same_stmt (s t: statement) : bool :=
  match s, t with
  | Sskip, Sskip | Sbreak, Sbreak => true
  | Sassign l r, Sassign l' r' => same_expr l l' && same_expr r r'
  | Sset id a, Sset id' a' => peq id id' && same_expr a a'
  | Ssequence a b, Ssequence a' b'
  | Sloop a b, Sloop a' b' => same_stmt a a' && same_stmt b b'
  | Sifthenelse c a b, Sifthenelse c' a' b' =>
      same_expr c c' && same_stmt a a' && same_stmt b b'
  | _, _ => false
  end.

Definition binding_eq (a b: ident * type) : {a = b} + {a <> b}.
Proof. decide equality; auto using peq, type_eq. Defined.

Definition matches (f: function) (p: plan) : bool :=
  type_eq (fn_return f) Tvoid && calling_convention_eq (fn_callconv f) cc_default &&
  list_eq_dec binding_eq (fn_params f) (parameters p) &&
  list_eq_dec binding_eq (fn_vars f) nil &&
  list_eq_dec binding_eq (fn_temps f) (scalar_temps p) &&
  same_stmt (fn_body f) (source_body p).

Fixpoint find_increment (s: statement) : option (int * signedness) :=
  match s with
  | Sassign _ (Ebinop Oadd _ (Econst_int k (Tint I32 sign _)) _) => Some (k, sign)
  | Ssequence a b | Sloop a b =>
      match find_increment a with Some k => Some k | None => find_increment b end
  | _ => None
  end.

Definition checked (f: function) (p: plan) : option plan :=
  if peq (pointer p) (bound p) then None else
  if match layout p with Indexed i => peq i (pointer p) || peq i (bound p) | _ => false end
  then None else if matches f p then Some p else None.

(** A named, explicitly aligned array supplies an offset-zero base. The
    recognizer checks its full type and the loop starting at index zero. *)
Fixpoint find_array (s: statement) : option (ident * (Z * N)) :=
  match s with
  | Sassign (Ederef (Ebinop Oadd (Evar id (Tarray _ len att)) _ _) _) _ =>
      match attr_alignas att with
      | Some log_alignment =>
          if N.leb 3 log_alignment && Z.leb 2 len
          then Some (id, (len, log_alignment)) else None
      | None => None
      end
  | Ssequence a b | Sloop a b =>
      match find_array a with Some base => Some base | None => find_array b end
  | _ => None
  end.

Definition selected (f: function) : option plan :=
  match fn_params f, find_increment (fn_body f) with
  | (ptr, _) :: (n, _) :: nil, Some (k, sign) =>
      match fn_temps f with
      | nil => match checked f (Plan ptr n WhilePointer k sign None) with
               | Some p => Some p
               | None => checked f (Plan ptr n ForPointer k sign None)
               end
      | (i, _) :: nil => checked f (Plan ptr n (Indexed i) k sign None)
      | _ => None
      end
  | (n, _) :: nil, Some (k, sign) =>
      match fn_temps f, find_array (fn_body f) with
      | (i, _) :: nil, Some (base, ty) => checked f (Plan base n (Indexed i) k sign (Some ty))
      | _, _ => None
      end
  | _, _ => None
  end.

Definition transf_function (f: function) : function :=
  match selected f with Some p => target_template p | None => f end.
Definition transf_fundef (fd: Clight.fundef) : Clight.fundef :=
  match fd with Internal f => Internal (transf_function f) | _ => fd end.

Definition transf_program (p: Clight.program) : Clight.program :=
  {| prog_defs := AST.prog_defs (AST.transform_program transf_fundef p);
     prog_public := prog_public p;
     prog_main := prog_main p;
     prog_types := prog_types p;
     prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.

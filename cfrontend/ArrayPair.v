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
Require Import Coqlib Maps AST Linking Integers Ctypes Cop Clight MemoryNeon.

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
  anchor: option (Z * N);
  pointer_wide: bool
}.

Definition array_anchor (p: plan) : option (Z * N) :=
  match layout p with Indexed _ => anchor p | _ => None end.

Definition anchored (p: plan) : bool :=
  match array_anchor p with Some _ => true | None => false end.

Definition wide (p: plan) : bool :=
  match layout p with Indexed _ => anchored p || pointer_wide p | _ => false end.

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
  if anchored p then (bound p, tuint) :: nil
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
  | Scall None callee (a :: b :: nil), Scall None callee' (a' :: b' :: nil) =>
      same_expr callee callee' && same_expr a a' && same_expr b b'
  | Ssequence a b, Ssequence a' b'
  | Sloop a b, Sloop a' b' => same_stmt a a' && same_stmt b b'
  | Sifthenelse c a b, Sifthenelse c' a' b' =>
      same_expr c c' && same_stmt a a' && same_stmt b b'
  | _, _ => false
  end.

Definition binding_eq (a b: ident * type) : {a = b} + {a <> b}.
Proof. decide equality; auto using peq, type_eq. Defined.

Definition matches (f: function) (p: plan) (body: statement) : bool :=
  type_eq (fn_return f) Tvoid && calling_convention_eq (fn_callconv f) cc_default &&
  list_eq_dec binding_eq (fn_params f) (parameters p) &&
  list_eq_dec binding_eq (fn_vars f) nil &&
  list_eq_dec binding_eq (fn_temps f) (scalar_temps p) &&
  same_stmt (fn_body f) body.

Fixpoint find_increment (s: statement) : option (int * signedness) :=
  match s with
  | Sassign _ (Ebinop Oadd _ (Econst_int k (Tint I32 sign _)) _) => Some (k, sign)
  | Ssequence a b | Sloop a b =>
      match find_increment a with Some k => Some k | None => find_increment b end
  | _ => None
  end.

Definition distinct (p: plan) : bool :=
  negb (peq (pointer p) (bound p)) &&
  match layout p with
  | Indexed i => negb (peq i (pointer p) || peq i (bound p))
  | _ => true
  end.

Definition checked (f: function) (p: plan) : option plan :=
  if distinct p && matches f p (source_body p) then Some p else None.

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

Definition selected_plain (f: function) : option plan :=
  match fn_params f, find_increment (fn_body f) with
  | (ptr, _) :: (n, _) :: nil, Some (k, sign) =>
      match fn_temps f with
      | nil => match checked f (Plan ptr n WhilePointer k sign None false) with
               | Some p => Some p
               | None => checked f (Plan ptr n ForPointer k sign None false)
               end
      | (i, _) :: nil => checked f (Plan ptr n (Indexed i) k sign None false)
      | _ => None
      end
  | (n, _) :: nil, Some (k, sign) =>
      match fn_temps f, find_array (fn_body f) with
      | (i, _) :: nil, Some (base, ty) => checked f (Plan base n (Indexed i) k sign (Some ty) false)
      | _, _ => None
      end
  | _, _ => None
  end.

(** A source equality witnesses that a parameter denotes an aligned element
    of a named array. Retain that test and both loop arms. *)
Record alignment_guard := AlignmentGuard {
  guard_array: ident;
  guard_length: Z;
  guard_alignment: N;
  guard_offset: option (int * signedness)
}.

Definition guard_address (g: alignment_guard) : expr :=
  let base := Evar (guard_array g) (array_type (guard_length g) (guard_alignment g)) in
  match guard_offset g with
  | None => base
  | Some (k, sign) => Ebinop Oadd base (Econst_int k (Tint I32 sign noattr)) tuint_ptr
  end.

Definition guard_test (p: plan) (g: alignment_guard) : expr :=
  Ebinop Oeq (Etempvar (pointer p) tuint_ptr) (guard_address g) tint.

Definition aligned_pointer_plan (p: plan) : plan :=
  Plan (pointer p) (bound p) (layout p) (increment p) (increment_signedness p) (anchor p) true.

Definition guarded_source (p: plan) (g: alignment_guard) : statement :=
  with_skip (Sifthenelse (guard_test p g) (source_body p) (source_body p)).

Definition guarded_target (p: plan) (g: alignment_guard) : statement :=
  with_skip (Sifthenelse (guard_test p g) (target_body (aligned_pointer_plan p)) (target_body p)).

Definition offset_index (o: option (int * signedness)) : Z :=
  match o with
  | None => 0
  | Some (k, Signed) => Int.signed k
  | Some (k, Unsigned) => Int.unsigned k
  end.

Definition valid_guard (g: alignment_guard) : bool :=
  let i := offset_index (guard_offset g) in
  N.leb 3 (guard_alignment g) && Z.leb 0 i && Z.ltb i (guard_length g) && Z.even i.

Definition guard_base (base: expr) (off: option (int * signedness)) : option alignment_guard :=
  match base with
  | Evar id (Tarray _ len (mk_attr _ (Some al))) => Some (AlignmentGuard id len al off)
  | _ => None
  end.

Definition find_aligned_address (a: expr) : option alignment_guard :=
  match a with
  | Ebinop Oadd base (Econst_int k (Tint I32 sign _)) _ => guard_base base (Some (k, sign))
  | _ => guard_base a None
  end.

Definition find_guard (a: expr) : option alignment_guard :=
  match a with
  | Ebinop Oeq _ rhs _ => find_aligned_address rhs
  | _ => None
  end.

Definition selected_guarded (f: function) : option (plan * alignment_guard) :=
  match fn_params f, fn_temps f, fn_body f with
  | (ptr, _) :: (n, _) :: nil, (i, _) :: nil, Ssequence Sskip (Sifthenelse a yes _) =>
      match find_guard a, find_increment yes with
      | Some g, Some (k, sign) =>
          let p := Plan ptr n (Indexed i) k sign None false in
          if valid_guard g && distinct p && matches f p (guarded_source p g)
          then Some (p, g) else None
      | _, _ => None
      end
  | _, _, _ => None
  end.

Definition selected (f: function) : option (plan * option alignment_guard) :=
  match selected_guarded f with
  | Some (p, g) => Some (p, Some g)
  | None => option_map (fun p => (p, None)) (selected_plain f)
  end.

Definition with_body (f: function) (s: statement) : function :=
  mkfunction (fn_return f) (fn_callconv f) (fn_params f) (fn_vars f) (fn_temps f) s.

Definition source_function (p: plan) (g: option alignment_guard) : function :=
  match g with
  | None => source_template p
  | Some test => with_body (source_template p) (guarded_source p test)
  end.

Definition target_function (p: plan) (g: option alignment_guard) : function :=
  match g with
  | None => target_template p
  | Some test => with_body (target_template p) (guarded_target p test)
  end.

Definition local_transf_function (f: function) : function :=
  match selected f with Some (p, g) => target_function p g | None => f end.

Record call_plan := CallPlan {
  call_worker: ident;
  call_loop: plan;
  call_count: ident;
  call_address: alignment_guard
}.

Definition caller_call (c: call_plan) : statement :=
  Scall None (Evar (call_worker c) (type_of_function (source_template (call_loop c))))
    (guard_address (call_address c) :: Etempvar (call_count c) tuint :: nil).

Definition caller_source (c: call_plan) : function :=
  mkfunction Tvoid cc_default ((call_count c, tuint) :: nil) nil nil
    (with_skip (caller_call c)).

Definition caller_setup (c: call_plan) : statement :=
  let p := call_loop c in
  Ssequence (Sset (pointer p) (guard_address (call_address c)))
    (target_body (aligned_pointer_plan p)).

Definition caller_target (c: call_plan) : function :=
  let p := call_loop c in
  mkfunction Tvoid cc_default ((bound p, tuint) :: nil) nil
    ((pointer p, tuint_ptr) :: (scratch p, tulong) :: scalar_temps p)
    (with_skip (caller_setup c)).

Definition caller_matches (f: function) (c: call_plan) : bool :=
  type_eq (fn_return f) Tvoid && calling_convention_eq (fn_callconv f) cc_default &&
  list_eq_dec binding_eq (fn_params f) ((call_count c, tuint) :: nil) &&
  list_eq_dec binding_eq (fn_vars f) nil &&
  list_eq_dec binding_eq (fn_temps f) nil &&
  same_stmt (fn_body f) (fn_body (caller_source c)).

Definition worker_plan (cu: Clight.program) (id: ident) : option plan :=
  if in_dec peq id (prog_public cu) then None else
  match (AST.prog_defmap cu)!id with
  | Some (Gfun (Internal worker)) =>
      match selected_plain worker with
      | Some p => match layout p, array_anchor p with
                  | Indexed _, None => Some p
                  | _, _ => None
                  end
      | None => None
      end
  | _ => None
  end.

(** Inline only an exact forwarding wrapper with a proved aligned argument.
    Its worker and all other calls to that worker keep their ordinary paths. *)
Definition selected_call (cu: Clight.program) (f: function) : option call_plan :=
  match fn_params f, fn_body f with
  | (n, _) :: nil, Ssequence Sskip (Scall None (Evar id _) (addr :: _ :: nil)) =>
      match worker_plan cu id, find_aligned_address addr with
      | Some p, Some g =>
          let c := CallPlan id p n g in
          if valid_guard g && caller_matches f c then Some c else None
      | _, _ => None
      end
  | _, _ => None
  end.

Definition transf_function (cu: Clight.program) (f: function) : function :=
  match selected_call cu f with
  | Some c => caller_target c
  | None => local_transf_function f
  end.

Definition transf_fundef (cu: Clight.program) (fd: Clight.fundef) : Clight.fundef :=
  match fd with Internal f => Internal (transf_function cu f) | _ => fd end.

Definition transf_program (p: Clight.program) : Clight.program :=
  {| prog_defs := AST.prog_defs (AST.transform_program (transf_fundef p) p);
     prog_public := prog_public p;
     prog_main := prog_main p;
     prog_types := prog_types p;
     prog_comp_env := prog_comp_env p;
     prog_comp_env_eq := prog_comp_env_eq p |}.

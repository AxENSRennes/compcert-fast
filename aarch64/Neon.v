(* Experimental integer NEON model and checked elementwise-loop plans.
   Copyright 2026. Distributed under the repository's INRIA
   Non-Commercial License Agreement. This module is not Asm.v and does not
   assert that hardware implements the model. *)
From Coq Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.

Inductive lane_width := W8 | W16 | W32 | W64.
Inductive lane_op := Vadd | Vsub | Vmul | Vand | Vorr | Veor.

Definition lane_bits (w: lane_width) : Z :=
  match w with W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64 end.
Definition lanes (w: lane_width) : nat :=
  match w with W8 => 16%nat | W16 => 8%nat | W32 => 4%nat | W64 => 2%nat end.
Definition modulus (w: lane_width) : Z := 2 ^ lane_bits w.
Definition normalize (w: lane_width) (x: Z) : Z := x mod modulus w.

Definition eval_lane (w: lane_width) (op: lane_op) (x y: Z) : Z :=
  normalize w
    (match op with
     | Vadd => x + y | Vsub => x - y | Vmul => x * y
     | Vand => Z.land x y | Vorr => Z.lor x y | Veor => Z.lxor x y
     end).

Definition lane_in_range w x := 0 <= x < modulus w.
Definition scalar_loop w op (input: list (Z * Z)) : list Z :=
  map (fun xy => eval_lane w op (fst xy) (snd xy)) input.
(* A hardware vector is represented by exactly [lanes w] lane pairs.
   Keeping evaluation total on other lengths simplifies scalar tails. *)
Definition eval_vector := scalar_loop.
Definition vector_well_formed w (input: list (Z * Z)) :=
  length input = lanes w /\
  Forall (fun xy => lane_in_range w (fst xy) /\ lane_in_range w (snd xy)) input.

Lemma lanes_positive: forall w, (0 < lanes w)%nat.
Proof. destruct w; simpl; lia. Qed.
Lemma modulus_positive: forall w, 0 < modulus w.
Proof. destruct w; vm_compute; reflexivity. Qed.
Lemma normalized_range: forall w x, lane_in_range w (normalize w x).
Proof. intros. unfold lane_in_range, normalize. apply Z.mod_pos_bound. apply modulus_positive. Qed.
Lemma normalize_idempotent: forall w x, normalize w (normalize w x) = normalize w x.
Proof. intros. unfold normalize. apply Z.mod_mod. pose proof (modulus_positive w); lia. Qed.
Lemma lane_result_range: forall w op x y, lane_in_range w (eval_lane w op x y).
Proof. intros. unfold eval_lane. apply normalized_range. Qed.
Lemma lane_add_zero: forall w x, eval_lane w Vadd x 0 = normalize w x.
Proof. intros. unfold eval_lane. rewrite Z.add_0_r. reflexivity. Qed.
Lemma lane_mul_one: forall w x, eval_lane w Vmul x 1 = normalize w x.
Proof. intros. unfold eval_lane. rewrite Z.mul_1_r. reflexivity. Qed.
Lemma lane_sub_self: forall w x, eval_lane w Vsub x x = 0.
Proof.
  intros. unfold eval_lane. rewrite Z.sub_diag. unfold normalize.
  apply Z.mod_0_l. pose proof (modulus_positive w); lia.
Qed.
Lemma vector_result_well_formed:
  forall w op input,
  length input = lanes w ->
  length (eval_vector w op input) = lanes w /\
  Forall (lane_in_range w) (eval_vector w op input).
Proof.
  intros. split.
  - unfold eval_vector, scalar_loop. rewrite map_length. auto.
  - unfold eval_vector, scalar_loop. apply Forall_forall.
    intros x IN. apply in_map_iff in IN. destruct IN as [xy [EQ IN]].
    subst x. apply lane_result_range.
Qed.

Record loop_plan := Plan { vector_chunks: nat; scalar_tail: nat }.
Definition plan_for w n := Plan (n / lanes w)%nat (n mod lanes w)%nat.
Definition validate_plan w n p :=
  Nat.eqb ((vector_chunks p * lanes w) + scalar_tail p)%nat n &&
  Nat.ltb (scalar_tail p) (lanes w).
Definition checked_plan w n candidate :=
  if validate_plan w n candidate then candidate else plan_for w n.
(* There is no ordinary NEON 64-by-64-bit integer vector multiply. *)
Definition instruction_supported w op :=
  match w, op with W64, Vmul => false | _, _ => true end.
Definition compile_loop w op n candidate : option loop_plan :=
  if instruction_supported w op then Some (checked_plan w n candidate) else None.

Lemma plan_for_valid: forall w n, validate_plan w n (plan_for w n) = true.
Proof.
  intros. unfold validate_plan, plan_for; simpl.
  apply andb_true_iff. split.
  - apply Nat.eqb_eq. pose proof (Nat.div_mod n (lanes w)).
    pose proof (lanes_positive w). nia.
  - apply Nat.ltb_lt. apply Nat.mod_upper_bound. pose proof (lanes_positive w); lia.
Qed.
Lemma validate_plan_partition:
  forall w n p, validate_plan w n p = true ->
  ((vector_chunks p * lanes w) + scalar_tail p = n)%nat /\
  (scalar_tail p < lanes w)%nat.
Proof.
  intros. unfold validate_plan in H. apply andb_true_iff in H.
  destruct H. split; [apply Nat.eqb_eq | apply Nat.ltb_lt]; auto.
Qed.
Lemma checked_plan_valid: forall w n candidate, validate_plan w n (checked_plan w n candidate) = true.
Proof.
  intros. unfold checked_plan. destruct (validate_plan w n candidate) eqn:V; auto.
  apply plan_for_valid.
Qed.
Lemma checked_plan_preserves_valid:
  forall w n candidate, validate_plan w n candidate = true -> checked_plan w n candidate = candidate.
Proof. intros. unfold checked_plan. rewrite H. reflexivity. Qed.

Fixpoint vectorized_loop (fuel: nat) w op (input: list (Z * Z)) : list Z :=
  match fuel with
  | O => scalar_loop w op input
  | S fuel' =>
      if Nat.leb (lanes w) (length input)
      then eval_vector w op (firstn (lanes w) input) ++
           vectorized_loop fuel' w op (skipn (lanes w) input)
      else scalar_loop w op input
  end.
Definition execute_plan w op input p := vectorized_loop (vector_chunks p) w op input.
Definition vectorize w op input candidate :=
  execute_plan w op input (checked_plan w (length input) candidate).

Lemma vectorized_loop_scalar_equivalence:
  forall fuel w op input, vectorized_loop fuel w op input = scalar_loop w op input.
Proof.
  induction fuel; intros; simpl; auto.
  destruct (Nat.leb (lanes w) (length input)); auto.
  rewrite IHfuel. unfold eval_vector, scalar_loop.
  rewrite <- map_app. rewrite firstn_skipn. reflexivity.
Qed.
Theorem vectorize_preserves_elementwise_loop:
  forall w op input candidate, vectorize w op input candidate = scalar_loop w op input.
Proof. intros. unfold vectorize, execute_plan. apply vectorized_loop_scalar_equivalence. Qed.

Theorem compiled_loop_correct:
  forall w op input candidate plan,
  compile_loop w op (length input) candidate = Some plan ->
  instruction_supported w op = true /\
  validate_plan w (length input) plan = true /\
  execute_plan w op input plan = scalar_loop w op input.
Proof.
  intros. unfold compile_loop in H.
  destruct (instruction_supported w op) eqn:SUPPORTED; try discriminate.
  inversion H; subst plan. split; auto. split.
  - apply checked_plan_valid.
  - unfold execute_plan. apply vectorized_loop_scalar_equivalence.
Qed.

Example unsupported_multiply_refused:
  compile_loop W64 Vmul 10%nat (Plan 5%nat 0%nat) = None.
Proof. reflexivity. Qed.

Inductive execution_plan := Scalar_plan | Neon_plan (p: loop_plan).
Definition compile_plan w op n candidate :=
  match compile_loop w op n candidate with
  | Some p => Neon_plan p
  | None => Scalar_plan
  end.
Definition run_compiled w op input plan :=
  match plan with
  | Scalar_plan => scalar_loop w op input
  | Neon_plan p => execute_plan w op input p
  end.

Theorem compile_plan_preserves_scalar:
  forall w op input candidate,
  run_compiled w op input (compile_plan w op (length input) candidate) = scalar_loop w op input.
Proof.
  intros. unfold compile_plan.
  destruct (compile_loop w op (length input) candidate); simpl; auto.
  unfold execute_plan. apply vectorized_loop_scalar_equivalence.
Qed.

Theorem unsupported_instruction_uses_scalar:
  forall w op n candidate, instruction_supported w op = false ->
  compile_plan w op n candidate = Scalar_plan.
Proof. intros. unfold compile_plan, compile_loop. rewrite H. reflexivity. Qed.

Example reject_missing_tail: validate_plan W32 5%nat (Plan 1%nat 0%nat) = false.
Proof. reflexivity. Qed.
Example checked_tail_5: checked_plan W32 5%nat (Plan 99%nat 0%nat) = Plan 1%nat 1%nat.
Proof. reflexivity. Qed.
Example unsigned_wrap: eval_lane W8 Vadd 255 1 = 0.
Proof. reflexivity. Qed.

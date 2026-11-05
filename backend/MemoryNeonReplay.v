(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement.           *)
(*                                                                     *)
(* *********************************************************************)

(** Exact replay of the guarded two-lane memory update. *)
Require Import Coqlib Maps AST Integers Values Memory Globalenvs.
Require Import Op Registers RTL Builtins1 MemoryLaneFacts MemoryNeon.

Lemma execute_op:
  forall ge f sp n pc rs m op args dst next,
  (fn_code f)!pc = Some (Iop op args dst next) ->
  execute ge f sp (S n) pc rs m =
  match eval_operation ge sp op rs##args m with
  | Some v => execute ge f sp n next (rs#dst <- v) m
  | None => None end.
Proof.
  intros. simpl. rewrite H. unfold transfer. rewrite H.
  destruct (eval_operation ge sp op rs##args m); reflexivity.
Qed.

Lemma execute_global:
  forall ge f sp n pc rs m id dst next b,
  (fn_code f)!pc = Some (Iop (Oaddrsymbol id Ptrofs.zero) nil dst next) ->
  Genv.find_symbol ge id = Some b ->
  execute ge f sp (S n) pc rs m =
  execute ge f sp n next (rs#dst <- (Vptr b Ptrofs.zero)) m.
Proof.
  intros. rewrite (execute_op ge f sp n pc rs m _ _ _ _ H).
  cbn [List.map eval_operation]. unfold Genv.symbol_address.
  rewrite H0. reflexivity.
Qed.

Lemma execute_load:
  forall ge f sp n pc rs m chunk addr args dst next,
  (fn_code f)!pc = Some (Iload chunk addr args dst next) ->
  execute ge f sp (S n) pc rs m =
  match eval_addressing ge sp addr rs##args with
  | Some a => match Mem.loadv chunk m a with
              | Some v => execute ge f sp n next (rs#dst <- v) m
              | None => None end
  | None => None end.
Proof.
  intros. simpl. rewrite H. unfold transfer. rewrite H.
  destruct (eval_addressing ge sp addr rs##args); auto.
  destruct (Mem.loadv chunk m v); reflexivity.
Qed.

Lemma execute_cond:
  forall ge f sp n pc rs m cond args yes no,
  (fn_code f)!pc = Some (Icond cond args yes no) ->
  execute ge f sp (S n) pc rs m =
  match eval_condition cond rs##args m with
  | Some b => execute ge f sp n (if b then yes else no) rs m
  | None => None end.
Proof.
  intros. simpl. rewrite H. unfold transfer. rewrite H.
  destruct (eval_condition cond rs##args m); reflexivity.
Qed.

Lemma execute_store:
  forall ge f sp n pc rs m chunk addr args src next,
  (fn_code f)!pc = Some (Istore chunk addr args src next) ->
  execute ge f sp (S n) pc rs m =
  match eval_addressing ge sp addr rs##args with
  | Some a => match Mem.storev chunk m a rs#src with
              | Some m' => execute ge f sp n next rs m'
              | None => None end
  | None => None end.
Proof.
  intros. simpl. rewrite H. unfold transfer. rewrite H.
  destruct (eval_addressing ge sp addr rs##args); auto.
  destruct (Mem.storev chunk m v rs#src); reflexivity.
Qed.

Lemma execute_nop:
  forall ge f sp n pc rs m next,
  (fn_code f)!pc = Some (Inop next) ->
  execute ge f sp (S n) pc rs m = execute ge f sp n next rs m.
Proof. intros. simpl. rewrite H. unfold transfer. rewrite H. reflexivity. Qed.

Lemma execute_return:
  forall ge f sp n pc rs m,
  (fn_code f)!pc = Some (Ireturn None) ->
  execute ge f sp (S n) pc rs m = Some m.
Proof. intros. simpl. rewrite H. reflexivity. Qed.

Lemma execute_builtin:
  forall ge f sp n pc rs m a b dst next,
  (fn_code f)!pc = Some (Ibuiltin packed_builtin (BA a::BA b::nil) (BR dst) next) ->
  execute ge f sp (S n) pc rs m =
  execute ge f sp n next (rs#dst <- (packed_eval (rs#a) (rs#b))) m.
Proof.
  intros. simpl. rewrite H. unfold transfer. rewrite H.
  destruct (external_function_eq packed_builtin packed_builtin); congruence.
Qed.

Local Opaque execute.

Lemma global_index_zero: forall b,
  Val.addl (Vptr b Ptrofs.zero) (Vlong Int64.zero) = Vptr b Ptrofs.zero.
Proof. intros. reflexivity. Qed.

Lemma global_index_four: forall b,
  Val.addl (Vptr b Ptrofs.zero) (Vlong (Int64.repr 4)) = Vptr b (Ptrofs.repr 4).
Proof. intros. reflexivity. Qed.

Lemma store32_zero: forall m b v,
  Mem.storev Mint32 m (Vptr b Ptrofs.zero) v = Mem.store Mint32 m b 0 v.
Proof. intros. reflexivity. Qed.
Lemma store32_four: forall m b v,
  Mem.storev Mint32 m (Vptr b (Ptrofs.repr 4)) v = Mem.store Mint32 m b 4 v.
Proof. intros. reflexivity. Qed.
Lemma load64_zero: forall m b,
  Mem.loadv Mint64 m (Vptr b Ptrofs.zero) = Mem.load Mint64 m b 0.
Proof. intros. reflexivity. Qed.
Lemma load32_four: forall m b,
  Mem.loadv Mint32 m (Vptr b (Ptrofs.repr 4)) = Mem.load Mint32 m b 4.
Proof. intros. reflexivity. Qed.
Lemma store64_zero: forall m b v,
  Mem.storev Mint64 m (Vptr b Ptrofs.zero) v = Mem.store Mint64 m b 0 v.
Proof. intros. reflexivity. Qed.

Definition target_guard_regs (rs: regset) (b: block) (lo hi: int): regset :=
  Regmap.set 3%positive (Vint hi)
    (Regmap.set 2%positive (Vint lo) (Regmap.set 1%positive (Vptr b Ptrofs.zero) rs)).

Ltac simplify_regs_in H :=
  repeat rewrite Regmap.gsspec in H;
  repeat rewrite peq_true in H;
  repeat rewrite peq_false in H by discriminate;
  cbn beta iota zeta in H.

Ltac source_op H :=
  erewrite execute_op in H by (vm_compute; reflexivity);
  cbn [List.map eval_operation] in H;
  simplify_regs_in H;
  cbn [Val.add] in H.

Lemma target_prefix:
  forall ge p sp rs m b lo hi,
  Genv.find_symbol ge (global_id p) = Some b ->
  Mem.load Mint32 m b 0 = Some (Vint lo) ->
  Mem.load Mint32 m b 4 = Some (Vint hi) ->
  execute ge (target_template p) sp 32 7%positive rs m =
  execute ge (target_template p) sp 28
    (if Int.cmp Clt lo hi then 3%positive else 1%positive)
    (target_guard_regs rs b lo hi) m.
Proof.
  intros ge p sp rs m b lo hi SYMBOL LO HI.
  erewrite execute_op by (vm_compute; reflexivity).
  change (execute ge (target_template p) sp 31 6%positive
    (Regmap.set 1%positive (Genv.symbol_address ge (global_id p) Ptrofs.zero) rs) m =
    execute ge (target_template p) sp 28
      (if Int.cmp Clt lo hi then 3%positive else 1%positive)
      (target_guard_regs rs b lo hi) m).
  unfold Genv.symbol_address. rewrite SYMBOL.
  erewrite execute_load by (vm_compute; reflexivity).
  cbn [List.map eval_addressing]. rewrite Regmap.gss.
  change (Vlong {| Int64.intval := 0; Int64.intrange := Int64.Z_mod_modulus_range' 0 |}) with (Vlong Int64.zero).
  rewrite global_index_zero.
  change (Mem.loadv Mint32 m (Vptr b Ptrofs.zero)) with (Mem.load Mint32 m b 0).
  rewrite LO.
  erewrite execute_load by (vm_compute; reflexivity).
  cbn [List.map eval_addressing]. rewrite !Regmap.gsspec.
  repeat rewrite peq_true. repeat rewrite peq_false by discriminate.
  cbn beta iota zeta.
  change (Vlong {| Int64.intval := 4; Int64.intrange := Int64.Z_mod_modulus_range' 4 |}) with (Vlong (Int64.repr 4)).
  rewrite global_index_four.
  change (Mem.loadv Mint32 m (Vptr b (Ptrofs.repr 4))) with (Mem.load Mint32 m b 4).
  rewrite HI.
  erewrite execute_cond by (vm_compute; reflexivity).
  cbn [List.map eval_condition]. rewrite !Regmap.gsspec.
  repeat rewrite peq_true. repeat rewrite peq_false by discriminate.
  cbn beta iota zeta. reflexivity.
Qed.

Lemma execute_source_target:
  forall ge p sp rs m result,
  execute ge (source_template p) sp 32 22%positive rs m = Some result ->
  execute ge (target_template p) sp 32 7%positive rs m = Some result.
Proof.
  intros ge p sp rs m result SOURCE.
  erewrite execute_op in SOURCE by (vm_compute; reflexivity).
  change (execute ge (source_template p) sp 31 21%positive
    (Regmap.set 12%positive (Genv.symbol_address ge (global_id p) Ptrofs.zero) rs) m = Some result) in SOURCE.
  unfold Genv.symbol_address in SOURCE.
  destruct (Genv.find_symbol ge (global_id p)) as [b|] eqn:SYMBOL.
  all: erewrite execute_load in SOURCE by (vm_compute; reflexivity).
  all: cbn [List.map eval_addressing Val.addl] in SOURCE.
  all: rewrite Regmap.gss in SOURCE.
  2: cbn [Val.addl Mem.loadv] in SOURCE; discriminate.
  change (Vlong {| Int64.intval := 0; Int64.intrange := Int64.Z_mod_modulus_range' 0 |}) with (Vlong Int64.zero) in SOURCE.
  rewrite global_index_zero in SOURCE.
  change (Mem.loadv Mint32 m (Vptr b Ptrofs.zero)) with (Mem.load Mint32 m b 0) in SOURCE.
  destruct (Mem.load Mint32 m b 0) as [lo|] eqn:LOADLO; try discriminate.
  erewrite execute_op in SOURCE by (vm_compute; reflexivity).
  cbn [List.map eval_operation] in SOURCE.
  rewrite !Regmap.gsspec in SOURCE. repeat rewrite peq_true in SOURCE. repeat rewrite peq_false in SOURCE by discriminate. cbn beta iota zeta in SOURCE.
  erewrite execute_load in SOURCE by (vm_compute; reflexivity).
  cbn [List.map eval_addressing] in SOURCE.
  rewrite !Regmap.gsspec in SOURCE. repeat rewrite peq_true in SOURCE. repeat rewrite peq_false in SOURCE by discriminate. cbn beta iota zeta in SOURCE.
  change (Vlong {| Int64.intval := 4; Int64.intrange := Int64.Z_mod_modulus_range' 4 |}) with (Vlong (Int64.repr 4)) in SOURCE.
  rewrite global_index_four in SOURCE.
  change (Mem.loadv Mint32 m (Vptr b (Ptrofs.repr 4))) with (Mem.load Mint32 m b 4) in SOURCE.
  destruct (Mem.load Mint32 m b 4) as [hi|] eqn:LOADHI; try discriminate.
  erewrite execute_cond in SOURCE by (vm_compute; reflexivity).
  cbn [List.map eval_condition] in SOURCE.
  rewrite !Regmap.gsspec in SOURCE.
  repeat rewrite peq_true in SOURCE. repeat rewrite peq_false in SOURCE by discriminate.
  cbn beta iota zeta in SOURCE.
  destruct lo as [|lo| | | | ]; try (cbn [Val.cmp_bool] in SOURCE; discriminate).
  destruct hi as [|hi| | | | ]; try (cbn [Val.cmp_bool] in SOURCE; discriminate).
  cbn [Val.cmp_bool] in SOURCE.
  rewrite (target_prefix ge p sp rs m b lo hi SYMBOL LOADLO LOADHI).
  destruct (Int.cmp Clt lo hi) eqn:GUARD.
  2: {
    erewrite execute_return in SOURCE by (vm_compute; reflexivity).
    inv SOURCE. erewrite execute_return by (vm_compute; reflexivity). reflexivity.
  }
  erewrite execute_nop in SOURCE by (vm_compute; reflexivity).
  do 4 (source_op SOURCE).
  erewrite execute_store in SOURCE by (vm_compute; reflexivity).
  cbn [List.map eval_addressing] in SOURCE.
  simplify_regs_in SOURCE.
  change (Vlong {| Int64.intval := 0; Int64.intrange := Int64.Z_mod_modulus_range' 0 |}) with (Vlong Int64.zero) in SOURCE.
  rewrite global_index_zero in SOURCE.
  rewrite store32_zero in SOURCE. fold (low_add p) in SOURCE.
  destruct (Mem.store Mint32 m b 0 (Vint (Int.add lo (low_add p)))) as [m1|] eqn:STORELO; try discriminate.
  assert (HI1: Mem.load Mint32 m1 b 4 = Some (Vint hi)).
  { rewrite <- LOADHI. eapply Mem.load_store_other.
    - exact STORELO.
    - right; right; simpl; lia. }
  erewrite execute_nop in SOURCE by (vm_compute; reflexivity).
  erewrite execute_global with (id:=global_id p) (b:=b) in SOURCE.
  2: vm_compute; reflexivity.
  2: exact SYMBOL.
  source_op SOURCE.
  erewrite execute_load in SOURCE by (vm_compute; reflexivity).
  cbn [List.map eval_addressing] in SOURCE. simplify_regs_in SOURCE.
  change (Vlong {| Int64.intval := 4; Int64.intrange := Int64.Z_mod_modulus_range' 4 |}) with (Vlong (Int64.repr 4)) in SOURCE.
  rewrite global_index_four, load32_four, HI1 in SOURCE.
  do 2 (erewrite execute_nop in SOURCE by (vm_compute; reflexivity)).
  source_op SOURCE.
  erewrite execute_store in SOURCE by (vm_compute; reflexivity).
  cbn [List.map eval_addressing] in SOURCE. simplify_regs_in SOURCE.
  change (Vlong {| Int64.intval := 4; Int64.intrange := Int64.Z_mod_modulus_range' 4 |}) with (Vlong (Int64.repr 4)) in SOURCE.
  rewrite global_index_four, store32_four in SOURCE. fold (high_add p) in SOURCE.
  destruct (Mem.store Mint32 m1 b 4 (Vint (Int.add hi (high_add p)))) as [m2|] eqn:STOREHI; try discriminate.
  erewrite execute_nop in SOURCE by (vm_compute; reflexivity).
  erewrite execute_return in SOURCE by (vm_compute; reflexivity).
  inv SOURCE.
  assert (WIDELOAD: Mem.load Mint64 m b 0 = Some (Vlong (Int64.ofwords hi lo))).
  { eapply load_two_int32; eauto. change (8 | 0). exists 0; reflexivity. }
  assert (WIDESTORE: Mem.store Mint64 m b 0
      (Vlong (Int64.ofwords (Int.add hi (high_add p)) (Int.add lo (low_add p)))) = Some result).
  { eapply store_two_int32; eauto. change (8 | 0). exists 0; reflexivity. }
  erewrite execute_load by (vm_compute; reflexivity).
  unfold target_guard_regs. cbn [List.map eval_addressing]. rewrite !Regmap.gsspec.
  repeat rewrite peq_true. repeat rewrite peq_false by discriminate.
  cbn beta iota zeta.
  change (Vlong {| Int64.intval := 0; Int64.intrange := Int64.Z_mod_modulus_range' 0 |}) with (Vlong Int64.zero).
  rewrite global_index_zero, load64_zero, WIDELOAD.
  erewrite execute_op with (op:=Olongconst (Int64.ofwords (high_add p) (low_add p)))
    by reflexivity.
  cbn [List.map eval_operation].
  erewrite execute_builtin by (vm_compute; reflexivity).
  rewrite !Regmap.gsspec.
  repeat rewrite peq_true. repeat rewrite peq_false by discriminate.
  cbn beta iota zeta.
  cbn [packed_eval packed_u32x2].
  unfold packed_u32x2. rewrite !Int64.lo_ofwords, !Int64.hi_ofwords.
  erewrite execute_store by (vm_compute; reflexivity).
  cbn [List.map eval_addressing]. rewrite !Regmap.gsspec.
  repeat rewrite peq_true. repeat rewrite peq_false by discriminate.
  cbn beta iota zeta.
  change (Vlong {| Int64.intval := 0; Int64.intrange := Int64.Z_mod_modulus_range' 0 |}) with (Vlong Int64.zero).
  rewrite global_index_zero, store64_zero, WIDESTORE.
  erewrite execute_return by (vm_compute; reflexivity). reflexivity.
Qed.

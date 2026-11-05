(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Whole-program correctness of guarded independent-lane packing. *)
Require Import Coqlib Maps AST Linking Integers.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import Op Registers RTL Builtins0 Builtins1 Builtins Scheduleproof PointerNeonFacts PointerNeon.
Record valid_pair(f:function)(p:vector_pair):Prop := {
 valid_guard:(fn_code f)!(guard_pc p)=Some(Icond(Ccomp(guard_cond p))(low_reg p::high_reg p::nil)(first_pc p)(false_pc p));
 valid_first:(fn_code f)!(first_pc p)=Some(Iop(Oaddimm(first_imm p))(low_reg p::nil)(first_dst p)(second_pc p));
 valid_second:(fn_code f)!(second_pc p)=Some(Iop(Oaddimm(second_imm p))(high_reg p::nil)(second_dst p)(after_pc p));
 different_pcs:first_pc p<>second_pc p;
 guard_not_first:guard_pc p<>first_pc p;
 guard_not_second:guard_pc p<>second_pc p;
 false_not_first:false_pc p<>first_pc p;
 false_not_second:false_pc p<>second_pc p;
 entry_not_first:fn_entrypoint f<>first_pc p;
 entry_not_second:fn_entrypoint f<>second_pc p;
 low_not_first_dst:first_dst p<>low_reg p;
 high_not_first_dst:first_dst p<>high_reg p;
 different_dsts:first_dst p<>second_dst p;
 first_predecessor:forall pc i,(fn_code f)!pc=Some i ->In(first_pc p)(successors_instr i)->pc=guard_pc p;
 second_predecessor:forall pc i,(fn_code f)!pc=Some i ->In(second_pc p)(successors_instr i)->pc=first_pc p
}.
Lemma validate_candidate_sound:forall f g p,validate_candidate f g=Some p->valid_pair f p.
Proof.
 intros f g p. unfold validate_candidate.
 destruct(fn_code f)!g as[i|]eqn:G;try discriminate.
 destruct i as[n|op ar d n|ch ad ar d n|ch ad ar d n|sg ros ar d n|sg ros ar|ef ar res n|c ar a no|r tbl|r];try discriminate.
 destruct c;try discriminate. destruct ar as[|lo[|hi tail]];try discriminate. destruct tail;try discriminate.
 destruct(fn_code f)!a as[i|]eqn:A;try discriminate.
 destruct i as[n|op ar d b|ch ad ar d n|ch ad ar d n|sg ros ar d n|sg ros ar|ef ar res n|cond ar n no2|r tbl|r];try discriminate.
 destruct op;try discriminate. destruct ar as[|rlo tail];try discriminate. destruct tail;try discriminate.
 destruct(fn_code f)!b as[i|]eqn:B;try discriminate.
 destruct i as[n2|op2 ar2 d2 aft|ch2 ad2 ar2 d2 n2|ch2 ad2 ar2 d2 n2|sg2 ros2 ar2 d2 n2|sg2 ros2 ar2|ef2 ar2 res2 n2|cond2 ar2 n2 no3|r2 tbl2|r2];try discriminate.
 destruct op2;try discriminate. destruct ar2 as[|rhi tail2];try discriminate. destruct tail2;try discriminate.
 destruct(peq lo rlo);try discriminate;subst rlo.
 destruct(peq hi rhi);try discriminate;subst rhi.
 destruct(peq g a);try discriminate. destruct(peq g b);try discriminate.
 destruct(peq a b);try discriminate. destruct(peq no a);try discriminate.
 destruct(peq no b);try discriminate. destruct(peq(fn_entrypoint f)a);try discriminate.
 destruct(peq(fn_entrypoint f)b);try discriminate. destruct(peq d lo);try discriminate.
 destruct(peq d hi);try discriminate. destruct(peq d d2);try discriminate.
 destruct(Schedule.predecessor_check f g a)eqn:P1;try discriminate.
 destruct(Schedule.predecessor_check f a b)eqn:P2;try discriminate.
 intro EQ;inv EQ. constructor;simpl;auto;
 eapply Scheduleproof.predecessor_check_sound;eauto.
Qed.
Lemma find_candidate_sound:forall f items p,find_candidate f items=Some p->valid_pair f p.
Proof.
 intros f items;induction items as[|[pc i]rest IH];simpl;intros p E;try discriminate.
 destruct(validate_candidate f pc)as[q|]eqn:C;[inv E;eapply validate_candidate_sound;eauto|eauto].
Qed.
Lemma selected_pair_sound:forall f p,selected_pair f=Some p->valid_pair f p.
Proof. unfold selected_pair;intros;destruct(Nat.leb _ _);try discriminate;eapply find_candidate_sound;eauto. Qed.
Definition regs_match (f: function) (rs trs: regset): Prop :=
  forall r, Ple r (max_reg_function f) -> trs#r = rs#r.
Lemma regs_match_refl: forall f rs, regs_match f rs rs.
Proof. red; auto. Qed.
Lemma regs_match_list:
  forall f rs trs args, regs_match f rs trs ->
  (forall r, In r args -> Ple r (max_reg_function f)) -> trs##args = rs##args.
Proof. intros; apply list_map_exten; intros; symmetry; auto. Qed.
Lemma regs_match_set:
  forall f rs trs r v, regs_match f rs trs ->
  regs_match f (rs#r <- v) (trs#r <- v).
Proof.
  red; intros. rewrite !Regmap.gsspec. destruct (peq r0 r); auto.
Qed.
Lemma regs_match_setres:
  forall f rs trs res v, regs_match f rs trs ->
  regs_match f (regmap_setres res v rs) (regmap_setres res v trs).
Proof. destruct res; simpl; intros; auto using regs_match_set. Qed.
Lemma regs_match_fresh:
  forall f rs trs r v, regs_match f rs trs -> Plt (max_reg_function f) r ->
  regs_match f rs (trs#r <- v).
Proof. red; intros. rewrite Regmap.gso by extlia. auto. Qed.

Lemma fresh_regs:
  forall f,
  Plt (max_reg_function f) (input_reg f) /\
  Plt (max_reg_function f) (constant_reg f) /\
  Plt (max_reg_function f) (result_reg f) /\
  input_reg f <> constant_reg f /\ input_reg f <> result_reg f /\
  constant_reg f <> result_reg f.
Proof. unfold result_reg, constant_reg, input_reg; intros; repeat split; extlia. Qed.
Lemma fresh_nodes:
  forall f,
  Plt (max_pc_function f) (constant_pc f) /\
  Plt (max_pc_function f) (builtin_pc f) /\
  Plt (max_pc_function f) (extract_pc f) /\
  constant_pc f <> builtin_pc f /\ constant_pc f <> extract_pc f /\
  builtin_pc f <> extract_pc f.
Proof. unfold extract_pc, builtin_pc, constant_pc; intros; repeat split; extlia. Qed.

Lemma metadata_preserved:forall f,
 fn_sig(transf_function f)=fn_sig f /\ fn_stacksize(transf_function f)=fn_stacksize f /\
 fn_params(transf_function f)=fn_params f /\fn_entrypoint(transf_function f)=fn_entrypoint f.
Proof. intros;unfold transf_function;destruct(selected_pair f);simpl;tauto. Qed.
Definition safe_pc(f:function)(pc:node):Prop :=
 match selected_pair f with Some p=>pc<>first_pc p /\pc<>second_pc p|None=>True end.
Lemma entry_safe:forall f,safe_pc f(fn_entrypoint f).
Proof.
 unfold safe_pc;intros;destruct(selected_pair f)as[p|]eqn:S;auto.
 pose proof(selected_pair_sound _ _ S);split;eauto using entry_not_first,entry_not_second.
Qed.
Definition match_prog(p tp:RTL.program):=match_program(fun ctx f tf=>tf=transf_fundef f)eq p tp.
Global Instance TransfPointerNeonLink:TransfLink match_prog:=TransfTotalLink transf_function.
Lemma transf_program_match:forall p,match_prog p(transf_program p).
Proof. intros;apply match_transform_program. Qed.
Lemma selected_bounds:forall f p,selected_pair f=Some p->
 Ple(guard_pc p)(max_pc_function f) /\Ple(first_pc p)(max_pc_function f) /\Ple(second_pc p)(max_pc_function f) /\
 Ple(low_reg p)(max_reg_function f) /\Ple(high_reg p)(max_reg_function f) /\
 Ple(first_dst p)(max_reg_function f) /\Ple(second_dst p)(max_reg_function f).
Proof.
 intros f p SELECT;pose proof(selected_pair_sound _ _ SELECT)as V.
 pose proof(valid_guard _ _ V)as G;pose proof(valid_first _ _ V)as A;pose proof(valid_second _ _ V)as B.
 repeat split;eauto using max_pc_function_sound,max_reg_function_def.
 - eapply max_reg_function_use;[exact A|simpl;auto].
 - eapply max_reg_function_use;[exact B|simpl;auto].
Qed.
Lemma transformed_first:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(first_pc plan) =
    Some (Iop Omakelong (plan.(high_reg) :: plan.(low_reg) :: nil)
               (input_reg f) (constant_pc f)).
Proof. unfold transf_function; intros. rewrite H. simpl. apply PTree.gss. Qed.
Lemma transformed_constant:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(constant_pc f) =
    Some (Iop (Olongconst (packed_constant plan)) nil (constant_reg f) (builtin_pc f)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  unfold transf_function; rewrite SELECT; simpl. rewrite PTree.gso by extlia. apply PTree.gss.
Qed.
Lemma transformed_builtin:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(builtin_pc f) =
    Some (Ibuiltin packed_builtin (BA (input_reg f) :: BA (constant_reg f) :: nil)
               (BR (result_reg f)) (extract_pc f)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  unfold transf_function; rewrite SELECT; simpl. rewrite !PTree.gso by extlia. apply PTree.gss.
Qed.
Lemma transformed_extract:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(extract_pc f) =
    Some (Iop Olowlong (result_reg f :: nil) plan.(first_dst) plan.(second_pc)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  unfold transf_function; rewrite SELECT; simpl. rewrite !PTree.gso by extlia. apply PTree.gss.
Qed.
Lemma transformed_second:
  forall f plan, selected_pair f = Some plan ->
  (fn_code (transf_function f))!(second_pc plan) =
    Some (Iop Ohighlong (result_reg f :: nil) plan.(second_dst) plan.(after_pc)).
Proof.
  intros f plan SELECT. pose proof (selected_bounds _ _ SELECT). pose proof (fresh_nodes f).
  pose proof (different_pcs _ _ (selected_pair_sound _ _ SELECT)).
  unfold transf_function; rewrite SELECT; simpl. rewrite !PTree.gso by extlia. apply PTree.gss.
Qed.


Lemma transformed_guard:forall f p,selected_pair f=Some p->
 (fn_code(transf_function f))!(guard_pc p)=Some(Icond(Ccomp(guard_cond p))(low_reg p::high_reg p::nil)(first_pc p)(false_pc p)).
Proof.
 intros f p SELECT;pose proof(selected_bounds _ _ SELECT);pose proof(fresh_nodes f).
 pose proof(selected_pair_sound _ _ SELECT)as V.
 pose proof(guard_not_first _ _ V);pose proof(guard_not_second _ _ V).
 unfold transf_function;rewrite SELECT;simpl. rewrite !PTree.gso by(try extlia;congruence).
 apply valid_guard;auto.
Qed.
Lemma false_safe:forall f p,selected_pair f=Some p->safe_pc f(false_pc p).
Proof.
 intros f p SELECT;pose proof(selected_pair_sound _ _ SELECT)as V.
 unfold safe_pc;rewrite SELECT;split;eauto using false_not_first,false_not_second.
Qed.
Lemma after_safe:forall f p,selected_pair f=Some p->safe_pc f(after_pc p).
Proof.
 intros f p SELECT;pose proof(selected_pair_sound _ _ SELECT)as V.
 unfold safe_pc;rewrite SELECT;split;intro E.
 - assert(second_pc p=guard_pc p).
   { eapply first_predecessor;[exact V|apply valid_second;auto|simpl;auto]. }
   pose proof(guard_not_second _ _ V);congruence.
 - assert(second_pc p=first_pc p).
   { eapply second_predecessor;[exact V|apply valid_second;auto|simpl;auto]. }
   pose proof(different_pcs _ _ V);congruence.
Qed.
Lemma normal_classification:forall f pc,safe_pc f pc->
 (exists p,selected_pair f=Some p /\pc=guard_pc p) \/
 ((forall i,(fn_code f)!pc=Some i->(fn_code(transf_function f))!pc=Some i) /\
  forall i next,(fn_code f)!pc=Some i->In next(successors_instr i)->safe_pc f next).
Proof.
 intros f pc SAFE;unfold safe_pc in SAFE;destruct(selected_pair f)as[p|]eqn:SELECT.
 - destruct(peq pc(guard_pc p))as[EQ|NE].
   + left;eauto.
   + right;split.
     * intros i GET;pose proof(max_pc_function_sound _ _ _ GET);pose proof(fresh_nodes f).
       destruct SAFE as[SF SS]. unfold transf_function;rewrite SELECT;simpl.
       rewrite !PTree.gso by(try extlia;congruence);auto.
     * intros i next GET EDGE;unfold safe_pc;rewrite SELECT;split;intro EQ;subst next.
       -- apply NE;eapply first_predecessor;eauto using selected_pair_sound.
       -- apply(proj1 SAFE);eapply second_predecessor;eauto using selected_pair_sound.
 - right;split.
   + intros;unfold transf_function;rewrite SELECT;auto.
   + intros;unfold safe_pc;rewrite SELECT;auto.
Qed.
Section PRESERVATION.
Variables prog tprog: RTL.program.
Hypothesis TRANSL: match_prog prog tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Lemma functions_translated:
  forall v f, Genv.find_funct ge v = Some f -> Genv.find_funct tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_transf TRANSL). Qed.
Lemma function_ptr_translated:
  forall v f, Genv.find_funct_ptr ge v = Some f -> Genv.find_funct_ptr tge v = Some (transf_fundef f).
Proof. exact (Genv.find_funct_ptr_transf TRANSL). Qed.
Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. exact (Genv.find_symbol_transf TRANSL). Qed.
Lemma senv_preserved: Senv.equiv ge tge.
Proof. exact (Genv.senv_transf TRANSL). Qed.
Lemma sig_preserved: forall f, funsig (transf_fundef f) = funsig f.
Proof. destruct f; simpl; auto. apply metadata_preserved. Qed.

Lemma builtin_arg_regs:
  forall f rs trs sp m arg v,
  regs_match f rs trs -> eval_builtin_arg ge (fun r => rs#r) sp m arg v ->
  (forall r, In r (params_of_builtin_arg arg) -> Ple r (max_reg_function f)) ->
  eval_builtin_arg ge (fun r => trs#r) sp m arg v.
Proof.
  intros f rs trs sp m arg v REGS EV. induction EV; simpl; intros;
  try (constructor; eauto using in_or_app).
  rewrite <- (REGS x) by eauto with coqlib. constructor.
Qed.
Lemma builtin_args_regs:
  forall f rs trs sp m args vl,
  regs_match f rs trs -> eval_builtin_args ge (fun r => rs#r) sp m args vl ->
  (forall r, In r (params_of_builtin_args args) -> Ple r (max_reg_function f)) ->
  eval_builtin_args ge (fun r => trs#r) sp m args vl.
Proof.
  unfold eval_builtin_args; intros f rs trs sp m args vl REGS EV.
  induction EV; simpl; intros; constructor; eauto using builtin_arg_regs, in_or_app.
Qed.

Inductive match_frames:RTL.stackframe->RTL.stackframe->Prop :=
 | match_frame:forall res f sp pc rs trs (REGS:regs_match f rs trs)(SAFE:safe_pc f pc),
   match_frames(Stackframe res f sp pc rs)(Stackframe res(transf_function f)sp pc trs).
Inductive match_states:RTL.state->RTL.state->Prop :=
 | match_normal:forall stk f sp pc rs trs m stk'
   (STACKS:list_forall2 match_frames stk stk')(REGS:regs_match f rs trs)(SAFE:safe_pc f pc),
   match_states(State stk f sp pc rs m)(State stk'(transf_function f)sp pc trs m)
 | match_ready:forall stk f sp rs trs m stk' p lo hi
   (STACKS:list_forall2 match_frames stk stk')(REGS:regs_match f rs trs)(SELECT:selected_pair f=Some p)
   (LOW:rs#(low_reg p)=Vint lo)(HIGH:rs#(high_reg p)=Vint hi),
   match_states(State stk f sp(first_pc p)rs m)(State stk'(transf_function f)sp(first_pc p)trs m)
 | match_intermediate:forall stk f sp rs trs m stk' p lo hi
   (STACKS:list_forall2 match_frames stk stk')(REGS:regs_match f rs trs)(SELECT:selected_pair f=Some p)
   (LOW:rs#(low_reg p)=Vint lo)(HIGH:rs#(high_reg p)=Vint hi),
   match_states(State stk f sp(second_pc p)(rs#(first_dst p)<-(Val.add rs#(low_reg p)(Vint(first_imm p))))m)
               (State stk'(transf_function f)sp(first_pc p)trs m)
 | match_call:forall stk fd args m stk'(STACKS:list_forall2 match_frames stk stk'),
   match_states(Callstate stk fd args m)(Callstate stk'(transf_fundef fd)args m)
 | match_return:forall stk v m stk'(STACKS:list_forall2 match_frames stk stk'),
   match_states(Returnstate stk v m)(Returnstate stk' v m).
Definition measure(st:RTL.state):nat :=
 match st with State _ f _ pc _ _=>match selected_pair f with
 Some p=>if peq pc(second_pc p)then O else S O|None=>S O end|_=>S O end.
Ltac ORIGINAL_BOUNDS :=
  match goal with
  | GET: (fn_code ?f)!?pc = Some ?i |- _ =>
      assert (USES: forall r, In r (instr_uses i) -> Ple r (max_reg_function f))
        by (intros; eapply max_reg_function_use; eauto)
  end.

Lemma normal_step:
 forall stk f sp pc rs m trace after,
 RTL.step ge(State stk f sp pc rs m)trace after->
 forall stk' trs,list_forall2 match_frames stk stk'->regs_match f rs trs->safe_pc f pc->
 exists target,plus RTL.step tge(State stk'(transf_function f)sp pc trs m)trace target /\match_states after target.
Proof.
 intros stk f sp pc rs m trace after STEP stk' trs STACKS REGS SAFE.
 destruct(normal_classification f pc SAFE)as[[p[SELECT PC]]|[CODE NEXT]].
 - subst pc;pose proof(selected_pair_sound _ _ SELECT)as V.
   pose proof(valid_guard _ _ V)as G;pose proof(selected_bounds _ _ SELECT)as BOUNDS.
   inversion STEP;subst;try congruence.
   match goal with GET:(fn_code f)!(guard_pc p)=Some _|-_=>rewrite G in GET;inv GET end.
   match goal with E:eval_condition _ _ _=Some _|-_=>rename E into COND end.
   assert(ARGS:trs##(low_reg p::high_reg p::nil)=rs##(low_reg p::high_reg p::nil)).
   { eapply (regs_match_list f);auto. intros r IN;simpl in IN;destruct IN as[<-|[<-|[]]];tauto. }
   exists(State stk'(transf_function f)sp(if b then first_pc p else false_pc p)trs m);split.
   + apply plus_one;eapply exec_Icond with(b:=b);[apply transformed_guard;eauto|rewrite ARGS;exact COND|reflexivity].
   + destruct b.
     * destruct(signed_condition_defined _ _ _ _ _ COND)as[lo[hi[LOW HIGH]]].
       eapply match_ready;eauto.
     * constructor;auto;eapply false_safe;eauto.
  - inversion STEP; subst; ORIGINAL_BOUNDS.
    + econstructor; split. apply plus_one; eapply exec_Inop; eauto.
      constructor; auto. eapply NEXT; eauto; simpl; auto.
    + econstructor; split. apply plus_one; eapply exec_Iop; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
      match goal with E: eval_operation ge _ _ _ _ = Some _ |- _ => rewrite <- E end.
      apply eval_operation_preserved; exact symbols_preserved.
      constructor; auto using regs_match_set. eapply NEXT; eauto; simpl; auto.
    + econstructor; split. apply plus_one; eapply exec_Iload; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; auto).
      match goal with E: eval_addressing ge _ _ _ = Some _ |- _ => rewrite <- E end.
      apply eval_addressing_preserved; exact symbols_preserved.
      constructor; auto using regs_match_set. eapply NEXT; eauto; simpl; auto.
    + econstructor; split. apply plus_one; eapply exec_Istore; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto).
      match goal with E: eval_addressing ge _ _ _ = Some _ |- _ => rewrite <- E end.
      apply eval_addressing_preserved; exact symbols_preserved.
      rewrite REGS by (apply USES; simpl; auto). eauto.
      constructor; auto. eapply NEXT; eauto; simpl; auto.
    + assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
      { unfold find_function in *. destruct ros as [r|id].
        rewrite REGS by (apply USES; simpl; auto). apply functions_translated; auto.
        rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
        apply function_ptr_translated; auto. }
      econstructor; split. apply plus_one; eapply exec_Icall; eauto.
      apply sig_preserved.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
      constructor. constructor; auto. constructor; auto.
      eapply NEXT; eauto; simpl; auto.
    + assert (FIND: find_function tge ros trs = Some (transf_fundef fd)).
      { unfold find_function in *. destruct ros as [r|id].
        rewrite REGS by (apply USES; simpl; auto). apply functions_translated; auto.
        rewrite symbols_preserved. destruct (Genv.find_symbol ge id); try congruence.
        apply function_ptr_translated; auto. }
      econstructor; split. apply plus_one; eapply exec_Itailcall; eauto.
      apply sig_preserved.
      rewrite (proj1 (proj2 (metadata_preserved f))); eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; destruct ros; simpl; auto).
      constructor; auto.
    + econstructor; split. apply plus_one; eapply exec_Ibuiltin; eauto.
      eapply eval_builtin_args_preserved with (ge1:=ge); eauto. exact symbols_preserved.
      eapply builtin_args_regs; eauto.
      eapply external_call_symbols_preserved; eauto; apply senv_preserved.
      constructor; auto using regs_match_setres. eapply NEXT; eauto; simpl; auto.
    + econstructor; split. apply plus_one; eapply exec_Icond; eauto.
      rewrite (regs_match_list f rs trs args REGS) by (intros; apply USES; simpl; auto); eauto.
      constructor; auto. eapply NEXT; eauto; simpl; destruct b; auto.
    + econstructor; split. apply plus_one; eapply exec_Ijumptable; eauto.
      rewrite REGS by (apply USES; simpl; auto); eauto.
      constructor; auto. eapply NEXT; eauto; simpl; eapply list_nth_z_in; eauto.
    + econstructor; split. apply plus_one; eapply exec_Ireturn; eauto.
      rewrite (proj1 (proj2 (metadata_preserved f))); eauto.
      destruct or; simpl. rewrite REGS by (apply USES; simpl; auto); constructor; auto.
      constructor; auto.
Qed.

Lemma ready_step:
 forall stk f sp rs trs m p lo hi trace after,
 selected_pair f=Some p->regs_match f rs trs->rs#(low_reg p)=Vint lo->rs#(high_reg p)=Vint hi->
 RTL.step ge(State stk f sp(first_pc p)rs m)trace after->
 forall stk',list_forall2 match_frames stk stk'->
 (measure after<measure(State stk f sp(first_pc p)rs m) /\trace=E0 /\
 match_states after(State stk'(transf_function f)sp(first_pc p)trs m))%nat.
Proof.
 intros stk f sp rs trs m p lo hi trace after SELECT REGS LOW HIGH STEP stk' STACKS.
 pose proof(selected_pair_sound _ _ SELECT)as V;pose proof(valid_first _ _ V)as FIRST.
 inversion STEP;subst;try congruence.
 match goal with GET:(fn_code f)!(first_pc p)=Some _|-_=>rewrite FIRST in GET;inv GET end.
 match goal with E:eval_operation _ _ _ _ _=Some _|-_=>simpl in E;inv E end.
 split.
 - unfold measure;rewrite SELECT;rewrite peq_true.
   destruct(peq(first_pc p)(second_pc p));simpl;try lia.
   pose proof(different_pcs _ _ V);congruence.
 - split;auto;eapply match_intermediate;eauto.
Qed.
Lemma run_vector_pair:
 forall f p stk sp rs trs m lo hi,
 selected_pair f=Some p->regs_match f rs trs->rs#(low_reg p)=Vint lo->rs#(high_reg p)=Vint hi->
 exists final_regs,
 plus RTL.step tge(State stk(transf_function f)sp(first_pc p)trs m)E0
   (State stk(transf_function f)sp(after_pc p)final_regs m) /\
 regs_match f ((rs#(first_dst p)<-(Val.add rs#(low_reg p)(Vint(first_imm p))))
   #(second_dst p)<-(Val.add rs#(high_reg p)(Vint(second_imm p))))final_regs.
Proof.
 intros f p stk sp rs trs m lo hi SELECT REGS LOW HIGH.
 pose proof(selected_bounds _ _ SELECT)as BOUNDS;pose proof(fresh_regs f)as FRESH.
 assert(LO:trs#(low_reg p)=Vint lo)by(rewrite REGS by tauto;auto).
 assert(HI:trs#(high_reg p)=Vint hi)by(rewrite REGS by tauto;auto).
 set(t0:=trs#(input_reg f)<-(Vlong(Int64.ofwords hi lo))).
 set(t1:=t0#(constant_reg f)<-(Vlong(packed_constant p))).
 set(t2:=t1#(result_reg f)<-(packed_add_result lo hi(first_imm p)(second_imm p))).
 set(t3:=t2#(first_dst p)<-(Val.add rs#(low_reg p)(Vint(first_imm p)))).
 set(t4:=t3#(second_dst p)<-(Val.add rs#(high_reg p)(Vint(second_imm p)))).
 exists t4;split.
 - eapply plus_left with(s2:=State stk(transf_function f)sp(constant_pc f)t0 m)(t1:=E0)(t2:=E0).
   + eapply exec_Iop;[apply transformed_first;eauto|]. simpl;rewrite LO,HI;reflexivity.
   + eapply star_four with
      (s2:=State stk(transf_function f)sp(builtin_pc f)t1 m)
      (s3:=State stk(transf_function f)sp(extract_pc f)t2 m)
      (s4:=State stk(transf_function f)sp(second_pc p)t3 m)
      (t1:=E0)(t2:=E0)(t3:=E0)(t4:=E0).
     * eapply exec_Iop;[apply transformed_constant;eauto|reflexivity].
     * eapply exec_Ibuiltin with(res:=BR(result_reg f))
        (vres:=packed_add_result lo hi(first_imm p)(second_imm p))
        (vargs:=Vlong(Int64.ofwords hi lo)::Vlong(packed_constant p)::nil).
       exact(transformed_builtin f p SELECT).
       assert(A1:t1#(input_reg f)=Vlong(Int64.ofwords hi lo)).
       { unfold t1,t0;rewrite Regmap.gso by extlia;apply Regmap.gss. }
       assert(A2:t1#(constant_reg f)=Vlong(packed_constant p))by(unfold t1;apply Regmap.gss).
       unfold eval_builtin_args;constructor;[rewrite <-A1;constructor|constructor;[rewrite <-A2;constructor|constructor]].
       exact(packed_add_builtin tge lo hi(first_imm p)(second_imm p)m).
     * eapply exec_Iop;[apply transformed_extract;eauto|].
       simpl;unfold t2;rewrite Regmap.gss,(proj1(packed_add_low_high _ _ _ _)),LOW;reflexivity.
     * eapply exec_Iop;[apply transformed_second;eauto|].
       simpl;unfold t3,t2;rewrite Regmap.gso by extlia.
       rewrite Regmap.gss,(proj2(packed_add_low_high _ _ _ _)),HIGH;reflexivity.
     * reflexivity.
   + reflexivity.
 - unfold t4,t3;apply regs_match_set;apply regs_match_set.
   unfold t2,t1,t0;repeat apply regs_match_fresh;tauto.
Qed.
Lemma intermediate_step:
  forall stk f sp rs trs m plan lo hi trace after,
  selected_pair f = Some plan -> regs_match f rs trs ->
  rs#(low_reg plan)=Vint lo ->rs#(high_reg plan)=Vint hi ->
  RTL.step ge
    (State stk f sp plan.(second_pc)
      (rs#(first_dst plan) <- (Val.add (rs#(low_reg plan)) (Vint plan.(first_imm)))) m)
    trace after ->
  forall stk', list_forall2 match_frames stk stk' ->
  exists target, plus RTL.step tge (State stk' (transf_function f) sp plan.(first_pc) trs m)
                   trace target /\ match_states after target.
Proof.
  intros stk f sp rs trs m plan lo hi trace after SELECT REGS LOW HIGH STEP stk' STACKS.
  pose proof (selected_pair_sound _ _ SELECT) as VALID.
  pose proof (valid_second _ _ VALID) as SECOND.
  inversion STEP; subst; try congruence.
  match goal with GET: (fn_code f)!(second_pc plan) = Some _ |- _ => rewrite SECOND in GET; inv GET end.
  pose proof (high_not_first_dst _ _ VALID) as NE.
  match goal with E: eval_operation _ _ _ _ _ = Some _ |- _ =>
    simpl in E; rewrite Regmap.gso in E by congruence; inv E end.
  destruct (run_vector_pair f plan stk' sp rs trs m lo hi SELECT REGS LOW HIGH) as [final_regs [RUN MATCH]].
  econstructor; split. exact RUN. constructor; auto. eapply after_safe; eauto.
Qed.

Lemma step_simulation:
  forall source trace after, RTL.step ge source trace after ->
  forall target, match_states source target ->
  (exists target_after, plus RTL.step tge target trace target_after /\ match_states after target_after) \/
  (measure after < measure source /\ trace = E0 /\ match_states after target)%nat.
Proof.
  intros source trace after STEP target MATCH. inv MATCH.
  - left. eapply normal_step; eauto.
  - right. eapply ready_step; eauto.
  - left. eapply intermediate_step; eauto.
  - inversion STEP; subst.
    + left. destruct (metadata_preserved f) as [SIG [STACK [PARAM ENTRY]]].
      exists (State stk' (transf_function f) (Vptr stk0 Ptrofs.zero)
                    (fn_entrypoint f) (init_regs args (fn_params f)) m'); split.
      * apply plus_one.
        assert (RUN: RTL.step tge (Callstate stk' (Internal (transf_function f)) args m)
          E0 (State stk' (transf_function f) (Vptr stk0 Ptrofs.zero)
            (fn_entrypoint (transf_function f)) (init_regs args (fn_params (transf_function f))) m')).
        { eapply exec_function_internal; rewrite ?SIG, ?STACK; eauto. }
        rewrite ENTRY, PARAM in RUN. exact RUN.
      * constructor; auto using regs_match_refl, entry_safe.
    + left; econstructor; split. apply plus_one; eapply exec_function_external; eauto.
      eapply external_call_symbols_preserved; eauto; apply senv_preserved.
      constructor; auto.
  - inversion STEP; subst. inv STACKS. inv H1.
    left; econstructor; split. apply plus_one; eapply exec_return; eauto.
    constructor; auto using regs_match_set.
Qed.
Lemma transf_initial_states:
  forall source, RTL.initial_state prog source ->
  exists target, RTL.initial_state tprog target /\ match_states source target.
Proof.
  intros;inv H. exists(Callstate nil(transf_fundef f)nil m0);split.
  - econstructor.
    + eapply(Genv.init_mem_transf TRANSL);eauto.
    + rewrite symbols_preserved.
      exact(eq_trans(f_equal(Genv.find_symbol ge)(match_program_main TRANSL))H1).
    + eapply function_ptr_translated;eauto.
    + rewrite <-H3;apply sig_preserved.
  - constructor;constructor.
Qed.
Lemma transf_final_states:
  forall source target result, match_states source target -> RTL.final_state source result ->
  RTL.final_state target result.
Proof. intros; inv H0; inv H; inv STACKS; constructor. Qed.
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  apply senv_preserved. exact transf_initial_states. exact transf_final_states. exact step_simulation.
Qed.
End PRESERVATION.

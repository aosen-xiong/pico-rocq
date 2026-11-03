From Stdlib Require Import List Lia PeanoNat Wf_nat.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation MutationSafety.

(** Progress.

    The evaluation relation of the development is big-step: a statement that
    gets stuck and a statement that runs forever both have no derivation, so
    theorems about derivations say nothing about either.  This file adds a
    step budget.  Only a method call can run forever (there are no loops), so
    a call spends one unit of budget and a call with no budget left ends in
    [FTimeout].

    With a budget, every well-typed statement run from a well-formed state
    has an outcome, and the outcome is one of three: it finished normally, it
    ended in a null dereference, or the budget ran out.  It is never stuck
    and never a rejected write.  A statement that runs forever is one whose
    budget runs out for every budget. *)

(* ------------------EVALUATION WITH A BUDGET------------------*)

Inductive fres :=
| FDone (r : eval_result)
| FTimeout.

(** The statements that are evaluated in one step. *)
Definition atomic (s : stmt) : Prop :=
  match s with
  | SSeq _ _ => False
  | SCall _ _ _ _ _ _ => False
  | _ => True
  end.

(** The rules follow the rules of [eval_stmt] one for one. *)
Inductive eval_fuel
    : class_table -> nat -> r_env -> heap -> stmt -> fres -> r_env -> heap -> Prop :=
  | EF_Atom : forall CT n rΓ h s r rΓ' h'
      (Hatom : atomic s)
      (Heval : eval_stmt CT rΓ h s r rΓ' h'),
      eval_fuel CT n rΓ h s (FDone r) rΓ' h'

  | EF_Call_NPE : forall CT n rΓ h x y m Us Qs zs
      (Hnull : runtime_getVal rΓ y = Some Null_a),
      eval_fuel CT n rΓ h (SCall x m y Us Qs zs) (FDone NPE) rΓ h

  (* a call that would start, with no budget left *)
  | EF_Call_Timeout : forall CT rΓ h x y m Us Qs zs vals ly cy D mdef rΓ'
      (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase  : r_basetype h ly = Some cy)
      (Hfind  : FindMethodWithName CT cy m D mdef)
      (Hargs  : runtime_lookup_list rΓ zs = Some vals)
      (Hframe : callee_env CT rΓ h ly D Us Qs vals rΓ'),
      eval_fuel CT 0 rΓ h (SCall x m y Us Qs zs) FTimeout rΓ h

  | EF_Call : forall CT n rΓ h x y m Us Qs zs vals ly cy D mdef retval h' rΓ' rΓ''
      (Hval_y  : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase   : r_basetype h ly = Some cy)
      (Hfind   : FindMethodWithName CT cy m D mdef)
      (Hargs   : runtime_lookup_list rΓ zs = Some vals)
      (Hframe  : callee_env CT rΓ h ly D Us Qs vals rΓ')
      (Hbody   : eval_fuel CT n rΓ' h (mbody_stmt (mbody mdef)) (FDone OK) rΓ'' h')
      (Hretval : runtime_getVal rΓ'' (mreturn (mbody mdef)) = Some retval),
      eval_fuel CT (S n) rΓ h (SCall x m y Us Qs zs) (FDone OK)
        (set_vars rΓ (update x retval (vars rΓ))) h'

  (* the body ends in an error, or its budget runs out *)
  | EF_Call_Fail : forall CT n rΓ h x y m Us Qs zs vals ly cy D mdef r h' rΓ' rΓ''
      (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase  : r_basetype h ly = Some cy)
      (Hfind  : FindMethodWithName CT cy m D mdef)
      (Hargs  : runtime_lookup_list rΓ zs = Some vals)
      (Hframe : callee_env CT rΓ h ly D Us Qs vals rΓ')
      (Hbody  : eval_fuel CT n rΓ' h (mbody_stmt (mbody mdef)) r rΓ'' h')
      (Hfail  : r <> FDone OK),
      eval_fuel CT (S n) rΓ h (SCall x m y Us Qs zs) r rΓ'' h'

  | EF_Seq : forall CT n rΓ h s1 s2 r rΓ' h' rΓ'' h''
      (Heval1 : eval_fuel CT n rΓ h s1 (FDone OK) rΓ' h')
      (Heval2 : eval_fuel CT n rΓ' h' s2 r rΓ'' h''),
      eval_fuel CT n rΓ h (SSeq s1 s2) r rΓ'' h''

  | EF_Seq_Fail : forall CT n rΓ h s1 s2 r rΓ' h'
      (Heval1 : eval_fuel CT n rΓ h s1 r rΓ' h')
      (Hfail  : r <> FDone OK),
      eval_fuel CT n rΓ h (SSeq s1 s2) r rΓ' h'.

(* ------------------AGREEMENT WITH THE BIG-STEP RELATION------------------*)

(** An evaluation that finishes within its budget is an evaluation. *)
Lemma eval_fuel_erase : forall CT n rΓ h s fr rΓ' h',
  eval_fuel CT n rΓ h s fr rΓ' h' ->
  forall r, fr = FDone r -> eval_stmt CT rΓ h s r rΓ' h'.
Proof.
  intros CT n rΓ h s fr rΓ' h' H.
  induction H; intros r0 Hr; try discriminate.
  - inversion Hr; subst. exact Heval.
  - inversion Hr; subst. apply SBS_Call_NPE. exact Hnull.
  - inversion Hr; subst.
    eapply SBS_Call; eauto.
  - subst r.
    destruct r0.
    + contradiction Hfail. reflexivity.
    + eapply SBS_Call_MUTATIONEXP_Body; eauto.
    + eapply SBS_Call_NPE_Body; eauto.
  - subst r. pose proof (IHeval_fuel1 OK eq_refl) as H1.
    pose proof (IHeval_fuel2 r0 eq_refl) as H2.
    destruct r0.
    + eapply SBS_Seq; eauto.
    + eapply SBS_Seq_MUTATIONEXP_second; eauto.
    + eapply SBS_Seq_NPE_second; eauto.
  - subst r. pose proof (IHeval_fuel r0 eq_refl) as H1.
    destruct r0.
    + contradiction Hfail. reflexivity.
    + eapply SBS_Seq_MUTATIONEXP_first; eauto.
    + eapply SBS_Seq_NPE_first; eauto.
Qed.

(** A finished evaluation finishes with any larger budget. *)
Lemma eval_fuel_mono : forall CT n rΓ h s fr rΓ' h',
  eval_fuel CT n rΓ h s fr rΓ' h' ->
  forall r, fr = FDone r ->
  forall m, n <= m -> eval_fuel CT m rΓ h s fr rΓ' h'.
Proof.
  intros CT n rΓ h s fr rΓ' h' H.
  induction H; intros r0 Hr m0 Hle; try discriminate.
  - apply EF_Atom; auto.
  - apply EF_Call_NPE; auto.
  - destruct m0 as [|m0]; [lia|].
    eapply EF_Call; eauto. eapply IHeval_fuel; eauto. lia.
  - destruct m0 as [|m0]; [lia|].
    eapply EF_Call_Fail; eauto. eapply IHeval_fuel; eauto. lia.
  - eapply EF_Seq; [eapply IHeval_fuel1; eauto | eapply IHeval_fuel2; eauto].
  - eapply EF_Seq_Fail; eauto.
Qed.

(** Every evaluation finishes within some budget. *)
Lemma eval_stmt_has_fuel : forall CT rΓ h s r rΓ' h',
  eval_stmt CT rΓ h s r rΓ' h' ->
  exists n, eval_fuel CT n rΓ h s (FDone r) rΓ' h'.
Proof.
  intros CT rΓ h s r rΓ' h' H. pose proof H as H0.
  induction H;
    try (exists 0; apply EF_Atom; [exact I | exact H0]).
  - (* call *)
    destruct (IHeval_stmt ltac:(assumption)) as [n Hn]. subst.
    exists (S n). eapply EF_Call; eauto.
  - exists 0. apply EF_Call_NPE. exact Hnull.
  - destruct (IHeval_stmt ltac:(assumption)) as [n Hn]. subst.
    exists (S n). eapply EF_Call_Fail; eauto. discriminate.
  - destruct (IHeval_stmt ltac:(assumption)) as [n Hn]. subst.
    exists (S n). eapply EF_Call_Fail; eauto. discriminate.
  - (* sequence *)
    destruct (IHeval_stmt1 ltac:(assumption)) as [n1 Hn1]. destruct (IHeval_stmt2 ltac:(assumption)) as [n2 Hn2].
    exists (Nat.max n1 n2).
    eapply EF_Seq.
    + eapply eval_fuel_mono; eauto. lia.
    + eapply eval_fuel_mono; eauto. lia.
  - destruct (IHeval_stmt ltac:(assumption)) as [n1 H1].
    exists n1. eapply EF_Seq_Fail; eauto. discriminate.
  - destruct (IHeval_stmt1 ltac:(assumption)) as [n1 Hn1]. destruct (IHeval_stmt2 ltac:(assumption)) as [n2 Hn2].
    exists (Nat.max n1 n2).
    eapply EF_Seq.
    + eapply eval_fuel_mono; eauto. lia.
    + eapply eval_fuel_mono; eauto. lia.
  - destruct (IHeval_stmt ltac:(assumption)) as [n1 H1].
    exists n1. eapply EF_Seq_Fail; eauto. discriminate.
  - destruct (IHeval_stmt1 ltac:(assumption)) as [n1 Hn1]. destruct (IHeval_stmt2 ltac:(assumption)) as [n2 Hn2].
    exists (Nat.max n1 n2).
    eapply EF_Seq.
    + eapply eval_fuel_mono; eauto. lia.
    + eapply eval_fuel_mono; eauto. lia.
Qed.

(* ------------------WHAT A WELL-FORMED STATE PROVIDES------------------*)

(** A variable with a static type has a value. *)
Lemma var_exists : forall CT Δ sΓ rΓ h x T,
  wf_r_config CT Δ sΓ rΓ h ->
  static_getType sΓ x = Some T ->
  exists v, runtime_getVal rΓ x = Some v.
Proof.
  intros CT Δ sΓ rΓ h x T Hwf Hx.
  destruct Hwf as (_ & _ & _ & _ & _ & Hlen & _).
  unfold static_getType in Hx. unfold runtime_getVal.
  assert (Hlt : x < length sΓ) by (apply nth_error_Some; congruence).
  destruct (nth_error (vars rΓ) x) as [v|] eqn:E; eauto.
  apply nth_error_None in E. lia.
Qed.

(** A variable that is not declared has no value. *)
Lemma var_none : forall CT Δ sΓ rΓ h x,
  wf_r_config CT Δ sΓ rΓ h ->
  static_getType sΓ x = None ->
  runtime_getVal rΓ x = None.
Proof.
  intros CT Δ sΓ rΓ h x Hwf Hx.
  destruct Hwf as (_ & _ & _ & _ & _ & Hlen & _).
  unfold static_getType in Hx. unfold runtime_getVal.
  apply nth_error_None in Hx. apply nth_error_None. lia.
Qed.

Lemma vars_exist : forall CT Δ sΓ rΓ h ys Ts,
  wf_r_config CT Δ sΓ rΓ h ->
  static_getType_list sΓ ys = Some Ts ->
  exists vals, runtime_lookup_list rΓ ys = Some vals.
Proof.
  intros CT Δ sΓ rΓ h ys Ts Hwf. revert Ts.
  unfold static_getType_list, runtime_lookup_list.
  induction ys as [|y ys IH]; simpl; intros Ts HTs.
  - eauto.
  - destruct (static_getType sΓ y) as [T|] eqn:Ey; [|discriminate].
    destruct (mapM (fun x => static_getType sΓ x) ys) as [Ts'|] eqn:Eys;
      [|discriminate].
    destruct (var_exists _ _ _ _ _ _ _ Hwf Ey) as [v Hv].
    destruct (IH _ eq_refl) as [vs Hvs].
    rewrite Hv. rewrite Hvs. eauto.
Qed.

(** The receiver of the running code. *)
Lemma this_exists : forall CT Δ sΓ rΓ h,
  wf_r_config CT Δ sΓ rΓ h ->
  exists ι o,
    runtime_getVal rΓ 0 = Some (Iot ι) /\
    runtime_getObj h ι = Some o /\
    r_muttype h ι = Some (rqtype (rt_type o)).
Proof.
  intros CT Δ sΓ rΓ h Hwf.
  destruct (wf_r_config_this _ _ _ _ _ Hwf) as (ι & o & Hthis & Hobj & Hmut & _).
  exists ι, o. split; [|split]; auto.
  apply get_this_runtime_getVal. exact Hthis.
Qed.

(** A non-null variable whose type is, through its bound, a class type holds
    an object of a subclass of that class. *)
Lemma var_object : forall CT Δ sΓ rΓ h x T q0 C Ts l,
  wf_r_config CT Δ sΓ rΓ h ->
  static_getType sΓ x = Some T ->
  ubound Δ T = Some (TClass q0 C Ts) ->
  runtime_getVal rΓ x = Some (Iot l) ->
  exists o Vs,
    runtime_getObj h l = Some o /\
    rsuper_inst CT (qr2q (rqtype (rt_type o)))
      (rctype (rt_type o)) (rtargs (rt_type o)) C Vs.
Proof.
  intros CT Δ sΓ rΓ h x T q0 C Ts l Hwf Hx Hub Hv.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hx) as Hty.
  rewrite Hv in Hty.
  pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ _ Hfb Hub Hty) as Hty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty')
    as (ox & Vs & Hox & _ & Hsup & _).
  eauto.
Qed.

(** A field declared in a class is present in every object of a subclass, and
    its slot has an assignability. *)
Lemma field_slot_exists : forall CT h l o C Vs f fd,
  wf_heap CT h ->
  runtime_getObj h l = Some o ->
  rsuper_inst CT (qr2q (rqtype (rt_type o)))
    (rctype (rt_type o)) (rtargs (rt_type o)) C Vs ->
  sf_def_rel CT C f fd ->
  exists v a0,
    getVal (fields_map o) f = Some v /\
    sf_assignability_rel CT (rctype (rt_type o)) f a0.
Proof.
  intros CT h l o C Vs f fd Hheap Ho Hsup Hfd.
  pose proof (Hheap l (runtime_getObj_dom _ _ _ Ho)) as Hw.
  unfold wf_obj in Hw. rewrite Ho in Hw.
  destruct Hw as (_ & fds & Hcf & Hlen & _).
  inversion Hfd as [? ? fsC ? ? HcfC Hget]; subst.
  unfold gget in Hget.
  destruct (field_inherit _ _ _ _ _ _ Hsup _ _ _ _ HcfC Hcf Hget)
    as (fd' & Hn & _).
  assert (Hlt : f < length (fields_map o)).
  { rewrite Hlen. apply nth_error_Some. congruence. }
  unfold getVal.
  destruct (nth_error (fields_map o) f) as [v|] eqn:E.
  - exists v, (assignability fd'). split; [reflexivity|].
    exists fd'. split; [|reflexivity].
    eapply FL_Found; eauto.
  - apply nth_error_None in E. lia.
Qed.

(** A method found in a class is found in every subclass, possibly as an
    overriding declaration. *)
Lemma method_found_below : forall CT qh cy Rs C Vs,
  rsuper_inst CT qh cy Rs C Vs ->
  forall m D mdef,
    FindMethodWithName CT C m D mdef ->
    exists D' mdef', FindMethodWithName CT cy m D' mdef'.
Proof.
  intros CT qh cy Rs C Vs H.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH]; intros m D mdef Hf.
  - eauto.
  - destruct (IH m D mdef Hf) as (D' & mdef' & Hf').
    unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [def|] eqn:Hfc; [|discriminate].
    destruct (gget_method (methods (body def)) m) as [md|] eqn:Hg.
    + exists C, md. eapply FOM_Here; eauto.
    + exists D', mdef'. eapply FOM_Super; eauto.
Qed.

(** The class that declares the selected method is a superclass. *)
Lemma method_decl_above : forall CT C m D mdef,
  FindMethodWithName CT C m D mdef ->
  forall qh Rs, exists Vs, rsuper_inst CT qh C Rs D Vs.
Proof.
  intros CT C m D mdef H.
  induction H; intros qh Rs.
  - exists Rs. apply rsi_refl.
  - destruct (IHFindMethodWithName qh (map (dyn qh Rs [] []) Ss)) as [Vs HVs].
    exists Vs. eapply rsi_step; [|exact HVs].
    unfold parent_lookup. rewrite Hfind. exact Hsuper.
Qed.

(** A well-typed expression evaluates: to a value, or to a null
    dereference. *)
Lemma expr_total : forall CT Δ sΓ mt rΓ h e T,
  wf_r_config CT Δ sΓ rΓ h ->
  expr_has_type CT Δ sΓ mt e T ->
  exists v r, eval_expr CT rΓ h e v r rΓ h /\ (r = OK \/ r = NPE).
Proof.
  intros CT Δ sΓ mt rΓ h e T Hwf He.
  inversion He; subst.
  - exists Null_a, OK. split; [constructor | auto].
  - destruct (var_exists _ _ _ _ _ _ _ Hwf Hget) as [v Hv].
    exists v, OK. split; [constructor; exact Hv | auto].
  - destruct (var_exists _ _ _ _ _ _ _ Hwf Hget_x) as [[|l] Hv].
    + exists Null_a, NPE. split; [apply EBS_Field_NPE; exact Hv | auto].
    + destruct (var_object _ _ _ _ _ _ _ _ _ _ _ Hwf Hget_x Hub Hv)
        as (o & Vs & Ho & Hsup).
      pose proof Hwf as (_ & Hheap & _).
      destruct (field_slot_exists _ _ _ _ _ _ _ _ Hheap Ho Hsup Hfld_def)
        as (v1 & a0 & Hv1 & _).
      exists v1, OK. split; [eapply EBS_Field; eauto | auto].
Qed.

(* ------------------EVERY BUDGET GIVES AN OUTCOME------------------*)

Definition total_at (n : nat) : Prop :=
  forall CT Δ sΓ mt rΓ h s sΓ',
    wf_r_config CT Δ sΓ rΓ h ->
    stmt_typing CT Δ sΓ mt s sΓ' ->
    exists r rΓ' h', eval_fuel CT n rΓ h s r rΓ' h'.

Lemma total_step : forall n, (forall k, k < n -> total_at k) -> total_at n.
Proof.
  intros n IHn CT Δ sΓ mt rΓ h s sΓ' Hwf Htype. revert rΓ h Hwf.
  induction Htype; intros rΓ h Hwf0.
  - (* skip *)
    do 3 eexists. apply EF_Atom; [exact I | constructor].
  - (* local *)
    do 3 eexists. apply EF_Atom; [exact I|].
    apply SBS_Local. eapply var_none; eauto.
  - (* assign *)
    destruct (var_exists _ _ _ _ _ _ _ Hwf0 Hget_x) as [v1 Hv1].
    destruct (expr_total _ _ _ _ _ _ _ _ Hwf0 Htype_e) as (v2 & r & He & [-> | ->]).
    + do 3 eexists. apply EF_Atom; [exact I|]. eapply SBS_Assign; eauto.
    + do 3 eexists. apply EF_Atom; [exact I|]. eapply SBS_Assign_NPE; eauto.
  - (* field write *)
    destruct (var_exists _ _ _ _ _ _ _ Hwf0 Hget_x) as [[|lx] Hvx].
    + do 3 eexists. apply EF_Atom; [exact I|]. apply SBS_FldWrite_NPE. exact Hvx.
    + destruct (var_object _ _ _ _ _ _ _ _ _ _ _ Hwf0 Hget_x Hub Hvx)
        as (o & Vs & Ho & Hsup).
      pose proof Hwf0 as (_ & Hheap & _).
      destruct (field_slot_exists _ _ _ _ _ _ _ _ Hheap Ho Hsup Hfld_def)
        as (vf & a0 & Hvf & Ha0).
      destruct (var_exists _ _ _ _ _ _ _ Hwf0 Hget_y) as [vy Hvy].
      assert (Hcase : runtime_vpa_assignability (rqtype (rt_type o)) a0 = Assignable \/
                      runtime_vpa_assignability (rqtype (rt_type o)) a0 = Final).
      { destruct (rqtype (rt_type o)), a0; simpl; auto. }
      destruct Hcase as [Hok | Hno].
      * do 3 eexists. apply EF_Atom; [exact I|]. eapply SBS_FldWrite; eauto.
      * do 3 eexists. apply EF_Atom; [exact I|].
        eapply SBS_FldWrite_MUTATIONEXP; eauto.
  - (* new *)
    destruct (this_exists _ _ _ _ _ Hwf0) as (ι & o & Hthis & Hobj & Hmut).
    destruct (vars_exist _ _ _ _ _ _ _ Hwf0 Hget_args) as [vals Hvals].
    do 3 eexists. apply EF_Atom; [exact I|]. eapply SBS_New; eauto.
  - (* call *)
    assert (Htc : stmt_typing CT Δ sΓ mt (SCall x m y Us Qs args) sΓ)
      by (eapply ST_Call; eauto).
    destruct (var_exists _ _ _ _ _ _ _ Hwf0 Hget_y) as [[|ly] Hvy].
    { do 3 eexists. apply EF_Call_NPE. exact Hvy. }
    destruct (var_object _ _ _ _ _ _ _ _ _ _ _ Hwf0 Hget_y Hub Hvy)
      as (oy & Vs1 & Hoy & Hsup1).
    assert (Hbase : r_basetype h ly = Some (rctype (rt_type oy))).
    { unfold r_basetype. rewrite Hoy. reflexivity. }
    destruct (method_found_below _ _ _ _ _ _ Hsup1 _ _ _ Hfind_m)
      as (D' & mdef' & Hf').
    destruct (vars_exist _ _ _ _ _ _ _ Hwf0 Hget_args) as [vals Hvals].
    destruct (this_exists _ _ _ _ _ Hwf0) as (ι & o & Hthis & Hobj & Hmut).
    destruct (method_decl_above _ _ _ _ _ Hf' (qr2q (rqtype (rt_type oy)))
                (rtargs (rt_type oy))) as [cargs' Hcargs].
    set (rΓc := mkr_env (Iot ly :: vals) cargs'
                  (map (dyn (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ)
                          (qargs rΓ)) Us)
                  (map (rqarg (qr2q (rqtype (rt_type o))) (qargs rΓ)) Qs)).
    assert (Hframe : callee_env CT rΓ h ly D' Us Qs vals rΓc).
    { exists ι, (rqtype (rt_type o)), oy, cargs'.
      repeat split; auto. }
    destruct n as [|k].
    { do 3 eexists. eapply EF_Call_Timeout; eauto. }
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf0 Htc Hvy Hbase Hf' Hvals Hframe)
      as (ι1 & o1 & oy1 & Tx1 & _ & _ & _ & _ & _ & _ & _ & Hwm & Hcfg & _).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & Hret & _) & _).
    destruct (IHn k (Nat.lt_succ_diag_r k) CT _ _ _ _ _ _ _ Hcfg Hbody)
      as (r & rΓ'' & h' & Hb).
    assert (Hdec : r = FDone OK \/ r <> FDone OK).
    { destruct r as [[| |]|]; [left; reflexivity | | |]; right; discriminate. }
    destruct Hdec as [-> | Hfail].
    + pose proof (eval_fuel_erase _ _ _ _ _ _ _ _ Hb OK eq_refl) as Hev.
      pose proof (preservation_pico _ _ _ _ _ _ _ Hev eq_refl _ _ _ _ Hcfg Hbody)
        as Hcfg''.
      destruct (var_exists _ _ _ _ _ _ _ Hcfg'' Hret) as [retval Hretval].
      do 3 eexists. eapply EF_Call; eauto.
    + do 3 eexists. eapply EF_Call_Fail; eauto.
  - (* cast *)
    destruct (var_exists _ _ _ _ _ _ _ Hwf0 Hget_x) as [v1 Hv1].
    destruct (var_exists _ _ _ _ _ _ _ Hwf0 Hget_y) as [v2 Hv2].
    do 3 eexists. apply EF_Atom; [exact I|]. eapply SBS_Cast; eauto.
  - (* sequence *)
    destruct (IHHtype1 rΓ h Hwf0) as (r1 & rΓ1 & h1 & H1).
    assert (Hdec : r1 = FDone OK \/ r1 <> FDone OK).
    { destruct r1 as [[| |]|]; [left; reflexivity | | |]; right; discriminate. }
    destruct Hdec as [-> | Hfail].
    + pose proof (eval_fuel_erase _ _ _ _ _ _ _ _ H1 OK eq_refl) as Hev.
      pose proof (preservation_pico _ _ _ _ _ _ _ Hev eq_refl _ _ _ _ Hwf0 Htype1)
        as Hwf1.
      destruct (IHHtype2 rΓ1 h1 Hwf1) as (r2 & rΓ2 & h2 & H2).
      do 3 eexists. eapply EF_Seq; eauto.
    + do 3 eexists. eapply EF_Seq_Fail; eauto.
Qed.

Theorem eval_fuel_total : forall n, total_at n.
Proof.
  intros n. induction n as [n IH] using lt_wf_ind. apply total_step. exact IH.
Qed.

(* ------------------THE THEOREMS------------------*)

(** No evaluation with a budget ends in a rejected write. *)
Theorem fuel_no_mutation_exp : forall CT Δ sΓ mt rΓ h s sΓ' n r rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_fuel CT n rΓ h s r rΓ' h' ->
  r <> FDone MUTATIONEXP.
Proof.
  intros CT Δ sΓ mt rΓ h s sΓ' n r rΓ' h' Hwf Htype Hev ->.
  pose proof (eval_fuel_erase _ _ _ _ _ _ _ _ Hev MUTATIONEXP eq_refl) as He.
  exact (well_typed_no_mutation_exp _ _ _ _ _ _ _ He eq_refl _ _ _ _ Hwf Htype).
Qed.

(** PROGRESS.  From a well-formed state, a well-typed statement run with any
    budget has an outcome, and the outcome is that it finished normally,
    ended in a null dereference, or ran out of budget.  It is never stuck and
    never ends in a rejected write. *)
Theorem progress : forall n CT Δ sΓ mt rΓ h s sΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  exists r rΓ' h',
    eval_fuel CT n rΓ h s r rΓ' h' /\
    (r = FDone OK \/ r = FDone NPE \/ r = FTimeout).
Proof.
  intros n CT Δ sΓ mt rΓ h s sΓ' Hwf Htype.
  destruct (eval_fuel_total n CT Δ sΓ mt rΓ h s sΓ' Hwf Htype)
    as (r & rΓ' & h' & Hev).
  exists r, rΓ', h'. split; [exact Hev|].
  pose proof (fuel_no_mutation_exp _ _ _ _ _ _ _ _ _ _ _ _ Hwf Htype Hev) as Hnm.
  destruct r as [[| |]|]; auto. contradiction Hnm. reflexivity.
Qed.

(** A normal finish within the budget leaves a well-formed state. *)
Corollary fuel_preservation : forall CT Δ sΓ mt rΓ h s sΓ' n rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_fuel CT n rΓ h s (FDone OK) rΓ' h' ->
  wf_r_config CT Δ sΓ' rΓ' h'.
Proof.
  intros CT Δ sΓ mt rΓ h s sΓ' n rΓ' h' Hwf Htype Hev.
  pose proof (eval_fuel_erase _ _ _ _ _ _ _ _ Hev OK eq_refl) as He.
  exact (preservation_pico _ _ _ _ _ _ _ He eq_refl _ _ _ _ Hwf Htype).
Qed.

Print Assumptions progress.
Print Assumptions fuel_no_mutation_exp.
Print Assumptions eval_stmt_has_fuel.

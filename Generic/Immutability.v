From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation.

(** Abstract-state and concrete-state immutability for generic PICO. *)

(* ------------------SHALLOW IMMUTABILITY------------------*)

(** A field of an immutable object keeps its value across a well-typed
    evaluation when the field is not assignable, or when the code runs in a
    mode with strict assignability (concrete-state or transitive-state). *)
Theorem shallow_abstract_immutability : forall CT rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ' l C Rs vals f,
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C Rs) vals) ->
      (sf_assignability_rel CT C f Final \/
       sf_assignability_rel CT C f RDA \/
       strict_assignability_method_scope mt) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type Imm_r C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT rΓ h s res rΓ' h' Heval.
  induction Heval;
    intros Hres Δ sΓ mt0 sΓ' l C0 Rs0 vals0 f0 Hwf Htype Hl Hprot;
    try discriminate; try (exists vals0; split; [exact Hl | reflexivity]).
  - (* field write *)
    subst h'.
    destruct (Nat.eq_dec loc_x l) as [-> | Hne].
    + rewrite Hl in Hobj. inversion Hobj; subst o. clear Hobj. simpl in *.
      rewrite (update_field_getObj_same _ _ _ _ _ Hl). simpl.
      eexists. split; [reflexivity|].
      destruct (Nat.eq_dec f f0) as [-> | Hnf].
      * exfalso.
        assert (a = Assignable) by (destruct a; simpl in *; congruence).
        subst a.
        destruct Hprot as [Hp | [Hp | Hstrict]].
        -- pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp).
           discriminate.
        -- pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp).
           discriminate.
        -- inversion Htype; subst.
           destruct (wf_r_config_this _ _ _ _ _ Hwf)
             as (ι & othis & Hthis & Hobj & _ & _ & _ & Hfb).
           pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x)
             as Hxty.
           rewrite Hval_x in Hxty.
           pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ Hfb Hub Hxty) as Hxty'.
           destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hxty')
             as (ox' & Vs & Hox' & Hhead & _).
           rewrite Hl in Hox'. inversion Hox'; subst ox'. simpl in Hhead.
           unfold head_ok in Hhead.
           destruct Hstrict as [-> | ->]; simpl in Hassignable;
             destruct qx, (assignability fieldT), (rqtype (rt_type othis));
             simpl in *; try discriminate;
             destruct Hhead as [Hh | [Hh | Hh]]; discriminate.
      * symmetry. apply update_diff; auto.
    + rewrite update_field_getObj_diff; auto.
      exists vals0. split; auto.
  - (* object creation *)
    subst. exists vals0. split; [|reflexivity].
    rewrite runtime_getObj_last2; [eapply runtime_getObj_dom; eauto | exact Hl].
  - (* call *)
    subst.
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ &
          _ & Hwm & Hcfg & _ & _ & Hscope).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _ & _) & _ & _).
    eapply (IHHeval eq_refl _ _ _ _ l C0 Rs0 vals0 f0 Hcfg Hbody Hl).
    destruct Hprot as [Hp | [Hp | Hstrict]]; auto.
    right. right. eapply concrete_assignability_submethod; eauto.
  - (* sequence *)
    inversion Htype; subst.
    destruct (IHHeval1 eq_refl _ _ _ _ l C0 Rs0 vals0 f0 Hwf Htype1 Hl Hprot)
      as (vals1 & Hl1 & Heq1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    destruct (IHHeval2 eq_refl _ _ _ _ l C0 Rs0 vals1 f0 Hwf1 Htype2 Hl1 Hprot)
      as (vals2 & Hl2 & Heq2).
    exists vals2. split; auto. congruence.
Qed.

(* ------------------ABSTRACT STATE------------------*)

(** A declared field type that makes the referenced object part of the
    abstract state: its written head is immutable or receiver-dependent; for
    a bare type variable, the declared bound must have such a head. *)
Definition abs_type (bounds : list qualified_type) (T : qualified_type) : Prop :=
  match T with
  | TClass q0 _ _ => q0 = Imm \/ q0 = RDM
  | TVar (TVQual q0) _ _ => q0 = Imm \/ q0 = RDM
  | TVar TVSub ClassVar n =>
      exists qb C Ts,
        nth_error bounds n = Some (TClass qb C Ts) /\ (qb = Imm \/ qb = RDM)
  | TVar TVSub MethodVar _ => False
  | THead _ _ _ _ => False
  end.

(** Reachability through abstract-state fields. *)
Inductive reachable_abs (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=

  | reachable_abs_heap : forall l
      (Hdom : l < dom h),
      reachable_abs CT h l l

  | reachable_abs_step : forall l0 l1 any C Rs vals k fd
      (Hobj        : runtime_getObj h l0 = Some (mkObj (mkruntime_type any C Rs) vals))
      (Hfield      : nth_error vals k = Some (Iot l1))
      (Hfld        : sf_def_rel CT C k fd)
      (Hmut_abs    : abs_type (class_tparams CT C) (ftype fd))
      (Hassign_abs : assignability fd = RDA \/ assignability fd = Final),
      reachable_abs CT h l0 l1

  | reachable_abs_trans : forall l0 l1 l2
      (Hreach1 : reachable_abs CT h l0 l1)
      (Hreach2 : reachable_abs CT h l1 l2),
      reachable_abs CT h l0 l2.

Lemma head_ok_imm : forall qo, head_ok qo Imm -> qo = Imm_r.
Proof.
  intros [] H; auto. unfold head_ok in H.
  destruct H as [H | [H | H]]; discriminate.
Qed.

Lemma loc_has_rtype_imm : forall CT h l C Rs,
  loc_has_rtype CT h l (RClass Imm C Rs) ->
  exists C' Rs' vals',
    runtime_getObj h l = Some (mkObj (mkruntime_type Imm_r C' Rs') vals').
Proof.
  intros CT h l C Rs H. unfold loc_has_rtype in H.
  destruct (runtime_getObj h l) as [[[qo Co Ro] fs]|]; [|contradiction].
  simpl in H. destruct H as [Hh _]. apply head_ok_imm in Hh. subst.
  eauto.
Qed.

(** An abstract-state field of an immutable object refers to an immutable
    object. *)
Lemma imm_step_preserves_imm : forall CT h l0 l1 C Rs vals k fd,
  wf_heap CT h ->
  runtime_getObj h l0 = Some (mkObj (mkruntime_type Imm_r C Rs) vals) ->
  nth_error vals k = Some (Iot l1) ->
  sf_def_rel CT C k fd ->
  abs_type (class_tparams CT C) (ftype fd) ->
  exists C' Rs' vals',
    runtime_getObj h l1 = Some (mkObj (mkruntime_type Imm_r C' Rs') vals').
Proof.
  intros CT h l0 l1 C Rs vals k fd Hheap Hobj Hk Hfld Habs.
  pose proof (Hheap l0 (runtime_getObj_dom _ _ _ Hobj)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hobj in Hwfo. simpl in Hwfo.
  destruct Hwfo as (Hrt & fsO & HcfO & _ & Hall).
  inversion Hfld as [? ? fsC ? ? HcfC Hget]; subst.
  assert (fsC = fsO) by eauto using collect_fields_deterministic_rel. subst fsC.
  pose proof (Forall2_nth_error_rel _ _ _ k Hall) as Hrel.
  rewrite Hk in Hrel. unfold gget in Hget. rewrite Hget in Hrel.
  unfold wf_r_typable in Hrel. simpl in Hrel.
  destruct (ftype fd) as [q0 Cf Tf | [|q0] [|] n | oh nh Ch Th];
    [| | | | | contradiction]; simpl in *.
  - assert (Hd : dynq Imm q0 = Imm) by (destruct Habs as [-> | ->]; reflexivity).
    rewrite Hd in Hrel. eapply loc_has_rtype_imm; eauto.
  - destruct Habs as (qb & Cb & Tb & Hnb & Hqb).
    unfold wf_rtypeuse in Hrt. simpl in Hrt.
    unfold class_tparams in Hnb.
    destruct (find_class CT C) as [def|]; [|contradiction].
    destruct Hrt as (_ & _ & Hbnd).
    pose proof (Forall2_nth_error_rel _ _ _ n Hbnd) as Hn.
    rewrite Hnb in Hn.
    destruct (nth_error Rs n) as [[q1 C1 R1]|]; [|contradiction].
    simpl in Hn.
    assert (Hd : dynq Imm qb = Imm) by (destruct Hqb as [-> | ->]; reflexivity).
    rewrite Hd in Hn.
    destruct Hn as [[-> _] | [Hq _]].
    + exfalso. unfold loc_has_rtype in Hrel.
      destruct (runtime_getObj h l1); [|contradiction].
      destruct Hrel as [Hh _]. eapply head_ok_not_bot; eauto.
    + unfold rq_sub in Hq.
      destruct Hq as [Hq | [Hq | [Hq _]]]; try discriminate.
      subst q1. eapply loc_has_rtype_imm; eauto.
  - contradiction.
  - destruct (match nth_error Rs n with Some R => R | None => default_rtype end)
      as [q1 C1 R1].
    simpl in Hrel.
    assert (Hd : dynq Imm q0 = Imm) by (destruct Habs as [-> | ->]; reflexivity).
    rewrite Hd in Hrel. eapply loc_has_rtype_imm; eauto.
  - destruct (match nth_error (@nil rtype) n with Some R => R | None => default_rtype end)
      as [q1 C1 R1].
    simpl in Hrel.
    assert (Hd : dynq Imm q0 = Imm) by (destruct Habs as [-> | ->]; reflexivity).
    rewrite Hd in Hrel. eapply loc_has_rtype_imm; eauto.
Qed.

(** Everything reachable from an immutable object through abstract-state
    fields is immutable. *)
Lemma reachable_abs_from_imm_points_to_imm : forall CT h l0 l1,
  wf_heap CT h ->
  reachable_abs CT h l0 l1 ->
  forall C0 Rs0 vals0,
    runtime_getObj h l0 = Some (mkObj (mkruntime_type Imm_r C0 Rs0) vals0) ->
    exists C' Rs' vals',
      runtime_getObj h l1 = Some (mkObj (mkruntime_type Imm_r C' Rs') vals').
Proof.
  intros CT h l0 l1 Hheap Hreach.
  induction Hreach; intros C0 Rs0 vals0 Himm.
  - eauto.
  - rewrite Hobj in Himm. inversion Himm; subst.
    eapply imm_step_preserves_imm; eauto.
  - destruct (IHHreach1 _ _ _ Himm) as (C1 & Rs1 & vals1 & H1).
    eapply IHHreach2; eauto.
Qed.

(** Abstract-state preservation: every non-assignable field of every object
    in the abstract state of an immutable root keeps its value. *)
Theorem abstract_state_preservation : forall CT Δ sΓ mt rΓ h stmt rΓ' h' sΓ'
    root C0 Rs0 vals0 l C qr Rs vals f,
  runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0 Rs0) vals0) ->
  reachable_abs CT h root l ->
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt stmt sΓ' ->
  eval_stmt CT rΓ h stmt OK rΓ' h' ->
  runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
  (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
  exists vals',
    runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
    nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 Rs0 vals0 l C qr Rs vals f
    Hroot Hreach Hwf Htype Heval Hobj Hprot.
  pose proof Hwf as (_ & Hheap & _).
  destruct (reachable_abs_from_imm_points_to_imm _ _ _ _ Hheap Hreach _ _ _ Hroot)
    as (C' & Rs' & vals' & Himm).
  rewrite Hobj in Himm. inversion Himm; subst.
  eapply shallow_abstract_immutability; eauto.
  destruct Hprot; auto.
Qed.

(** Concrete-state preservation: in a mode with strict assignability, every
    field of every object in the abstract state of an immutable root keeps
    its value, including fields declared assignable. *)
Theorem concrete_state_preservation : forall CT Δ sΓ mt rΓ h stmt rΓ' h' sΓ'
    root C0 Rs0 vals0 l C qr Rs vals f,
  strict_assignability_method_scope mt ->
  runtime_getObj h root = Some (mkObj (mkruntime_type Imm_r C0 Rs0) vals0) ->
  reachable_abs CT h root l ->
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt stmt sΓ' ->
  eval_stmt CT rΓ h stmt OK rΓ' h' ->
  runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
  exists vals',
    runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
    nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h stmt rΓ' h' sΓ' root C0 Rs0 vals0 l C qr Rs vals f
    Hstrict Hroot Hreach Hwf Htype Heval Hobj.
  pose proof Hwf as (_ & Hheap & _).
  destruct (reachable_abs_from_imm_points_to_imm _ _ _ _ Hheap Hreach _ _ _ Hroot)
    as (C' & Rs' & vals' & Himm).
  rewrite Hobj in Himm. inversion Himm; subst.
  eapply shallow_abstract_immutability; eauto.
Qed.

Print Assumptions abstract_state_preservation.
Print Assumptions concrete_state_preservation.

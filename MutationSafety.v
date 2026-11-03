From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation.

(** Mutation safety: a well-typed statement never raises the mutation
    exception. *)

Lemma fldwrite_no_mutation_exp : forall CT Δ sΓ rΓ h mt x f y sΓ' lx o a0,
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SFldWrite x f y) sΓ' ->
  runtime_getVal rΓ x = Some (Iot lx) ->
  runtime_getObj h lx = Some o ->
  sf_assignability_rel CT (rctype (rt_type o)) f a0 ->
  runtime_vpa_assignability (rqtype (rt_type o)) a0 = Final ->
  False.
Proof.
  intros CT Δ sΓ rΓ h mt x f y sΓ' lx o a0 Hwf Htype Hvx Hox Hassign Hfinal.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & othis & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hxty.
  rewrite Hvx in Hxty.
  pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ _ Hfb Hub Hxty) as Hxty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hxty')
    as (ox' & Vs & Hox' & Hhead & Hsup & _).
  rewrite Hox in Hox'. inversion Hox'; subst ox'. clear Hox'.
  destruct Hassign as (fdO & HlookO & Ha).
  inversion HlookO as [? ? fsO ? ? HcfO HgetO]; subst.
  inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
  destruct (field_inherit _ _ _ _ _ _ Hsup _ _ _ _ HcfC HcfO HgetC)
    as (fd' & Hnth' & Hassign_eq & _).
  unfold gget in HgetO. rewrite HgetO in Hnth'. inversion Hnth'; subst fd'.
  rewrite Hassign_eq in Hfinal.
  apply vpa_a_assignable_implies_assignable in Hassignable.
  unfold head_ok in Hhead.
  destruct (assignability fieldT), qx, (rqtype (rt_type o)),
    (rqtype (rt_type othis)); simpl in *; try discriminate;
    destruct Hhead as [Hh | [Hh | Hh]]; discriminate.
Qed.

Theorem well_typed_no_mutation_exp : forall CT rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = MUTATIONEXP ->
    forall Δ sΓ mt sΓ',
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      False.
Proof.
  intros CT rΓ h s res rΓ' h' Heval.
  induction Heval; intros Hres Δ sΓ mt0 sΓ' Hwf Htype; try discriminate.
  - eapply fldwrite_no_mutation_exp; eauto.
  - subst.
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ &
          _ & Hwm & Hcfg & _).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _ & _) & _ & _).
    eapply IHHeval; eauto.
  - inversion Htype; subst. eapply IHHeval; eauto.
  - inversion Htype; subst.
    eapply IHHeval2; eauto.
    eapply preservation_pico; eauto.
Qed.

Print Assumptions well_typed_no_mutation_exp.

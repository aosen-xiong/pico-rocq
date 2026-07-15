From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability Preservation.
Require Import ReadonlyHelper.

Lemma well_typed_field_write_no_mutation_exp :
  forall CT sΓ mt rΓ h x f y sΓ'
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SFldWrite x f y) sΓ')
    (Heval : eval_stmt OK CT rΓ h (SFldWrite x f y) MUTATIONEXP rΓ h),
    False.
Proof.
  intros.
  inversion Heval; subst.
  rename Hval_x into Hgetval_x.
  rename Hobj into Hgetobj.
  rename Hassign into Hassign.
  rename Hfinal into Hvpa_final.
  inversion Htyping; subst.
  -
  rename sΓ' into sΓ.
  destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  specialize (Hcorr iot qcontext Hget_iot Hqcontext).
  have Htype_x : static_getType sΓ x = Some Tx by exact Hget_x.
  have Hxdom: x < dom sΓ by (apply static_getType_dom in Htype_x; auto).
  specialize (Hcorr x Hxdom Tx Htype_x).
  rewrite Hgetval_x in Hcorr.
  unfold wf_r_typable in Hcorr.
  unfold r_type in Hcorr.
  rewrite Hgetobj in Hcorr.
  destruct Hcorr as [Hbase Hqualifer].
  assert (sf_assignability_rel CT (rctype (rt_type o)) f a0).
  {
    eapply sf_assignability_subtyping; eauto.
  }
  assert (a0 = a).
  {
    eapply sf_assignability_deterministic_rel; eauto.
  }
  subst a0.
  rename Hassignable into Hvpa_assignable.
  unfold runtime_vpa_assignability in Hvpa_final.
  unfold vpa_assignability in Hvpa_assignable.
  destruct a eqn: Heq_a; destruct (rqtype (rt_type o)) eqn: Heq_rq; destruct (sqtype Tx) eqn: Heq_sq; try discriminate.
  destruct qcontext eqn: Heq_qc; try easy.
  -
  rename sΓ' into sΓ.
  destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  specialize (Hcorr iot qcontext Hget_iot Hqcontext).
  have Htype_x : static_getType sΓ x = Some Tx by exact Hget_x.
  have Hxdom: x < dom sΓ by (apply static_getType_dom in Htype_x; auto).
  specialize (Hcorr x Hxdom Tx Htype_x).
  rewrite Hgetval_x in Hcorr.
  unfold wf_r_typable in Hcorr.
  unfold r_type in Hcorr.
  rewrite Hgetobj in Hcorr.
  destruct Hcorr as [Hbase Hqualifer].
  assert (sf_assignability_rel CT (rctype (rt_type o)) f a0).
  {
    eapply sf_assignability_subtyping; eauto.
  }
  assert (a0 = a).
  {
    eapply sf_assignability_deterministic_rel; eauto.
  }
  subst a0.
  rename Hassignable into Hvpa_assignable.
  unfold runtime_vpa_assignability in Hvpa_final.
  unfold vpa_assignability in Hvpa_assignable.
  destruct a eqn: Heq_a; destruct (rqtype (rt_type o)) eqn: Heq_rq; destruct (sqtype Tx) eqn: Heq_sq; try discriminate.
  destruct qcontext eqn: Heq_qc; try easy.
  -
  rename sΓ' into sΓ.
  destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  specialize (Hcorr iot qcontext Hget_iot Hqcontext).
  have Htype_x : static_getType sΓ x = Some Tx by exact Hget_x.
  have Hxdom: x < dom sΓ by (apply static_getType_dom in Htype_x; auto).
  specialize (Hcorr x Hxdom Tx Htype_x).
  rewrite Hgetval_x in Hcorr.
  unfold wf_r_typable in Hcorr.
  unfold r_type in Hcorr.
  rewrite Hgetobj in Hcorr.
  destruct Hcorr as [Hbase Hqualifer].
  assert (sf_assignability_rel CT (rctype (rt_type o)) f a0).
  {
    eapply sf_assignability_subtyping; eauto.
  }
  assert (a0 = a).
  {
    eapply sf_assignability_deterministic_rel; eauto.
  }
  subst a0.
  rename Hassignable into Hvpa_assignable.
  unfold runtime_vpa_assignability in Hvpa_final.
  unfold vpa_assignability in Hvpa_assignable.
  destruct a eqn: Heq_a; destruct (rqtype (rt_type o)) eqn: Heq_rq; destruct (sqtype Tx) eqn: Heq_sq; try discriminate.
  destruct qcontext eqn: Heq_qc; try easy.
  -
  rename sΓ' into sΓ.
  destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  specialize (Hcorr iot qcontext Hget_iot Hqcontext).
  have Htype_x : static_getType sΓ x = Some Tx by exact Hget_x.
  have Hxdom: x < dom sΓ by (apply static_getType_dom in Htype_x; auto).
  specialize (Hcorr x Hxdom Tx Htype_x).
  rewrite Hgetval_x in Hcorr.
  unfold wf_r_typable in Hcorr.
  unfold r_type in Hcorr.
  rewrite Hgetobj in Hcorr.
  destruct Hcorr as [Hbase Hqualifer].
  assert (sf_assignability_rel CT (rctype (rt_type o)) f a0).
  {
    eapply sf_assignability_subtyping; eauto.
  }
  assert (a0 = a).
  {
    eapply sf_assignability_deterministic_rel; eauto.
  }
  subst a0.
  rename Hassignable into Hvpa_assignable.
  unfold runtime_vpa_assignability in Hvpa_final.
  unfold vpa_assignability_concret_imm in Hvpa_assignable.
  destruct a eqn: Heq_a; destruct (rqtype (rt_type o)) eqn: Heq_rq; destruct (sqtype Tx) eqn: Heq_sq; try discriminate.
  destruct qcontext eqn: Heq_qc; try easy.
Qed.

(** Mutation exceptions cannot arise anywhere in the evaluation of a
    well-typed statement.  In particular, the result covers writes nested in
    sequences and in dynamically dispatched method bodies. *)
Theorem well_typed_no_mutation_exp :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Heval : eval_stmt OK CT rΓ h stmt MUTATIONEXP rΓ' h'),
    False.
Proof.
  intros CT sΓ mt rΓ h stmt rΓ' h' sΓ'
    Hwf Htyping Heval.
  generalize dependent sΓ'.
  generalize dependent mt.
  generalize dependent sΓ.
  remember MUTATIONEXP as mutation_result eqn:Hmutation in Heval.
  induction Heval; intros; try (discriminate Hmutation).
  - eapply well_typed_field_write_no_mutation_exp with
      (mt := mt) (sΓ' := sΓ'); eauto.
    eapply SBS_FldWrite_MUTATIONEXP; eauto.
  - destruct Hfind as [Hfind Hmbody].
    destruct (typed_call_target CT sΓ mt rΓ h x m y zs
                sΓ' vals ly cy mdef Hwf Htyping Hval_y Hbase Hfind Hargs)
      as [D [ddef [sΓbody'
        [_ [_ [_ [_ [Hbody_typing Hframe_wf]]]]]]]].
    subst mbody mstmt rΓ'.
    eapply IHHeval; eauto.
  - inversion Htyping; subst.
    eapply IHHeval; eauto.
  - inversion Htyping; subst.
    eapply IHHeval2; eauto.
    eapply preservation_pico; eauto.
Qed.

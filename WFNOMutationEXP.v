From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability Preservation.
Require Import ReadonlyHelper.

Theorem well_typed_no_mutation_exp :
  forall CT sΓ mt rΓ h x f y sΓ'
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt (SFldWrite x f y) sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h (SFldWrite x f y) MUTATIONEXP (reachable_locations_from_initial_env CT h rΓ) rΓ h),
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
Qed.

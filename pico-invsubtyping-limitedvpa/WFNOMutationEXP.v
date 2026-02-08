From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.
Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties DeepImmutability Reachability.
Require Import ReadonlyReachability.

Theorem well_typed_no_mutation_exp :
  forall CT sΓ rΓ h x f y sΓ' loc_x o a vf val_y
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ (SFldWrite x f y) sΓ')
    (Hgetval_x : runtime_getVal rΓ x = Some (Iot loc_x))
    (Hgetobj : runtime_getObj h loc_x = Some o)
    (Hgetval_f : getVal o.(fields_map) f = Some vf)
    (Hassign : sf_assignability_rel CT (rctype (rt_type o)) f a)
    (Hgetval_y : runtime_getVal rΓ y = Some val_y)
    (Hvpa_final : runtime_vpa_assignability (rqtype (rt_type o)) a = Final),
    False.
Proof.
  intros.
  inversion Htyping; subst.
  rename sΓ' into sΓ.
  destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [Hheap [Hrenv [Hsenv [Hlen Hcorr]]]]].
  specialize (Hcorr iot qcontext Hget_iot Hqcontext).
  have Hxdom: x < dom sΓ by (apply static_getType_dom in H3; auto).
  specialize (Hcorr x Hxdom Tx H3).
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
  unfold runtime_vpa_assignability in Hvpa_final.
  unfold vpa_assignability in H12.
  destruct a eqn: Heq_a; destruct (rqtype (rt_type o)) eqn: Heq_rq;
  destruct (sqtype Tx) eqn: Heq_sq; try discriminate.
  destruct qcontext eqn: Heq_qc; try easy.
Qed.

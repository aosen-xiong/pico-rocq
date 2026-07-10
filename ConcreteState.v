Require Import Syntax Helpers Typing ViewpointAdaptation Bigstep Properties.

(** CS combines AS mutability adaptation with TS assignability adaptation.
    Consequently, a well-typed field write in CS must have a mutable
    receiver.  In particular, fields selected through immutable or readonly
    receivers are fixed, including fields declared [Assignable]. *)
Theorem concrete_state_field_write_requires_mutable_receiver :
  forall CT sΓ x f y sΓ',
    stmt_typing CT sΓ ConcreteState (SFldWrite x f y) sΓ' ->
    exists Tx,
      static_getType sΓ x = Some Tx /\
      sqtype Tx = Mut.
Proof.
  intros CT sΓ x f y sΓ' Htyping.
  inversion Htyping; subst.
  exists Tx.
  split; [assumption|].
  unfold vpa_assignability_concret_imm in Hassignable.
  destruct (sqtype Tx), a; simpl in Hassignable;
    try discriminate; reflexivity.
Qed.

(** The CS assignability policy is a strengthening of the AS/RS policy. *)
Corollary concrete_state_write_is_abstract_state_write :
  forall q a,
    vpa_assignability_concret_imm q a = Assignable ->
    vpa_assignability q a = Assignable.
Proof.
  exact concrete_assignable_implies_assignable.
Qed.

(** A CS write cannot target an immutable runtime object in a well-formed
    configuration.  CS requires a statically mutable receiver, while runtime
    correspondence forbids a mutable reference from denoting an immutable
    object. *)
Lemma concrete_state_write_cannot_target_immutable :
  forall CT sΓ rΓ h x f y sΓ' loc C vals,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ ConcreteState (SFldWrite x f y) sΓ' ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    runtime_getObj h loc = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    False.
Proof.
  intros CT sΓ rΓ h x f y sΓ' loc C vals Hwf Htyping Hval Hobj.
  destruct (concrete_state_field_write_requires_mutable_receiver
              CT sΓ x f y sΓ' Htyping) as [Tx [Hget_x Hmut]].
  have Hwf_copy := Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [_ [Hrenv [_ [_ Hcorr]]]]].
  unfold wf_renv in Hrenv.
  destruct Hrenv as [_ [Hreceiver _]].
  destruct Hreceiver as [thisLoc [Hget_this Hthis_dom]].
  destruct (runtime_getObj_Some h thisLoc Hthis_dom) as [thisType [thisVals Hthis_obj]].
  remember (rqtype thisType) as qcontext.
  assert (Hqcontext : r_muttype h thisLoc = Some qcontext).
  { unfold r_muttype. rewrite Hthis_obj. simpl. rewrite Heqqcontext. reflexivity. }
  specialize (Hcorr thisLoc qcontext Hget_this Hqcontext).
  have Hxdom : x < dom sΓ by (apply static_getType_dom in Hget_x; exact Hget_x).
  specialize (Hcorr x Hxdom Tx Hget_x).
  rewrite Hval in Hcorr.
  unfold wf_r_typable, r_type in Hcorr.
  rewrite Hobj in Hcorr.
  destruct Hcorr as [_ Hqual].
  rewrite Hmut in Hqual.
  unfold qualifier_typable_context, vpa_mutability_rs,
    qualifier_typable_heap in Hqual.
  destruct qcontext; simpl in Hqual; contradiction.
Qed.

Theorem concrete_immutability_field_write_requires_mutable_receiver :
  forall CT sΓ x f y sΓ',
    stmt_typing CT sΓ ConcreteImm (SFldWrite x f y) sΓ' ->
    exists Tx,
      static_getType sΓ x = Some Tx /\
      sqtype Tx = Mut.
Proof.
  intros CT sΓ x f y sΓ' Htyping.
  inversion Htyping; subst.
  exists Tx.
  split; [assumption|].
  unfold vpa_assignability_concret_imm in Hassignable.
  destruct (sqtype Tx), a; simpl in Hassignable;
    try discriminate; reflexivity.
Qed.

Lemma concrete_immutability_write_cannot_target_immutable :
  forall CT sΓ rΓ h x f y sΓ' loc C vals,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ ConcreteImm (SFldWrite x f y) sΓ' ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    runtime_getObj h loc = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    False.
Proof.
  intros CT sΓ rΓ h x f y sΓ' loc C vals Hwf Htyping Hval Hobj.
  destruct (concrete_immutability_field_write_requires_mutable_receiver
              CT sΓ x f y sΓ' Htyping) as [Tx [Hget_x Hmut]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [Hrenv [_ [_ Hcorr]]]]].
  unfold wf_renv in Hrenv.
  destruct Hrenv as [_ [Hreceiver _]].
  destruct Hreceiver as [thisLoc [Hget_this Hthis_dom]].
  destruct (runtime_getObj_Some h thisLoc Hthis_dom) as [thisType [thisVals Hthis_obj]].
  remember (rqtype thisType) as qcontext.
  assert (Hqcontext : r_muttype h thisLoc = Some qcontext).
  { unfold r_muttype. rewrite Hthis_obj. simpl. rewrite Heqqcontext. reflexivity. }
  specialize (Hcorr thisLoc qcontext Hget_this Hqcontext).
  have Hxdom : x < dom sΓ by (apply static_getType_dom in Hget_x; exact Hget_x).
  specialize (Hcorr x Hxdom Tx Hget_x).
  rewrite Hval in Hcorr.
  unfold wf_r_typable, r_type in Hcorr.
  rewrite Hobj in Hcorr.
  destruct Hcorr as [_ Hqual].
  rewrite Hmut in Hqual.
  unfold qualifier_typable_context, vpa_mutability_rs,
    qualifier_typable_heap in Hqual.
  destruct qcontext; simpl in Hqual; contradiction.
Qed.

Lemma runtime_and_static_method_signatures_agree :
  forall CT sΓ rΓ h y loc Ty runtimeClass m mdefRuntime mdefStatic,
    wf_r_config CT sΓ rΓ h ->
    static_getType sΓ y = Some Ty ->
    runtime_getVal rΓ y = Some (Iot loc) ->
    r_basetype h loc = Some runtimeClass ->
    FindMethodWithName CT runtimeClass m mdefRuntime ->
    FindMethodWithName CT (sctype Ty) m mdefStatic ->
    msignature mdefRuntime = msignature mdefStatic.
Proof.
  intros CT sΓ rΓ h y loc Ty runtimeClass m mdefRuntime mdefStatic
    Hwf Hget_y Hval_y Hbase Hfind_runtime Hfind_static.
  unfold wf_r_config in Hwf.
  destruct Hwf as [Hclass [_ [Hrenv [_ [_ Hcorr]]]]].
  unfold wf_renv in Hrenv.
  destruct Hrenv as [_ [Hreceiver _]].
  destruct Hreceiver as [thisLoc [Hget_this Hthis_dom]].
  destruct (runtime_getObj_Some h thisLoc Hthis_dom) as [thisType [thisVals Hthis_obj]].
  remember (rqtype thisType) as qcontext.
  assert (Hqcontext : r_muttype h thisLoc = Some qcontext).
  { unfold r_muttype. rewrite Hthis_obj. simpl. rewrite Heqqcontext. reflexivity. }
  specialize (Hcorr thisLoc qcontext Hget_this Hqcontext).
  have Hydom : y < dom sΓ by (apply static_getType_dom in Hget_y; exact Hget_y).
  specialize (Hcorr y Hydom Ty Hget_y).
  rewrite Hval_y in Hcorr.
  unfold r_basetype in Hbase.
  destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; try discriminate.
  injection Hbase as Hclass_eq; subst runtimeClass.
  unfold wf_r_typable, r_type in Hcorr.
  rewrite Hobj in Hcorr.
  destruct Hcorr as [Hbase_sub _].
  simpl in Hbase_sub.
  eapply method_signature_consistent_subtype; eauto.
Qed.

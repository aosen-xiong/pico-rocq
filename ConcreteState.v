Require Import Syntax Helpers Typing ViewpointAdaptation Bigstep Properties.

(** Extract the runtime typability fact supplied by a well-formed
    configuration for a non-null variable.  This packages the repeated work
    of recovering the receiver's runtime context and specializing static/
    runtime correspondence. *)
Lemma wf_config_variable_typable :
  forall CT sΓ rΓ h x loc T,
    wf_r_config CT sΓ rΓ h ->
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    exists qcontext, wf_r_typable CT h loc T qcontext.
Proof.
  intros CT sΓ rΓ h x loc T Hwf Hget_x Hval_x.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [Hrenv [_ [_ Hcorr]]]]].
  unfold wf_renv in Hrenv.
  destruct Hrenv as [_ [Hreceiver _]].
  destruct Hreceiver as [thisLoc [Hget_this Hthis_dom]].
  destruct (runtime_getObj_Some h thisLoc Hthis_dom)
    as [thisType [thisVals Hthis_obj]].
  remember (rqtype thisType) as qcontext.
  assert (Hqcontext : r_muttype h thisLoc = Some qcontext).
  { unfold r_muttype. rewrite Hthis_obj. simpl. rewrite Heqqcontext. reflexivity. }
  specialize (Hcorr thisLoc qcontext Hget_this Hqcontext).
  have Hxdom : x < dom sΓ by (apply static_getType_dom in Hget_x; exact Hget_x).
  specialize (Hcorr x Hxdom T Hget_x).
  rewrite Hval_x in Hcorr.
  exists qcontext.
  exact Hcorr.
Qed.

(** Both CS and TS use concrete assignability adaptation.  A field write in
    either scope therefore requires a statically mutable receiver. *)
Theorem concrete_assignability_field_write_requires_mutable_receiver :
  forall CT sΓ mt x f y sΓ',
    strict_assignability_method_scope mt ->
    stmt_typing CT sΓ mt (SFldWrite x f y) sΓ' ->
    exists Tx,
      static_getType sΓ x = Some Tx /\
      sqtype Tx = Mut.
Proof.
  intros CT sΓ mt x f y sΓ' Hscope Htyping.
  inversion Htyping; subst.
  - destruct Hscope as [H | H]; discriminate.
  - exists Tx. split; [assumption|].
    unfold vpa_assignability_cs_ts in Hassignable.
    destruct (sqtype Tx), a; simpl in Hassignable;
      try discriminate; reflexivity.
  - destruct Hscope as [H | H]; discriminate.
  - exists Tx. split; [assumption|].
    unfold vpa_assignability_cs_ts in Hassignable.
    destruct (sqtype Tx), a; simpl in Hassignable;
      try discriminate; reflexivity.
Qed.

Corollary concrete_state_field_write_requires_mutable_receiver :
  forall CT sΓ x f y sΓ',
    stmt_typing CT sΓ ConcreteState (SFldWrite x f y) sΓ' ->
    exists Tx,
      static_getType sΓ x = Some Tx /\
      sqtype Tx = Mut.
Proof.
  intros. eapply concrete_assignability_field_write_requires_mutable_receiver; eauto.
  left. reflexivity.
Qed.

Corollary transitive_state_field_write_requires_mutable_receiver :
  forall CT sΓ x f y sΓ',
    stmt_typing CT sΓ TransitiveState (SFldWrite x f y) sΓ' ->
    exists Tx,
      static_getType sΓ x = Some Tx /\
      sqtype Tx = Mut.
Proof.
  intros. eapply concrete_assignability_field_write_requires_mutable_receiver; eauto.
  right. reflexivity.
Qed.

(** The CS/TS assignability policy is a strengthening of the AS/RS policy. *)
Corollary concrete_state_write_is_abstract_state_write :
  forall q a,
    vpa_assignability_cs_ts q a = Assignable ->
    vpa_assignability q a = Assignable.
Proof.
  exact concrete_assignable_implies_assignable.
Qed.

(** No field write checked with concrete assignability can target an immutable
    runtime object in a well-formed configuration. *)
Lemma concrete_assignability_write_cannot_target_immutable :
  forall CT sΓ mt rΓ h x f y sΓ' loc C vals,
    strict_assignability_method_scope mt ->
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt (SFldWrite x f y) sΓ' ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    runtime_getObj h loc = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    False.
Proof.
  intros CT sΓ mt rΓ h x f y sΓ' loc C vals
    Hscope Hwf Htyping Hval Hobj.
  destruct (concrete_assignability_field_write_requires_mutable_receiver
              CT sΓ mt x f y sΓ' Hscope Htyping) as [Tx [Hget_x Hmut]].
  destruct (wf_config_variable_typable CT sΓ rΓ h x loc Tx Hwf Hget_x Hval)
    as [qcontext Htypable].
  unfold wf_r_typable, r_type in Htypable.
  rewrite Hobj in Htypable.
  destruct Htypable as [_ Hqual].
  rewrite Hmut in Hqual.
  unfold qualifier_typable_context, vpa_mutability_runtime,
    qualifier_typable_heap in Hqual.
  destruct qcontext; simpl in Hqual; contradiction.
Qed.

Corollary concrete_state_write_cannot_target_immutable :
  forall CT sΓ rΓ h x f y sΓ' loc C vals,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ ConcreteState (SFldWrite x f y) sΓ' ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    runtime_getObj h loc = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    False.
Proof.
  intros. eapply concrete_assignability_write_cannot_target_immutable; eauto.
  left. reflexivity.
Qed.

Corollary transitive_state_write_cannot_target_immutable :
  forall CT sΓ rΓ h x f y sΓ' loc C vals,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ TransitiveState (SFldWrite x f y) sΓ' ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    runtime_getObj h loc = Some (mkObj (mkruntime_type Imm_r C) vals) ->
    False.
Proof.
  intros. eapply concrete_assignability_write_cannot_target_immutable; eauto.
  right. reflexivity.
Qed.

(** Runtime and static method lookup agree because well-formedness relates the
    runtime receiver class to its static base type. *)
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
  have Hwf_copy := Hwf.
  destruct (wf_config_variable_typable CT sΓ rΓ h y loc Ty Hwf Hget_y Hval_y)
    as [qcontext Htypable].
  unfold r_basetype in Hbase.
  destruct (runtime_getObj h loc) as [obj|] eqn:Hobj; try discriminate.
  injection Hbase as Hclass_eq; subst runtimeClass.
  unfold wf_r_typable, r_type in Htypable.
  rewrite Hobj in Htypable.
  destruct Htypable as [Hbase_sub _].
  simpl in Hbase_sub.
  unfold wf_r_config in Hwf_copy.
  destruct Hwf_copy as [Hclass _].
  eapply method_signature_consistent_subtype; eauto.
Qed.

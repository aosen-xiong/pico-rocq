Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import CallFrameWellformed.
Require Import ConcreteState MutableCapability ProtectionHistory ForwardCapabilityHistory
  LiveCapabilityStack.
Require Import WatchedFrames PotentialCapability.
From Stdlib Require Import List Lia Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

Definition protected_field_condition
  (CT : class_table) (C : class_name) (field : var)
  (mt : method_type) : Prop :=
  sf_assignability_rel CT C field Final \/
  sf_assignability_rel CT C field RDA \/
  concrete_assignability_method_type mt.

Lemma active_mut_root_cannot_be_protected :
  forall CT P Z cutoff h authority sGamma rGamma stack x T location,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    static_getType sGamma x = Some T ->
    runtime_getVal rGamma x = Some (Iot location) ->
    sqtype T = Mut ->
    In Loc P location ->
    False.
Proof.
  intros CT P Z cutoff h authority sGamma rGamma stack x T location
    [Hlive Hseparated] Htype Hvalue Hmut HinP.
  have Hcomponent := proj1 (proj1 Hlive).
  have Hforward := proj1 Hcomponent.
  have Hcontains : protected_zone_contains P Z := proj1 Hforward.
  apply (Hseparated location location).
  - exists location. split.
    + left. exists x, T. repeat split; try assumption.
      unfold capability_in_context. left. exact Hmut.
    + constructor.
  - exact (Hcontains location HinP).
  - apply rt_refl.
Qed.

Lemma safe_field_write_cannot_target_protected_slot :
  forall CT P Z cutoff authority sGamma mt rGamma h stack
    x field y sGamma' rGamma' h' source runtime_q C fields,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    safe_readonly_method_type mt ->
    eval_stmt OK P CT rGamma h (SFldWrite x field y) OK P rGamma' h' ->
    runtime_getVal rGamma x = Some (Iot source) ->
    runtime_getObj h source = Some (mkObj (mkruntime_type runtime_q C) fields) ->
    In Loc P source ->
    protected_field_condition CT C field mt ->
    False.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack
    x field y sGamma' rGamma' h' source runtime_q C fields
    Hstate Hwf Htyping Hsafe Heval
    Hvalue Hobj HinP Hprotected.
  inversion Htyping; subst.
  - exact ((proj1 Hsafe) eq_refl).
  - exact ((proj2 Hsafe) eq_refl).
  - destruct Hprotected as [Hfinal | [Hrda | Hconcrete]].
    + destruct (wf_config_variable_typable CT _ rGamma h x source Tx
        Hwf Hget_x Hvalue) as [qcontext Htypable].
      unfold wf_r_typable, r_type in Htypable. rewrite Hobj in Htypable.
      destruct Htypable as [Hbase _].
      destruct (base_subtype_from_ref CT C (sbase Tx) Hbase) as
        [D [Hstatic_base Hclass]].
      rewrite Href in Hstatic_base. injection Hstatic_base as <-.
      have Heq : Final = a.
      { eapply sf_assignability_consistent_subtype.
        - exact (proj1 Hwf).
        - exact Hclass.
        - exact Hfinal.
        - exact Hassign_rel. }
      subst a. unfold vpa_assignability in Hassignable.
      destruct (sqtype Tx); discriminate.
    + destruct (wf_config_variable_typable CT _ rGamma h x source Tx
        Hwf Hget_x Hvalue) as [qcontext Htypable].
      unfold wf_r_typable, r_type in Htypable. rewrite Hobj in Htypable.
      destruct Htypable as [Hbase _].
      destruct (base_subtype_from_ref CT C (sbase Tx) Hbase) as
        [D [Hstatic_base Hclass]].
      rewrite Href in Hstatic_base. injection Hstatic_base as <-.
      have Heq : RDA = a.
      { eapply sf_assignability_consistent_subtype.
        - exact (proj1 Hwf).
        - exact Hclass.
        - exact Hrda.
        - exact Hassign_rel. }
      subst a. unfold vpa_assignability in Hassignable.
      destruct (sqtype Tx) eqn:Hreceiver; try discriminate.
      eapply (active_mut_root_cannot_be_protected CT P Z cutoff h authority
        _ rGamma stack x Tx source); eauto.
    + destruct Hconcrete as [Hbad | Hbad]; discriminate.
  - destruct (concrete_immutability_field_write_requires_mutable_receiver
      CT _ x field y _ Htyping) as [Tx0 [Hget Hmut]].
    eapply (active_mut_root_cannot_be_protected CT P Z cutoff h authority
      _ rGamma stack x Tx0 source); eauto.
Qed.

Lemma safe_typed_call_preserves_protected_field_condition :
  forall CT sGamma mt rGamma h x y method args sGamma'
    receiver_location receiver_class runtime_mdef C field,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x y method args) sGamma' ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma y = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some receiver_class ->
    FindMethodWithName CT receiver_class method runtime_mdef ->
    protected_field_condition CT C field mt ->
    protected_field_condition CT C field
      (mtype (msignature runtime_mdef)).
Proof.
  intros CT sGamma mt rGamma h x y method args sGamma'
    receiver_location receiver_class runtime_mdef C field Hwf Htyping Hsafe
    Hreceiver Hbase Hfind Hprotected.
  destruct Hprotected as [Hfinal | [Hrda | Hconcrete]].
  - left. exact Hfinal.
  - right. left. exact Hrda.
  - right. right.
    inversion Htyping; subst.
    + destruct Hsafe as [Hnot_abs Hnot_cs].
      destruct Hscope as [-> | [-> _]]; contradiction.
    + have Hsignature : msignature runtime_mdef = msignature mdef.
      { eapply runtime_call_signature_agrees; eauto. }
      rewrite Hsignature.
      eapply concrete_assignability_submethod; eauto.
Qed.

Theorem successful_stmt_preserves_protected_field :
  forall P CT rGamma h statement rGamma' h',
    eval_stmt OK P CT rGamma h statement OK P rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff,
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      safe_readonly_method_type mt ->
      forall location runtime_q C fields fields' field,
        In Loc P location ->
        runtime_getObj h location =
          Some (mkObj (mkruntime_type runtime_q C) fields) ->
        runtime_getObj h' location =
          Some (mkObj (mkruntime_type runtime_q C) fields') ->
        protected_field_condition CT C field mt ->
        nth_error fields field = nth_error fields' field.
Proof.
  intros P CT rGamma h statement rGamma' h' Heval.
  have Heval_copy := Heval.
  dependent induction Heval;
    intros sGamma mt sGamma' authority stack Z cutoff Hstate Htyping Hsafe
      location runtime_q C fields fields' protected_field HinP Hobj_start
      Hobj_end Hprotected.
  - rewrite Hobj_start in Hobj_end. injection Hobj_end as ->. reflexivity.
  - rewrite Hobj_start in Hobj_end. injection Hobj_end as ->. reflexivity.
  - rewrite Hobj_start in Hobj_end. injection Hobj_end as ->. reflexivity.
  - destruct (Nat.eq_dec loc_x location) as [Hsame_location | Hother_location].
    + subst loc_x. rewrite Hobj_start in Hobj. injection Hobj as <-.
      destruct (Nat.eq_dec f protected_field) as [Hsame_field | Hother_field].
      * subst f. exfalso.
        eapply safe_field_write_cannot_target_protected_slot with
          (Z := Z) (cutoff := cutoff) (authority := authority)
          (stack := stack)
          (source := location) (runtime_q := runtime_q)
          (C := C) (fields := fields).
        -- exact Hstate.
        -- exact (proj1 (proj1 (proj2 (proj1 Hstate)))).
        -- exact Htyping.
        -- exact Hsafe.
        -- exact Heval_copy.
        -- exact Hval_x.
        -- exact Hobj_start.
        -- exact HinP.
        -- exact Hprotected.
      * unfold update_field in Hupdate. rewrite Hobj_start in Hupdate.
        subst h'. unfold runtime_getObj in Hobj_end.
        have Hlocation_dom := Hobj_start.
        apply runtime_getObj_dom in Hlocation_dom.
        rewrite update_same in Hobj_end; try exact Hlocation_dom.
        injection Hobj_end as Hfields_eq. subst fields'.
        simpl. rewrite update_diff; auto.
    + unfold update_field in Hupdate. rewrite Hobj in Hupdate. subst h'.
      unfold runtime_getObj in Hobj_end.
      rewrite update_diff in Hobj_end; auto.
      unfold runtime_getObj in Hobj_start. rewrite Hobj_start in Hobj_end.
      injection Hobj_end as ->. reflexivity.
  - inversion Htyping; subst.
    unfold runtime_getObj in Hobj_end.
    have Hlocation_dom := Hobj_start.
    apply runtime_getObj_dom in Hlocation_dom.
    rewrite nth_error_app1 in Hobj_end; try exact Hlocation_dom.
    unfold runtime_getObj in Hobj_start. rewrite Hobj_start in Hobj_end.
    injection Hobj_end as Hfields_eq. subst fields'. reflexivity.
  - destruct Hfind as [Hfind_method Hbody_definition].
    subst mbody. subst mstmt. subst mret. subst rΓ'. subst rΓ'''.
    have Hcaller_wf : wf_r_config CT sGamma rΓ h :=
      proj1 (proj1 (proj2 (proj1 Hstate))).
    destruct (safe_typed_call_static_result CT sGamma mt rΓ h x y m zs
      sGamma' ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase Hfind_method)
      as [destination_type [receiver_type
        [HsGamma [Hdestination_not_receiver [Hdestination_type
          [Hreceiver_type Hresult_sub]]]]]].
    subst sGamma'.
    have Hcallee_safe := safe_typed_call_target_method_safe CT sGamma mt rΓ
      h x y m zs sGamma ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase
      Hfind_method.
    destruct (typed_call_target CT sGamma mt rΓ h x y m zs sGamma vals ly
      cy mdef Hcaller_wf Htyping Hval_y Hbase Hfind_method Hargs) as
      [declaring_class [declaring_def [body_end
        [Hruntime_sub [Hdeclaring_class [Hmethod_member
          [Hmethod_wf [Hbody_typing Hcallee_initial_wf]]]]]]]].
    destruct (potential_history_enter_call CT P Z cutoff authority sGamma mt
      rΓ h stack x y m zs sGamma vals ly cy mdef receiver_type Hstate
      Htyping Hsafe Hreceiver_type Hval_y Hbase Hfind_method Hargs) as
      [origins Hentry].
    have Hcallee_protected :=
      safe_typed_call_preserves_protected_field_condition CT sGamma mt rΓ h
        x y m zs sGamma ly cy mdef C protected_field Hcaller_wf Htyping Hsafe
        Hval_y Hbase Hfind_method Hprotected.
    eapply (IHHeval eq_refl eq_refl eq_refl Heval); eauto.
  - inversion Htyping; subst.
    have Hmiddle_state := successful_stmt_preserves_potential_history
      P CT rΓ h s1 rΓ' h' Heval1 sGamma mt sΓ' authority stack Z cutoff
      Hstate Htype1 Hsafe.
    destruct (runtime_preserves_r_type_heap P CT rΓ h location
      (mkruntime_type runtime_q C) h' fields s1 rΓ' Hobj_start Heval1) as
      [middle_fields Hobj_middle].
    have Hfirst := IHHeval1 eq_refl eq_refl eq_refl Heval1
      sGamma mt sΓ' authority stack Z cutoff Hstate Htype1 Hsafe
      location runtime_q C fields middle_fields protected_field HinP
      Hobj_start Hobj_middle Hprotected.
    have Hsecond := IHHeval2 eq_refl eq_refl eq_refl Heval2
      sΓ' mt sGamma' authority stack Z cutoff Hmiddle_state Htype2 Hsafe
      location runtime_q C middle_fields fields' protected_field HinP
      Hobj_middle Hobj_end Hprotected.
    rewrite Hfirst. exact Hsecond.
  - inversion Htyping; subst.
    eapply (IHHeval eq_refl eq_refl eq_refl Heval); eauto.
  - inversion Htyping; subst.
    eapply (IHHeval eq_refl eq_refl eq_refl Heval); eauto.
Qed.

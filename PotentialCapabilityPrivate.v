Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityAtomic.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

(** Result package for the strengthened, proof-internal statement induction.
    The first conjunct is the phase-aware authority history maintained by the
    flexible-call semantics.  It deliberately does not assert separation in
    the unrestricted potential graph: allocation through a read-only alias
    may create a benign fresh potential overlap without transferring mutation
    authority.  The remaining conjuncts are ghost state: [final_snapshots]
    may evolve while a statement executes, but its immutable call-entry
    metadata continues to correspond pointwise to [initial_snapshots], and
    every protected latent exposure reflects to the corresponding entry
    image. *)
Definition private_statement_preservation_result
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (final_senv : s_env) (final_renv : r_env)
  (stack : list watched_boundary) (incoming : Ensemble authority_flow_state)
  (initial_snapshots final_snapshots : list frozen_caller_snapshot_slot)
  (final_h : heap) : Prop :=
  principled_phased_authority_live_history_state CT P Z cutoff
    (mk_watched_frame authority final_senv final_renv) stack incoming
    final_h /\
  private_fresh_frozen_statement_state CT P Z cutoff
    (mk_watched_frame authority final_senv final_renv) stack incoming
    final_snapshots final_h /\
  frozen_caller_snapshot_list_metadata_eq final_snapshots initial_snapshots /\
  frozen_snapshot_list_resume_exposure_protected_reflected Z final_snapshots
    initial_snapshots.

Lemma caller_post_capability_root_origin_private :
  forall caller_authority caller_senv caller_renv destination
    destination_type return_location root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) root ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv caller_renv) root \/
    root = return_location.
Proof.
  intros caller_authority caller_senv caller_renv destination
    destination_type return_location root Hdestination_nonzero Hdestination
    Hlength [variable [T [Htype [Hvalue Hcapability]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom. rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hdestination_dom) in Hvalue.
    injection Hvalue as <-. right. reflexivity.
  - left. exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable (Iot return_location) (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hcapability.
Qed.

Lemma caller_post_rdm_root_origin_private :
  forall caller_senv caller_renv destination destination_type return_location
    root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (root = return_location /\ sqtype destination_type = RDM).
Proof.
  intros caller_senv caller_renv destination destination_type return_location
    root Hdestination_nonzero Hdestination Hlength
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom. rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hdestination_dom) in Hvalue.
    injection Hvalue as <-. right. split; [reflexivity|]. congruence.
  - left. exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable (Iot return_location) (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hrdm.
Qed.

Definition return_pop_location_covered
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (location : Loc) : Prop :=
  prospective_location_covered_by_frame CT h caller location \/
  prospective_location_covered_by_frame CT h callee location.

Lemma return_pop_prospective_step_covered :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    r_muttype h target = Some Mut_r ->
    prospective_location_covered_by_frame CT h callee return_location ->
    return_pop_location_covered CT h caller callee source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      (FlowProspective, source) (FlowProspective, target) ->
    return_pop_location_covered CT h caller callee target.
Proof.
  intros CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target Hcaller
    Hdestination_nonzero Hdestination Hlength Htarget_runtime Hreturn Hsource
    Hstep.
  inversion Hstep; subst.
  - destruct Hsource as
      [[root [Hroot Hpath]] | [root [Hroot Hpath]]].
    + left. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_retained. exact H1.
    + right. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_retained. exact H1.
  - destruct Hsource as
      [[root [Hroot Hpath]] | [root [Hroot Hpath]]].
    + left. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_rdm_backward. exact H1.
    + right. exists root. split; [exact Hroot|].
      eapply rt_trans; [exact Hpath|]. apply rt_step.
      apply frozen_caller_prospective_rdm_backward. exact H1.
  - destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
      destination destination_type return_location target
      Hdestination_nonzero Hdestination Hlength H2) as
      [Hold_root | [Hreturn_root Hdestination_rdm]].
    + left. exists target. split.
      * right. split.
        -- exact Hold_root.
        -- exact Htarget_runtime.
      * apply rt_refl.
    + subst target. right. exact Hreturn.
Qed.

Definition return_pop_prospective_state_covered
  (CT : class_table) (h : heap) (caller callee : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowProspective /\
  r_muttype h (snd state) = Some Mut_r /\
  return_pop_location_covered CT h caller callee (snd state).

Lemma return_pop_prospective_state_step_covered :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    prospective_location_covered_by_frame CT h callee return_location ->
    return_pop_prospective_state_covered CT h caller callee source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      source target ->
    return_pop_prospective_state_covered CT h caller callee target.
Proof.
  intros CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location [source_mode source]
    [target_mode target] Hcaller Hdestination_nonzero Hdestination Hlength
    Hpost_wf Hreturn [Hsource_mode [Hsource_runtime Hsource]] Hstep.
  simpl in *. subst source_mode.
  have Htarget_mode : target_mode = FlowProspective.
  { inversion Hstep; reflexivity. }
  subst target_mode.
  have Htarget_runtime := phased_authority_frame_step_preserves_runtime_mutability
    CT h
    (mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)))
    (FlowProspective, source) (FlowProspective, target) Mut_r Hpost_wf
    (frozen_caller_authority_step_is_phased CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      (FlowProspective, source) (FlowProspective, target) Hstep)
    Hsource_runtime.
  split; [reflexivity|]. split; [exact Htarget_runtime|].
  eapply return_pop_prospective_step_covered; eauto.
Qed.

Lemma return_pop_prospective_state_connected_covered :
  forall CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target,
    caller = mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    prospective_location_covered_by_frame CT h callee return_location ->
    return_pop_prospective_state_covered CT h caller callee source ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      source target ->
    return_pop_prospective_state_covered CT h caller callee target.
Proof.
  intros CT h caller callee caller_authority caller_senv caller_renv
    destination destination_type return_location source target Hcaller
    Hdestination_nonzero Hdestination Hlength Hpost_wf Hreturn Hsource
    Hconnected.
  induction Hconnected.
  - eapply return_pop_prospective_state_step_covered; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma caller_post_mutable_authority_root_covered :
  forall CT caller_authority caller_senv caller_renv destination destination_type
    return_location h callee root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    r_muttype h root = Some Mut_r ->
    prospective_location_covered_by_frame CT h callee return_location ->
    mutable_authority_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      h root ->
    return_pop_location_covered CT h
      (mk_watched_frame caller_authority caller_senv caller_renv) callee root.
Proof.
  intros CT caller_authority caller_senv caller_renv destination destination_type
    return_location h callee root Hdestination_nonzero Hdestination Hlength
    Hroot_runtime Hreturn [Hmut | [Hrdm Hruntime]].
  - have Hcapability : frame_capability_root
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        root.
    { destruct Hmut as [variable [T [Htype [Hvalue Hmut]]]].
      exists variable, T. repeat split; try assumption.
      unfold capability_in_context. left. exact Hmut. }
    destruct (caller_post_capability_root_origin_private caller_authority
      caller_senv caller_renv destination destination_type return_location
      root Hdestination_nonzero Hdestination Hlength Hcapability) as
      [Hold_root | Hreturn_root].
    + left. exists root. split; [|apply rt_refl].
      destruct Hold_root as
        [variable [T [Htype [Hvalue [Hold_mut | [Hold_rdm Hauthority]]]]]].
      * left. exists variable, T. repeat split; assumption.
      * right. split.
        -- exists variable, T. repeat split; assumption.
        -- exact Hroot_runtime.
    + subst root. right. exact Hreturn.
  - destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
      destination destination_type return_location root
      Hdestination_nonzero Hdestination Hlength Hrdm) as
      [Hold_root | [Hreturn_root Hdestination_rdm]].
    + left. exists root. split.
      * right. split; assumption.
      * apply rt_refl.
    + subst root. right. exact Hreturn.
Qed.

Lemma caller_null_post_capability_root_is_old :
  forall caller_authority caller_senv caller_renv destination
    destination_type root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) root ->
    frame_capability_root
      (mk_watched_frame caller_authority caller_senv caller_renv) root.
Proof.
  intros caller_authority caller_senv caller_renv destination
    destination_type root Hdestination_nonzero Hdestination Hlength
    [variable [T [Htype [Hvalue Hcapability]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination Null_a
      Hdestination_dom) in Hvalue. discriminate.
  - exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable Null_a (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hcapability.
Qed.

Lemma caller_null_post_rdm_root_is_old :
  forall caller_senv caller_renv destination destination_type root,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination Null_a) root ->
    typed_root RDM caller_senv caller_renv root.
Proof.
  intros caller_senv caller_renv destination destination_type root
    Hdestination_nonzero Hdestination Hlength
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    rewrite Hlength in Hdestination_dom.
    rewrite (runtime_getVal_update_same caller_renv destination Null_a
      Hdestination_dom) in Hvalue. discriminate.
  - exists variable, T. split; [exact Htype|]. split.
    + have Hold_value := runtime_getVal_update_diff caller_renv destination
        variable Null_a (ltac:(congruence)).
      rewrite Hvalue in Hold_value. symmetry. exact Hold_value.
    + exact Hrdm.
Qed.

Definition boundary_view_anchor
  (boundary : watched_boundary) (root : Loc) : Prop :=
  match boundary.(boundary_receiver_view) with
  | Mut => typed_root Mut
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | Imm => typed_root Imm
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | RDM => typed_root RDM
      boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) root
  | RO | Lost | Bot => False
  end.

Definition boundary_view_attachment
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    potential_connected CT h boundary.(boundary_caller) stack anchor root.

Definition boundary_view_entry
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    potential_connected CT h boundary.(boundary_caller) stack root anchor.

Definition authority_boundary_view_attachment
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    authority_color_connected CT h boundary.(boundary_caller) stack
      anchor root.

Definition authority_boundary_view_entry
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    authority_color_connected CT h boundary.(boundary_caller) stack
      root anchor.

Lemma boundary_view_attachment_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    boundary_view_attachment CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma boundary_view_entry_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    boundary_view_entry CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma boundary_view_attachment_transport :
  forall CT h boundary stack first second,
    boundary_view_attachment CT h boundary stack first ->
    potential_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_view_attachment CT h boundary stack second.
Proof.
  intros CT h boundary stack first second
    [anchor [Hanchor Hanchor_first]] Hfirst_second.
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.

Lemma boundary_view_entry_transport :
  forall CT h boundary stack first second,
    potential_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_view_entry CT h boundary stack second ->
    boundary_view_entry CT h boundary stack first.
Proof.
  intros CT h boundary stack first second Hfirst_second
    [anchor [Hanchor Hsecond_anchor]].
  exists anchor. split; [exact Hanchor|].
  eapply potential_connected_trans; eauto.
Qed.

Lemma readonly_boundary_roots_equal :
  forall boundary left right,
    boundary.(boundary_receiver_view) = RO ->
    typed_root RDM boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) left ->
    typed_root RDM boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) right ->
    left = right.
Proof.
  intros boundary left right Hview Hleft Hright.
  have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
  have Hright_origin := boundary_entry_rdm_root_by_view boundary right Hright.
  rewrite Hview in Hleft_origin, Hright_origin.
  destruct Hleft_origin as
    [left_receiver [Hleft_receiver [Hleft_eq Hleft_root]]].
  destruct Hright_origin as
    [right_receiver [Hright_receiver [Hright_eq Hright_root]]].
  rewrite Hleft_receiver in Hright_receiver.
  injection Hright_receiver as <-. congruence.
Qed.

Lemma potential_adjacent_after_call_push :
  forall CT h boundary stack callee_authority left right,
    potential_adjacent CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    potential_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_view_entry CT h boundary stack left /\
     boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right
    [Hheap | [Hframe | Hreturn]].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin := boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * left. have Heq := readonly_boundary_roots_equal boundary left right
          Hview Hleft Hright. subst right. apply rt_refl.
      * contradiction.
      * contradiction.
    + simpl in H.
      destruct H as [Htop | Htail].
      * subst boundary0. left. eapply live_frame_rdm_roots_potentially_connected
          with (frame := boundary.(boundary_caller)).
        -- constructor.
        -- exact Hleft.
        -- exact Hright.
      * left. apply rt_step. right. left. exists boundary0.(boundary_caller).
        repeat split; try assumption. constructor. exact Htail.
  - destruct Hreturn as
      [callee [return_boundary
        [Hlive [Hview [Hcallee_return
          [Hruntime [Hroots | Hroots]]]]]]].
    + inversion Hlive; subst.
      * have Horigin := boundary_entry_rdm_root_by_view return_boundary left
          (proj1 Hroots).
        rewrite Hview in Horigin. simpl in Horigin.
        left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := return_boundary.(boundary_caller)).
        -- constructor.
        -- exact Horigin.
        -- exact (proj2 Hroots).
      * left. apply rt_step. right. right. exists callee, return_boundary.
        split.
        { match goal with
          | Htail : live_call_boundary _ _ _ _ |- _ => exact Htail
          end. }
        split; [exact Hview|]. split; [exact Hcallee_return|].
        split; [exact Hruntime|]. left. exact Hroots.
    + inversion Hlive; subst.
      * have Horigin := boundary_entry_rdm_root_by_view return_boundary right
          (proj2 Hroots).
        rewrite Hview in Horigin. simpl in Horigin.
        left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := return_boundary.(boundary_caller)).
        -- constructor.
        -- exact (proj1 Hroots).
        -- exact Horigin.
      * left. apply rt_step. right. right. exists callee, return_boundary.
        split.
        { match goal with
          | Htail : live_call_boundary _ _ _ _ |- _ => exact Htail
          end. }
        split; [exact Hview|]. split; [exact Hcallee_return|].
        split; [exact Hruntime|]. right. exact Hroots.
Qed.

Lemma potential_connected_after_call_push :
  forall CT h boundary stack callee_authority left right,
    potential_connected CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    potential_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_view_entry CT h boundary stack left /\
     boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right Hconnected.
  induction Hconnected.
  - eapply potential_adjacent_after_call_push; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as [Hxy | [Hentry_x Hattach_y]];
      destruct IHHconnected2 as [Hyz | [Hentry_y Hattach_z]].
    + left. eapply potential_connected_trans; eauto.
    + right. split.
      * eapply boundary_view_entry_transport; eauto.
      * exact Hattach_z.
    + right. split.
      * exact Hentry_x.
      * eapply boundary_view_attachment_transport; eauto.
    + right. split; assumption.
Qed.

Lemma potential_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)))
        (mk_watched_call_boundary
          (mk_watched_frame caller_authority sGamma rGamma)
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) (sqtype Ty)
          (mreturn (mbody runtime_mdef)) (sqtype destination_type)
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins ::
          stack) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hlive [Hpotential Hcutoffs]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs.
  have Hcomponent : component_forward_history_state CT P Z
      (live_capability_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) stack)
      cutoff sGamma rGamma h.
  { eapply mutable_authority_component_history
      with (authority := caller_authority).
    exact (proj1 Hlive). }
  destruct (live_history_enter_call CT P Z cutoff caller_authority sGamma mt
    rGamma h stack x method y args sGamma' vals ly cy runtime_mdef Ty Hlive
    Hcomponent Htyping Hscope Hgety Hvalue Hbase Hfind Hargs) as
    [origins [destination_type [Hdestination Hlive_post]]].
  exists origins, destination_type. split; [exact Hdestination|].
  split; [exact Hlive_post|].
  split.
  {
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  set (boundary := mk_watched_call_boundary caller callee_senv callee_renv
    (sqtype Ty) (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 Hlive)).
  have Hframes : live_frames_wf CT h caller stack.
  { unfold caller. exact (proj1 (proj2 Hlive)). }
  have Hsound : live_frames_authority_sound h caller stack.
  { unfold caller. exact (proj1 (proj2 (proj2 Hlive))). }
  intros capability protected Hcapability Hprotected Hconnected.
  have Hcapability_old : In Loc
      (live_capability_set CT h caller stack) capability.
  { unfold boundary, caller, callee_senv, callee_renv in Hcapability |- *.
    apply (proj1 (call_push_live_reachability_equivalent CT caller_authority
      sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
      origins (mreturn (mbody runtime_mdef)) (sqtype destination_type)
      (sqtype (mret (msignature runtime_mdef))) (dom h) stack capability
      Hwf Htyping Hscope Hgety Hvalue Hbase Hfind
      Hargs)).
    exact Hcapability. }
  destruct (potential_connected_after_call_push CT h boundary stack
    (call_authority caller_authority (sqtype Ty)) capability protected
    Hconnected) as
    [Hold_connected | [Hcapability_entry Hprotected_attachment]].
  - unfold caller in Hcapability_old, Hold_connected, Hframes, Hsound |- *.
    exact (Hpotential capability protected Hcapability_old Hprotected
      Hold_connected).
  - destruct (sqtype Ty) eqn:Hview.
    + destruct Hprotected_attachment as
        [zone_anchor [Hzone_anchor Hzone_connected]].
      unfold boundary_view_anchor in Hzone_anchor.
      unfold boundary in Hzone_anchor, Hzone_connected. simpl in *.
      have Hzone_capability : In Loc
          (live_capability_set CT h caller stack) zone_anchor.
      { unfold caller. eapply typed_mut_root_is_live_capability; eauto. }
      unfold caller in Hzone_capability, Hzone_connected.
      exact (Hpotential zone_anchor protected Hzone_capability Hprotected
        Hzone_connected).
    + destruct Hcapability_entry as
        [capability_anchor [Hcapability_anchor Hanchor_connected]].
      unfold boundary_view_anchor in Hcapability_anchor.
      unfold boundary in Hcapability_anchor, Hanchor_connected. simpl in *.
      have Hcapability_runtime := live_capability_members_runtime_mutable CT h
        caller stack Hframes Hsound capability Hcapability_old.
      have Hanchor_immutable := typed_imm_root_runtime_immutable CT sGamma
        rGamma h capability_anchor Hwf Hcapability_anchor.
      have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
      have Hanchor_runtime := potential_connected_preserves_runtime_mutability
        CT h caller stack capability capability_anchor Mut_r Hframes Hheap_wf
        Hanchor_connected Hcapability_runtime.
      rewrite Hanchor_immutable in Hanchor_runtime. discriminate.
    + destruct Hcapability_entry as
        [capability_anchor [Hcapability_anchor Hcapability_connected]].
      destruct Hprotected_attachment as
        [zone_anchor [Hzone_anchor Hzone_connected]].
      unfold boundary_view_anchor in Hcapability_anchor, Hzone_anchor.
      unfold boundary in Hcapability_anchor, Hzone_anchor,
        Hcapability_connected, Hzone_connected. simpl in *.
      unfold caller in Hcapability_old, Hcapability_connected, Hzone_connected.
      apply (Hpotential capability protected Hcapability_old Hprotected).
      eapply potential_connected_trans.
	      * exact Hcapability_connected.
      * eapply potential_connected_trans.
        -- eapply live_frame_rdm_roots_potentially_connected
             with (frame := mk_watched_frame caller_authority sGamma rGamma).
           ++ constructor.
           ++ exact Hcapability_anchor.
           ++ exact Hzone_anchor.
        -- exact Hzone_connected.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
    + destruct Hcapability_entry as
        [anchor [Hanchor Hanchor_connected]].
      unfold boundary_view_anchor in Hanchor.
      unfold boundary in Hanchor. simpl in Hanchor.
      contradiction.
  }
  { constructor.
    - simpl. lia.
    - exact Hcutoffs.
  }
Qed.

Lemma readonly_adaptation_subtype_rdm :
  forall receiver_q return_q,
    receiver_q <> Bot ->
    q_subtype
      (vpa_mutability_qq_readonly_state receiver_q return_q) RDM ->
    (receiver_q = RDM /\ return_q = RDM) \/ return_q = Bot.
Proof.
  intros receiver_q return_q Hreceiver Hsub.
  destruct receiver_q, return_q; simpl in Hsub;
    inversion Hsub; subst; auto; contradiction.
Qed.

Lemma refined_call_rdm_result_classifies_body_return :
  forall CT receiver_type body_return_type runtime_sig static_sig
    destination_type,
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype body_return_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype receiver_type = RDM /\
    (sqtype body_return_type = RDM \/
     sqtype body_return_type = Mut \/
     sqtype body_return_type = Imm).
Proof.
  intros CT receiver_type body_return_type runtime_sig static_sig
    destination_type Hbody Hrefine Hresult Hreceiver_nonbottom
    Hbody_nonbottom Hdestination.
  have Hresult_q := qualified_type_subtype_q_subtype CT
    (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
    destination_type Hresult.
  rewrite sq_vpa_tt_eq_qq_readonly_state in Hresult_q.
  rewrite Hdestination in Hresult_q.
  destruct (readonly_adaptation_subtype_rdm
    (sqtype receiver_type) (sqtype (mret static_sig))
    Hreceiver_nonbottom Hresult_q) as
    [[Hreceiver_rdm Hstatic_rdm] | Hstatic_bot].
  - split; [exact Hreceiver_rdm|].
    have Hruntime_cases :
      is_concrete_or_rdm_or_bot (sqtype (mret runtime_sig)).
    { eapply method_signature_refinement_return_concrete_or_rdm_or_bot;
        eauto.
      unfold is_concrete_or_rdm_or_bot. auto. }
    have Hbody_cases :
      is_concrete_or_rdm_or_bot (sqtype body_return_type).
    { eapply subtype_concrete_or_rdm_or_bot; eauto. }
    unfold is_concrete_or_rdm_or_bot in Hbody_cases.
    destruct Hbody_cases as
      [Hmut | [Himm | [Hrdm | Hbot]]]; auto.
    contradiction.
  - have Hruntime_bot :
      sqtype (mret runtime_sig) = Bot.
    { eapply method_signature_refinement_return_bot; eauto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hruntime_bot in Hbody_q.
    have Hbody_bot : sqtype body_return_type = Bot.
    { inversion Hbody_q; subst; reflexivity. }
    contradiction.
Qed.

Lemma refined_call_rdm_mut_body_signature_shape :
  forall CT receiver_type body_return_type runtime_sig static_sig
    destination_type,
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype body_return_type = Mut ->
    sqtype (mret static_sig) = RDM /\
    sqtype (mret runtime_sig) = Mut.
Proof.
  intros CT receiver_type body_return_type runtime_sig static_sig
    destination_type Hbody Hrefine Hresult Hreceiver_nonbottom Hdestination
    Hbody_mut.
  have Hresult_q := qualified_type_subtype_q_subtype CT
    (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
    destination_type Hresult.
  rewrite sq_vpa_tt_eq_qq_readonly_state in Hresult_q.
  rewrite Hdestination in Hresult_q.
  destruct (readonly_adaptation_subtype_rdm
    (sqtype receiver_type) (sqtype (mret static_sig))
    Hreceiver_nonbottom Hresult_q) as
    [[_ Hstatic_rdm] | Hstatic_bot].
  - split; [exact Hstatic_rdm|].
    have Hruntime_cases :
        is_concrete_or_rdm_or_bot (sqtype (mret runtime_sig)).
    { eapply method_signature_refinement_return_concrete_or_rdm_or_bot;
        eauto.
      unfold is_concrete_or_rdm_or_bot. auto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_mut in Hbody_q.
    unfold is_concrete_or_rdm_or_bot in Hruntime_cases.
    destruct Hruntime_cases as
      [Hruntime_mut | [Hruntime_imm | [Hruntime_rdm | Hruntime_bot]]].
    + exact Hruntime_mut.
    + rewrite Hruntime_imm in Hbody_q. inversion Hbody_q.
    + rewrite Hruntime_rdm in Hbody_q. inversion Hbody_q.
    + rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
  - have Hruntime_bot :
        sqtype (mret runtime_sig) = Bot.
    { eapply method_signature_refinement_return_bot; eauto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_mut in Hbody_q.
    rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
Qed.

Lemma refined_call_rdm_rdm_body_signature_return :
  forall CT receiver_type body_return_type runtime_sig static_sig
    destination_type,
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype body_return_type = RDM ->
    sqtype (mret runtime_sig) = RDM.
Proof.
  intros CT receiver_type body_return_type runtime_sig static_sig
    destination_type Hbody Hrefine Hresult Hreceiver_nonbottom Hdestination
    Hbody_rdm.
  have Hresult_q := qualified_type_subtype_q_subtype CT
    (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
    destination_type Hresult.
  rewrite sq_vpa_tt_eq_qq_readonly_state in Hresult_q.
  rewrite Hdestination in Hresult_q.
  destruct (readonly_adaptation_subtype_rdm
    (sqtype receiver_type) (sqtype (mret static_sig))
    Hreceiver_nonbottom Hresult_q) as
    [[_ Hstatic_rdm] | Hstatic_bot].
  - have Hruntime_cases :
        is_concrete_or_rdm_or_bot (sqtype (mret runtime_sig)).
    { eapply method_signature_refinement_return_concrete_or_rdm_or_bot;
        eauto.
      unfold is_concrete_or_rdm_or_bot. auto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_rdm in Hbody_q.
    unfold is_concrete_or_rdm_or_bot in Hruntime_cases.
    destruct Hruntime_cases as
      [Hruntime_mut | [Hruntime_imm | [Hruntime_rdm | Hruntime_bot]]].
    + rewrite Hruntime_mut in Hbody_q. inversion Hbody_q.
    + rewrite Hruntime_imm in Hbody_q. inversion Hbody_q.
    + exact Hruntime_rdm.
    + rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
  - have Hruntime_bot :
        sqtype (mret runtime_sig) = Bot.
    { eapply method_signature_refinement_return_bot; eauto. }
    have Hbody_q := qualified_type_subtype_q_subtype CT
      body_return_type (mret runtime_sig) Hbody.
    rewrite Hbody_rdm in Hbody_q.
    rewrite Hruntime_bot in Hbody_q. inversion Hbody_q.
Qed.

(** In the only flexible-override shape that refines a statically RDM result
    to a dynamically mutable result, the callee cannot start with a non-null
    RDM root.  The receiver is RO.  For an ordinary dynamic RDM parameter,
    class-bounded contravariance forces the corresponding static parameter to
    be Bot, so a well-formed caller can pass only null at that position.

    This is the signature-level fact that rules out publishing a fresh Mut
    result through an old RDM parameter; it follows from behavioral subtyping
    rather than from a dispatch-side premise. *)
Lemma refined_mut_return_call_entry_has_no_rdm_roots :
  forall CT sGamma mt rGamma h x method receiver args vals receiver_location
    receiver_type runtime_mdef static_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method receiver args) sGamma ->
    readonly_state_method_scope mt ->
    static_getType sGamma receiver = Some receiver_type ->
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    runtime_lookup_list rGamma args = Some vals ->
    FindMethodWithName CT (sctype receiver_type) method static_mdef ->
    method_signature_refinement CT
      (msignature runtime_mdef) (msignature static_mdef) ->
    sqtype (mret (msignature static_mdef)) = RDM ->
    sqtype (mret (msignature runtime_mdef)) = Mut ->
    sqtype (mreceiver (msignature runtime_mdef)) = RO ->
    forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot receiver_location :: vals)) root.
Proof.
  intros CT sGamma mt rGamma h x method receiver args vals
    receiver_location receiver_type runtime_mdef static_mdef Hwf Htyping
    Hsafe Hreceiver_type Hreceiver_value Hargs Hfind_static Hrefine
    Hstatic_return Hruntime_return Hruntime_receiver root
    [variable [T [Htype [Hvalue Hrdm]]]].
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst;
      destruct Hscope as [Has | [Hcs _]]; discriminate.
  - assert (Ty = receiver_type) by congruence. subst Ty.
    have Hstatic_method :=
      find_method_with_name_deterministic CT (sctype receiver_type) method
        mdef static_mdef Hfind_m Hfind_static.
    subst mdef.
    destruct variable as [|i].
    + simpl in Htype. injection Htype as <-.
      rewrite Hruntime_receiver in Hrdm. discriminate.
    + simpl in Htype, Hvalue.
      unfold static_getType in Htype.
      assert (Hi_runtime :
          i < length (mparams (msignature runtime_mdef))).
      { apply nth_error_Some. rewrite Htype. discriminate. }
      have Hrefine_lengths :=
        method_signature_refinement_params_length CT
          (msignature runtime_mdef) (msignature static_mdef) Hrefine.
      assert (Hi_static :
          i < length (mparams (msignature static_mdef))) by lia.
      destruct (nth_error_Some_exists
        (mparams (msignature static_mdef)) i Hi_static) as
        [static_parameter Hstatic_parameter].
      have Hstatic_parameter_bot :
          sqtype static_parameter = Bot.
      { eapply method_signature_refinement_mut_return_rdm_parameter_parent_bot;
          eauto. }
      have Harg_lengths := Forall2_length Harg_sub.
      assert (Hi_argtypes : i < length argtypes) by lia.
      destruct (nth_error_Some_exists argtypes i Hi_argtypes)
        as [argument_type Hargument_type].
      have Hsub_i := Harg_sub.
      eapply Forall2_nth_error with
        (i := i) (a := argument_type) (b := static_parameter) in Hsub_i;
        [|exact Hargument_type|exact Hstatic_parameter].
      destruct (static_getType_list_nth_zs _ args argtypes i argument_type
        Hget_args Hargument_type) as
        [argument [Hargument_index Hargument_static]].
      destruct (runtime_lookup_list_nth_zs rGamma args vals i (Iot root)
        Hargs Hvalue) as
        [runtime_argument [Hruntime_index Hargument_value]].
      rewrite Hargument_index in Hruntime_index.
      injection Hruntime_index as <-.
      apply qualified_type_subtype_q_subtype in Hsub_i.
      unfold vpa_mutability_tt_readonly_state in Hsub_i.
      rewrite Hstatic_parameter_bot in Hsub_i. simpl in Hsub_i.
      have Hargument_not_bot :=
        wf_config_nonnull_variable_not_bot CT sGamma rGamma h argument
          argument_type root Hwf Hargument_static Hargument_value.
      destruct (sqtype receiver_type);
        destruct (sqtype argument_type) eqn:Hargument_q;
        simpl in Hsub_i;
        inversion Hsub_i;
        subst;
        try congruence.
Qed.

Lemma caller_post_rdm_root_origin :
  forall CT caller_senv caller_renv h destination destination_type
    return_location root,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (root = return_location /\ sqtype destination_type = RDM).
Proof.
  intros CT caller_senv caller_renv h destination destination_type
    return_location root Hwf Hdestination
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable. rewrite Hdestination in Htype. injection Htype as <-.
    have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
    assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
    have Hupdated := runtime_getVal_update_same caller_renv destination
      (Iot return_location) Hruntime_dom.
    rewrite Hupdated in Hvalue. injection Hvalue as <-.
    right. split; [reflexivity|exact Hrdm].
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable (Iot return_location).
    assert (Hdestination_variable : destination <> variable) by congruence.
    specialize (Hunchanged Hdestination_variable).
    rewrite Hunchanged in Hvalue.
    left. exists variable, T. repeat split; assumption.
Qed.

Lemma caller_post_rdm_root_reflects_before_pop :
  forall CT caller_senv caller_renv h destination destination_type receiver
    receiver_location receiver_type callee_senv callee_renv return_var
    body_return_type runtime_sig static_sig return_location root,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) root ->
    typed_root RDM caller_senv caller_renv root \/
    (root = return_location /\
     sqtype destination_type = RDM /\
     sqtype receiver_type = RDM /\
     (typed_root RDM callee_senv callee_renv root \/
      typed_root Mut callee_senv callee_renv root \/
      typed_root Imm callee_senv callee_renv root)).
Proof.
  intros CT caller_senv caller_renv h destination destination_type receiver
    receiver_location receiver_type callee_senv callee_renv return_var
    body_return_type runtime_sig static_sig return_location root Hcaller_wf
    Hdestination Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hrefine Hresult_sub Hroot.
  destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
    destination destination_type return_location root Hcaller_wf Hdestination
    Hroot) as [Hold | [Hroot_return Hdestination_rdm]].
  - left. exact Hold.
  - right. subst root. split; [reflexivity|].
    split; [exact Hdestination_rdm|].
    have Hreceiver_nonbottom : sqtype receiver_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT caller_senv caller_renv h
        receiver receiver_type receiver_location); eauto. }
    have Hreturn_nonbottom : sqtype body_return_type <> Bot.
    { eapply (wf_config_nonnull_variable_not_bot CT callee_senv callee_renv h
        return_var body_return_type return_location); eauto. }
    destruct (refined_call_rdm_result_classifies_body_return CT receiver_type
      body_return_type runtime_sig static_sig destination_type Hbody_sub
      Hrefine Hresult_sub Hreceiver_nonbottom Hreturn_nonbottom
      Hdestination_rdm) as [Hreceiver_rdm Hbody_cases].
    split; [exact Hreceiver_rdm|].
    destruct Hbody_cases as [Hbody_rdm | [Hbody_mut | Hbody_imm]].
    + left. exists return_var, body_return_type. repeat split; assumption.
    + right. left. exists return_var, body_return_type.
      repeat split; assumption.
    + right. right. exists return_var, body_return_type.
      repeat split; assumption.
Qed.

Definition call_pop_bridge
  (CT : class_table) (h : heap)
  (callee : watched_frame) (stack : list watched_boundary)
  (receiver_location return_location left right : Loc) : Prop :=
  (potential_connected CT h callee stack left receiver_location /\
   potential_connected CT h callee stack return_location right) \/
  (potential_connected CT h callee stack left return_location /\
   potential_connected CT h callee stack receiver_location right).

Definition call_pop_merge_safe
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (callee : watched_frame) (stack : list watched_boundary)
  (receiver_location return_location : Loc) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ call_pop_bridge CT h callee stack receiver_location return_location
      capability protected.

Lemma potential_adjacent_after_call_pop_decomposes :
  forall CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right,
    wf_r_config CT caller_senv caller_renv h ->
    destination <> 0 ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    potential_adjacent CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    potential_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      left right \/
    (sqtype destination_type = RDM /\
     call_pop_bridge CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      receiver_location return_location left right).
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hrefine Hresult_sub
    [Hheap | [Hframe | Hreturn]].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
        caller_renv h destination destination_type receiver receiver_location
        receiver_type callee_senv callee_renv return_var body_return_type
        runtime_sig static_sig return_location left Hcaller_wf Hdestination
        Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
        Hbody_sub Hrefine Hresult_sub Hleft) as
        [Hleft_old |
          [Hleft_return [Hdestination_rdm_left [Hview_left Hleft_body]]]];
      destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
        caller_renv h destination destination_type receiver receiver_location
        receiver_type callee_senv callee_renv return_var body_return_type
        runtime_sig static_sig return_location right Hcaller_wf Hdestination
        Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
        Hbody_sub Hrefine Hresult_sub Hright) as
        [Hright_old |
          [Hright_return
            [Hdestination_rdm_right [Hview_right Hright_body]]]].
      * left. eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame caller_authority caller_senv caller_renv).
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- exact Hleft_old.
        -- exact Hright_old.
      * right. split; [exact Hdestination_rdm_right|].
        left. subst right. split; [|apply rt_refl].
        eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame caller_authority caller_senv caller_renv).
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- exact Hleft_old.
        -- exists receiver, receiver_type. repeat split; assumption.
      * right. split; [exact Hdestination_rdm_left|].
        right. subst left. split; [apply rt_refl|].
        eapply live_frame_rdm_roots_potentially_connected with
          (frame := mk_watched_frame caller_authority caller_senv caller_renv).
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- exists receiver, receiver_type. repeat split; assumption.
        -- exact Hright_old.
      * left. subst left right. apply rt_refl.
    + left. apply rt_step. right. left. exists boundary.(boundary_caller).
      split.
      * apply live_frame_suspended with (boundary := boundary).
        right. exact H.
      * split; assumption.
  - destruct Hreturn as
      [return_callee [return_boundary
        [Hlive [Hview [Hcallee_return [Hruntime Hroots]]]]]].
    inversion Hlive; subst.
    + destruct Hroots as [Hroots | Hroots].
      * destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
          caller_renv h destination destination_type receiver receiver_location
          receiver_type callee_senv callee_renv return_var body_return_type
          runtime_sig static_sig return_location left Hcaller_wf Hdestination
          Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
          Hbody_sub Hrefine Hresult_sub (proj1 Hroots)) as
          [Hleft_old |
            [Hleft_return
              [Hdestination_rdm [Hreceiver_rdm Hleft_body]]]].
        -- left. apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hruntime|]. left. split;
             [exact Hleft_old|exact (proj2 Hroots)].
        -- subst left. right. split; [exact Hdestination_rdm|].
           right. split; [apply rt_refl|].
           assert (Hcaller_receiver_root :
             typed_root RDM caller_senv caller_renv receiver_location).
           { exists receiver, receiver_type. repeat split; assumption. }
           destruct (extract_receiver_from_wf_config CT caller_senv caller_renv
             h Hcaller_wf) as
             [this [runtime_q [Hthis [Hthis_dom Hthis_runtime]]]].
           have Hthis_value := get_this_var_mapping_runtime_getVal caller_renv
             this Hthis.
           have Hpost_this_value := runtime_getVal_update_diff caller_renv
             destination 0 (Iot return_location) Hdestination_not_receiver.
           rewrite Hthis_value in Hpost_this_value.
           have Hleft_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv
             (update_r_env_value caller_renv destination (Iot return_location))
             h this runtime_q return_location Hcaller_post_wf
             Hpost_this_value Hthis_runtime
             (proj1 Hroots).
           have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv caller_renv h this runtime_q receiver_location
             Hcaller_wf Hthis_value Hthis_runtime Hcaller_receiver_root.
           apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split.
           ++ rewrite Hreceiver_runtime. rewrite <- Hruntime.
              symmetry. exact Hleft_runtime.
           ++ left. split;
                [exact Hcaller_receiver_root|exact (proj2 Hroots)].
      * destruct (caller_post_rdm_root_reflects_before_pop CT caller_senv
          caller_renv h destination destination_type receiver receiver_location
          receiver_type callee_senv callee_renv return_var body_return_type
          runtime_sig static_sig return_location right Hcaller_wf Hdestination
          Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value
          Hbody_sub Hrefine Hresult_sub (proj2 Hroots)) as
          [Hright_old |
            [Hright_return
              [Hdestination_rdm [Hreceiver_rdm Hright_body]]]].
        -- left. apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split; [exact Hruntime|]. right. split;
             [exact (proj1 Hroots)|exact Hright_old].
        -- subst right. right. split; [exact Hdestination_rdm|].
           left. split; [|apply rt_refl].
           assert (Hcaller_receiver_root :
             typed_root RDM caller_senv caller_renv receiver_location).
           { exists receiver, receiver_type. repeat split; assumption. }
           destruct (extract_receiver_from_wf_config CT caller_senv caller_renv
             h Hcaller_wf) as
             [this [runtime_q [Hthis [Hthis_dom Hthis_runtime]]]].
           have Hthis_value := get_this_var_mapping_runtime_getVal caller_renv
             this Hthis.
           have Hpost_this_value := runtime_getVal_update_diff caller_renv
             destination 0 (Iot return_location) Hdestination_not_receiver.
           rewrite Hthis_value in Hpost_this_value.
           have Hright_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv
             (update_r_env_value caller_renv destination (Iot return_location))
             h this runtime_q return_location Hcaller_post_wf
             Hpost_this_value Hthis_runtime
             (proj2 Hroots).
           have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
             caller_senv caller_renv h this runtime_q receiver_location
             Hcaller_wf Hthis_value Hthis_runtime Hcaller_receiver_root.
           apply rt_step. right. right. exists
             (mk_watched_frame caller_authority caller_senv caller_renv),
             return_boundary.
           split; [constructor; constructor|]. split; [exact Hview|].
           split; [exact Hcallee_return|].
           split.
           ++ transitivity (Some runtime_q).
              ** rewrite Hruntime. exact Hright_runtime.
              ** symmetry. exact Hreceiver_runtime.
           ++ right. split;
                [exact (proj1 Hroots)|exact Hcaller_receiver_root].
    + left. apply rt_step. right. right. exists return_callee, return_boundary.
      split; [constructor; constructor; exact H|].
      split; [exact Hview|].
      split; [exact Hcallee_return|].
      split; assumption.
Qed.

Lemma potential_connected_after_call_pop_decomposes :
  forall CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right,
    wf_r_config CT caller_senv caller_renv h ->
    destination <> 0 ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    wf_r_config CT callee_senv callee_renv h ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    potential_connected CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    potential_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      left right \/
    (sqtype destination_type = RDM /\
     call_pop_bridge CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) entry_cutoff origins :: stack)
      receiver_location return_location left right).
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type Hreceiver_value
    Hcallee_wf Hreturn_type
    Hreturn_value Hbody_sub Hrefine Hresult_sub Hconnected.
  induction Hconnected.
  - eapply potential_adjacent_after_call_pop_decomposes; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as
      [Hxy |
        [Hdestination_rdm1
          [[Hx_receiver Hreturn_y] | [Hx_return Hreceiver_y]]]];
      destruct IHHconnected2 as
      [Hyz |
        [Hdestination_rdm2
          [[Hy_receiver Hreturn_z] | [Hy_return Hreceiver_z]]]].
    + left. eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm2|]. left. split.
      * eapply potential_connected_trans; eauto.
      * exact Hreturn_z.
    + right. split; [exact Hdestination_rdm2|]. right. split.
      * eapply potential_connected_trans; eauto.
      * exact Hreceiver_z.
    + right. split; [exact Hdestination_rdm1|].
      left. split; [exact Hx_receiver|].
      eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      left. split; [exact Hx_receiver|exact Hreturn_z].
    + left. eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      right. split; [exact Hx_return|].
      eapply potential_connected_trans; eauto.
    + left. eapply potential_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      right. split; [exact Hx_return|exact Hreceiver_z].
Qed.

Lemma potential_history_leave_call :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location,
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    static_getType callee_senv return_var = Some body_return_type ->
    runtime_getVal callee_renv return_var = Some (Iot return_location) ->
    qualified_type_subtype CT body_return_type (mret runtime_sig) ->
    method_signature_refinement CT runtime_sig static_sig ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type (mret static_sig))
      destination_type ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) (dom caller_h) origins :: stack)
      callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      callee_h ->
    (sqtype destination_type = RDM ->
    call_pop_merge_safe CT callee_h
      (live_capability_set CT callee_h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location)))
        stack)
      Z
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig)) (dom caller_h) origins :: stack)
      receiver_location return_location) ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver receiver_location receiver_type
    entry_senv entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location Hcaller_zone
    Hcaller_confined Hcaller_wf Hdestination_not_receiver Hdestination_type
    Hreceiver_type Hreceiver_value Hreturn_type Hreturn_value Hbody_sub
    Hrefine Hresult_sub [Hlive [Hpotential Hcutoffs]] Hcaller_post_wf
    Hmerge_safe.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_call_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type)
    return_var (sqtype destination_type) (sqtype (mret runtime_sig)) (dom caller_h) origins).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  have Hpre_frames : live_frames_wf CT callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 Hlive).
  have Hcallee_wf : wf_r_config CT callee_senv callee_renv callee_h :=
    proj1 Hpre_frames.
  have Hcaller_current_wf : wf_r_config CT caller_senv caller_renv callee_h.
  { have Hcaller_boundary_wf := Forall_inv (proj2 Hpre_frames).
    change (wf_r_config CT caller_senv caller_renv callee_h)
      in Hcaller_boundary_wf.
    exact Hcaller_boundary_wf. }
  set (Mpre := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  set (Mpost := live_capability_set CT callee_h caller_post stack).
  have Hpre_sounds : live_frames_authority_sound callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 (proj2 Hlive)).
  have Hcaller_sound :
      authority_context_sound callee_h caller_renv caller_authority.
  { exact (Forall_inv (proj2 Hpre_sounds)). }
  have Hpost_in_pre : Included Loc Mpost Mpre.
  { intros location Hlocation.
    unfold Mpost, caller_post in Hlocation.
    unfold Mpre, callee_frame, caller_boundary.
    eapply call_return_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type)
      (receiver := receiver) (receiver_location := receiver_location)
      (receiver_type := receiver_type) (entry_senv := entry_senv)
      (entry_renv := entry_renv) (origins := origins)
      (callee_senv := callee_senv) (callee_renv := callee_renv)
      (return_var := return_var) (body_return_type := body_return_type)
      (runtime_sig := runtime_sig) (static_sig := static_sig)
      (return_location := return_location); eauto. }
  assert (Hpost_separated :
    potential_colors_separated CT callee_h Mpost Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    unfold caller_post, callee_frame, caller_boundary in *.
    destruct (potential_connected_after_call_pop_decomposes CT callee_h
      caller_authority caller_senv caller_renv stack destination
      destination_type receiver receiver_location receiver_type entry_senv
      entry_renv origins callee_senv callee_renv return_var body_return_type
      runtime_sig static_sig (dom caller_h) return_location capability protected
      Hcaller_current_wf Hdestination_not_receiver Hcaller_post_wf
      Hdestination_type Hreceiver_type Hreceiver_value Hcallee_wf Hreturn_type
      Hreturn_value Hbody_sub Hrefine Hresult_sub Hconnected)
      as [Hreflected | [Hdestination_rdm Hbridge]].
    - exact (Hpotential capability protected (Hpost_in_pre _ Hcapability)
        Hprotected Hreflected).
    - exact (Hmerge_safe Hdestination_rdm capability protected Hcapability
        Hprotected Hbridge). }
  have Hcaller_components :
      component_colors_separated CT callee_h Mpost Z.
  { eapply potential_colors_imply_component_colors; eauto. }
  have Hcaller_colors :
      watched_frame_colors CT callee_h Mpost Z caller_post.
  { eapply potential_colors_imply_active_colors; eauto. }
  have Hlive_post := live_history_leave_call_given_caller_colors CT P Z cutoff
    caller_authority caller_senv caller_renv caller_h stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv callee_h return_var
    body_return_type runtime_sig static_sig return_location Hcaller_zone
    Hcaller_confined Hcaller_wf Hdestination_not_receiver Hdestination_type
    Hreceiver_type Hreceiver_value Hreturn_type Hreturn_value Hbody_sub
    Hrefine Hresult_sub Hlive Hcaller_post_wf
    (ltac:(unfold Mpost, caller_post in Hcaller_components;
      exact Hcaller_components))
    (ltac:(unfold Mpost, caller_post in Hcaller_colors;
      exact Hcaller_colors)).
  split; [exact Hlive_post|]. split.
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpost_separated capability protected).
  - exact Hcapability.
  - exact Hprotected.
  - exact Hconnected.
  - exact (Forall_inv_tail Hcutoffs).
Qed.

Lemma caller_null_rdm_roots_descend :
  forall CT caller_senv caller_renv h destination destination_type,
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    rdm_roots_descend_from CT h caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a).
Proof.
  intros CT caller_senv caller_renv h destination destination_type Hwf
    Hdestination root [variable [T [Htype [Hvalue Hrdm]]]].
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable.
    have Hdestination_dom := Hdestination.
    apply static_getType_dom in Hdestination_dom.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength Hcorr]]]]].
    assert (Hruntime_dom : destination < dom (vars caller_renv)) by lia.
    have Hupdated := runtime_getVal_update_same caller_renv destination
      Null_a Hruntime_dom.
    rewrite Hupdated in Hvalue. discriminate.
  - have Hunchanged := runtime_getVal_update_diff caller_renv destination
      variable Null_a.
    assert (Hdestination_variable : destination <> variable) by congruence.
    specialize (Hunchanged Hdestination_variable).
    rewrite Hunchanged in Hvalue.
    exists root. split.
    + exists variable, T. repeat split; assumption.
    + constructor.
Qed.

Lemma potential_adjacent_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right,
    potential_adjacent CT h caller_frame stack left right ->
    potential_adjacent CT h callee_frame
      (mk_watched_call_boundary caller_frame entry_senv entry_renv receiver_view
        return_var result_qualifier callee_return_qualifier entry_cutoff
        origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right [Hheap | [Hframe | Hreturn]].
  - left. exact Hheap.
  - right. left.
    destruct Hframe as
      [frame [Hlive [Hleft Hright]]].
    exists frame. split.
    + inversion Hlive; subst.
      * apply live_frame_suspended with
          (boundary := mk_watched_call_boundary frame entry_senv entry_renv
            receiver_view return_var result_qualifier
            callee_return_qualifier entry_cutoff origins).
        left. reflexivity.
      * apply live_frame_suspended with (boundary := boundary).
        right. exact H.
    + split; assumption.
  - right. right.
    destruct Hreturn as
      [return_callee [return_boundary
        [Hlive [Hview [Hcallee_return [Hruntime Hroots]]]]]].
    exists return_callee, return_boundary. split.
    + constructor. exact Hlive.
    + split; [exact Hview|].
      split; [exact Hcallee_return|].
      split; assumption.
Qed.

Lemma potential_connected_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right,
    potential_connected CT h caller_frame stack left right ->
    potential_connected CT h callee_frame
      (mk_watched_call_boundary caller_frame entry_senv entry_renv receiver_view
        return_var result_qualifier callee_return_qualifier entry_cutoff
        origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right Hconnected.
  eapply potential_connected_map_edges; [|exact Hconnected].
  intros edge_left edge_right Hedge. apply rt_step.
  eapply potential_adjacent_before_call_pop_included; eauto.
Qed.

Lemma potential_history_leave_call_null :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins
    callee_senv callee_renv callee_h,
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) callee_return_q
        (dom caller_h) origins :: stack)
      callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination Null_a) callee_h ->
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins
    callee_senv callee_renv callee_h Hcaller_zone Hcaller_env Hcaller_wf
    Hdestination_not_receiver Hdestination_type
    [Hlive [Hpotential Hcutoffs]]
    Hcaller_post_wf.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_call_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type)
    return_var (sqtype destination_type) callee_return_q
    (dom caller_h) origins).
  set (caller_old := mk_watched_frame caller_authority caller_senv caller_renv).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  have Hpre_frames : live_frames_wf CT callee_h callee_frame
      (caller_boundary :: stack) := proj1 (proj2 Hlive).
  have Hcaller_current_wf : wf_r_config CT caller_senv caller_renv callee_h.
  { have Hcaller_boundary_wf := Forall_inv (proj2 Hpre_frames).
    change (wf_r_config CT caller_senv caller_renv callee_h)
      in Hcaller_boundary_wf.
    exact Hcaller_boundary_wf. }
  have Hdescend := caller_null_rdm_roots_descend CT caller_senv caller_renv
    callee_h destination destination_type Hcaller_current_wf Hdestination_type.
  set (Mpre := live_capability_set CT callee_h callee_frame
    (caller_boundary :: stack)).
  assert (Hpost_separated_pre :
    potential_colors_separated CT callee_h Mpre Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    destruct (potential_connected_after_active_descent_reflects CT callee_h
      caller_authority caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a) stack capability
      protected Hcaller_current_wf Hdescend Hconnected) as
      [Hold_connected | [anchor [Hanchor_live Hanchor_path]]].
    - apply (Hpotential capability protected Hcapability Hprotected).
      unfold callee_frame, caller_boundary, caller_old.
      eapply potential_connected_before_call_pop_included; eauto.
    - have Hanchor_pre : In Loc Mpre anchor.
      { unfold Mpre, caller_post, callee_frame, caller_boundary in *.
        eapply call_return_null_live_reachability_reflects_before_pop with
          (caller_h := caller_h) (destination_type := destination_type);
          eauto. }
      apply (Hpotential anchor protected Hanchor_pre Hprotected).
      unfold callee_frame, caller_boundary, caller_old.
      eapply potential_connected_before_call_pop_included; eauto. }
  set (Mpost := live_capability_set CT callee_h caller_post stack).
  have Hpost_in_pre : Included Loc Mpost Mpre.
  { intros location Hlocation.
    unfold Mpost, caller_post in Hlocation.
    unfold Mpre, callee_frame, caller_boundary.
    eapply call_return_null_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type); eauto. }
  have Hcaller_components_pre :
      component_colors_separated CT callee_h Mpre Z.
  { eapply potential_colors_imply_component_colors; eauto. }
  have Hcaller_components :
      component_colors_separated CT callee_h Mpost Z.
  { intros capability protected Hcapability Hprotected Hconnected.
    eapply Hcaller_components_pre; eauto. }
  have Hcaller_colors_pre :
      watched_frame_colors CT callee_h Mpre Z caller_post.
  { eapply potential_colors_imply_active_colors; eauto. }
  have Hcaller_colors :
      watched_frame_colors CT callee_h Mpost Z caller_post.
  { intros capability_root zone_root Hcapability_root
      [capability [Hcapability Hcapability_connected]]
      Hzone_root Hzone_connected.
    eapply Hcaller_colors_pre with
      (capability_root := capability_root) (zone_root := zone_root); eauto.
    exists capability. split; [eapply Hpost_in_pre; eauto|].
    exact Hcapability_connected. }
  have Hlive_post := live_history_leave_call_null_given_caller_colors CT P Z
    cutoff caller_authority caller_senv caller_renv caller_h stack destination
    destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins callee_senv callee_renv callee_h Hcaller_zone
    Hcaller_env Hcaller_wf
    Hdestination_not_receiver Hdestination_type Hlive Hcaller_post_wf
    (ltac:(unfold Mpost, caller_post in Hcaller_components;
      exact Hcaller_components))
    (ltac:(unfold Mpost, caller_post in Hcaller_colors;
      exact Hcaller_colors)).
  split; [exact Hlive_post|]. split.
  intros capability protected Hcapability Hprotected Hconnected.
  apply (Hpost_separated_pre capability protected).
  - unfold Mpre, caller_post, callee_frame, caller_boundary.
    eapply call_return_null_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type); eauto.
  - exact Hprotected.
  - exact Hconnected.
  - exact (Forall_inv_tail Hcutoffs).
Qed.

Lemma safe_typed_call_target_method_safe :
  forall CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    readonly_state_method_scope (mscope (msignature runtime_mdef)).
Proof.
  intros CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef
    Hwf Htyping Hsafe Hvalue Hbase Hfind.
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst mt;
      destruct Hscope as [Has | [Hcs Hcallee]]; discriminate.
  - have Hscope_eq :
      mscope (msignature runtime_mdef) = mscope (msignature mdef).
    { eapply runtime_call_scope_eq; eauto. }
    rewrite Hscope_eq.
    eapply readonly_state_submethod; eauto.
Qed.

Lemma safe_typed_call_static_result :
  forall CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    exists destination_type receiver_type static_mdef,
      sGamma' = sGamma /\
      x <> 0 /\
      static_getType sGamma x = Some destination_type /\
      static_getType sGamma y = Some receiver_type /\
      FindMethodWithName CT (sctype receiver_type) method static_mdef /\
      method_signature_refinement CT
        (msignature runtime_mdef) (msignature static_mdef) /\
      qualified_type_subtype CT
        (vpa_mutability_tt_readonly_state receiver_type
          (mret (msignature static_mdef))) destination_type /\
      (qualified_type_subtype CT receiver_type
        (vpa_mutability_tt_readonly_state receiver_type
          (mreceiver (msignature static_mdef))) \/
       (sqtype receiver_type = RO /\
        sqtype (mreceiver (msignature static_mdef)) = RDM /\
        base_subtype CT (sctype receiver_type)
          (sctype (mreceiver (msignature static_mdef))))).
Proof.
  intros CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef
    Hwf Htyping Hsafe Hvalue Hbase Hfind.
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst mt;
      destruct Hscope as [Has | [Hcs Hcallee]]; discriminate.
  - exists Tx, Ty, mdef. repeat split; try assumption;
      try (exact Hrcv_sub).
    eapply runtime_call_signature_refines; eauto.
Qed.

Lemma safe_call_callee_owned_reflects_to_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty location,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frame_owned_location CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) location ->
    frame_owned_location CT h
      (mk_watched_frame caller_authority sGamma rGamma) location.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty location Hwf Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs [root [Hroot Hreachable]].
  exists root. split; [|exact Hreachable].
  eapply safe_call_callee_capability_root_reflects_to_caller; eauto.
Qed.

Lemma safe_call_callee_mutable_authority_root_reflects_to_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty root,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    mutable_authority_root
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) h root ->
    mutable_authority_root
      (mk_watched_frame caller_authority sGamma rGamma) h root \/
    (sqtype Ty = RO /\ root = ly /\ typed_root RO sGamma rGamma root /\
     r_muttype h root = Some Mut_r).
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty root Hwf Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs [Hmut | [Hrdm Hruntime]].
  - left. left. eapply safe_call_callee_mut_root_origin; eauto.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs Hrdm) as
      [caller_T [Hcaller_type [[Hshape Hcaller_root] |
        [Hro [Hrooteq Hro_root]]]]].
    + assert (caller_T = Ty) by congruence. subst caller_T.
      destruct Hshape as [Hcaller_mut | [Hcaller_imm | Hcaller_rdm]].
      * left. left. rewrite Hcaller_mut in Hcaller_root. exact Hcaller_root.
      * have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h root Hwf (ltac:(rewrite Hcaller_imm in Hcaller_root;
            exact Hcaller_root)).
        congruence.
      * left. right. split.
        -- rewrite Hcaller_rdm in Hcaller_root. exact Hcaller_root.
        -- exact Hruntime.
    + assert (caller_T = Ty) by congruence. subst caller_T.
      right. split; [exact Hro|]. split; [exact Hrooteq|].
      split; [exact Hro_root | exact Hruntime].
Qed.

Lemma safe_call_prospective_step_covered_by_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    prospective_location_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (FlowProspective, source) (FlowProspective, target) ->
    prospective_location_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target Hwf Hsound Hcallee_wf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hsource Hstep.
  have Hsource_runtime := prospective_location_covered_by_frame_runtime_mutable
    CT h (mk_watched_frame caller_authority sGamma rGamma) source Hwf Hsound
    Hsource.
  inversion Hstep; subst.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_retained. exact H1.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_rdm_backward. exact H1.
  - have Htarget_runtime : r_muttype h target = Some Mut_r.
    { destruct (active_rdm_roots_share_runtime_context CT
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)) h source target Hcallee_wf H1 H2) as
        [runtime_q [Hsource_context Htarget_context]].
      rewrite Hsource_runtime in Hsource_context.
      injection Hsource_context as <-. exact Htarget_context. }
    destruct (safe_call_callee_mutable_authority_root_reflects_to_caller
        CT caller_authority sGamma mt rGamma h x method y args sGamma' vals
        ly cy runtime_mdef Ty target Hwf Htyping Hscope Hgety Hvalue Hbase
        Hfind Hargs (or_intror (conj H2 Htarget_runtime))) as
      [Hcaller_root | [Hro [Htarget_eq [Hro_root Hro_runtime]]]].
    + exists target. split; [exact Hcaller_root | apply rt_refl].
    + destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
        method y args sGamma' vals ly cy runtime_mdef source Hwf Htyping
        Hscope Hvalue Hbase Hfind Hargs H1) as
        [Ts [Hgets [[Hshape_s _] | [_ [Hsource_eq _]]]]].
      * exfalso. assert (Ts = Ty) by congruence. subst Ts.
        destruct Hshape_s as [Hq | [Hq | Hq]]; congruence.
      * rewrite Hsource_eq in Hsource. rewrite Htarget_eq. exact Hsource.
Qed.

Definition prospective_state_covered_by_frame
  (CT : class_table) (h : heap) (frame : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowProspective /\
  prospective_location_covered_by_frame CT h frame (snd state).

Lemma safe_call_prospective_state_step_covered_by_caller :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    prospective_state_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    prospective_state_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty [source_mode source] [target_mode target] Hwf
    Hsound Hcallee_wf Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
    [Hsource_mode Hsource] Hstep. simpl in *. subst source_mode.
  have Htarget_mode : target_mode = FlowProspective.
  { inversion Hstep; reflexivity. }
  subst target_mode. split; [reflexivity|].
  eapply safe_call_prospective_step_covered_by_caller; eauto.
Qed.

Lemma safe_call_callee_rdm_join_is_caller_colored :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming old_mode left right,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) ->
    authority_mode_dangerous old_mode ->
    In authority_flow_state
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming)
      (old_mode, left) ->
    typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) left ->
    typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) right ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming)
        (target_mode, right).
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming old_mode left right Hwf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hruntime Hold_mode Hold_color
    Hleft Hright.
  destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x method
    y args sGamma' vals ly cy runtime_mdef left Hwf Htyping Hscope Hvalue
    Hbase Hfind Hargs Hleft) as
    [left_T [Hleft_get Hleft_cases]].
  destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
    method y args sGamma' vals ly cy runtime_mdef right Hwf Htyping Hscope
    Hvalue Hbase Hfind Hargs Hright) as
    [right_T [Hright_get Hright_cases]].
  assert (left_T = Ty) by congruence.
  assert (right_T = Ty) by congruence. subst left_T right_T.
  destruct Hleft_cases as [[Hleft_shape Hleft_root] |
      [Hleft_ro [Hleft_eq Hleft_ro_root]]];
    destruct Hright_cases as [[Hright_shape Hright_root] |
      [Hright_ro [Hright_eq Hright_ro_root]]].
  - destruct Hleft_shape as [Hview | [Hview | Hview]].
    + exists FlowPowered. split; [left; reflexivity|].
      eapply executing_authority_typed_mut_root_is_powered.
      rewrite Hview in Hright_root. exact Hright_root.
    + have Hleft_immutable := typed_imm_root_runtime_immutable CT sGamma
        rGamma h left Hwf (ltac:(rewrite Hview in Hleft_root;
          exact Hleft_root)).
      have Hleft_mutable := Hruntime old_mode left Hold_color.
      congruence.
    + exists FlowProspective. split; [right; reflexivity|].
      eapply executing_authority_dangerous_frame_join; eauto.
      * rewrite Hview in Hleft_root. exact Hleft_root.
      * rewrite Hview in Hright_root. exact Hright_root.
  - destruct Hleft_shape as [Hq | [Hq | Hq]]; congruence.
  - destruct Hright_shape as [Hq | [Hq | Hq]]; congruence.
  - exists old_mode. split; [exact Hold_mode|].
    rewrite Hright_eq. rewrite <- Hleft_eq. exact Hold_color.
Qed.

Lemma safe_call_callee_frame_step_preserves_coverage :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) source ->
    phased_authority_frame_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target Hwf Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hruntime Hcovered Hstep.
  inversion Hstep; subst; simpl in *.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists old_mode.
    split; [exact Hold_mode|].
    eapply executing_authority_dangerous_retained; eauto.
  - intros _. destruct (Hcovered (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists old_mode.
    split; [exact Hold_mode|].
    eapply executing_authority_dangerous_retained; eauto.
  - intros _. destruct (Hcovered (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists FlowProspective.
    split; [right; reflexivity|].
    eapply executing_authority_dangerous_reverse_rdm; eauto.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists FlowProspective.
    split; [right; reflexivity|].
    eapply executing_authority_dangerous_reverse_rdm; eauto.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply safe_call_callee_rdm_join_is_caller_colored; eauto.
  - intros _. destruct (Hcovered (or_intror eq_refl)) as
      [old_mode [Hold_mode Hold_color]].
    eapply safe_call_callee_rdm_join_is_caller_colored; eauto.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros Hdangerous. destruct Hdangerous as [Hbad | Hbad]; discriminate.
  - intros _. destruct (Hcovered (or_introl eq_refl)) as
      [old_mode [Hold_mode Hold_color]]. exists old_mode. split; assumption.
  - intros _. exists FlowPowered. split; [left; reflexivity|].
    apply executing_authority_owned_is_powered.
    eapply safe_call_callee_owned_reflects_to_caller; eauto.
Qed.

Lemma safe_call_callee_frame_connected_preserves_coverage :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) source ->
    phased_authority_frame_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    authority_state_covered
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming source target Hwf Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hruntime Hcovered Hconnected.
  induction Hconnected.
  - eapply safe_call_callee_frame_step_preserves_coverage; eauto.
  - exact Hcovered.
  - apply IHHconnected2. apply IHHconnected1. exact Hcovered.
Qed.

(** The internal call-pop obligation is deliberately disjunctive.  A
    dangerous color in the resumed caller must either be represented by a
    dangerous color of the completed callee phase, or its location must be
    outside the protected zone.  Requiring callee-color containment alone
    would be too strong for a fresh flexible-return component that is
    harmless but was not present in the callee's entry frame. *)
Definition executing_authority_call_pop_safe
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame)
  (callee_incoming : Ensemble authority_flow_state)
  (caller : watched_frame)
  (caller_incoming : Ensemble authority_flow_state) : Prop :=
  forall mode location,
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (mode, location) ->
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (callee_mode, location)) \/
    ~ In Loc Z location.

Lemma phased_dangerous_path_has_frozen_origin_or_owned_promotion :
  forall CT h frame source target,
    authority_mode_dangerous (fst target) ->
    phased_authority_frame_connected CT h frame source target ->
    (authority_mode_dangerous (fst source) /\
      frozen_caller_authority_connected CT h frame source target) \/
    (exists anchor,
      frame_owned_location CT h frame anchor /\
      frozen_caller_authority_connected CT h frame
        (FlowPowered, anchor) target).
Proof.
  intros CT h frame source target Htarget Hconnected.
  induction Hconnected.
  - inversion H; subst; simpl in *.
    + left. split; [left; reflexivity|].
      apply rt_step. apply frozen_caller_retained. exact H0.
    + left. split; [right; reflexivity|].
      apply rt_step. apply frozen_caller_prospective_retained. exact H0.
    + left. split; [right; reflexivity|].
      apply rt_step. apply frozen_caller_prospective_rdm_backward. exact H0.
    + left. split; [left; reflexivity|].
      apply rt_step. apply frozen_caller_reverse_rdm. exact H0.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + left. split; [left; reflexivity|].
      apply rt_step. eapply frozen_caller_powered_frame_join; eauto.
    + left. split; [right; reflexivity|].
      apply rt_step. eapply frozen_caller_prospective_frame_join; eauto.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + destruct Htarget as [Hbad | Hbad]; discriminate.
    + left. split; [left; reflexivity|].
      apply rt_step. apply frozen_caller_mark_prospective.
    + right. eexists. split; [eassumption|apply rt_refl].
  - left. split; [exact Htarget|apply rt_refl].
  - destruct (IHHconnected2 Htarget) as
      [[Hmiddle Hfrozen_tail] | [anchor [Howned Hfrozen_tail]]].
    + destruct (IHHconnected1 Hmiddle) as
        [[Hsource Hfrozen_prefix] | [anchor [Howned Hfrozen_prefix]]].
      * left. split; [exact Hsource|].
        eapply rt_trans; eauto.
      * right. exists anchor. split; [exact Howned|].
        eapply rt_trans; eauto.
    + right. exists anchor. split; assumption.
Qed.

(** Coverage used only while proving that a write preserves a boundary-local
    prospective component.  The first frame is the tracked live frame whose
    old component is being advanced; the second is the currently executing
    frame that owns or types the newly installed edge. *)
Definition prospective_location_covered_by_old_or_active
  (CT : class_table) (h : heap) (old_frame : watched_frame)
  (active : watched_frame) (location : Loc) : Prop :=
  (exists old_root,
    mutable_authority_root old_frame h old_root /\
    frozen_caller_authority_connected CT h old_frame
      (FlowProspective, old_root) (FlowProspective, location)) \/
  exists active_root,
    mutable_authority_root active h active_root /\
    frozen_caller_authority_connected CT h active
      (FlowProspective, active_root) (FlowProspective, location).

Lemma prospective_location_covered_runtime_mutable :
  forall CT h old_frame active location,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    prospective_location_covered_by_old_or_active CT h old_frame active
      location ->
    r_muttype h location = Some Mut_r.
Proof.
  intros CT h old_frame active location Hold_wf Hold_sound Hactive_wf
    Hactive_sound [[old_root [Hold_root Hold]] |
      [active_root [Hactive_root Hpath]]].
  - have Hroot_runtime := mutable_authority_root_runtime_mutable CT h
      old_frame old_root Hold_wf Hold_sound Hold_root.
    have Hphased := frozen_caller_authority_connected_is_phased CT h old_frame
      (FlowProspective, old_root) (FlowProspective, location) Hold.
    exact (phased_authority_frame_connected_preserves_runtime_mutability CT h
      old_frame (FlowProspective, old_root) (FlowProspective, location) Mut_r
      Hold_wf Hphased Hroot_runtime).
  - have Hactive_runtime := mutable_authority_root_runtime_mutable CT h active
      active_root Hactive_wf Hactive_sound Hactive_root.
    have Hphased := frozen_caller_authority_connected_is_phased CT h active
      (FlowProspective, active_root) (FlowProspective, location) Hpath.
    exact (phased_authority_frame_connected_preserves_runtime_mutability CT h
      active (FlowProspective, active_root) (FlowProspective, location) Mut_r
      Hactive_wf Hphased Hactive_runtime).
Qed.

Lemma active_owned_has_prospective_root :
  forall CT h active location,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    frame_owned_location CT h active location ->
    exists root,
      mutable_authority_root active h root /\
      frozen_caller_authority_connected CT h active
        (FlowProspective, root) (FlowProspective, location).
Proof.
  intros CT h active location Hwf Hsound [root [Hroot Hreachable]].
  exists root. split.
  - have Hruntime := frame_capability_root_runtime_mutable CT h active root
      Hwf Hsound Hroot.
    destruct Hroot as
      [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
    + left. exists variable, T. repeat split; assumption.
    + right. split.
      * exists variable, T. repeat split; assumption.
      * exact Hruntime.
  - eapply frozen_caller_prospective_retained_forward. exact Hreachable.
Qed.

Lemma frozen_prospective_step_after_safe_field_update_covered :
  forall CT h old_frame active lx old field written source target,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    prospective_location_covered_by_old_or_active CT h old_frame active
      source ->
    frozen_caller_authority_step CT
      (update_field h lx field (Iot written)) old_frame
      (FlowProspective, source) (FlowProspective, target) ->
    prospective_location_covered_by_old_or_active CT h old_frame active
      target.
Proof.
  intros CT h old_frame active lx old field written source target Hold_wf
    Hold_sound Hactive_wf Hactive_sound Hobj Hendpoints Hsource Hstep.
  have Hsource_runtime := prospective_location_covered_runtime_mutable CT h
    old_frame active source Hold_wf Hold_sound Hactive_wf Hactive_sound
    Hsource.
  inversion Hstep; subst.
  - destruct (retained_edge_after_field_update CT h lx old field
      (Iot written) source target Hobj H1) as
      [Hold_edge | [Heq_left [Heq_value Hnew_edge]]].
    + destruct Hsource as
        [[old_component_root [Hold_root Hold_path]] |
         [active_root [Hactive_root Hpath]]].
      * left. exists old_component_root. split; [exact Hold_root|].
        eapply rt_trans; [exact Hold_path|].
        apply rt_step. apply frozen_caller_prospective_retained.
        exact Hold_edge.
      * right. exists active_root. split; [exact Hactive_root|].
        eapply rt_trans; [exact Hpath|].
        apply rt_step. apply frozen_caller_prospective_retained.
        exact Hold_edge.
    + injection Heq_value as Heq_right. subst source target.
      inversion Hendpoints; subst.
      * right. eapply active_owned_has_prospective_root; eauto.
      * rewrite H in Hsource_runtime. discriminate.
      * right. exists written. split.
        -- right. split; [exact H0|].
           destruct (active_rdm_roots_share_runtime_context CT
             active.(frame_senv) active.(frame_renv) h lx written Hactive_wf
             H H0) as [runtime_q [Hleft_runtime Hright_runtime]].
           rewrite Hsource_runtime in Hleft_runtime.
           injection Hleft_runtime as <-. exact Hright_runtime.
        -- apply rt_refl.
  - destruct (mutable_edge_after_field_update CT h lx old field
      (Iot written) target source Hobj H1) as
      [Hold_edge | [Heq_right [Heq_value Hnew_edge]]].
    + destruct Hsource as
        [[old_component_root [Hold_root Hold_path]] |
         [active_root [Hactive_root Hpath]]].
      * left. exists old_component_root. split; [exact Hold_root|].
        eapply rt_trans; [exact Hold_path|].
        apply rt_step. apply frozen_caller_prospective_rdm_backward.
        exact Hold_edge.
      * right. exists active_root. split; [exact Hactive_root|].
        eapply rt_trans; [exact Hpath|].
        apply rt_step. apply frozen_caller_prospective_rdm_backward.
        exact Hold_edge.
    + injection Heq_value as Heq_left. subst source target.
      inversion Hendpoints; subst.
      * right. eapply active_owned_has_prospective_root; eauto.
      * rewrite H0 in Hsource_runtime. discriminate.
      * right. exists lx. split.
        -- right. split; [exact H|].
           destruct (active_rdm_roots_share_runtime_context CT
             active.(frame_senv) active.(frame_renv) h lx written Hactive_wf
             H H0) as [runtime_q [Hleft_runtime Hright_runtime]].
           rewrite Hsource_runtime in Hright_runtime.
           injection Hright_runtime as <-. exact Hleft_runtime.
        -- apply rt_refl.
  - have Htarget_runtime : r_muttype h target = Some Mut_r.
    { destruct (active_rdm_roots_share_runtime_context CT
        old_frame.(frame_senv) old_frame.(frame_renv) h source target Hold_wf
        H1 H2) as [runtime_q [Hleft_runtime Hright_runtime]].
      rewrite Hsource_runtime in Hleft_runtime.
      injection Hleft_runtime as <-. exact Hright_runtime. }
    left. exists target. split.
    + right. split; [exact H2|exact Htarget_runtime].
    + apply rt_refl.
Qed.

Definition prospective_state_covered_by_old_or_active
  (CT : class_table) (h : heap) (old_frame active : watched_frame)
  (state : authority_flow_state) : Prop :=
  fst state = FlowProspective /\
  prospective_location_covered_by_old_or_active CT h old_frame active
    (snd state).

Lemma frozen_state_step_after_safe_field_update_covered :
  forall CT h old_frame active lx old field written source target,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    prospective_state_covered_by_old_or_active CT h old_frame active source ->
    frozen_caller_authority_step CT
      (update_field h lx field (Iot written)) old_frame source target ->
    prospective_state_covered_by_old_or_active CT h old_frame active target.
Proof.
  intros CT h old_frame active lx old field written
    [source_mode source] [target_mode target] Hold_wf Hold_sound Hactive_wf
    Hactive_sound Hobj Hendpoints [Hsource_mode Hsource] Hstep. simpl in *.
  subst source_mode.
  have Htarget_mode : target_mode = FlowProspective.
  { inversion Hstep; reflexivity. }
  subst target_mode. split; [reflexivity|].
  eapply frozen_prospective_step_after_safe_field_update_covered; eauto.
Qed.

Lemma frozen_state_connected_after_safe_field_update_covered :
  forall CT h old_frame active lx old field written source target,
    wf_r_config CT old_frame.(frame_senv) old_frame.(frame_renv) h ->
    authority_context_sound h old_frame.(frame_renv)
      old_frame.(frame_authority) ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    prospective_state_covered_by_old_or_active CT h old_frame active source ->
    frozen_caller_authority_connected CT
      (update_field h lx field (Iot written)) old_frame source target ->
    prospective_state_covered_by_old_or_active CT h old_frame active target.
Proof.
  intros CT h old_frame active lx old field written source target Hold_wf
    Hold_sound Hactive_wf Hactive_sound Hobj Hendpoints Hsource Hconnected.
  induction Hconnected.
  - eapply frozen_state_step_after_safe_field_update_covered; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma live_prospective_mutable_authority_components_after_safe_field_update :
  forall CT cutoff active stack h lx old field written,
    live_frames_wf CT h active stack ->
    live_frames_authority_sound h active stack ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active stack ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    live_prospective_mutable_authority_components_after_cutoff CT
      (update_field h lx field (Iot written)) cutoff active stack.
Proof.
  intros CT cutoff active stack h lx old field written Hframes Hsounds Hold
    Hobj Hendpoints frame root target Hlive [Hroot Hpath].
  have Hframe_wf := live_frame_member_wf CT h active stack frame Hframes Hlive.
  have Hframe_sound := live_frame_member_authority_sound h active stack frame
    Hsounds Hlive.
  have Hactive_wf := live_frame_member_wf CT h active stack active Hframes
    (live_frame_active active stack).
  have Hactive_sound := live_frame_member_authority_sound h active stack
    active Hsounds (live_frame_active active stack).
  have Hroot_old : mutable_authority_root frame h root.
  { destruct Hroot as [Hmut | [Hrdm Hruntime]].
    - left. exact Hmut.
    - right. split; [exact Hrdm|].
      rewrite r_muttype_update_field_preserve in Hruntime. exact Hruntime. }
  have Hsource : prospective_state_covered_by_old_or_active CT h frame active
      (FlowProspective, root).
  { split; [reflexivity|]. left. exists root. split.
    - exact Hroot_old.
    - apply rt_refl. }
  have Htarget := frozen_state_connected_after_safe_field_update_covered CT h
    frame active lx old field written (FlowProspective, root)
    (FlowProspective, target) Hframe_wf Hframe_sound Hactive_wf Hactive_sound
    Hobj Hendpoints Hsource Hpath.
  destruct Htarget as [_
    [[old_root [Hold_root Hold_path]] |
     [active_root [Hactive_root Hactive_path]]]].
  - eapply Hold with (frame := frame) (root := old_root).
    + exact Hlive.
    + split; assumption.
  - eapply Hold with (frame := active) (root := active_root).
    + constructor.
    + split; assumption.
Qed.

(** Private evidence that a color observed while the callee executes really
    originates in authority of the suspended caller.  In particular, mere
    membership in the callee's executing colors is not enough: independently
    owned callee authority is demoted at return. *)
Definition resumed_caller_frozen_origin
  (CT : class_table) (h : heap) (caller : watched_frame)
  (caller_incoming : Ensemble authority_flow_state)
  (state : authority_flow_state) : Prop :=
  frozen_authority_origin CT h caller caller_incoming state.

Lemma resumed_caller_owned_has_frozen_origin :
  forall CT h caller caller_incoming anchor,
    frame_owned_location CT h caller anchor ->
    resumed_caller_frozen_origin CT h caller caller_incoming
      (FlowPowered, anchor).
Proof.
  intros CT h caller caller_incoming anchor Howned.
  exists (FlowPowered, anchor). split.
  - right. exists anchor. split; [reflexivity|exact Howned].
  - apply rt_refl.
Qed.

Lemma resumed_caller_frozen_origin_connected :
  forall CT h caller caller_incoming source target,
    resumed_caller_frozen_origin CT h caller caller_incoming source ->
    frozen_caller_authority_connected CT h caller source target ->
    resumed_caller_frozen_origin CT h caller caller_incoming target.
Proof.
  intros CT h caller caller_incoming source target
    [seed [Hseed Hprefix]] Hsuffix.
  exists seed. split; [exact Hseed|].
  eapply rt_trans; eauto.
Qed.

(** Classification maintained while a resumed caller follows only dangerous
    frozen flow.  The callee-color case carries the private caller-origin
    evidence above.  The final case remembers a whole resume-exposure set
    plus its already-derived protected-zone certificate. *)
Definition tracked_resume_frozen_color_class
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (callee_incoming : Ensemble authority_flow_state)
  (caller : watched_frame) (caller_incoming : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state snapshot.(frozen_snapshot_current_colors) state \/
  (In authority_flow_state
     (executing_authority_color_set CT h callee callee_incoming) state /\
   resumed_caller_frozen_origin CT h caller caller_incoming state) \/
  (In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure) state /\
   forall mode location,
     authority_mode_dangerous mode ->
     In authority_flow_state
       snapshot.(frozen_snapshot_current_resume_exposure) (mode, location) ->
     ~ In Loc Z location).

Inductive frozen_caller_authority_nonjoin_step
  (CT : class_table) (h : heap) :
  authority_flow_state -> authority_flow_state -> Prop :=
| frozen_nonjoin_retained : forall left right,
    retained_mut_edge CT h left right ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowPowered, left) (FlowPowered, right)
| frozen_nonjoin_prospective_retained : forall left right,
    retained_mut_edge CT h left right ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowProspective, left) (FlowProspective, right)
| frozen_nonjoin_prospective_rdm_backward : forall left right,
    mutable_edge CT h right left ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowProspective, left) (FlowProspective, right)
| frozen_nonjoin_reverse_rdm : forall left right,
    mutable_edge CT h right left ->
    frozen_caller_authority_nonjoin_step CT h
      (FlowPowered, left) (FlowProspective, right)
| frozen_nonjoin_mark_prospective : forall location,
    frozen_caller_authority_nonjoin_step CT h
      (FlowPowered, location) (FlowProspective, location).

Lemma frozen_nonjoin_step_in_frame :
  forall CT h frame source target,
    frozen_caller_authority_nonjoin_step CT h source target ->
    frozen_caller_authority_step CT h frame source target.
Proof.
  intros CT h frame source target Hstep. inversion Hstep; subst.
  - apply frozen_caller_retained. exact H.
  - apply frozen_caller_prospective_retained. exact H.
  - apply frozen_caller_prospective_rdm_backward. exact H.
  - apply frozen_caller_reverse_rdm. exact H.
  - apply frozen_caller_mark_prospective.
Qed.

(** Lossless proof-local provenance for resumed-caller flow.  Unlike the
    extensional class above, this object remembers the strictly smaller
    derivation that crossed each caller-frame RDM join.  The return proof can
    therefore peel a return-root source back to the join that introduced it,
    rather than postulating a global pop-compatibility premise. *)
Inductive tracked_resume_frozen_color_derivation
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (callee_incoming : Ensemble authority_flow_state)
  (caller : watched_frame) (caller_incoming : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot) :
  authority_flow_state -> Prop :=
| tracked_resume_from_snapshot : forall state,
    In authority_flow_state snapshot.(frozen_snapshot_current_colors) state ->
    In authority_flow_state caller_incoming state ->
    resumed_caller_frozen_origin CT h caller caller_incoming state ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot state
| tracked_resume_from_caller_owned : forall anchor,
    frame_owned_location CT h caller anchor ->
    In authority_flow_state
      (executing_authority_color_set CT h callee callee_incoming)
      (FlowPowered, anchor) ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot (FlowPowered, anchor)
| tracked_resume_by_nonjoin : forall source target,
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot target
| tracked_resume_by_frame_join : forall mode left right,
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot (FlowProspective, right).

Lemma tracked_resume_frozen_step_derives :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    source target,
    authority_mode_dangerous (fst source) ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot source ->
    frozen_caller_authority_step CT h caller source target ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot target.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    source target Hmode Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_retained. exact H.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_retained. exact H.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_rdm_backward. exact H.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_reverse_rdm. exact H.
  - eapply tracked_resume_by_frame_join; eauto.
  - eapply tracked_resume_by_frame_join; eauto.
  - eapply tracked_resume_by_nonjoin; eauto.
    apply frozen_nonjoin_mark_prospective.
Qed.

Lemma executing_dangerous_covered_by_frozen_or_independent :
  forall CT h frame incoming colors mode location,
    Included authority_flow_state
      (frozen_caller_authority_closure CT h frame colors) colors ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      In authority_flow_state colors (incoming_mode, incoming_location)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h frame incoming) (mode, location) ->
    (exists frozen_mode,
      authority_mode_dangerous frozen_mode /\
      In authority_flow_state colors (frozen_mode, location)) \/
    (exists active_mode,
      authority_mode_dangerous active_mode /\
      In authority_flow_state
        (independent_active_authority_colors CT h frame)
        (active_mode, location)).
Proof.
  intros CT h frame incoming colors mode location Hclosed Hincoming Hmode
    [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    frame seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Howned Hfrozen]]].
  - inversion Hseed; subst.
    + left. exists mode. split; [exact Hmode|].
      apply Hclosed. exists seed. split.
      * destruct seed as [seed_mode seed_location].
        eapply Hincoming; eauto.
      * exact Hfrozen.
    + right. exists mode. split; [exact Hmode|].
      exists seed. split.
      * right. exact H.
      * eapply frozen_caller_authority_connected_is_phased. exact Hfrozen.
  - right. exists mode. split; [exact Hmode|].
    exists (FlowPowered, anchor). split.
    + right. exists anchor. split; [reflexivity|exact Howned].
    + eapply frozen_caller_authority_connected_is_phased. exact Hfrozen.
Qed.

(** Well-founded classifier for the top snapshot when it is used as the
    summary of older frozen slots.  Its base constructor is frozen
    membership, not immediate-caller provenance.  The only exceptional case
    is leaving a fresh return root: a snapshot base is discharged by the
    root-scoped overlap certificate, while a join-derived base is rerouted to
    its strictly smaller predecessor. *)
(** An older resume-exposure whose captured root already has caller-entry
    provenance is not a new pop obligation.  Nested coverage maps the whole
    exposure derivation into the tracked head, whose well-founded classifier
    then supplies the ordinary pop class.  All arguments are components of
    the private frozen state or consequences of the return typing derivation;
    in particular, this lemma introduces no public preservation premise. *)
(** Stronger, reusable form of
    [advance_nested_frozen_tail_after_return_avoids_protected].  The latter
    is the safety projection needed by the phased state, whereas the private
    statement induction also needs the provenance of every newly closed
    older-slot color.  The provenance is deliberately expressed by
    [nested_frozen_pop_color_class]: no compatibility test is performed at
    dispatch, and no hypothesis is added to the public preservation theorem.

    Keeping the corresponding old snapshot in the conclusion is useful for
    metadata-preserving obligations at an enclosing return. *)
Definition pop_resume_exposure_state_class
  (CT : class_table) (h : heap) (caller : watched_frame)
  (old_exposure : Ensemble authority_flow_state)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state old_exposure state \/
  (fst state = FlowProspective /\
   prospective_location_covered_by_frame CT h caller (snd state)).

Lemma prospective_location_covered_after_prospective_frame_step :
  forall CT h frame source target,
    wf_r_config CT frame.(frame_senv) frame.(frame_renv) h ->
    authority_context_sound h frame.(frame_renv) frame.(frame_authority) ->
    prospective_location_covered_by_frame CT h frame source ->
    frozen_caller_authority_step CT h frame
      (FlowProspective, source) (FlowProspective, target) ->
    prospective_location_covered_by_frame CT h frame target.
Proof.
  intros CT h frame source target Hwf Hsound Hsource Hstep.
  have Hsource_runtime := prospective_location_covered_by_frame_runtime_mutable
    CT h frame source Hwf Hsound Hsource.
  have Htarget_runtime := phased_authority_frame_step_preserves_runtime_mutability
    CT h frame (FlowProspective, source) (FlowProspective, target) Mut_r Hwf
    (frozen_caller_authority_step_is_phased CT h frame
      (FlowProspective, source) (FlowProspective, target) Hstep)
    Hsource_runtime.
  inversion Hstep; subst.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_retained. exact H1.
  - destruct Hsource as [root [Hroot Hpath]]. exists root. split;
      [exact Hroot|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    apply frozen_caller_prospective_rdm_backward. exact H1.
  - exists target. split.
    + right. split; [exact H2|exact Htarget_runtime].
    + apply rt_refl.
Qed.

Lemma pop_resume_exposure_state_class_step :
  forall CT h active caller old_exposure source target,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    authority_colors_runtime_mutable h old_exposure ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active old_exposure)
      old_exposure ->
    pop_resume_exposure_state_class CT h caller old_exposure source ->
    frozen_caller_authority_step CT h caller source target ->
    pop_resume_exposure_state_class CT h caller old_exposure target.
Proof.
  intros CT h active caller old_exposure [source_mode source]
    [target_mode target] Hcaller_wf Hcaller_sound Hruntime Hclosed Hclass
    Hstep. simpl in *.
  destruct Hclass as [Hold | [Hsource_mode Hcovered]].
  - inversion Hstep; subst.
    + left. eapply Hclosed. exists (FlowPowered, source). split;
        [exact Hold|]. apply rt_step. apply frozen_caller_retained. assumption.
    + left. eapply Hclosed. exists (FlowProspective, source). split;
        [exact Hold|]. apply rt_step.
      apply frozen_caller_prospective_retained. assumption.
    + left. eapply Hclosed. exists (FlowProspective, source). split;
        [exact Hold|]. apply rt_step.
      apply frozen_caller_prospective_rdm_backward. assumption.
    + left. eapply Hclosed. exists (FlowPowered, source). split;
        [exact Hold|]. apply rt_step.
      apply frozen_caller_reverse_rdm. assumption.
    + right. split; [reflexivity|].
      have Hsource_runtime := Hruntime FlowPowered source Hold.
      destruct (active_rdm_roots_share_runtime_context CT
        caller.(frame_senv) caller.(frame_renv) h source target Hcaller_wf
        (ltac:(eassumption)) (ltac:(eassumption))) as
        [runtime_q [Hsource_context Htarget_context]].
      rewrite Hsource_runtime in Hsource_context. injection Hsource_context as <-.
      exists target. split.
      * right. split; [eassumption|exact Htarget_context].
      * apply rt_refl.
    + right. split; [reflexivity|].
      have Hsource_runtime := Hruntime FlowProspective source Hold.
      destruct (active_rdm_roots_share_runtime_context CT
        caller.(frame_senv) caller.(frame_renv) h source target Hcaller_wf
        (ltac:(eassumption)) (ltac:(eassumption))) as
        [runtime_q [Hsource_context Htarget_context]].
      rewrite Hsource_runtime in Hsource_context. injection Hsource_context as <-.
      exists target. split.
      * right. split; [eassumption|exact Htarget_context].
      * apply rt_refl.
    + left. eapply Hclosed. exists (FlowPowered, target). split;
        [exact Hold|]. apply rt_step. apply frozen_caller_mark_prospective.
  - change (source_mode = FlowProspective) in Hsource_mode.
    subst source_mode.
    have Htarget_mode : target_mode = FlowProspective.
    { inversion Hstep; reflexivity. }
    subst target_mode. right. split; [reflexivity|].
    eapply prospective_location_covered_after_prospective_frame_step; eauto.
Qed.

Lemma pop_resume_exposure_state_class_connected :
  forall CT h active caller old_exposure source target,
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    authority_colors_runtime_mutable h old_exposure ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active old_exposure)
      old_exposure ->
    pop_resume_exposure_state_class CT h caller old_exposure source ->
    frozen_caller_authority_connected CT h caller source target ->
    pop_resume_exposure_state_class CT h caller old_exposure target.
Proof.
  intros CT h active caller old_exposure source target Hcaller_wf
    Hcaller_sound Hruntime Hclosed Hsource Hconnected.
  induction Hconnected.
  - eapply pop_resume_exposure_state_class_step; eauto.
  - exact Hsource.
  - apply IHHconnected2.
    apply IHHconnected1. exact Hsource.
Qed.

Lemma frozen_snapshot_live_partition_before_boundary :
  forall snapshots stack snapshot boundary above below,
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    frozen_snapshot_live_partition snapshots stack snapshot boundary above
      below ->
    frozen_snapshot_slot_before_boundary (Some snapshot) boundary.
Proof.
  intros snapshots stack snapshot boundary above below Hbefore Hpartition.
  induction Hpartition.
  - inversion Hbefore; subst. exact H2.
  - inversion Hbefore; subst. apply IHHpartition. exact H4.
Qed.

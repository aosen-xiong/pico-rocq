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

Lemma private_statement_preservation_result_refl :
  forall CT P Z cutoff authority sGamma rGamma stack incoming snapshots h,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    private_statement_preservation_result CT P Z cutoff authority sGamma
      rGamma stack incoming snapshots snapshots h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack incoming snapshots h
    Hmain Hprivate.
  unfold private_statement_preservation_result. split.
  - exact (proj1 (proj1 (proj1 Hprivate))).
  - split; [exact Hprivate|].
    split.
    + clear Hprivate.
      induction snapshots as [|slot tail IH].
      * constructor.
      * constructor.
        -- destruct slot; simpl.
           ++ unfold frozen_caller_snapshot_metadata_eq. repeat split;
                intros state Hstate; exact Hstate.
           ++ exact I.
        -- exact IH.
    + apply frozen_snapshot_list_resume_exposure_protected_reflected_refl.
Qed.

(** Public-to-private bridge used exactly once, at the wrapper boundary.
    Existing operational boundaries receive [None], so the strengthened
    induction starts without assuming any history for frames that predate the
    public theorem invocation. *)
Lemma potential_live_history_starts_private_statement_result :
  forall CT P Z cutoff authority sGamma rGamma stack h,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    private_statement_preservation_result CT P Z cutoff authority sGamma
      rGamma stack (Empty_set authority_flow_state)
      (repeat None (length stack)) (repeat None (length stack)) h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack h Hpotential.
  eapply private_statement_preservation_result_refl.
  - eapply potential_live_history_starts_principled_phased_authority.
    exact Hpotential.
  - apply potential_live_history_starts_private_fresh_frozen_statement.
    exact Hpotential.
Qed.

(** Atomic cases of the strengthened induction.  These lemmas deliberately
    preserve both layers in lockstep rather than deriving either layer from
    the other.  In particular, no private certificate is smuggled into the
    public history premise. *)
Lemma private_statement_preservation_after_assignment :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x expression old value,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    private_statement_preservation_result CT P Z cutoff authority sGamma
      (update_r_env_value rGamma x value) stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)) snapshots) h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x expression old value Hpotential Hprivate Htyping Hscope Hvalue Heval.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hdescend := rdm_roots_descend_after_assignment CT sGamma mt rGamma h
    x expression old value Hwf Htyping Hscope Hvalue Heval.
  unfold private_statement_preservation_result. split.
  - eapply principled_phased_authority_history_after_assignment; eauto.
  - split.
    + eapply private_fresh_frozen_statement_after_assignment; eauto.
    + split.
      * apply advance_frozen_caller_snapshots_metadata_eq.
      * eapply frozen_snapshot_list_resume_exposure_reflected_after_active_descent;
          eauto.
Qed.

Lemma private_statement_preservation_after_local :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    T x sGamma',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    private_statement_preservation_result CT P Z cutoff authority sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])) stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [Null_a]))) snapshots) h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    T x sGamma' Hpotential Hprivate Htyping Hnone.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hdescend := rdm_roots_descend_after_local CT sGamma mt rGamma h
    T x sGamma' Hwf Htyping Hnone.
  unfold private_statement_preservation_result. split.
  - eapply principled_phased_authority_history_after_local; eauto.
  - split.
    + eapply private_fresh_frozen_statement_after_local; eauto.
    + split.
      * apply advance_frozen_caller_snapshots_metadata_eq.
      * eapply frozen_snapshot_list_resume_exposure_reflected_after_active_descent;
          eauto.
Qed.

Lemma private_statement_preservation_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x qc C args sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    private_statement_preservation_result CT P Z cutoff authority sGamma'
      rGamma' stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x qc C args sGamma' rGamma' h' Hpotential Hprivate Htyping Heval.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hprivate_post := private_fresh_frozen_statement_after_new CT P Z
    cutoff authority sGamma mt rGamma h stack incoming snapshots x qc C args
    sGamma' rGamma' h' Hprivate Htyping Heval.
  have Hpost_main := proj1 (proj1 (proj1 Hprivate_post)).
  have Hpost_wf : wf_r_config CT sGamma' rGamma' h' :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hpost_main))))).
  have Hpost_sound : authority_context_sound h' rGamma' authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpost_main)))))).
  have Hcutoff_bound : cutoff <= dom h :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hzone : protected_zone_before_cutoff Z cutoff :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (proj2 Hmain))))))).
  have Hactive_safe : forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location.
  { intros active_mode location Hmode Hcolor Hprotected.
    eapply (proj1 (proj2 (proj2 (proj2 Hmain))));
      [exact Hmode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  inversion Heval; subst.
  assert (Hupdate :
      set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Hpost_main, Hprivate_post, Hpost_wf, Hpost_sound |- *.
  set (new_runtime := vpa_mutability_object_creation qthisr qc) in *.
  unfold private_statement_preservation_result. split.
  - exact Hpost_main.
  - split.
    + exact Hprivate_post.
    + split.
      * apply advance_frozen_caller_snapshots_metadata_eq.
      * eapply frozen_snapshot_list_resume_exposure_reflected_after_new
          with (qreceiver := qthisr) (qruntime := new_runtime); eauto.
Qed.

(** Sequential composition for the strengthened induction.  Only snapshot
    metadata is composed from the first result; the public and private final
    states are exactly those established by the second evaluation. *)
Lemma private_statement_preservation_result_trans :
  forall CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots middle_h final_h,
    private_statement_preservation_result CT P Z cutoff authority middle_senv
      middle_renv stack incoming initial_snapshots middle_snapshots middle_h ->
    private_statement_preservation_result CT P Z cutoff authority final_senv
      final_renv stack incoming middle_snapshots final_snapshots final_h ->
    private_statement_preservation_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots final_h.
Proof.
  intros CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots middle_h final_h
    [_ [_ [Hfirst_metadata Hfirst_reflection]]]
    [Hpotential [Hprivate [Hsecond_metadata Hsecond_reflection]]].
  unfold private_statement_preservation_result. split; [exact Hpotential|].
  split; [exact Hprivate|].
  split.
  - eapply frozen_caller_snapshot_list_metadata_eq_trans; eauto.
  - eapply frozen_snapshot_list_resume_exposure_protected_reflected_trans;
      eauto.
Qed.

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

Lemma live_prospective_mutable_authority_components_after_return_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination (Iot return_location))
      caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    prospective_location_covered_by_frame CT h active return_location ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active (boundary :: stack) ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location Hcaller
    Hdestination_nonzero Hcaller_wf Hpost_wf Hpost_sound Hdestination Hreturn
    Hold frame root target Hlive [Hroot Hpath].
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hlive; subst.
  - have Hroot_runtime := mutable_authority_root_runtime_mutable CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      root Hpost_wf Hpost_sound Hroot.
    have Hroot_covered := caller_post_mutable_authority_root_covered
      CT caller_authority caller_senv caller_renv destination destination_type
      return_location h active root Hdestination_nonzero Hdestination Hlength
      Hroot_runtime Hreturn Hroot.
    have Hsource : return_pop_prospective_state_covered CT h
        (mk_watched_frame caller_authority caller_senv caller_renv) active
        (FlowProspective, root).
    { split; [reflexivity|]. split; [exact Hroot_runtime|exact Hroot_covered]. }
    have Htarget := return_pop_prospective_state_connected_covered CT h
      (mk_watched_frame caller_authority caller_senv caller_renv) active
      caller_authority caller_senv caller_renv destination destination_type
      return_location (FlowProspective, root) (FlowProspective, target)
      eq_refl Hdestination_nonzero Hdestination Hlength Hpost_wf Hreturn
      Hsource Hpath.
    destruct Htarget as [_ [_
      [[caller_root [Hcaller_root Hcaller_path]] |
       [callee_root [Hcallee_root Hcallee_path]]]]].
    + eapply Hold with (frame := boundary.(boundary_caller))
        (root := caller_root).
      * constructor. simpl. left. reflexivity.
      * rewrite Hcaller. split; assumption.
    + eapply Hold with (frame := active) (root := callee_root).
      * constructor.
      * split; assumption.
  - eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + split; assumption.
Qed.

Lemma live_mutable_authority_components_after_return_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    live_mutable_authority_components_after_cutoff CT h cutoff active
      (boundary :: stack) ->
    (forall target,
      retained_mut_reachable CT h return_location target ->
      cutoff <= target) ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location Hcaller
    Hdestination_nonzero Hcaller_wf Hdestination Hlive Hreturn frame root
    target Hframe Hreachable.
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hframe; subst.
  - inversion Hreachable; subst.
    + destruct (caller_post_capability_root_origin_private caller_authority
        caller_senv caller_renv destination destination_type return_location
        root Hdestination_nonzero Hdestination Hlength H) as
        [Hold_root | Hreturn_root].
      * eapply Hlive with (frame := boundary.(boundary_caller)) (root := root).
        -- constructor. simpl. left. reflexivity.
        -- apply mutable_authority_reachable_capability.
           ++ rewrite Hcaller. exact Hold_root.
           ++ exact H0.
           ++ exact H1.
      * subst root. eapply Hreturn. exact H1.
    + destruct (caller_post_rdm_root_origin_private caller_senv caller_renv
        destination destination_type return_location root
        Hdestination_nonzero Hdestination Hlength H) as
        [Hold_root | [Hreturn_root Hdestination_rdm]].
      * eapply Hlive with (frame := boundary.(boundary_caller)) (root := root).
        -- constructor. simpl. left. reflexivity.
        -- apply mutable_authority_reachable_rdm.
           ++ rewrite Hcaller. exact Hold_root.
           ++ exact H0.
           ++ exact H1.
      * subst root. eapply Hreturn. exact H1.
  - eapply Hlive with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma frozen_callee_side_components_after_return_pop :
  forall CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    frame_owned_location CT h active return_location ->
    r_muttype h return_location = Some Mut_r ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (head_slot :: snapshots) (boundary :: stack) ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location)))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) stack.
Proof.
  intros CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location
    Hcaller Hdestination_nonzero Hactive_wf Hcaller_wf Hdestination
    Hreturn_owned Hreturn_runtime Hold snapshot tracked_boundary above below
    Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head_slot :: snapshots) (boundary :: stack) old_snapshot
      tracked_boundary (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hreturn_component : forall target,
      retained_mut_reachable CT h return_location target ->
      tracked_boundary.(boundary_entry_cutoff) <= target.
  { intros target Hreturn_target.
    destruct Hreturn_owned as [owner [Howner Howner_return]].
    have Howner_runtime : r_muttype h owner = Some Mut_r.
    { eapply retained_reachable_reflects_runtime_context_private;
        [exact (proj1 (proj2 Hactive_wf))|exact Howner_return|].
      exact Hreturn_runtime. }
    eapply Hinput_components with (frame := active) (root := owner).
    - constructor.
    - apply mutable_authority_reachable_capability.
      + exact Howner.
      + exact Howner_runtime.
      + eapply retained_mut_reachable_transitive; eauto. }
  unfold caller_post.
  eapply live_mutable_authority_components_after_return_pop; eauto.
Qed.

(** The prospective analogue of the return/pop transport.  The returned
    location is covered by the completed callee component because frame
    ownership supplies a capability root and a retained path to the result.
    All other post-return prospective paths are classified by
    [live_prospective_mutable_authority_components_after_return_pop]. *)
Lemma frozen_callee_side_prospective_components_after_return_pop :
  forall CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination (Iot return_location))
      caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    frame_owned_location CT h active return_location ->
    r_muttype h return_location = Some Mut_r ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (head_slot :: snapshots) (boundary :: stack) ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) stack.
Proof.
  intros CT h active boundary stack head_slot snapshots caller_authority
    caller_senv caller_renv destination destination_type return_location
    Hcaller Hdestination_nonzero Hactive_wf Hactive_sound Hcaller_wf
    Hcaller_post_wf Hcaller_post_sound Hdestination Hreturn_owned
    Hreturn_runtime Hold snapshot tracked_boundary above below Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head_slot :: snapshots) (boundary :: stack) old_snapshot
      tracked_boundary (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hreturn_covered : prospective_location_covered_by_frame CT h active
      return_location.
  { destruct Hreturn_owned as [owner [Howner Howner_return]].
    have Howner_runtime : r_muttype h owner = Some Mut_r.
    { eapply retained_reachable_reflects_runtime_context_private;
        [exact (proj1 (proj2 Hactive_wf))|exact Howner_return|].
      exact Hreturn_runtime. }
    exists owner. split.
    - destruct Howner as
        [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
      + left. exists variable, T. repeat split; assumption.
      + right. split.
        * exists variable, T. repeat split; assumption.
        * exact Howner_runtime.
    - eapply frozen_caller_prospective_retained_forward.
      exact Howner_return. }
  unfold caller_post.
  eapply live_prospective_mutable_authority_components_after_return_pop;
    eauto.
Qed.

(** The complete stack-age package transported by a tracked non-null return.
    Keeping the ordinary and prospective partitions together prevents the
    return proof from silently falling back to retained-edge reachability
    when an RDM join or reverse RDM edge is involved. *)
Lemma private_fresh_return_partitions_after_nonnull_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h
    caller_authority caller_senv caller_renv destination destination_type
    return_location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination (Iot return_location))
      caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    frame_owned_location CT h active return_location ->
    r_muttype h return_location = Some Mut_r ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    let tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
      snapshots in
    frozen_callee_side_mutable_components_after_boundaries CT h caller_post
      tail_snapshots stack /\
    frozen_callee_side_prospective_components_after_boundaries CT h
      caller_post tail_snapshots stack /\
    frozen_snapshot_boundaries_after_cutoff cutoff tail_snapshots stack.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h
    caller_authority caller_senv caller_renv destination destination_type
    return_location
    [Hprivate [Hcomponents [Hprospective Hafter]]] Hcaller
    Hdestination_nonzero Hactive_wf Hactive_sound Hcaller_wf Hcaller_post_wf
    Hcaller_post_sound Hdestination Hreturn_owned Hreturn_runtime caller_post
    tail_snapshots.
  split.
  - unfold caller_post, tail_snapshots.
    eapply frozen_callee_side_components_after_return_pop; eauto.
  - split.
    + unfold caller_post, tail_snapshots.
      eapply frozen_callee_side_prospective_components_after_return_pop;
        eauto.
    + unfold tail_snapshots.
      eapply advance_snapshot_boundaries_after_cutoff.
      eapply snapshot_boundaries_after_cutoff_tail. exact Hafter.
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

Lemma caller_null_post_rdm_roots_descend :
  forall CT h caller_senv caller_renv destination destination_type,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    rdm_roots_descend_from CT h caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a).
Proof.
  intros CT h caller_senv caller_renv destination destination_type
    Hdestination_nonzero Hdestination Hlength root Hroot.
  exists root. split.
  - eapply caller_null_post_rdm_root_is_old; eauto.
  - constructor.
Qed.

Lemma caller_null_post_owned_is_old :
  forall CT h caller_authority caller_senv caller_renv destination
    destination_type,
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    length caller_senv = length caller_renv.(vars) ->
    Included Loc
      (phase_frame_capability_set CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)))
      (phase_frame_capability_set CT h
        (mk_watched_frame caller_authority caller_senv caller_renv)).
Proof.
  intros CT h caller_authority caller_senv caller_renv destination
    destination_type Hdestination_nonzero Hdestination Hlength location
    [root [Hroot Hreachable]].
  exists root. split; [|exact Hreachable].
  eapply caller_null_post_capability_root_is_old; eauto.
Qed.

Lemma live_prospective_components_after_plain_pop :
  forall CT h cutoff active boundary stack caller,
    boundary.(boundary_caller) = caller ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      active (boundary :: stack) ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      caller stack.
Proof.
  intros CT h cutoff active boundary stack caller Hcaller Hold frame root
    target Hlive Hreachable.
  inversion Hlive; subst.
  - eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
    + constructor. simpl. left. reflexivity.
    + exact Hreachable.
  - eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma frozen_callee_side_prospective_components_after_null_return_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    authority_context_sound h caller_renv caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)) snapshots)
      stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_sound Hdestination Hold snapshot
    tracked_boundary above below Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head :: snapshots) (boundary :: stack) old_snapshot tracked_boundary
      (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  have Hcaller_components :
      live_prospective_mutable_authority_components_after_cutoff CT h
        tracked_boundary.(boundary_entry_cutoff)
        (mk_watched_frame caller_authority caller_senv caller_renv) above.
  { eapply live_prospective_components_after_plain_pop with
      (active := active) (boundary := boundary).
    - exact Hcaller.
    - exact Hinput_components. }
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  unfold caller_post.
  eapply live_prospective_mutable_authority_components_after_active_descent.
  - exact Hcaller_wf.
  - exact Hcaller_sound.
  - eapply caller_null_post_rdm_roots_descend; eauto.
  - eapply caller_null_post_owned_is_old; eauto.
  - exact Hcaller_components.
Qed.

Lemma live_mutable_authority_components_after_null_return_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    live_mutable_authority_components_after_cutoff CT h cutoff active
      (boundary :: stack) ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type Hcaller Hdestination_nonzero
    Hcaller_wf Hdestination Hold frame root target Hlive Hreachable.
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  inversion Hlive; subst.
  - inversion Hreachable; subst.
    + eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
      * constructor. simpl. left. reflexivity.
      * apply mutable_authority_reachable_capability.
        -- rewrite Hcaller. eapply caller_null_post_capability_root_is_old;
             eauto.
        -- exact H0.
        -- exact H1.
    + eapply Hold with (frame := boundary.(boundary_caller)) (root := root).
      * constructor. simpl. left. reflexivity.
      * apply mutable_authority_reachable_rdm.
        -- rewrite Hcaller. eapply caller_null_post_rdm_root_is_old; eauto.
        -- exact H0.
        -- exact H1.
  - eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
    + constructor. simpl. right. exact H.
    + exact Hreachable.
Qed.

Lemma frozen_callee_side_components_after_null_return_pop :
  forall CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      (head :: snapshots) (boundary :: stack) ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a))
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)) snapshots)
      stack.
Proof.
  intros CT h active boundary stack head snapshots caller_authority
    caller_senv caller_renv destination destination_type Hcaller
    Hdestination_nonzero Hcaller_wf Hdestination Hold snapshot
    tracked_boundary above below Hpartition.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  destruct (advance_frozen_snapshot_live_partition_reflects CT h caller_post
    snapshots stack snapshot tracked_boundary above below Hpartition) as
    [old_snapshot Hold_partition].
  have Hinput_partition : frozen_snapshot_live_partition
      (head :: snapshots) (boundary :: stack) old_snapshot tracked_boundary
      (boundary :: above) below.
  { constructor. exact Hold_partition. }
  have Hinput_components := Hold old_snapshot tracked_boundary
    (boundary :: above) below Hinput_partition.
  unfold caller_post.
  eapply live_mutable_authority_components_after_null_return_pop; eauto.
Qed.

Lemma private_fresh_return_partitions_after_null_pop :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head :: snapshots) h ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    authority_context_sound h caller_renv caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    let caller_post := mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination Null_a) in
    let tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
      snapshots in
    frozen_callee_side_mutable_components_after_boundaries CT h caller_post
      tail_snapshots stack /\
    frozen_callee_side_prospective_components_after_boundaries CT h
      caller_post tail_snapshots stack /\
    frozen_snapshot_boundaries_after_cutoff cutoff tail_snapshots stack.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h
    caller_authority caller_senv caller_renv destination destination_type
    [Hprivate [Hcomponents [Hprospective Hafter]]] Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_sound Hdestination caller_post
    tail_snapshots.
  split.
  - unfold caller_post, tail_snapshots.
    eapply frozen_callee_side_components_after_null_return_pop; eauto.
  - split.
    + unfold caller_post, tail_snapshots.
      eapply frozen_callee_side_prospective_components_after_null_return_pop;
        eauto.
    + unfold tail_snapshots.
      eapply advance_snapshot_boundaries_after_cutoff.
      eapply snapshot_boundaries_after_cutoff_tail. exact Hafter.
Qed.

Lemma advance_frozen_caller_snapshots_resume_roots_in_heap :
  forall CT h active snapshots,
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hroots snapshot root Hsnapshot Hroot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot. simpl in Hroot.
  eapply Hroots; eauto.
Qed.

Lemma advance_frozen_caller_snapshots_resume_exposures_wf :
  forall CT h active snapshots,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    frozen_caller_snapshots_resume_exposures_wf CT h active snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h active
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hwf
    [Hruntime [Hclosed [Hdangerous [Hentry Hroots]]]].
  repeat split.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    eapply advance_frozen_caller_snapshot_runtime_mutable; eauto.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    apply (proj1 (frozen_caller_authority_closure_idempotent CT h active
      old_snapshot.(frozen_snapshot_current_resume_exposure))).
  - intros snapshot mode location Hsnapshot Hcolor.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in Hcolor.
    destruct Hcolor as [seed [Hseed Hpath]].
    destruct seed as [seed_mode seed_location].
    have Hseed_mode := Hdangerous old_snapshot seed_mode seed_location
      Hslot Hseed.
    have Hmode := frozen_caller_authority_connected_preserves_dangerous CT h
      active (seed_mode, seed_location) (mode, location) Hseed_mode Hpath.
    simpl in Hmode. exact Hmode.
  - intros snapshot Hsnapshot state Hstate.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in *.
    apply frozen_caller_authority_closure_contains.
    eapply Hentry; eauto.
  - intros snapshot root Hsnapshot Hroot Hroot_runtime.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in *.
    apply frozen_caller_authority_closure_contains.
    eapply Hroots; eauto.
Qed.

(** Cross-phase form used at return.  The old closure certificate is relative
    to the completed callee and need not hold for the resumed caller.  Only
    the frame-independent parts of the old exposure certificate are reused;
    closure under [new_active] is rebuilt by taking its closure explicitly. *)
Lemma advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active :
  forall CT h old_active new_active snapshots,
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    frozen_caller_snapshots_resume_exposures_wf CT h old_active snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h new_active
      (advance_frozen_caller_snapshots CT h new_active snapshots).
Proof.
  intros CT h old_active new_active snapshots Hwf
    [Hruntime [_ [Hdangerous [Hentry Hroots]]]].
  repeat split.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    eapply advance_frozen_caller_snapshot_runtime_mutable; eauto.
  - intros snapshot Hsnapshot.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl.
    apply (proj1 (frozen_caller_authority_closure_idempotent CT h new_active
      old_snapshot.(frozen_snapshot_current_resume_exposure))).
  - intros snapshot mode location Hsnapshot Hcolor.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in Hcolor.
    destruct Hcolor as [seed [Hseed Hpath]].
    destruct seed as [seed_mode seed_location].
    have Hseed_mode := Hdangerous old_snapshot seed_mode seed_location
      Hslot Hseed.
    exact (frozen_caller_authority_connected_preserves_dangerous CT h
      new_active (seed_mode, seed_location) (mode, location) Hseed_mode
      Hpath).
  - intros snapshot Hsnapshot state Hstate.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in *.
    apply frozen_caller_authority_closure_contains.
    eapply Hentry; eauto.
  - intros snapshot root Hsnapshot Hroot Hroot_runtime.
    unfold advance_frozen_caller_snapshots in Hsnapshot.
    apply in_map_iff in Hsnapshot.
    destruct Hsnapshot as [slot [Heq Hslot]].
    destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst snapshot. simpl in *.
    apply frozen_caller_authority_closure_contains.
    eapply Hroots; eauto.
Qed.

(** The structural part of the private frozen state.  These facts are
    transported uniformly whenever a suspended snapshot is advanced through
    the currently active frame.  The protected-zone and resume-safety facts
    are intentionally absent: those are the semantic obligations discharged
    by the pop classifier. *)
Definition private_frozen_snapshot_structural_state
  (CT : class_table) (h : heap) (active : watched_frame)
  (snapshots : list frozen_caller_snapshot_slot)
  (stack : list watched_boundary) : Prop :=
  frozen_caller_snapshots_aligned snapshots stack /\
  frozen_caller_snapshots_runtime_mutable h snapshots /\
  frozen_caller_snapshots_closed CT h active snapshots /\
  frozen_caller_snapshots_retain_entry snapshots /\
  frozen_caller_snapshots_dangerous snapshots /\
  frozen_caller_snapshots_resume_roots_in_heap h snapshots /\
  frozen_caller_snapshots_resume_exposures_wf CT h active snapshots /\
  frozen_caller_snapshots_before_boundaries snapshots stack /\
  frozen_caller_snapshots_nested_covered snapshots /\
  frozen_caller_snapshots_entry_exposure_covered snapshots /\
  frozen_caller_snapshots_cover_phase_incoming snapshots.

Lemma advance_frozen_caller_snapshots_structural_state :
  forall CT h old_active new_active snapshots stack,
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    private_frozen_snapshot_structural_state CT h old_active snapshots stack ->
    private_frozen_snapshot_structural_state CT h new_active
      (advance_frozen_caller_snapshots CT h new_active snapshots) stack /\
    frozen_caller_snapshot_list_metadata_eq
      (advance_frozen_caller_snapshots CT h new_active snapshots) snapshots.
Proof.
  intros CT h old_active new_active snapshots stack Hwf
    (Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Hroots &
      Hexposure & Hbefore & Hnested & Hentry & Hphase).
  split.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
    + unfold frozen_caller_snapshots_aligned in *.
      unfold advance_frozen_caller_snapshots. rewrite length_map.
      exact Haligned.
    + eapply advance_frozen_caller_snapshots_runtime_mutable; eauto.
    + apply advance_frozen_caller_snapshots_closed.
    + eapply advance_frozen_caller_snapshots_retain_entry; eauto.
    + eapply advance_frozen_caller_snapshots_dangerous; eauto.
    + eapply advance_frozen_caller_snapshots_resume_roots_in_heap; eauto.
    + eapply advance_frozen_caller_snapshots_resume_exposures_wf_from_any_active;
        eauto.
    + eapply advance_frozen_caller_snapshots_before_boundaries; eauto.
    + eapply advance_frozen_caller_snapshots_nested_covered; eauto.
    + eapply advance_frozen_caller_snapshots_entry_exposure_covered; eauto.
    + eapply advance_frozen_caller_snapshots_cover_phase_incoming; eauto.
  - apply advance_frozen_caller_snapshots_metadata_eq.
Qed.

(** Dropping the snapshot paired with the top call boundary exposes exactly
    the structural data for the older suspended callers. *)
Lemma private_frozen_statement_tail_structural_state :
  forall CT P Z cutoff active boundary stack incoming slot snapshots h,
    private_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    private_frozen_snapshot_structural_state CT h active snapshots stack.
Proof.
  intros CT P Z cutoff active boundary stack incoming slot snapshots h
    [Hfrozen [_ [Hbefore [Hnested _]]]].
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
  - eapply frozen_caller_snapshots_aligned_pop; eauto.
  - intros snapshot Hsnapshot. eapply Hruntime. simpl. right. exact Hsnapshot.
  - intros snapshot Hsnapshot. eapply Hclosed. simpl. right. exact Hsnapshot.
  - intros snapshot Hsnapshot. eapply Hretain. simpl. right. exact Hsnapshot.
  - intros snapshot mode location Hsnapshot. eapply Hdangerous.
    simpl. right. exact Hsnapshot.
  - intros snapshot root Hsnapshot. eapply Hroots.
    simpl. right. exact Hsnapshot.
  - destruct Hexposure as
      (Hexposure_runtime & Hexposure_closed & Hexposure_dangerous &
        Hexposure_entry & Hexposure_roots).
    repeat split.
    + intros snapshot Hsnapshot. eapply Hexposure_runtime.
      simpl. right. exact Hsnapshot.
    + intros snapshot Hsnapshot. eapply Hexposure_closed.
      simpl. right. exact Hsnapshot.
    + intros snapshot mode location Hsnapshot. eapply Hexposure_dangerous.
      simpl. right. exact Hsnapshot.
    + intros snapshot Hsnapshot. eapply Hexposure_entry.
      simpl. right. exact Hsnapshot.
    + intros snapshot root Hsnapshot. eapply Hexposure_roots.
      simpl. right. exact Hsnapshot.
  - inversion Hbefore; subst. exact H4.
  - eapply frozen_caller_snapshots_nested_covered_tail. exact Hnested.
  - intros snapshot source_mode source Hsnapshot. eapply Hentry.
    simpl. right. exact Hsnapshot.
  - intros snapshot mode location Hsnapshot. eapply Hphase.
    simpl. right. exact Hsnapshot.
Qed.

Lemma private_frozen_statement_advance_tail_structural_state :
  forall CT P Z cutoff active boundary stack incoming slot snapshots h
    caller_post,
    private_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    wf_r_config CT caller_post.(frame_senv) caller_post.(frame_renv) h ->
    private_frozen_snapshot_structural_state CT h caller_post
      (advance_frozen_caller_snapshots CT h caller_post snapshots) stack /\
    frozen_caller_snapshot_list_metadata_eq
      (advance_frozen_caller_snapshots CT h caller_post snapshots) snapshots.
Proof.
  intros CT P Z cutoff active boundary stack incoming slot snapshots h
    caller_post Hprivate Hcaller_wf.
  eapply advance_frozen_caller_snapshots_structural_state; [exact Hcaller_wf|].
  eapply private_frozen_statement_tail_structural_state. exact Hprivate.
Qed.

(** The genuinely semantic residue of a return transition.  Keeping this
    separate from structural snapshot transport makes explicit that all
    assumptions remain proof-local: none can become a dispatch check or a
    premise of [successful_stmt_preserves_potential_history]. *)
Definition private_frozen_snapshot_return_safety
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (active : watched_frame) (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) : Prop :=
  frozen_caller_snapshots_active_resume_justified CT h Z active snapshots /\
  frozen_caller_snapshots_avoid_protected Z snapshots /\
  frozen_caller_snapshots_nested_resume_safe Z snapshots /\
  frozen_caller_snapshots_resume_roots_safe CT h Z active snapshots /\
  frozen_caller_snapshots_resume_joins_safe Z snapshots /\
  frozen_completed_colors_resume_safe Z
    (executing_authority_color_set CT h active incoming) snapshots.

Lemma private_fresh_frozen_statement_state_from_return_parts :
  forall CT P Z cutoff active stack incoming snapshots h,
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h ->
    private_frozen_snapshot_structural_state CT h active snapshots stack ->
    private_frozen_snapshot_return_safety CT h Z active incoming snapshots ->
    frozen_callee_side_mutable_components_after_boundaries CT h active
      snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack ->
    private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
      snapshots h.
Proof.
  intros CT P Z cutoff active stack incoming snapshots h Hmain
    (Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Hroots &
      Hexposure & Hbefore & Hcovered & Hentry & Hphase)
    (Horigins & Havoid & Hnested & Hresume & Hjoins & Hcompleted)
    Hcomponents Hprospective Hafter.
  split.
  - split.
    + refine (conj Hmain (conj Haligned (conj Hruntime (conj Hclosed
        (conj Hretain (conj Hdangerous (conj Havoid (conj Hroots
          (conj Hexposure (conj Hresume (conj Hjoins
            (conj Hentry Hphase)))))))))))).
    + exact (conj Horigins (conj Hbefore (conj Hcovered
        (conj Hnested Hcompleted)))).
  - split; [exact Hcomponents|]. split; assumption.
Qed.

(** Return reconstruction with the mechanical obligations discharged.  The
    sole semantic input is [private_frozen_snapshot_return_safety], which is
    supplied by the authority-sensitive pop classifier. *)
Lemma private_fresh_frozen_statement_after_nonnull_return_parts :
  forall CT P Z cutoff active boundary stack active_incoming head_slot snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type return_location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) active_incoming (head_slot :: snapshots) h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack caller_incoming h ->
    private_frozen_snapshot_return_safety CT h Z
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination (Iot return_location))
      caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    frame_owned_location CT h active return_location ->
    r_muttype h return_location = Some Mut_r ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) snapshots) h.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming head_slot snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type return_location Hbody Hpost Hreturn_safety Hcaller
    Hdestination_nonzero Hactive_wf Hactive_sound Hcaller_wf Hcaller_post_wf
    Hcaller_post_sound Hdestination Hreturn_owned Hreturn_runtime.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination (Iot return_location))).
  set (tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
    snapshots).
  have Hbody_private := proj1 Hbody.
  destruct (private_frozen_statement_advance_tail_structural_state CT P Z
    cutoff active boundary stack active_incoming head_slot snapshots h
    caller_post Hbody_private Hcaller_post_wf) as [Hstructural Hmetadata].
  destruct (private_fresh_return_partitions_after_nonnull_pop CT P Z cutoff
    active boundary stack active_incoming head_slot snapshots h caller_authority
    caller_senv caller_renv destination destination_type return_location
    Hbody Hcaller Hdestination_nonzero Hactive_wf Hactive_sound Hcaller_wf
    Hcaller_post_wf Hcaller_post_sound Hdestination Hreturn_owned
    Hreturn_runtime) as [Hcomponents [Hprospective Hafter]].
  unfold caller_post, tail_snapshots in *.
  eapply private_fresh_frozen_statement_state_from_return_parts; eauto.
Qed.

Lemma private_fresh_frozen_statement_after_null_return_parts :
  forall CT P Z cutoff active boundary stack active_incoming head snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) active_incoming (head :: snapshots) h ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a))
      stack caller_incoming h ->
    private_frozen_snapshot_return_safety CT h Z
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)) snapshots) ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    destination <> 0 ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination Null_a) h ->
    authority_context_sound h caller_renv caller_authority ->
    static_getType caller_senv destination = Some destination_type ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a))
      stack caller_incoming
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a)) snapshots) h.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming head snapshots h
    caller_incoming caller_authority caller_senv caller_renv destination
    destination_type Hbody Hpost Hreturn_safety Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_post_wf Hcaller_sound Hdestination.
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value caller_renv destination Null_a)).
  set (tail_snapshots := advance_frozen_caller_snapshots CT h caller_post
    snapshots).
  have Hbody_private := proj1 Hbody.
  destruct (private_frozen_statement_advance_tail_structural_state CT P Z
    cutoff active boundary stack active_incoming head snapshots h caller_post
    Hbody_private Hcaller_post_wf) as [Hstructural Hmetadata].
  destruct (private_fresh_return_partitions_after_null_pop CT P Z cutoff
    active boundary stack active_incoming head snapshots h caller_authority
    caller_senv caller_renv destination destination_type Hbody Hcaller
    Hdestination_nonzero Hcaller_wf Hcaller_sound Hdestination) as
    [Hcomponents [Hprospective Hafter]].
  unfold caller_post, tail_snapshots in *.
  eapply private_fresh_frozen_statement_state_from_return_parts; eauto.
Qed.

Lemma principled_local_mutable_rdm_history_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming
    x qc C args sGamma' rGamma' h',
    principled_local_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    principled_local_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack incoming h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming
    x qc C args sGamma' rGamma' h' [Hstate Hcomponents] Htyping Heval.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Hpost_wf := preservation_pico CT sGamma mt rGamma h
    (SNew x qc C args) rGamma' h' sGamma' Hwf Htyping Heval.
  split.
  - eapply principled_phased_authority_history_after_new; eauto.
  - have Hcutoff : cutoff <= dom h :=
      proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
    inversion Heval; subst.
    assert (Hupdate :
        set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
        update_r_env_value rGamma x (Iot (dom h))).
    { destruct rGamma. reflexivity. }
    rewrite Hupdate in Hpost_wf |- *.
    eapply active_mutable_rdm_components_after_new
      with (mt := mt) (qc := qc).
    + exact Hwf.
    + exact Htyping.
    + exact Hargs.
    + exact (proj1 (proj2 Hpost_wf)).
    + exact Hcutoff.
    + exact Hcomponents.
Qed.

Lemma principled_live_mutable_rdm_history_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming
    x qc C args sGamma' rGamma' h',
    principled_live_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    principled_live_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack incoming h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming
    x qc C args sGamma' rGamma' h' [Hstate Hcomponents] Htyping Heval.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Hframes : live_frames_wf CT h
      (mk_watched_frame authority sGamma rGamma) stack :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
  have Hpost_wf := preservation_pico CT sGamma mt rGamma h
    (SNew x qc C args) rGamma' h' sGamma' Hwf Htyping Heval.
  split.
  - eapply principled_phased_authority_history_after_new; eauto.
  - have Hcutoff : cutoff <= dom h :=
      proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
    inversion Heval; subst.
    assert (Hupdate :
        set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
        update_r_env_value rGamma x (Iot (dom h))).
    { destruct rGamma. reflexivity. }
    rewrite Hupdate in Hpost_wf |- *.
    eapply live_mutable_rdm_components_after_new
      with (mt := mt) (qc := qc).
    + exact Hwf.
    + exact Hframes.
    + exact Htyping.
    + exact Hargs.
    + exact (proj1 (proj2 Hpost_wf)).
    + exact Hcutoff.
    + exact Hcomponents.
Qed.

Lemma principled_root_scoped_frozen_mutable_rdm_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x qc C args sGamma' rGamma' h',
    principled_root_scoped_frozen_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    principled_root_scoped_frozen_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack incoming
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x qc C args sGamma' rGamma' h' [Hfrozen [Hcomponents Horigins]] Htyping
    Heval.
  have Hmain := proj1 Hfrozen.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hfull_post := principled_frozen_authority_history_after_new CT P Z
    cutoff authority sGamma mt rGamma h stack incoming snapshots x qc C args
    sGamma' rGamma' h' Hfrozen Htyping Heval.
  have Hlive_post := principled_live_mutable_rdm_history_after_new CT P Z
    cutoff authority sGamma mt rGamma h stack incoming x qc C args sGamma'
    rGamma' h' (conj Hmain Hcomponents) Htyping Heval.
  inversion Heval; subst.
  assert (Hupdate :
      set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Hfull_post, Hlive_post |- *.
  split; [exact Hfull_post|]. split; [exact (proj2 Hlive_post)|].
  match goal with
  | |- frozen_caller_snapshots_active_resume_origins _
      (h ++ [mkObj (mkruntime_type ?runtime_q C) vals]) _ _ =>
      set (new_runtime := runtime_q) in *
  end.
  have Hpost_main := proj1 Hfull_post.
  have Hpost_wf : wf_r_config CT sGamma'
      (update_r_env_value rGamma x (Iot (dom h)))
      (h ++ [mkObj (mkruntime_type new_runtime C) vals]) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hpost_main))))).
  have Hpost_sound : authority_context_sound
      (h ++ [mkObj (mkruntime_type new_runtime C) vals])
      (update_r_env_value rGamma x (Iot (dom h))) authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpost_main)))))).
  eapply frozen_caller_snapshots_active_resume_origins_after_new
    with (qreceiver := qthisr).
  - exact Hwf.
  - exact Hpost_wf.
  - exact Hsound.
  - exact Hpost_sound.
  - exact Htyping.
  - exact Hargs.
  - unfold new_runtime. reflexivity.
  - exact (proj1 (proj2 (proj2 Hfrozen))).
  - exact (proj1 (proj2 (proj2 (proj2 Hfrozen)))).
  - exact Horigins.
Qed.

(** Non-call transitions for the public existential package.  Each proof
    preserves the hidden incoming-color witness unchanged. *)
Lemma flexible_history_after_assignment :
  forall CT P Z cutoff authority sGamma mt rGamma h stack
    x e old value,
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) stack h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x e old value
    [incoming Hstate] Htyping Hscope Hvalue Heval.
  exists incoming.
  eapply principled_phased_authority_history_after_assignment; eauto.
Qed.

Lemma flexible_history_after_local :
  forall CT P Z cutoff authority sGamma mt rGamma h stack T x sGamma',
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))) stack h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack T x sGamma'
    [incoming Hstate] Htyping Hnone.
  exists incoming.
  eapply principled_phased_authority_history_after_local; eauto.
Qed.

Lemma flexible_history_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack
    x field y sGamma' rGamma' h',
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x field y
    sGamma' rGamma' h' [incoming Hstate] Htyping Hscope Heval.
  exists incoming.
  eapply principled_phased_authority_history_after_field_write; eauto.
Qed.

Lemma flexible_history_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack
    x qc C args sGamma' rGamma' h',
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    flexible_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack x qc C args
    sGamma' rGamma' h' [incoming Hstate] Htyping Heval.
  exists incoming.
  eapply principled_phased_authority_history_after_new; eauto.
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

Lemma authority_boundary_view_attachment_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    authority_boundary_view_attachment CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma authority_boundary_view_entry_root :
  forall CT h boundary stack root,
    boundary_view_anchor boundary root ->
    authority_boundary_view_entry CT h boundary stack root.
Proof.
  intros. exists root. split; [assumption|apply rt_refl].
Qed.

Lemma authority_boundary_view_attachment_transport :
  forall CT h boundary stack first second,
    authority_boundary_view_attachment CT h boundary stack first ->
    authority_color_connected CT h boundary.(boundary_caller) stack
      first second ->
    authority_boundary_view_attachment CT h boundary stack second.
Proof.
  intros CT h boundary stack first second
    [anchor [Hanchor Hanchor_first]] Hfirst_second.
  exists anchor. split; [exact Hanchor|].
  eapply authority_color_connected_trans; eauto.
Qed.

Lemma authority_boundary_view_entry_transport :
  forall CT h boundary stack first second,
    authority_color_connected CT h boundary.(boundary_caller) stack
      first second ->
    authority_boundary_view_entry CT h boundary stack second ->
    authority_boundary_view_entry CT h boundary stack first.
Proof.
  intros CT h boundary stack first second Hfirst_second
    [anchor [Hanchor Hsecond_anchor]].
  exists anchor. split; [exact Hanchor|].
  eapply authority_color_connected_trans; eauto.
Qed.

Definition boundary_color_attachment
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    boundary_connected CT h boundary.(boundary_caller) stack anchor root.

Definition boundary_color_entry
  (CT : class_table) (h : heap) (boundary : watched_boundary)
  (stack : list watched_boundary) (root : Loc) : Prop :=
  exists anchor,
    boundary_view_anchor boundary anchor /\
    boundary_connected CT h boundary.(boundary_caller) stack root anchor.

Lemma boundary_view_attachment_is_color_attachment :
  forall CT h boundary stack root,
    boundary_view_attachment CT h boundary stack root ->
    boundary_color_attachment CT h boundary stack root.
Proof.
  intros CT h boundary stack root [anchor [Hanchor Hconnected]].
  exists anchor. split; [exact Hanchor|].
  apply potential_connected_is_boundary_connected. exact Hconnected.
Qed.

Lemma boundary_view_entry_is_color_entry :
  forall CT h boundary stack root,
    boundary_view_entry CT h boundary stack root ->
    boundary_color_entry CT h boundary stack root.
Proof.
  intros CT h boundary stack root [anchor [Hanchor Hconnected]].
  exists anchor. split; [exact Hanchor|].
  apply potential_connected_is_boundary_connected. exact Hconnected.
Qed.

Lemma boundary_color_attachment_transport :
  forall CT h boundary stack first second,
    boundary_color_attachment CT h boundary stack first ->
    boundary_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_color_attachment CT h boundary stack second.
Proof.
  intros CT h boundary stack first second
    [anchor [Hanchor Hanchor_first]] Hfirst_second.
  exists anchor. split; [exact Hanchor|].
  eapply rt_trans; eauto.
Qed.

Lemma boundary_color_entry_transport :
  forall CT h boundary stack first second,
    boundary_connected CT h boundary.(boundary_caller) stack first second ->
    boundary_color_entry CT h boundary stack second ->
    boundary_color_entry CT h boundary stack first.
Proof.
  intros CT h boundary stack first second Hfirst_second
    [anchor [Hanchor Hsecond_anchor]].
  exists anchor. split; [exact Hanchor|].
  eapply rt_trans; eauto.
Qed.

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

Lemma authority_color_adjacent_after_call_push :
  forall CT h boundary stack callee_authority left right,
    authority_color_adjacent CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    authority_color_connected CT h boundary.(boundary_caller) stack
      left right \/
    (authority_boundary_view_entry CT h boundary stack left /\
     authority_boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right [Hheap | Hframe].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin := boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin :=
        boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. split.
        -- apply authority_boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply authority_boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply authority_boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply authority_boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * right. split.
        -- apply authority_boundary_view_entry_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
        -- apply authority_boundary_view_attachment_root;
             unfold boundary_view_anchor; rewrite Hview; assumption.
      * left. have Heq := readonly_boundary_roots_equal boundary left right
          Hview Hleft Hright. subst right. apply rt_refl.
      * contradiction.
      * contradiction.
    + simpl in H.
      destruct H as [Htop | Htail].
      * subst boundary0. left. apply rt_step. right.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left. apply rt_step. right. exists boundary0.(boundary_caller).
        split; [constructor; exact Htail|]. split; assumption.
Qed.

Lemma authority_color_connected_after_call_push :
  forall CT h boundary stack callee_authority left right,
    authority_color_connected CT h
      (mk_watched_frame callee_authority
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    authority_color_connected CT h boundary.(boundary_caller) stack
      left right \/
    (authority_boundary_view_entry CT h boundary stack left /\
     authority_boundary_view_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack callee_authority left right Hconnected.
  induction Hconnected.
  - eapply authority_color_adjacent_after_call_push; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as [Hxy | [Hentry_x Hattach_y]];
      destruct IHHconnected2 as [Hyz | [Hentry_y Hattach_z]].
    + left. eapply authority_color_connected_trans; eauto.
    + right. split.
      * eapply authority_boundary_view_entry_transport; eauto.
      * exact Hattach_z.
    + right. split.
      * exact Hentry_x.
      * eapply authority_boundary_view_attachment_transport; eauto.
    + right. split; assumption.
Qed.

Lemma authority_call_push_live_capability_included_in_caller :
  forall CT h boundary above location,
    In Loc
      (live_capability_set CT h
        (mk_watched_frame
          (call_authority boundary.(boundary_caller).(frame_authority)
            boundary.(boundary_receiver_view))
          boundary.(boundary_callee_entry_senv)
          boundary.(boundary_callee_entry_renv))
        (boundary :: above)) location ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) above) location.
Proof.
  intros CT h boundary above location
    [root [[Hactive | [suspended [Hin Hsuspended]]] Hreach]].
  - exists root. split; [left|exact Hreach].
    exact (boundary_capability_origins boundary root Hactive).
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst suspended. exists root.
      split; [left; exact Hsuspended|exact Hreach].
    + exists root. split.
      * right. exists suspended. split; assumption.
      * exact Hreach.
Qed.

Lemma authority_flow_step_after_call_push_decomposes :
  forall CT h boundary stack source target,
    wf_r_config CT boundary.(boundary_caller).(frame_senv)
      boundary.(boundary_caller).(frame_renv) h ->
    r_muttype h (snd source) = Some Mut_r ->
    authority_flow_step CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) source target ->
    authority_flow_connected CT h boundary.(boundary_caller) stack
      source target \/
    exists anchor,
      typed_root Mut boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) anchor /\
      authority_flow_connected CT h boundary.(boundary_caller) stack
        source (FlowPowered, anchor).
Proof.
  intros CT h boundary stack source target Hcaller_wf Hsource_runtime Hstep.
  inversion Hstep; subst; simpl in *.
  - left. apply rt_step. apply authority_flow_retained. exact H.
  - left. apply rt_step. apply authority_flow_reverse_rdm. exact H.
  - left. apply rt_step. apply authority_flow_neutral_rdm_forward. exact H.
  - left. apply rt_step. apply authority_flow_neutral_rdm_backward. exact H.
  - destruct H as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin :=
        boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin :=
        boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. exists left. split; [exact Hleft_origin|apply rt_refl].
      * have Hleft_immutable :=
          typed_imm_root_runtime_immutable CT
            boundary.(boundary_caller).(frame_senv)
            boundary.(boundary_caller).(frame_renv) h left Hcaller_wf
            Hleft_origin.
        congruence.
      * left. apply rt_step. apply authority_flow_powered_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left.
        have Heq := readonly_boundary_roots_equal boundary left right Hview
          Hleft Hright.
        subst right. apply rt_step. apply authority_flow_forget.
      * contradiction.
      * contradiction.
    + simpl in H. destruct H as [Htop | Htail].
      * subst boundary0. left. apply rt_step.
        apply authority_flow_powered_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left. apply rt_step. apply authority_flow_powered_frame.
        exists boundary0.(boundary_caller).
        split; [constructor; exact Htail|]. split; assumption.
  - destruct H as [frame [Hlive [Hleft Hright]]].
    inversion Hlive; subst.
    + have Hleft_origin :=
        boundary_entry_rdm_root_by_view boundary left Hleft.
      have Hright_origin :=
        boundary_entry_rdm_root_by_view boundary right Hright.
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        simpl in Hleft_origin, Hright_origin.
      * right. exists left. split; [exact Hleft_origin|].
        apply rt_step. apply authority_flow_promote.
        eapply typed_mut_root_is_live_capability. exact Hleft_origin.
      * have Hleft_immutable :=
          typed_imm_root_runtime_immutable CT
            boundary.(boundary_caller).(frame_senv)
            boundary.(boundary_caller).(frame_renv) h left Hcaller_wf
            Hleft_origin.
        congruence.
      * left. apply rt_step. apply authority_flow_neutral_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left.
        have Heq := readonly_boundary_roots_equal boundary left right Hview
          Hleft Hright.
        subst right. apply rt_refl.
      * contradiction.
      * contradiction.
    + simpl in H. destruct H as [Htop | Htail].
      * subst boundary0. left. apply rt_step.
        apply authority_flow_neutral_frame.
        exists boundary.(boundary_caller).
        split; [constructor|]. split; assumption.
      * left. apply rt_step. apply authority_flow_neutral_frame.
        exists boundary0.(boundary_caller).
        split; [constructor; exact Htail|]. split; assumption.
  - left. apply rt_step. apply authority_flow_forget.
  - left. apply rt_step. apply authority_flow_promote.
    eapply authority_call_push_live_capability_included_in_caller.
    exact H.
Qed.

Lemma authority_flow_connected_after_call_push_decomposes :
  forall CT h boundary stack source target,
    live_frames_wf CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) ->
    wf_heap CT h ->
    r_muttype h (snd source) = Some Mut_r ->
    authority_flow_connected CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) source target ->
    authority_flow_connected CT h boundary.(boundary_caller) stack
      source target \/
    exists anchor,
      typed_root Mut boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) anchor /\
      authority_flow_connected CT h boundary.(boundary_caller) stack
        source (FlowPowered, anchor).
Proof.
  intros CT h boundary stack source target Hframes Hheap Hsource_runtime
    Hconnected.
  have Hcaller_wf :
      wf_r_config CT boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) h.
  { exact (Forall_inv (proj2 Hframes)). }
  revert Hsource_runtime.
  induction Hconnected; intros Hsource_runtime.
  - eapply authority_flow_step_after_call_push_decomposes; eauto.
  - left. apply rt_refl.
  - destruct (IHHconnected1 Hsource_runtime) as
      [Hfirst_old | [anchor [Hanchor Hfirst_anchor]]].
    + have Hmiddle_runtime :
        r_muttype h (snd y) = Some Mut_r.
      { eapply authority_flow_connected_preserves_runtime_mutability;
          eauto. }
      destruct (IHHconnected2 Hmiddle_runtime) as
        [Hsecond_old | [anchor [Hanchor Hmiddle_anchor]]].
      * left. eapply rt_trans; eauto.
      * right. exists anchor. split; [exact Hanchor|].
        eapply rt_trans; eauto.
    + right. exists anchor. split; assumption.
Qed.

Lemma pending_call_stateful_authority_enter_call :
  forall CT h boundary stack tracked_depth,
    live_frames_wf CT h boundary.(boundary_caller) stack ->
    live_frames_authority_sound h boundary.(boundary_caller) stack ->
    live_frames_wf CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) ->
    pending_call_stateful_authority_separated CT h
      boundary.(boundary_caller) stack tracked_depth ->
    pending_call_stateful_authority_separated CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) (S tracked_depth).
Proof.
  intros CT h boundary stack tracked_depth Hframes Hsound Hnew_frames
    Hpending context_boundary above below capability owned Hpartition Htracked
    Hentry_free Howned Hcapability Hconnected.
  inversion Hpartition as
    [new_boundary new_below
    |new_head new_tail old_boundary old_above old_below Hold_partition];
    subst.
  - destruct Howned as
      [root [[Hactive_root | [suspended [Hin _]]] Hreach]].
    + exact ((proj1 Hentry_free) root Hactive_root).
    + inversion Hin.
  - have Hold_partition' :
      live_call_partition boundary.(boundary_caller) stack
        context_boundary old_above below.
    { eapply live_call_partition_change_active. exact Hold_partition. }
    have Hold_tracked : length old_above < tracked_depth.
    { simpl in Htracked. lia. }
    have Howned_old :
      In Loc
        (pending_owned_authority_set CT h boundary.(boundary_caller)
          old_above)
        owned.
    { eapply authority_call_push_live_capability_included_in_caller.
      exact Howned. }
    have Hcapability_global :
      In Loc
        (live_capability_set CT h boundary.(boundary_caller) stack)
        capability.
    { eapply live_call_partition_caller_capability_is_live; eauto. }
    have Hcapability_runtime :=
      live_capability_members_runtime_mutable CT h boundary.(boundary_caller)
        stack Hframes Hsound capability Hcapability_global.
    have Hheap : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
    destruct (authority_flow_connected_after_call_push_decomposes CT h
      boundary stack (FlowPowered, capability) (FlowPowered, owned)
      Hnew_frames Hheap Hcapability_runtime Hconnected) as
      [Hold_path | [anchor [Hanchor Hanchor_path]]].
    + exact (Hpending context_boundary old_above below capability owned
        Hold_partition' Hold_tracked Hentry_free Howned_old Hcapability
        Hold_path).
    + have Hanchor_owned :
        In Loc
          (pending_owned_authority_set CT h boundary.(boundary_caller)
            old_above)
          anchor.
      { eapply typed_mut_root_is_live_capability. exact Hanchor. }
      exact (Hpending context_boundary old_above below capability anchor
        Hold_partition' Hold_tracked Hentry_free Hanchor_owned Hcapability
        Hanchor_path).
Qed.

(*
Lemma pending_call_authority_colors_enter_call :
  forall CT h boundary stack,
    live_frames_wf CT h boundary.(boundary_caller) stack ->
    live_frames_authority_sound h boundary.(boundary_caller) stack ->
    pending_call_authority_colors_separated CT h
      boundary.(boundary_caller) stack ->
    pending_call_authority_colors_separated CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack).
Proof.
  intros CT h boundary stack Hframes Hsound Hpending context_boundary above
    below capability owned Hpartition Hentry_free Howned Hcapability common
    [Hcapability_common Howned_common].
  inversion Hpartition as
    [new_boundary new_below
    |new_head new_tail old_boundary old_above old_below Hold_partition];
    subst.
  - destruct Howned as
      [root [[Hactive_root | [suspended [Hin _]]] Hreach]].
    + exact ((proj1 Hentry_free) root Hactive_root).
    + inversion Hin.
  - have Hold_partition' :
      live_call_partition boundary.(boundary_caller) stack
        context_boundary old_above below.
    { eapply live_call_partition_change_active. exact Hold_partition. }
    have Howned_old :
      In Loc
        (live_capability_set CT h boundary.(boundary_caller) old_above)
        owned.
    { eapply authority_call_push_live_capability_included_in_caller.
      exact Howned. }
    assert (Hcaller_origin :
      exists caller_capability,
        In Loc
          (live_capability_set CT h context_boundary.(boundary_caller) below)
          caller_capability /\
        authority_color_connected CT h boundary.(boundary_caller) stack
          caller_capability common).
    { destruct (authority_color_connected_after_call_push CT h boundary stack
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        capability common Hcapability_common) as
        [Hold_path | [Hentry Hattachment]].
      - exists capability. split; assumption.
      - destruct Hentry as
          [entry_anchor [Hentry_anchor Hcapability_entry]].
        destruct Hattachment as
          [attachment_anchor [Hattachment_anchor Hattachment_common]].
        destruct boundary.(boundary_receiver_view) eqn:Hview;
          unfold boundary_view_anchor in
            Hentry_anchor, Hattachment_anchor;
          rewrite Hview in Hentry_anchor, Hattachment_anchor;
          simpl in Hentry_anchor, Hattachment_anchor.
        + have Hentry_owned :
            In Loc
              (live_capability_set CT h boundary.(boundary_caller) old_above)
              entry_anchor.
          { eapply typed_mut_root_is_live_capability.
            exact Hentry_anchor. }
          exfalso.
          apply (Hpending context_boundary old_above below capability
            entry_anchor Hold_partition' Hentry_free Hentry_owned
            Hcapability entry_anchor).
          split; [exact Hcapability_entry|apply rt_refl].
        + have Hcapability_global :
            In Loc
              (live_capability_set CT h boundary.(boundary_caller) stack)
              capability.
          { eapply live_call_partition_caller_capability_is_live; eauto. }
          have Hcapability_runtime :=
            live_capability_members_runtime_mutable CT h
              boundary.(boundary_caller) stack Hframes Hsound capability
              Hcapability_global.
          have Hanchor_immutable :=
            typed_imm_root_runtime_immutable CT
              boundary.(boundary_caller).(frame_senv)
              boundary.(boundary_caller).(frame_renv) h entry_anchor
              (proj1 Hframes) Hentry_anchor.
          have Hheap : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
          have Hanchor_runtime :=
            authority_color_connected_preserves_runtime_mutability CT h
              boundary.(boundary_caller) stack capability entry_anchor Mut_r
              Hframes Hheap Hcapability_entry Hcapability_runtime.
          congruence.
        + exists capability. split; [exact Hcapability|].
          eapply authority_color_connected_trans;
            [exact Hcapability_entry|].
          eapply authority_color_connected_trans.
          * apply rt_step. right.
            exists boundary.(boundary_caller).
            split; [constructor|].
            split; [exact Hentry_anchor|exact Hattachment_anchor].
          * exact Hattachment_common.
        + contradiction.
        + contradiction.
        + contradiction. }
    assert (Howned_origin :
      exists owned_capability,
        In Loc
          (live_capability_set CT h boundary.(boundary_caller) old_above)
          owned_capability /\
        authority_color_connected CT h boundary.(boundary_caller) stack
          owned_capability common).
    { destruct (authority_color_connected_after_call_push CT h boundary stack
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        owned common Howned_common) as
        [Hold_path | [Hentry Hattachment]].
      - exists owned. split; assumption.
      - destruct Hentry as
          [entry_anchor [Hentry_anchor Howned_entry]].
        destruct Hattachment as
          [attachment_anchor [Hattachment_anchor Hattachment_common]].
        destruct boundary.(boundary_receiver_view) eqn:Hview;
          unfold boundary_view_anchor in
            Hentry_anchor, Hattachment_anchor;
          rewrite Hview in Hentry_anchor, Hattachment_anchor;
          simpl in Hentry_anchor, Hattachment_anchor.
        + exists attachment_anchor. split.
          * eapply typed_mut_root_is_live_capability.
            exact Hattachment_anchor.
          * exact Hattachment_common.
        + have Howned_global :
            In Loc
              (live_capability_set CT h boundary.(boundary_caller) stack)
              owned.
          { eapply live_call_partition_above_capability_is_live;
              [exact Hold_partition'|exact Howned_old]. }
          have Howned_runtime :=
            live_capability_members_runtime_mutable CT h
              boundary.(boundary_caller) stack Hframes Hsound owned
              Howned_global.
          have Hanchor_immutable :=
            typed_imm_root_runtime_immutable CT
              boundary.(boundary_caller).(frame_senv)
              boundary.(boundary_caller).(frame_renv) h entry_anchor
              (proj1 Hframes) Hentry_anchor.
          have Hheap : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
          have Hanchor_runtime :=
            authority_color_connected_preserves_runtime_mutability CT h
              boundary.(boundary_caller) stack owned entry_anchor Mut_r
              Hframes Hheap Howned_entry Howned_runtime.
          congruence.
        + exists owned. split; [exact Howned_old|].
          eapply authority_color_connected_trans; [exact Howned_entry|].
          eapply authority_color_connected_trans.
          * apply rt_step. right.
            exists boundary.(boundary_caller).
            split; [constructor|].
            split; [exact Hentry_anchor|exact Hattachment_anchor].
          * exact Hattachment_common.
        + contradiction.
        + contradiction.
        + contradiction. }
    destruct Hcaller_origin as
      [caller_capability [Hcaller_capability Hcaller_common]].
    destruct Howned_origin as
      [owned_capability [Howned_capability Howned_common_old]].
    apply (Hpending context_boundary old_above below caller_capability
      owned_capability Hold_partition' Hentry_free Howned_capability
      Hcaller_capability common).
    split; [exact Hroot|exact Hroot_path].
Qed.
*)

Lemma pending_call_authority_colors_enter_call :
  forall CT h boundary stack,
    live_frames_wf CT h boundary.(boundary_caller) stack ->
    live_frames_authority_sound h boundary.(boundary_caller) stack ->
    pending_call_authority_colors_separated CT h
      boundary.(boundary_caller) stack ->
    pending_call_authority_colors_separated CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack).
Proof.
  intros CT h boundary stack Hframes Hsound Hpending context_boundary above
    below capability owned Hpartition Hentry_free Howned Hcapability
    Hconnected.
  inversion Hpartition as
    [new_boundary new_below
    |new_head new_tail old_boundary old_above old_below Hold_partition];
    subst.
  - destruct Howned as
      [root [[Hactive_root | [suspended [Hin _]]] Hreach]].
    + exact ((proj1 Hentry_free) root Hactive_root).
    + inversion Hin.
  - have Hold_partition' :
      live_call_partition boundary.(boundary_caller) stack
        context_boundary old_above below.
    { eapply live_call_partition_change_active. exact Hold_partition. }
    have Howned_old :
      In Loc
        (live_capability_set CT h boundary.(boundary_caller) old_above)
        owned.
    { eapply authority_call_push_live_capability_included_in_caller.
      exact Howned. }
    destruct (authority_color_connected_after_call_push CT h boundary stack
      (call_authority boundary.(boundary_caller).(frame_authority)
        boundary.(boundary_receiver_view))
      capability owned Hconnected) as
      [Hold_path | [Hentry Hattachment]].
    + exact (Hpending context_boundary old_above below capability owned
        Hold_partition' Hentry_free Howned_old Hcapability Hold_path).
    + destruct Hentry as
        [entry_anchor [Hentry_anchor Hcapability_entry]].
      destruct Hattachment as
        [attachment_anchor [Hattachment_anchor Hattachment_owned]].
      destruct boundary.(boundary_receiver_view) eqn:Hview;
        unfold boundary_view_anchor in Hentry_anchor, Hattachment_anchor;
        rewrite Hview in Hentry_anchor, Hattachment_anchor;
        simpl in Hentry_anchor, Hattachment_anchor.
      * have Hentry_owned :
          In Loc
            (live_capability_set CT h boundary.(boundary_caller) old_above)
            entry_anchor.
        { eapply typed_mut_root_is_live_capability.
          exact Hentry_anchor. }
        exact (Hpending context_boundary old_above below capability
          entry_anchor Hold_partition' Hentry_free Hentry_owned Hcapability
          Hcapability_entry).
      * have Hcapability_global :
          In Loc
            (live_capability_set CT h boundary.(boundary_caller) stack)
            capability.
        { eapply live_call_partition_caller_capability_is_live; eauto. }
        have Hcapability_runtime :=
          live_capability_members_runtime_mutable CT h
            boundary.(boundary_caller) stack Hframes Hsound capability
            Hcapability_global.
        have Hanchor_immutable :=
          typed_imm_root_runtime_immutable CT
            boundary.(boundary_caller).(frame_senv)
            boundary.(boundary_caller).(frame_renv) h entry_anchor
            (proj1 Hframes) Hentry_anchor.
        have Hheap : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
        have Hanchor_runtime :=
          authority_color_connected_preserves_runtime_mutability CT h
            boundary.(boundary_caller) stack capability entry_anchor Mut_r
            Hframes Hheap Hcapability_entry Hcapability_runtime.
        congruence.
      * apply (Hpending context_boundary old_above below capability owned
          Hold_partition' Hentry_free Howned_old Hcapability).
        eapply authority_color_connected_trans;
          [exact Hcapability_entry|].
        eapply authority_color_connected_trans.
        -- apply rt_step. right.
           exists boundary.(boundary_caller).
           split; [constructor|].
           split; [exact Hentry_anchor|exact Hattachment_anchor].
        -- exact Hattachment_owned.
      * contradiction.
      * contradiction.
      * contradiction.
Qed.

Lemma ownership_frame_edge_after_call_push_is_old :
  forall CT h boundary stack left right,
    ownership_frame_edge CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    ownership_frame_edge CT h boundary.(boundary_caller) stack left right.
Proof.
  intros CT h boundary stack left right
    [frame [Hlive [Hleft Hright]]].
  inversion Hlive; subst.
  - exists boundary.(boundary_caller). split; [constructor|].
    split.
    + destruct Hleft as [root [Hroot Hreach]].
      exists root. split.
      * exact (boundary_capability_origins boundary root Hroot).
      * exact Hreach.
    + destruct Hright as [root [Hroot Hreach]].
      exists root. split.
      * exact (boundary_capability_origins boundary root Hroot).
      * exact Hreach.
  - simpl in H. destruct H as [Heq | Hin].
    + subst boundary0. exists boundary.(boundary_caller).
      split; [constructor|]. split; assumption.
    + exists boundary0.(boundary_caller).
      split; [constructor; exact Hin|]. split; assumption.
Qed.

Lemma call_push_live_capability_included_in_caller :
  forall CT h boundary above location,
    In Loc
      (live_capability_set CT h
        (mk_watched_frame
          (call_authority boundary.(boundary_caller).(frame_authority)
            boundary.(boundary_receiver_view))
          boundary.(boundary_callee_entry_senv)
          boundary.(boundary_callee_entry_renv))
        (boundary :: above)) location ->
    In Loc
      (live_capability_set CT h boundary.(boundary_caller) above) location.
Proof.
  intros CT h boundary above location
    [root [[Hactive | [suspended [Hin Hsuspended]]] Hreach]].
  - exists root. split; [left|exact Hreach].
    exact (boundary_capability_origins boundary root Hactive).
  - simpl in Hin. destruct Hin as [Heq | Hin].
    + subst suspended. exists root. split; [left; exact Hsuspended|exact Hreach].
    + exists root. split.
      * right. exists suspended. split; assumption.
      * exact Hreach.
Qed.

Lemma boundary_adjacent_after_call_push :
  forall CT h boundary stack left right,
    boundary_adjacent CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    boundary_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_color_entry CT h boundary stack left /\
     boundary_color_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack left right
    [Hpotential | Hownership].
  - destruct (potential_adjacent_after_call_push CT h boundary stack
      (call_authority boundary.(boundary_caller).(frame_authority)
        boundary.(boundary_receiver_view))
      left right Hpotential) as
      [Hold | [Hentry Hattachment]].
    + left. apply potential_connected_is_boundary_connected. exact Hold.
    + right. split.
      * apply boundary_view_entry_is_color_entry. exact Hentry.
      * apply boundary_view_attachment_is_color_attachment. exact Hattachment.
  - left. apply rt_step. right.
    eapply ownership_frame_edge_after_call_push_is_old; eauto.
Qed.

Lemma boundary_connected_after_call_push :
  forall CT h boundary stack left right,
    boundary_connected CT h
      (mk_watched_frame
        (call_authority boundary.(boundary_caller).(frame_authority)
          boundary.(boundary_receiver_view))
        boundary.(boundary_callee_entry_senv)
        boundary.(boundary_callee_entry_renv))
      (boundary :: stack) left right ->
    boundary_connected CT h boundary.(boundary_caller) stack left right \/
    (boundary_color_entry CT h boundary stack left /\
     boundary_color_attachment CT h boundary stack right).
Proof.
  intros CT h boundary stack left right Hconnected.
  induction Hconnected.
  - eapply boundary_adjacent_after_call_push; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as [Hxy | [Hentry_x Hattach_y]];
      destruct IHHconnected2 as [Hyz | [Hentry_y Hattach_z]].
    + left. eapply rt_trans; eauto.
    + right. split.
      * eapply boundary_color_entry_transport; eauto.
      * exact Hattach_z.
    + right. split.
      * exact Hentry_x.
      * eapply boundary_color_attachment_transport; eauto.
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

Lemma authority_color_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    authority_color_live_history_state CT P Z cutoff
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
      authority_color_live_history_state CT P Z cutoff
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
    [Hlive [Hcolors Hcutoffs]]
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
  split; [exact Hlive_post|]. split.
  - set (caller := mk_watched_frame caller_authority sGamma rGamma).
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
        Hwf Htyping Hscope Hgety Hvalue Hbase Hfind Hargs)).
      exact Hcapability. }
    destruct (authority_color_connected_after_call_push CT h boundary stack
      (call_authority caller_authority (sqtype Ty)) capability protected
      Hconnected) as
      [Hold_connected |
        [Hcapability_entry Hprotected_attachment]].
    + unfold caller in Hcapability_old, Hold_connected |- *.
      exact (Hcolors capability protected Hcapability_old Hprotected
        Hold_connected).
    + destruct (sqtype Ty) eqn:Hview.
      * destruct Hprotected_attachment as
          [zone_anchor [Hzone_anchor Hzone_connected]].
        unfold boundary_view_anchor in Hzone_anchor.
        unfold boundary in Hzone_anchor, Hzone_connected. simpl in *.
        have Hzone_capability : In Loc
            (live_capability_set CT h caller stack) zone_anchor.
        { unfold caller. eapply typed_mut_root_is_live_capability; eauto. }
        unfold caller in Hzone_capability, Hzone_connected.
        exact (Hcolors zone_anchor protected Hzone_capability Hprotected
          Hzone_connected).
      * destruct Hcapability_entry as
          [capability_anchor [Hcapability_anchor Hanchor_connected]].
        unfold boundary_view_anchor in Hcapability_anchor.
        unfold boundary in Hcapability_anchor, Hanchor_connected. simpl in *.
        have Hcapability_runtime :=
          live_capability_members_runtime_mutable CT h caller stack Hframes
            Hsound capability Hcapability_old.
        have Hanchor_immutable := typed_imm_root_runtime_immutable CT sGamma
          rGamma h capability_anchor Hwf Hcapability_anchor.
        have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
        have Hanchor_runtime :=
          authority_color_connected_preserves_runtime_mutability CT h caller
            stack capability capability_anchor Mut_r Hframes Hheap_wf
            Hanchor_connected Hcapability_runtime.
        congruence.
      * destruct Hcapability_entry as
          [capability_anchor
            [Hcapability_anchor Hcapability_connected]].
        destruct Hprotected_attachment as
          [zone_anchor [Hzone_anchor Hzone_connected]].
        unfold boundary_view_anchor in Hcapability_anchor, Hzone_anchor.
        unfold boundary in Hcapability_anchor, Hzone_anchor,
          Hcapability_connected, Hzone_connected. simpl in *.
        unfold caller in Hcapability_old, Hcapability_connected,
          Hzone_connected.
        apply (Hcolors capability protected Hcapability_old Hprotected).
        eapply authority_color_connected_trans.
        -- exact Hcapability_connected.
        -- eapply authority_color_connected_trans.
           ++ apply rt_step. right.
              exists (mk_watched_frame caller_authority sGamma rGamma).
              split; [constructor|].
              split; [exact Hcapability_anchor|exact Hzone_anchor].
           ++ exact Hzone_connected.
      * destruct Hcapability_entry as
          [anchor [Hanchor Hanchor_connected]].
        unfold boundary_view_anchor in Hanchor.
        unfold boundary in Hanchor. simpl in Hanchor. contradiction.
      * destruct Hcapability_entry as
          [anchor [Hanchor Hanchor_connected]].
        unfold boundary_view_anchor in Hanchor.
        unfold boundary in Hanchor. simpl in Hanchor. contradiction.
      * destruct Hcapability_entry as
          [anchor [Hanchor Hanchor_connected]].
        unfold boundary_view_anchor in Hanchor.
        unfold boundary in Hanchor. simpl in Hanchor. contradiction.
  - constructor.
    + simpl. lia.
    + exact Hcutoffs.
Qed.

Lemma principled_authority_color_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty tracked_depth,
    principled_authority_color_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack tracked_depth
      h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      principled_authority_color_live_history_state CT P Z cutoff
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
          stack) (S tracked_depth) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty tracked_depth
    [Hstate Hpending] Htyping Hscope Hgety Hvalue Hbase Hfind Hargs.
  destruct (authority_color_history_enter_call CT P Z cutoff
    caller_authority sGamma mt rGamma h stack x method y args sGamma' vals
    ly cy runtime_mdef Ty Hstate Htyping Hscope Hgety Hvalue Hbase Hfind
    Hargs) as
    [origins [destination_type [Hdestination Hpost]]].
  exists origins, destination_type. split; [exact Hdestination|].
  split; [exact Hpost|].
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  set (boundary := mk_watched_call_boundary caller callee_senv callee_renv
    (sqtype Ty) (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  have Hlive := proj1 Hstate.
  have Hframes : live_frames_wf CT h caller stack.
  { unfold caller. exact (proj1 (proj2 Hlive)). }
  have Hsound : live_frames_authority_sound h caller stack.
  { unfold caller. exact (proj1 (proj2 (proj2 Hlive))). }
  apply (pending_call_stateful_authority_enter_call CT h boundary stack
    tracked_depth).
  - unfold boundary. simpl. exact Hframes.
  - unfold boundary. simpl. exact Hsound.
  - unfold boundary. simpl.
    exact (proj1 (proj2 (proj1 Hpost))).
  - unfold boundary. simpl. exact Hpending.
Qed.

Lemma principled_potential_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_potential_live_history_state CT P Z cutoff
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
      principled_potential_live_history_state CT P Z cutoff
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
    [Hstate Hpending] Htyping Hscope Hgety Hvalue Hbase Hfind Hargs.
  destruct (potential_history_enter_call CT P Z cutoff caller_authority
    sGamma mt rGamma h stack x method y args sGamma' vals ly cy
    runtime_mdef Ty Hstate Htyping Hscope Hgety Hvalue Hbase Hfind Hargs)
    as [origins [destination_type [Hdestination Hpost]]].
  exists origins, destination_type. split; [exact Hdestination|].
  split; [exact Hpost|].
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  set (boundary := mk_watched_call_boundary caller callee_senv callee_renv
    (sqtype Ty) (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  have Hlive := proj1 Hstate.
  have Hframes : live_frames_wf CT h caller stack.
  { unfold caller. exact (proj1 (proj2 Hlive)). }
  have Hsound : live_frames_authority_sound h caller stack.
  { unfold caller. exact (proj1 (proj2 (proj2 Hlive))). }
  have Hheap : wf_heap CT h := proj1 (proj2 (proj1 Hframes)).
  intros context_boundary above below capability owned Hpartition
    Hentry_empty Howned Hcapability.
  inversion Hpartition as
    [new_boundary new_below
    |new_head new_tail old_boundary old_above old_below Hold_partition];
    subst.
  - destruct Howned as
      [root [[Hactive_root | [suspended [Hin _]]] Hreach]].
    + exfalso. exact ((proj1 Hentry_empty) root Hactive_root).
    + inversion Hin.
  - have Hold_partition' :
        live_call_partition caller stack
          context_boundary old_above below.
    { eapply live_call_partition_change_active.
      exact Hold_partition. }
    have Howned_old :
        In Loc
          (live_capability_set CT h caller old_above) owned.
    { change (In Loc
        (live_capability_set CT h boundary.(boundary_caller) old_above)
        owned).
      eapply call_push_live_capability_included_in_caller.
      change (In Loc
        (live_capability_set CT h
          (mk_watched_frame
            (call_authority boundary.(boundary_caller).(frame_authority)
              boundary.(boundary_receiver_view))
            boundary.(boundary_callee_entry_senv)
            boundary.(boundary_callee_entry_renv))
          (boundary :: old_above)) owned) in Howned.
      exact Howned. }
    (*
    Temporary two-direction formulation, superseded by forward-cone
    disjointness.
    split; intros Hconnected.
    + destruct (potential_connected_after_call_push CT h boundary stack
        (call_authority caller_authority (sqtype Ty))
        capability owned Hconnected) as
        [Hold_connected | [Hentry Hattachment]].
      * exact (proj1 (Hpending context_boundary old_above below
          capability owned Hold_partition' Hentry_empty Howned_old
          Hcapability) Hold_connected).
      * destruct Hentry as
        [entry_anchor [Hentry_anchor Hcapability_entry]].
        destruct Hattachment as
        [attachment_anchor [Hattachment_anchor Hattachment_owned]].
        destruct (sqtype Ty) eqn:Hview;
        unfold boundary_view_anchor in
          Hentry_anchor, Hattachment_anchor;
        unfold boundary in
          Hentry_anchor, Hattachment_anchor,
          Hcapability_entry, Hattachment_owned;
        simpl in *.
        -- have Hentry_owned :
               In Loc (live_capability_set CT h caller old_above)
                 entry_anchor.
           { unfold caller.
             eapply typed_mut_root_is_live_capability. exact Hentry_anchor. }
           exact (proj1 (Hpending context_boundary old_above below
             capability entry_anchor Hold_partition' Hentry_empty
             Hentry_owned Hcapability) Hcapability_entry).
        -- have Hcapability_overall :
          In Loc (live_capability_set CT h caller stack) capability.
        { eapply live_call_partition_caller_capability_is_live; eauto. }
        have Hcapability_runtime :=
          live_capability_members_runtime_mutable CT h caller stack Hframes
            Hsound capability Hcapability_overall.
        have Hanchor_immutable := typed_imm_root_runtime_immutable CT sGamma
          rGamma h entry_anchor (proj1 Hframes) Hentry_anchor.
        have Hanchor_runtime :=
          potential_connected_preserves_runtime_mutability CT h caller stack
            capability entry_anchor Mut_r Hframes Hheap
            Hcapability_entry Hcapability_runtime.
           rewrite Hanchor_immutable in Hanchor_runtime. discriminate.
        -- apply (proj1 (Hpending context_boundary old_above below
             capability owned Hold_partition' Hentry_empty Howned_old
             Hcapability)).
        eapply rt_trans; [exact Hcapability_entry|].
        eapply rt_trans.
        --- eapply live_frame_rdm_roots_potentially_connected
             with (frame := caller).
            +++ constructor.
            +++ exact Hentry_anchor.
            +++ exact Hattachment_anchor.
        --- exact Hattachment_owned.
        -- contradiction.
        -- contradiction.
        -- contradiction.
    + destruct (potential_connected_after_call_push CT h boundary stack
        (call_authority caller_authority (sqtype Ty))
        owned capability Hconnected) as
        [Hold_connected | [Hentry Hattachment]].
      * exact (proj2 (Hpending context_boundary old_above below
          capability owned Hold_partition' Hentry_empty Howned_old
          Hcapability) Hold_connected).
      * destruct Hentry as
          [entry_anchor [Hentry_anchor Howned_entry]].
        destruct Hattachment as
          [attachment_anchor
            [Hattachment_anchor Hattachment_capability]].
        destruct (sqtype Ty) eqn:Hview;
          unfold boundary_view_anchor in
            Hentry_anchor, Hattachment_anchor;
          unfold boundary in
            Hentry_anchor, Hattachment_anchor,
            Howned_entry, Hattachment_capability;
          simpl in *.
        -- have Hattachment_owned :
               In Loc (live_capability_set CT h caller old_above)
                 attachment_anchor.
           { unfold caller.
             eapply typed_mut_root_is_live_capability.
             exact Hattachment_anchor. }
           exact (proj2 (Hpending context_boundary old_above below
             capability attachment_anchor Hold_partition' Hentry_empty
             Hattachment_owned Hcapability) Hattachment_capability).
        -- have Hcapability_overall :
               In Loc (live_capability_set CT h caller stack) capability.
           { eapply live_call_partition_caller_capability_is_live; eauto. }
           have Hcapability_runtime :=
             live_capability_members_runtime_mutable CT h caller stack
               Hframes Hsound capability Hcapability_overall.
           have Hanchor_immutable :=
             typed_imm_root_runtime_immutable CT sGamma rGamma h
               attachment_anchor (proj1 Hframes) Hattachment_anchor.
           have Hanchor_runtime :=
             potential_connected_reflects_runtime_mutability CT h caller
               stack attachment_anchor capability Mut_r Hframes Hheap
               Hattachment_capability Hcapability_runtime.
           rewrite Hanchor_immutable in Hanchor_runtime. discriminate.
        -- apply (proj2 (Hpending context_boundary old_above below
             capability owned Hold_partition' Hentry_empty Howned_old
             Hcapability)).
           eapply rt_trans; [exact Howned_entry|].
           eapply rt_trans.
           --- eapply live_frame_rdm_roots_potentially_connected
                 with (frame := caller).
               +++ constructor.
               +++ exact Hentry_anchor.
               +++ exact Hattachment_anchor.
           --- exact Hattachment_capability.
        -- contradiction.
        -- contradiction.
        -- contradiction.
    *)
    intros common [Hcapability_common Howned_common].
    assert (Hcaller_origin :
      exists caller_capability,
        In Loc
          (live_capability_set CT h context_boundary.(boundary_caller) below)
          caller_capability /\
        potential_connected CT h caller stack caller_capability common).
    { destruct (potential_connected_after_call_push CT h boundary stack
        (call_authority caller_authority (sqtype Ty))
        capability common Hcapability_common) as
        [Hold_path | [Hentry Hattachment]].
      - exists capability. split; [exact Hcapability|exact Hold_path].
      - destruct Hentry as
          [entry_anchor [Hentry_anchor Hcapability_entry]].
        destruct Hattachment as
          [attachment_anchor [Hattachment_anchor Hattachment_common]].
        destruct (sqtype Ty) eqn:Hview;
          unfold boundary_view_anchor in
            Hentry_anchor, Hattachment_anchor;
          unfold boundary in
            Hentry_anchor, Hattachment_anchor,
            Hcapability_entry, Hattachment_common;
          simpl in *.
        + have Hentry_owned :
              In Loc (live_capability_set CT h caller old_above)
                entry_anchor.
          { unfold caller. eapply typed_mut_root_is_live_capability.
            exact Hentry_anchor. }
          exfalso.
          apply (Hpending context_boundary old_above below capability
            entry_anchor Hold_partition' Hentry_empty Hentry_owned
            Hcapability entry_anchor).
          split; [exact Hcapability_entry|apply rt_refl].
        + have Hcapability_overall :
              In Loc (live_capability_set CT h caller stack) capability.
          { eapply live_call_partition_caller_capability_is_live; eauto. }
          have Hcapability_runtime :=
            live_capability_members_runtime_mutable CT h caller stack Hframes
              Hsound capability Hcapability_overall.
          have Hanchor_immutable := typed_imm_root_runtime_immutable CT sGamma
            rGamma h entry_anchor (proj1 Hframes) Hentry_anchor.
          have Hanchor_runtime :=
            potential_connected_preserves_runtime_mutability CT h caller stack
              capability entry_anchor Mut_r Hframes Hheap
              Hcapability_entry Hcapability_runtime.
          rewrite Hanchor_immutable in Hanchor_runtime. discriminate.
        + exists capability. split; [exact Hcapability|].
          eapply rt_trans; [exact Hcapability_entry|].
          eapply rt_trans.
          * eapply live_frame_rdm_roots_potentially_connected
              with (frame := caller).
            -- constructor.
            -- exact Hentry_anchor.
            -- exact Hattachment_anchor.
          * exact Hattachment_common.
        + contradiction.
        + contradiction.
        + contradiction. }
    assert (Hcallee_origin :
      exists callee_capability,
        In Loc (live_capability_set CT h caller old_above)
          callee_capability /\
        potential_connected CT h caller stack callee_capability common).
    { destruct (potential_connected_after_call_push CT h boundary stack
        (call_authority caller_authority (sqtype Ty))
        owned common Howned_common) as
        [Hold_path | [Hentry Hattachment]].
      - exists owned. split; [exact Howned_old|exact Hold_path].
      - destruct Hentry as
          [entry_anchor [Hentry_anchor Howned_entry]].
        destruct Hattachment as
          [attachment_anchor [Hattachment_anchor Hattachment_common]].
        destruct (sqtype Ty) eqn:Hview;
          unfold boundary_view_anchor in
            Hentry_anchor, Hattachment_anchor;
          unfold boundary in
            Hentry_anchor, Hattachment_anchor,
            Howned_entry, Hattachment_common;
          simpl in *.
        + exists attachment_anchor. split.
          * unfold caller. eapply typed_mut_root_is_live_capability.
            exact Hattachment_anchor.
          * exact Hattachment_common.
        + have Howned_overall :
              In Loc (live_capability_set CT h caller stack) owned.
          { apply live_capability_iff_live_frame_owned in Howned_old.
            destruct Howned_old as [frame [Hframe_live Hframe_owned]].
            apply live_capability_iff_live_frame_owned.
            exists frame. split.
            - eapply live_call_partition_above_frame_is_live; eauto.
            - exact Hframe_owned. }
          have Howned_runtime :=
            live_capability_members_runtime_mutable CT h caller stack Hframes
              Hsound owned Howned_overall.
          have Hanchor_immutable := typed_imm_root_runtime_immutable CT sGamma
            rGamma h entry_anchor (proj1 Hframes) Hentry_anchor.
          have Hanchor_runtime :=
            potential_connected_preserves_runtime_mutability CT h caller stack
              owned entry_anchor Mut_r Hframes Hheap Howned_entry
              Howned_runtime.
          rewrite Hanchor_immutable in Hanchor_runtime. discriminate.
        + exists owned. split; [exact Howned_old|].
          eapply rt_trans; [exact Howned_entry|].
          eapply rt_trans.
          * eapply live_frame_rdm_roots_potentially_connected
              with (frame := caller).
            -- constructor.
            -- exact Hentry_anchor.
            -- exact Hattachment_anchor.
          * exact Hattachment_common.
        + contradiction.
        + contradiction.
        + contradiction. }
    destruct Hcaller_origin as
      [caller_capability [Hcaller_capability Hcaller_common]].
    destruct Hcallee_origin as
      [callee_capability [Hcallee_capability Hcallee_common]].
    apply (Hpending context_boundary old_above below caller_capability
      callee_capability Hold_partition' Hentry_empty Hcallee_capability
      Hcaller_capability common).
    split; assumption.
Qed.

(** A non-null result stored in an RDM caller destination can only arise from
    an RDM body result viewed through an RDM receiver. *)
Lemma safe_call_rdm_result_reflects_to_body_return :
  forall receiver_q body_return_q declared_return_q result_q,
    q_subtype body_return_q declared_return_q ->
    q_subtype (vpa_mutability_qq_readonly_state receiver_q declared_return_q)
      result_q ->
    receiver_q <> Bot ->
    body_return_q <> Bot ->
    result_q = RDM ->
    receiver_q = RDM /\ body_return_q = RDM.
Proof.
  intros receiver_q body_return_q declared_return_q result_q Hbody Hresult
    Hreceiver_nonbottom Hbody_nonbottom Hresult_rdm.
  subst result_q.
  destruct receiver_q, body_return_q, declared_return_q; simpl in *;
    try contradiction;
    repeat match goal with
    | H : q_subtype _ _ |- _ => inversion H; subst; clear H
    end;
    try solve [split; reflexivity | contradiction | congruence].
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

Lemma safe_signature_immutable_frame_has_no_live_capability :
  forall CT h msig rGamma location,
    signature_has_no_mutable_roots msig ->
    ~ In Loc
        (live_capability_set CT h
          (mk_watched_frame Imm_r
            (mreceiver msig :: mparams msig) rGamma) [])
        location.
Proof.
  intros CT h msig rGamma location Hsafe
    [root [[Hactive | [boundary [Hin _]]] Hreachable]].
  - destruct Hactive as
      [variable [T [Htype [Hvalue Hcapability]]]].
    unfold capability_in_context in Hcapability.
    destruct Hcapability as [Hmut | [Hrdm Hauthority]];
      [|discriminate].
    destruct Hsafe as [Hreceiver_safe Hparameters_safe].
    destruct variable as [|parameter].
    + simpl in Htype. injection Htype as <-.
      unfold is_nonmutable_qualifier in Hreceiver_safe.
      rewrite Hmut in Hreceiver_safe.
      destruct Hreceiver_safe as
        [Hbad | [Hbad | [Hbad | Hbad]]]; discriminate.
    + simpl in Htype. unfold static_getType in Htype.
      have Hparameter_safe :
          is_nonmutable_qualifier (sqtype T).
      { exact (Forall_nth_error _ _ _ _ Hparameters_safe Htype). }
      unfold is_nonmutable_qualifier in Hparameter_safe.
      rewrite Hmut in Hparameter_safe.
      destruct Hparameter_safe as
        [Hbad | [Hbad | [Hbad | Hbad]]]; discriminate.
  - contradiction.
Qed.

Lemma safe_signature_immutable_frame_has_no_capability_root :
  forall msig rGamma root,
    signature_has_no_mutable_roots msig ->
    ~ frame_capability_root
        (mk_watched_frame Imm_r
          (mreceiver msig :: mparams msig) rGamma) root.
Proof.
  intros msig rGamma root Hsafe Hroot.
  eapply (safe_signature_immutable_frame_has_no_live_capability
    [] [] msig rGamma root Hsafe).
  exists root. split; [left; exact Hroot|constructor].
Qed.

(** The flexible RDM-to-Mut refinement gives a stronger entry fact than
    immutable authority alone: the dynamic frame has neither mutable nor RDM
    roots.  Consequently it has no capability root under either runtime
    authority. *)
Lemma safe_signature_without_rdm_has_no_capability_root :
  forall msig rGamma authority root,
    signature_has_no_mutable_roots msig ->
    (forall location,
      ~ typed_root RDM (mreceiver msig :: mparams msig) rGamma location) ->
    ~ frame_capability_root
        (mk_watched_frame authority
          (mreceiver msig :: mparams msig) rGamma) root.
Proof.
  intros msig rGamma authority root [Hreceiver_safe Hparams_safe] Hno_rdm
    [variable [T [Htype [Hvalue Hcapability]]]].
  unfold capability_in_context in Hcapability.
  destruct Hcapability as [Hmut | [Hrdm Hauthority]].
  - destruct variable as [|parameter].
    + simpl in Htype. injection Htype as <-.
      unfold is_nonmutable_qualifier in Hreceiver_safe.
      rewrite Hmut in Hreceiver_safe.
      destruct Hreceiver_safe as
        [Hbad | [Hbad | [Hbad | Hbad]]]; discriminate.
    + simpl in Htype. unfold static_getType in Htype.
      have Hparameter_safe : is_nonmutable_qualifier (sqtype T).
      { exact (Forall_nth_error _ _ _ _ Hparams_safe Htype). }
      unfold is_nonmutable_qualifier in Hparameter_safe.
      rewrite Hmut in Hparameter_safe.
      destruct Hparameter_safe as
        [Hbad | [Hbad | [Hbad | Hbad]]]; discriminate.
  - apply (Hno_rdm root).
    exists variable, T. repeat split; assumption.
Qed.

Lemma channel_free_boundary_from_safe_signature_without_rdm :
  forall caller receiver_view msig rGamma return_var result_q return_q
    entry_cutoff origins,
    signature_has_no_mutable_roots msig ->
    (forall location,
      ~ typed_root RDM (mreceiver msig :: mparams msig) rGamma location) ->
    entry_ownership_channel_free
      (mk_watched_call_boundary caller
        (mreceiver msig :: mparams msig) rGamma receiver_view return_var
        result_q return_q entry_cutoff origins).
Proof.
  intros caller receiver_view msig rGamma return_var result_q return_q
    entry_cutoff origins Hsafe Hno_rdm.
  split.
  - intros root Hroot.
    eapply safe_signature_without_rdm_has_no_capability_root
      with (msig := msig) (rGamma := rGamma)
        (authority := call_authority caller.(frame_authority) receiver_view)
        (root := root); eauto.
  - exact Hno_rdm.
Qed.

(** Confinement is directional, but an execution cannot create the reverse
    half of an RDM-component edge from an old unreachable object into the
    fresh part of the heap.  Such an old source object is unchanged, and the
    initial well-formed heap could not already contain a pointer to a location
    beyond its domain. *)
Lemma eval_fresh_mutable_adjacent_is_fresh_or_protected :
  forall CT sGamma rGamma h stmt rGamma' h' fresh next,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h stmt OK rGamma' h' ->
    dom h <= fresh ->
    mutable_adjacent CT h' fresh next ->
    dom h <= next \/
    In Loc (reachable_locations_from_initial_env h rGamma) next.
Proof.
  intros CT sGamma rGamma h stmt rGamma' h' fresh next Hwf Heval
    Hfresh [Hforward | Hbackward].
  - have Hinitial := initial_state_is_confined CT sGamma rGamma h Hwf.
    have Hfinal := eval_stmt_preserves_confinement CT rGamma h stmt OK
      rGamma' h' (reachable_locations_from_initial_env h rGamma) (dom h)
      (Nat.le_refl _) Hinitial Heval.
    destruct Hfinal as [_ Hheap].
    have Hraw : raw_heap_edge h' fresh next.
    { inversion Hforward; subst. exists o, f. split; assumption. }
    destruct (Hheap fresh next (ltac:(right; exact Hfresh)) Hraw)
      as [Hreachable | Hnext_fresh].
    + right. exact Hreachable.
    + left. exact Hnext_fresh.
  - destruct (le_lt_dec (dom h) next) as [Hnext_fresh | Hnext_old].
    + left. exact Hnext_fresh.
    + destruct (reachable_locations_from_initial_env_dec h rGamma next)
        as [Hnext_protected | Hnext_outside].
      * right. exact Hnext_protected.
      * exfalso.
        inversion Hbackward as
          [source target final_obj field D fdef Hfinal_obj Hfield
            Hbase Hfield_def Hrdm]; subst.
        destruct (runtime_getObj_Some h next ltac:(lia)) as
          [old_type [old_fields Hold_obj]].
        destruct old_type as [old_runtime_q old_class].
        destruct (runtime_preserves_r_type_heap CT rGamma h next
          (mkruntime_type old_runtime_q old_class) h'
          old_fields stmt rGamma' Hold_obj Heval) as
          [final_fields Hfinal_same_type].
        rewrite Hfinal_obj in Hfinal_same_type.
        injection Hfinal_same_type as Hfinal_fields.
        subst final_obj.
        have Hfields_unchanged := confined_eval_preserves_old_object CT
          rGamma h stmt rGamma' h'
          (reachable_locations_from_initial_env h rGamma) (dom h) next
          old_class old_runtime_q old_fields final_fields
          (Nat.le_refl _) (initial_state_is_confined CT sGamma rGamma h Hwf)
          Heval Hold_obj Hfinal_obj Hnext_old.
        assert (Hnot_reachable :
          ~ In Loc (reachable_locations_from_initial_env h rGamma) next).
        { exact Hnext_outside. }
        specialize (Hfields_unchanged Hnot_reachable).
        subst final_fields.
        have Hinitial_raw : raw_heap_edge h next fresh.
        { exists (mkObj (mkruntime_type old_runtime_q old_class) old_fields),
            field.
          split; assumption. }
        have Hheap_wf : wf_heap CT h := proj1 (proj2 Hwf).
        have Hfresh_old := wf_raw_edge_target_dom CT h next fresh
          Hheap_wf Hinitial_raw.
        lia.
Qed.

(** Along an undirected RDM component starting in the fresh part of the heap,
    either every endpoint remains fresh or the component reaches the initial
    protected/reachable set.  This is the pop-time provenance fact needed for
    a concrete overriding return; it is derived from evaluation, not assumed
    by the call rule. *)
Lemma eval_fresh_mutable_component_is_fresh_or_protected :
  forall CT sGamma rGamma h stmt rGamma' h' fresh target,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h stmt OK rGamma' h' ->
    dom h <= fresh ->
    mutable_connected CT h' fresh target ->
    dom h <= target \/
    component_touches CT h'
      (reachable_locations_from_initial_env h rGamma) fresh.
Proof.
  intros CT sGamma rGamma h stmt rGamma' h' fresh target Hwf Heval
    Hfresh Hconnected.
  induction Hconnected.
  - destruct (eval_fresh_mutable_adjacent_is_fresh_or_protected CT sGamma
      rGamma h stmt rGamma' h' x y Hwf Heval Hfresh H)
      as [Hy_fresh | Hy_protected].
    + left. exact Hy_fresh.
    + right. exists y. split; [exact Hy_protected|].
      apply rt_step. exact H.
  - left. exact Hfresh.
  - destruct (IHHconnected1 Hfresh) as
      [Hy_fresh | Hfirst_protected].
    + destruct (IHHconnected2 Hy_fresh) as
        [Hz_fresh | [protected [Hprotected Hy_protected]]].
      * left. exact Hz_fresh.
      * right. exists protected. split; [exact Hprotected|].
        eapply mutable_connected_trans; eauto.
    + right. exact Hfirst_protected.
Qed.

(** Local body executions need no caller-visible no-publication premise.
    Evaluation provenance says that a fresh mutable component either remains
    fresh or touches the body's entry-reachable set; final authority
    separation rules out the latter for a powered result. *)
Lemma principled_local_powered_component_is_fresh :
  forall CT sGamma rGamma h statement rGamma' h' active stack incoming
    root target,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    principled_phased_authority_live_history_state CT
      (reachable_locations_from_initial_env h rGamma)
      (reachable_locations_from_initial_env h rGamma) (dom h)
      active stack incoming h' ->
    In authority_flow_state
      (executing_authority_color_set CT h' active incoming)
      (FlowPowered, root) ->
    dom h <= root ->
    mutable_connected CT h' root target ->
    dom h <= target.
Proof.
  intros CT sGamma rGamma h statement rGamma' h' active stack incoming
    root target Hwf Heval Hstate Hroot Hroot_fresh Hconnected.
  destruct (eval_fresh_mutable_component_is_fresh_or_protected CT sGamma
    rGamma h statement rGamma' h' root target Hwf Heval Hroot_fresh
    Hconnected) as [Htarget_fresh | [protected [Hprotected Htouches]]].
  - exact Htarget_fresh.
  - exfalso.
    have Hseparated := proj1 (proj2 (proj2 (proj2 Hstate))).
    destruct (executing_authority_dangerous_mutable_connected CT h' active
      incoming root protected FlowPowered (or_introl eq_refl) Hroot Htouches)
      as [mode [Hmode Hcolored]].
    exact (Hseparated mode protected Hmode Hcolored Hprotected).
Qed.

Lemma principled_local_mut_result_component_is_fresh :
  forall CT sGamma rGamma h statement rGamma' h' active stack incoming
    return_var return_type return_location target,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    principled_phased_authority_live_history_state CT
      (reachable_locations_from_initial_env h rGamma)
      (reachable_locations_from_initial_env h rGamma) (dom h)
      active stack incoming h' ->
    static_getType active.(frame_senv) return_var = Some return_type ->
    runtime_getVal active.(frame_renv) return_var =
      Some (Iot return_location) ->
    sqtype return_type = Mut ->
    mutable_connected CT h' return_location target ->
    dom h <= target.
Proof.
  intros CT sGamma rGamma h statement rGamma' h' active stack incoming
    return_var return_type return_location target Hwf Heval Hstate Htype
    Hvalue Hmut Hconnected.
  have Hroot : typed_root Mut active.(frame_senv) active.(frame_renv)
      return_location.
  { exists return_var, return_type. repeat split; assumption. }
  have Howned : frame_owned_location CT h' active return_location.
  { apply frame_owned_location_iff_active_live.
    eapply typed_mut_root_is_live_capability. exact Hroot. }
  have Hpowered : In authority_flow_state
      (executing_authority_color_set CT h' active incoming)
      (FlowPowered, return_location).
  { eapply executing_authority_owned_is_powered. exact Howned. }
  have Hfresh : dom h <= return_location.
  { eapply principled_phased_local_mut_root_is_fresh with
      (variable := return_var) (T := return_type); eauto. }
  eapply principled_local_powered_component_is_fresh; eauto.
Qed.

Lemma retained_mut_edge_is_raw :
  forall CT h source target,
    retained_mut_edge CT h source target ->
    raw_heap_edge h source target.
Proof.
  intros CT h source target Hedge.
  inversion Hedge.
  - inversion H; subst. exists o, f. split; assumption.
  - exists o, f. split; assumption.
Qed.

(** A new retained edge out of an old object can cross the call-entry heap
    boundary only when that old source was reachable by the callee.  Otherwise
    confinement preserves the source object byte-for-byte, and the initial
    well-formed heap rules out its having pointed to a not-yet-allocated
    location. *)
Lemma eval_old_retained_edge_to_fresh_source_is_reachable :
  forall CT sGamma rGamma h stmt rGamma' h' source target,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h stmt OK rGamma' h' ->
    source < dom h ->
    dom h <= target ->
    retained_mut_edge CT h' source target ->
    In Loc (reachable_locations_from_initial_env h rGamma) source.
Proof.
  intros CT sGamma rGamma h stmt rGamma' h' source target Hwf Heval
    Hsource_old Htarget_fresh Hedge.
  destruct (reachable_locations_from_initial_env_dec h rGamma source)
    as [Hreachable | Hunreachable]; [exact Hreachable|].
  exfalso.
  have Hraw_final := retained_mut_edge_is_raw CT h' source target Hedge.
  destruct Hraw_final as [final_obj [field [Hfinal_obj Hfield]]].
  destruct (runtime_getObj_Some h source Hsource_old) as
    [old_type [old_fields Hold_obj]].
  destruct old_type as [old_runtime_q old_class].
  destruct (runtime_preserves_r_type_heap CT rGamma h source
    (mkruntime_type old_runtime_q old_class) h' old_fields stmt rGamma'
    Hold_obj Heval) as [final_fields Hfinal_same_type].
  rewrite Hfinal_obj in Hfinal_same_type.
  injection Hfinal_same_type as Hfinal_fields.
  subst final_obj.
  have Hfields_unchanged := confined_eval_preserves_old_object CT
    rGamma h stmt rGamma' h'
    (reachable_locations_from_initial_env h rGamma) (dom h) source
    old_class old_runtime_q old_fields final_fields
    (Nat.le_refl _) (initial_state_is_confined CT sGamma rGamma h Hwf)
    Heval Hold_obj Hfinal_obj Hsource_old Hunreachable.
  subst final_fields.
  have Hraw_initial : raw_heap_edge h source target.
  { exists (mkObj (mkruntime_type old_runtime_q old_class) old_fields),
      field.
    split; assumption. }
  have Htarget_old := wf_raw_edge_target_dom CT h source target
    (proj1 (proj2 Hwf)) Hraw_initial.
  lia.
Qed.

(** If a capability rooted in the entry heap gains retained reachability to a
    fresh location, its retained path must pass through the callee's initial
    reachable set. *)
Lemma eval_old_retained_reaches_fresh_passes_initial_reachable :
  forall CT sGamma rGamma h stmt rGamma' h' root target,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h stmt OK rGamma' h' ->
    root < dom h ->
    dom h <= target ->
    retained_mut_reachable CT h' root target ->
    exists reachable,
      In Loc (reachable_locations_from_initial_env h rGamma) reachable /\
      retained_mut_reachable CT h' root reachable.
Proof.
  intros CT sGamma rGamma h stmt rGamma' h' root target Hwf Heval
    Hroot_old Htarget_fresh Hreach.
  induction Hreach.
  - lia.
  - destruct (le_lt_dec (dom h) l2) as [Hmiddle_fresh | Hmiddle_old].
    + eapply IHHreach; eauto.
    + exists l2. split.
      * eapply eval_old_retained_edge_to_fresh_source_is_reachable; eauto.
      * exact Hreach.
Qed.

(** The same crossing argument can retain the suffix of the path.  This is
    the useful direction at call return: once an old live root reaches a fresh
    capability, some location reachable at call entry reaches that capability
    in the final retained graph. *)
Lemma eval_old_retained_reaches_fresh_has_initial_reachable_suffix :
  forall CT sGamma rGamma h stmt rGamma' h' root target,
    wf_r_config CT sGamma rGamma h ->
    eval_stmt CT rGamma h stmt OK rGamma' h' ->
    root < dom h ->
    dom h <= target ->
    retained_mut_reachable CT h' root target ->
    exists reachable,
      In Loc (reachable_locations_from_initial_env h rGamma) reachable /\
      retained_mut_reachable CT h' reachable target.
Proof.
  intros CT sGamma rGamma h stmt rGamma' h' root target Hwf Heval
    Hroot_old Htarget_fresh Hreach.
  induction Hreach as [location | start middle finish Hprefix IH Hedge].
  - lia.
  - destruct (le_lt_dec (dom h) middle) as [Hmiddle_fresh | Hmiddle_old].
    + destruct (IH Hroot_old Hmiddle_fresh) as
        [reachable [Hreachable Hsuffix]].
      exists reachable. split; [exact Hreachable|].
      eapply rmr_step; eauto.
    + exists middle. split.
      * eapply eval_old_retained_edge_to_fresh_source_is_reachable; eauto.
      * eapply rmr_step; [constructor|exact Hedge].
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

(** The stack-wide mutable-RDM freshness package is closed by call return.
    Every RDM root of the resumed caller is either an unchanged suspended
    root, whose component is covered by the body invariant, or the newly
    installed return root, whose component is discharged by the local
    mutable-result argument.  This is the missing compositional pop rule for
    the private flexible-return package. *)
Lemma live_mutable_rdm_components_after_mutable_return_pop :
  forall CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location,
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority caller_senv caller_renv ->
    wf_r_config CT caller_senv caller_renv h ->
    static_getType caller_senv destination = Some destination_type ->
    live_mutable_rdm_components_after_cutoff CT h cutoff active
      (boundary :: stack) ->
    (forall target,
      mutable_reachable CT h return_location target ->
      cutoff <= target) ->
    live_mutable_rdm_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination
          (Iot return_location))) stack.
Proof.
  intros CT h cutoff active boundary stack caller_authority caller_senv
    caller_renv destination destination_type return_location Hcaller
    Hcaller_wf Hdestination Hlive Hreturn_component frame root target
    Hframe Hroot Hroot_runtime Hreachable.
  inversion Hframe; subst.
  - destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
      destination destination_type return_location root Hcaller_wf
      Hdestination Hroot) as [Hroot_old | [Hroot_return _]].
    + eapply Hlive with (frame := boundary.(boundary_caller)) (root := root).
      * apply live_frame_suspended. simpl. left. reflexivity.
      * rewrite Hcaller. exact Hroot_old.
      * exact Hroot_runtime.
      * exact Hreachable.
    + subst root. eapply Hreturn_component. exact Hreachable.
  - eapply Hlive with (frame := boundary0.(boundary_caller)) (root := root).
    + apply live_frame_suspended. simpl. right. exact H.
    + exact Hroot.
    + exact Hroot_runtime.
    + exact Hreachable.
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

Definition authority_call_pop_bridge
  (CT : class_table) (h : heap)
  (callee : watched_frame) (stack : list watched_boundary)
  (receiver_location return_location left right : Loc) : Prop :=
  (authority_color_connected CT h callee stack left receiver_location /\
   authority_color_connected CT h callee stack return_location right) \/
  (authority_color_connected CT h callee stack left return_location /\
   authority_color_connected CT h callee stack receiver_location right).

Lemma authority_color_adjacent_after_call_pop_decomposes :
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
    authority_color_adjacent CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    authority_color_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig))
        entry_cutoff origins :: stack)
      left right \/
    (sqtype destination_type = RDM /\
     authority_call_pop_bridge CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig))
        entry_cutoff origins :: stack)
      receiver_location return_location left right).
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type
    Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value Hbody_sub Hrefine
    Hresult_sub [Hheap | Hframe].
  - left. apply rt_step. left. exact Hheap.
  - destruct Hframe as [frame [Hlive [Hleft Hright]]].
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
      * left. apply rt_step. right.
        exists (mk_watched_frame caller_authority caller_senv caller_renv).
        split.
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type)
               (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- split; assumption.
      * right. split; [exact Hdestination_rdm_right|].
        left. subst right. split; [|apply rt_refl].
        apply rt_step. right.
        exists (mk_watched_frame caller_authority caller_senv caller_renv).
        split.
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type)
               (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- split; [exact Hleft_old|].
           exists receiver, receiver_type. repeat split; assumption.
      * right. split; [exact Hdestination_rdm_left|].
        right. subst left. split; [apply rt_refl|].
        apply rt_step. right.
        exists (mk_watched_frame caller_authority caller_senv caller_renv).
        split.
        -- apply live_frame_suspended with
             (boundary := mk_watched_call_boundary
               (mk_watched_frame caller_authority caller_senv caller_renv)
               entry_senv entry_renv (sqtype receiver_type)
               return_var (sqtype destination_type)
               (sqtype (mret runtime_sig)) entry_cutoff origins).
           left. reflexivity.
        -- split.
           ++ exists receiver, receiver_type. repeat split; assumption.
           ++ exact Hright_old.
      * left. subst left right. apply rt_refl.
    + left. apply rt_step. right.
      exists boundary.(boundary_caller). split.
      * apply live_frame_suspended with (boundary := boundary).
        right. exact H.
      * split; assumption.
Qed.

Lemma authority_color_connected_after_call_pop_decomposes :
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
    authority_color_connected CT h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      stack left right ->
    authority_color_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig))
        entry_cutoff origins :: stack)
      left right \/
    (sqtype destination_type = RDM /\
     authority_call_pop_bridge CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig))
        entry_cutoff origins :: stack)
      receiver_location return_location left right).
Proof.
  intros CT h caller_authority caller_senv caller_renv stack destination
    destination_type receiver receiver_location receiver_type entry_senv
    entry_renv origins callee_senv callee_renv return_var body_return_type
    runtime_sig static_sig entry_cutoff return_location left right Hcaller_wf
    Hdestination_not_receiver Hcaller_post_wf Hdestination Hreceiver_type
    Hreceiver_value Hcallee_wf Hreturn_type Hreturn_value Hbody_sub Hrefine
    Hresult_sub Hconnected.
  induction Hconnected.
  - eapply authority_color_adjacent_after_call_pop_decomposes; eauto.
  - left. apply rt_refl.
  - destruct IHHconnected1 as
      [Hxy |
        [Hdestination_rdm1
          [[Hx_receiver Hreturn_y] | [Hx_return Hreceiver_y]]]];
      destruct IHHconnected2 as
      [Hyz |
        [Hdestination_rdm2
          [[Hy_receiver Hreturn_z] | [Hy_return Hreceiver_z]]]].
    + left. eapply authority_color_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm2|]. left. split.
      * eapply authority_color_connected_trans; eauto.
      * exact Hreturn_z.
    + right. split; [exact Hdestination_rdm2|]. right. split.
      * eapply authority_color_connected_trans; eauto.
      * exact Hreceiver_z.
    + right. split; [exact Hdestination_rdm1|].
      left. split; [exact Hx_receiver|].
      eapply authority_color_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      left. split; [exact Hx_receiver|exact Hreturn_z].
    + left. eapply authority_color_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      right. split; [exact Hx_return|].
      eapply authority_color_connected_trans; eauto.
    + left. eapply authority_color_connected_trans; eauto.
    + right. split; [exact Hdestination_rdm1|].
      right. split; [exact Hx_return|exact Hreceiver_z].
Qed.

Definition authority_call_pop_merge_safe
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (callee : watched_frame) (stack : list watched_boundary)
  (receiver_location return_location : Loc) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ authority_call_pop_bridge CT h callee stack
      receiver_location return_location capability protected.

Lemma authority_color_history_leave_call :
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
    authority_color_live_history_state CT P Z cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type))
        callee_senv callee_renv)
      (mk_watched_call_boundary
        (mk_watched_frame caller_authority caller_senv caller_renv)
        entry_senv entry_renv (sqtype receiver_type)
        return_var (sqtype destination_type) (sqtype (mret runtime_sig))
        (dom caller_h) origins :: stack)
      callee_h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location))
      callee_h ->
    (sqtype destination_type = RDM ->
     authority_call_pop_merge_safe CT callee_h
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
        return_var (sqtype destination_type) (sqtype (mret runtime_sig))
        (dom caller_h) origins :: stack)
      receiver_location return_location) ->
    authority_color_live_history_state CT P Z cutoff
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
    Hrefine Hresult_sub [Hlive [Hcolors Hcutoffs]] Hcaller_post_wf
    Hmerge_safe.
  set (callee_frame := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    callee_senv callee_renv).
  set (caller_boundary := mk_watched_call_boundary
    (mk_watched_frame caller_authority caller_senv caller_renv)
    entry_senv entry_renv (sqtype receiver_type)
    return_var (sqtype destination_type) (sqtype (mret runtime_sig))
    (dom caller_h) origins).
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
    authority_colors_separated CT callee_h Mpost Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    unfold caller_post, callee_frame, caller_boundary in *.
    destruct (authority_color_connected_after_call_pop_decomposes CT callee_h
      caller_authority caller_senv caller_renv stack destination
      destination_type receiver receiver_location receiver_type entry_senv
      entry_renv origins callee_senv callee_renv return_var body_return_type
      runtime_sig static_sig (dom caller_h) return_location
      capability protected Hcaller_current_wf Hdestination_not_receiver
      Hcaller_post_wf Hdestination_type Hreceiver_type Hreceiver_value
      Hcallee_wf Hreturn_type Hreturn_value Hbody_sub Hrefine Hresult_sub
      Hconnected) as [Hreflected | [Hdestination_rdm Hbridge]].
    - exact (Hcolors capability protected (Hpost_in_pre _ Hcapability)
        Hprotected Hreflected).
    - exact (Hmerge_safe Hdestination_rdm capability protected Hcapability
        Hprotected Hbridge). }
  have Hcaller_components :
      component_colors_separated CT callee_h Mpost Z.
  { eapply authority_colors_imply_component_colors; eauto. }
  have Hcaller_colors :
      watched_frame_colors CT callee_h Mpost Z caller_post.
  { eapply authority_colors_imply_active_colors; eauto. }
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
  - exact Hpost_separated.
  - exact (Forall_inv_tail Hcutoffs).
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

Lemma authority_color_adjacent_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right,
    authority_color_adjacent CT h caller_frame stack left right ->
    authority_color_adjacent CT h callee_frame
      (mk_watched_call_boundary caller_frame entry_senv entry_renv
        receiver_view return_var result_qualifier callee_return_qualifier
        entry_cutoff origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right [Hheap | Hframe].
  - left. exact Hheap.
  - right.
    destruct Hframe as [frame [Hlive [Hleft Hright]]].
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
Qed.

Lemma authority_color_connected_before_call_pop_included :
  forall CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right,
    authority_color_connected CT h caller_frame stack left right ->
    authority_color_connected CT h callee_frame
      (mk_watched_call_boundary caller_frame entry_senv entry_renv
        receiver_view return_var result_qualifier callee_return_qualifier
        entry_cutoff origins :: stack) left right.
Proof.
  intros CT h caller_frame stack callee_frame entry_senv entry_renv
    receiver_view return_var result_qualifier callee_return_qualifier
    entry_cutoff origins left right Hconnected.
  induction Hconnected.
  - apply rt_step.
    eapply authority_color_adjacent_before_call_pop_included; eauto.
  - apply rt_refl.
  - eapply authority_color_connected_trans; eauto.
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

Lemma authority_color_history_leave_call_null :
  forall CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins callee_senv callee_renv callee_h,
    zone_env_safe Z caller_senv caller_renv ->
    env_is_confined P cutoff caller_renv ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    authority_color_live_history_state CT P Z cutoff
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
    authority_color_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) stack callee_h.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_renv caller_h stack
    destination destination_type receiver_type entry_senv entry_renv return_var
    callee_return_q origins callee_senv callee_renv callee_h Hcaller_zone
    Hcaller_env Hcaller_wf Hdestination_not_receiver Hdestination_type
    [Hlive [Hcolors Hcutoffs]] Hcaller_post_wf.
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
    authority_colors_separated CT callee_h Mpre Z caller_post stack).
  { intros capability protected Hcapability Hprotected Hconnected.
    have Hold_connected :=
      authority_color_connected_after_active_descent_reflects CT
      callee_h caller_authority caller_senv caller_renv caller_senv
      (update_r_env_value caller_renv destination Null_a) stack capability
      protected Hdescend Hconnected.
    apply (Hcolors capability protected Hcapability Hprotected).
    unfold callee_frame, caller_boundary, caller_old.
    eapply authority_color_connected_before_call_pop_included; eauto. }
  set (Mpost := live_capability_set CT callee_h caller_post stack).
  have Hpost_in_pre : Included Loc Mpost Mpre.
  { intros location Hlocation.
    unfold Mpost, caller_post in Hlocation.
    unfold Mpre, callee_frame, caller_boundary.
    eapply call_return_null_live_reachability_reflects_before_pop with
      (caller_h := caller_h) (destination_type := destination_type); eauto. }
  have Hcaller_components_pre :
      component_colors_separated CT callee_h Mpre Z.
  { eapply authority_colors_imply_component_colors; eauto. }
  have Hcaller_components :
      component_colors_separated CT callee_h Mpost Z.
  { intros capability protected Hcapability Hprotected Hconnected.
    eapply Hcaller_components_pre; eauto. }
  have Hcaller_colors_pre :
      watched_frame_colors CT callee_h Mpre Z caller_post.
  { eapply authority_colors_imply_active_colors; eauto. }
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
    Hcaller_env Hcaller_wf Hdestination_not_receiver Hdestination_type Hlive
    Hcaller_post_wf
    (ltac:(unfold Mpost, caller_post in Hcaller_components;
      exact Hcaller_components))
    (ltac:(unfold Mpost, caller_post in Hcaller_colors;
      exact Hcaller_colors)).
  split; [exact Hlive_post|]. split.
  - intros capability protected Hcapability Hprotected Hconnected.
    apply (Hpost_separated_pre capability protected).
    + unfold Mpre, caller_post, callee_frame, caller_boundary.
      eapply call_return_null_live_reachability_reflects_before_pop with
        (caller_h := caller_h) (destination_type := destination_type); eauto.
    + exact Hprotected.
    + exact Hconnected.
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
      qualified_type_subtype CT receiver_type
        (vpa_mutability_tt_readonly_state receiver_type
          (mreceiver (msignature static_mdef))).
Proof.
  intros CT sGamma mt rGamma h x method y args sGamma' ly cy runtime_mdef
    Hwf Htyping Hsafe Hvalue Hbase Hfind.
  inversion Htyping; subst.
  - destruct Hsafe as [Hrs | Hts]; subst mt;
      destruct Hscope as [Has | [Hcs Hcallee]]; discriminate.
  - exists Tx, Ty, mdef. repeat split; try assumption.
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
      (mk_watched_frame caller_authority sGamma rGamma) h root.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty root Hwf Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs [Hmut | [Hrdm Hruntime]].
  - left. eapply safe_call_callee_mut_root_origin; eauto.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs Hrdm) as
      [caller_T [Hcaller_type [Hshape Hcaller_root]]].
    assert (caller_T = Ty) by congruence. subst caller_T.
    destruct Hshape as [Hcaller_mut | [Hcaller_imm | Hcaller_rdm]].
    + left. rewrite Hcaller_mut in Hcaller_root. exact Hcaller_root.
    + have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma h
        root Hwf (ltac:(rewrite Hcaller_imm in Hcaller_root;
          exact Hcaller_root)).
      congruence.
    + right. split.
      * rewrite Hcaller_rdm in Hcaller_root. exact Hcaller_root.
      * exact Hruntime.
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
    exists target. split.
    + eapply safe_call_callee_mutable_authority_root_reflects_to_caller;
        eauto.
      right. split; [exact H2|exact Htarget_runtime].
    + apply rt_refl.
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

Lemma safe_call_prospective_state_connected_covered_by_caller :
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
    frozen_caller_authority_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    prospective_state_covered_by_frame CT h
      (mk_watched_frame caller_authority sGamma rGamma) target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty source target Hwf Hsound Hcallee_wf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hsource Hconnected.
  induction Hconnected.
  - eapply safe_call_prospective_state_step_covered_by_caller; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

Lemma live_prospective_mutable_authority_components_enter_safe_call :
  forall CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary,
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
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority sGamma rGamma ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack ->
    live_prospective_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) (boundary :: stack).
Proof.
  intros CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary Hwf Hsound Hcallee_wf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hboundary Hold frame root target
    Hlive [Hroot Hpath].
  inversion Hlive; subst.
  - have Hcaller_root : mutable_authority_root
        (mk_watched_frame caller_authority sGamma rGamma) h root.
    { eapply safe_call_callee_mutable_authority_root_reflects_to_caller;
        eauto. }
    have Hsource : prospective_state_covered_by_frame CT h
        (mk_watched_frame caller_authority sGamma rGamma)
        (FlowProspective, root).
    { split; [reflexivity|]. exists root. split;
        [exact Hcaller_root|apply rt_refl]. }
    have Htarget := safe_call_prospective_state_connected_covered_by_caller
      CT caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
      cy runtime_mdef Ty (FlowProspective, root) (FlowProspective, target)
      Hwf Hsound Hcallee_wf Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
      Hsource Hpath.
    destruct Htarget as [_ [caller_root [Hcaller_root' Hcaller_path]]].
    eapply Hold with
      (frame := mk_watched_frame caller_authority sGamma rGamma)
      (root := caller_root).
    + constructor.
    + split; assumption.
  - simpl in H. destruct H as [Heq | Hin].
    + subst boundary0. rewrite Hboundary in Hroot, Hpath.
      eapply Hold with
        (frame := mk_watched_frame caller_authority sGamma rGamma)
        (root := root).
      * constructor.
      * split; assumption.
    + eapply Hold with (frame := boundary0.(boundary_caller)) (root := root).
      * constructor. exact Hin.
      * split; assumption.
Qed.

Lemma live_mutable_authority_components_enter_safe_call :
  forall CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority sGamma rGamma ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack ->
    live_mutable_authority_components_after_cutoff CT h cutoff
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) (boundary :: stack).
Proof.
  intros CT cutoff caller_authority sGamma mt rGamma h stack x method y args
    sGamma' vals ly cy runtime_mdef Ty boundary Hwf Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hboundary Hold frame root target Hlive
    Hreachable.
  inversion Hlive; subst.
  - destruct Hreachable as
      [root target Hcallee_capability Hruntime Hretained
      |root target Hcallee_rdm Hruntime Hmutable].
    + eapply Hold; [constructor|].
      apply mutable_authority_reachable_capability.
      * eapply safe_call_callee_capability_root_reflects_to_caller; eauto.
      * exact Hruntime.
      * exact Hretained.
    + destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
        method y args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope
        Hvalue Hbase Hfind Hargs Hcallee_rdm) as
        [caller_T [Hcaller_type [Hshape Hcaller_root]]].
      assert (caller_T = Ty) by congruence. subst caller_T.
      destruct Hshape as [Hcaller_mut | [Hcaller_imm | Hcaller_rdm]].
      * eapply Hold; [constructor|].
        apply mutable_authority_reachable_capability.
        -- rewrite Hcaller_mut in Hcaller_root.
           destruct Hcaller_root as
             [variable [root_T [Htype [Hroot_value Hmut]]]].
           exists variable, root_T. split; [exact Htype|].
           split; [exact Hroot_value|].
           unfold capability_in_context. left. exact Hmut.
        -- exact Hruntime.
        -- exact Hmutable.
      * have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h root Hwf (ltac:(rewrite Hcaller_imm in Hcaller_root;
            exact Hcaller_root)).
        congruence.
      * eapply Hold; [constructor|].
        apply mutable_authority_reachable_rdm.
        -- rewrite Hcaller_rdm in Hcaller_root. exact Hcaller_root.
        -- exact Hruntime.
        -- exact Hmutable.
  - destruct H as [Heq | Hin].
    + subst boundary0. rewrite Hboundary in Hreachable.
      eapply Hold; eauto. constructor.
    + eapply Hold; eauto. constructor. exact Hin.
Qed.

Lemma frozen_callee_side_components_enter_untracked_safe_call :
  forall CT h caller_authority sGamma mt rGamma stack snapshots
    x method y args sGamma' vals ly cy runtime_mdef Ty boundary,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority sGamma rGamma ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots stack ->
    frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (None :: advance_frozen_caller_snapshots CT h
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals))) snapshots)
      (boundary :: stack).
Proof.
  intros CT h caller_authority sGamma mt rGamma stack snapshots x
    method y args sGamma' vals ly cy runtime_mdef Ty boundary Hwf Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs Hboundary Hold snapshot
    tracked_boundary above below Hpartition.
  inversion Hpartition; subst.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h
    (mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals))) snapshots stack snapshot tracked_boundary
    above0 below H7) as [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot tracked_boundary above0 below
    Hold_partition.
  eapply live_mutable_authority_components_enter_safe_call with
    (boundary := boundary); eauto.
Qed.

Lemma frozen_callee_side_prospective_components_enter_untracked_safe_call :
  forall CT h caller_authority sGamma mt rGamma stack snapshots
    x method y args sGamma' vals ly cy runtime_mdef Ty boundary,
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
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority sGamma rGamma ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (None :: advance_frozen_caller_snapshots CT h
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals))) snapshots)
      (boundary :: stack).
Proof.
  intros CT h caller_authority sGamma mt rGamma stack snapshots x method y
    args sGamma' vals ly cy runtime_mdef Ty boundary Hwf Hsound Hcallee_wf
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hboundary Hold snapshot
    tracked_boundary above below Hpartition.
  inversion Hpartition; subst.
  destruct (advance_frozen_snapshot_live_partition_reflects CT h
    (mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals))) snapshots stack snapshot tracked_boundary
    above0 below H7) as [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot tracked_boundary above0 below
    Hold_partition.
  eapply live_prospective_mutable_authority_components_enter_safe_call with
    (boundary := boundary).
  - exact Hwf.
  - exact Hsound.
  - exact Hcallee_wf.
  - exact Htyping.
  - exact Hscope.
  - exact Hgety.
  - exact Hvalue.
  - exact Hbase.
  - exact Hfind.
  - exact Hargs.
  - exact Hboundary.
  - exact Hold_components.
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
    [left_T [Hleft_get [Hleft_shape Hleft_root]]].
  destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
    method y args sGamma' vals ly cy runtime_mdef right Hwf Htyping Hscope
    Hvalue Hbase Hfind Hargs Hright) as
    [right_T [Hright_get [Hright_shape Hright_root]]].
  assert (left_T = Ty) by congruence.
  assert (right_T = Ty) by congruence. subst left_T right_T.
  destruct Hleft_shape as [Hview | [Hview | Hview]].
  - exists FlowPowered. split; [left; reflexivity|].
    eapply executing_authority_typed_mut_root_is_powered.
    rewrite Hview in Hright_root. exact Hright_root.
  - have Hleft_immutable := typed_imm_root_runtime_immutable CT sGamma
      rGamma h left Hwf (ltac:(rewrite Hview in Hleft_root;
        exact Hleft_root)).
    have Hleft_mutable := Hruntime old_mode left Hold_color.
    congruence.
  - exists FlowProspective. split; [right; reflexivity|].
    eapply executing_authority_dangerous_frame_join; eauto.
    + rewrite Hview in Hleft_root. exact Hleft_root.
    + rewrite Hview in Hright_root. exact Hright_root.
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

(** Call entry is origin-reflecting: every dangerous color introduced by
    the callee view is represented in the caller's completed entry colors.
    This is the summary bridge used to compose a recursively proved body
    summary with its caller. *)
Lemma executing_authority_colors_enter_call_covered :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals)))
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) incoming))
        (mode, location) ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) incoming)
          (caller_mode, location).
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming Hwf Hsound Hincoming Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs mode location Hmode
    [seed [Hseed Hconnected]].
  set (old_colors := executing_authority_color_set CT h
    (mk_watched_frame caller_authority sGamma rGamma) incoming).
  have Hold_runtime : authority_colors_runtime_mutable h old_colors.
  { unfold old_colors. eapply executing_authority_colors_runtime_mutable;
      eauto. }
  assert (Hseed_covered : authority_state_covered old_colors seed).
  { destruct seed as [seed_mode seed_location]. simpl. intros Hseed_mode.
    inversion Hseed; subst.
    - exists seed_mode. split; [exact Hseed_mode|exact H].
    - destruct H as [owned [Heq Howned]]. inversion Heq; subst.
      exists FlowPowered. split; [left; reflexivity|].
      unfold old_colors. apply executing_authority_owned_is_powered.
      eapply safe_call_callee_owned_reflects_to_caller; eauto. }
  have Hcovered := safe_call_callee_frame_connected_preserves_coverage CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming seed (mode, location) Hwf Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hold_runtime Hseed_covered Hconnected Hmode.
  destruct Hcovered as [caller_mode [Hcaller_mode Hcaller_color]].
  exists caller_mode. split; [exact Hcaller_mode|].
  unfold old_colors in Hcaller_color. exact Hcaller_color.
Qed.

Lemma executing_authority_colors_enter_call :
  forall CT Z caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame caller_authority sGamma rGamma) incoming ->
    executing_authority_colors_separated CT h Z
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming).
Proof.
  intros CT Z caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty incoming Hwf Hsound Hincoming Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hseparated mode protected Hmode
    [seed [Hseed Hconnected]] Hprotected.
  set (old_colors := executing_authority_color_set CT h
    (mk_watched_frame caller_authority sGamma rGamma) incoming).
  have Hold_runtime : authority_colors_runtime_mutable h old_colors.
  { unfold old_colors. eapply executing_authority_colors_runtime_mutable;
      eauto. }
  assert (Hseed_covered : authority_state_covered old_colors seed).
  { destruct seed as [seed_mode seed_location]. simpl. intros Hseed_mode.
    inversion Hseed; subst.
    - exists seed_mode. split; [exact Hseed_mode|exact H].
    - destruct H as [location [Heq Howned]]. inversion Heq; subst.
      exists FlowPowered. split; [left; reflexivity|].
      unfold old_colors. apply executing_authority_owned_is_powered.
      eapply safe_call_callee_owned_reflects_to_caller; eauto. }
  have Hcovered := safe_call_callee_frame_connected_preserves_coverage CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming seed (mode, protected) Hwf Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hold_runtime Hseed_covered Hconnected Hmode.
  destruct Hcovered as [old_mode [Hold_mode Hold_color]].
  unfold old_colors in Hold_color.
  exact (Hseparated old_mode protected Hold_mode Hold_color Hprotected).
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_avoid_protected :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs callee new_snapshot mode location Hnew Hmode Hcolor Hprotected.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  simpl in Hcolor.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  have Hcallee_color : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          old_snapshot.(frozen_snapshot_current_colors)))
      (mode, location).
  { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming. exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    old_snapshot.(frozen_snapshot_current_colors) Hwf Hsound
    (Hruntime old_snapshot Hold) Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
    mode location Hmode Hcallee_color) as
    [caller_mode [Hcaller_mode Hcaller_color]].
  destruct
    (executing_with_frozen_incoming_dangerous_covered_by_old_or_active CT h
      (mk_watched_frame caller_authority sGamma rGamma)
      old_snapshot.(frozen_snapshot_current_colors) caller_mode location
      (Hclosed old_snapshot Hold) Hcaller_mode Hcaller_color) as
    [[snapshot_mode [Hsnapshot_mode Hsnapshot_color]] |
     [active_mode [Hactive_mode Hactive_color]]].
  - exact (Havoid old_snapshot snapshot_mode location Hold Hsnapshot_mode
      Hsnapshot_color Hprotected).
  - eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    exact Hactive_color.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_roots_in_heap :
  forall CT h callee snapshots,
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_roots_in_heap h
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT h callee snapshots Hroots new_snapshot root Hnew Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in Hroot.
  eapply Hroots; eauto.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_exposures_wf :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_exposures_wf CT h callee
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs callee.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hcallee_wf : wf_r_config CT callee.(frame_senv)
      callee.(frame_renv) h.
  { unfold callee. simpl.
    destruct (typed_call_has_wf_callee_frame CT sGamma mt rGamma h x method
      y args sGamma' vals ly cy runtime_mdef Hwf Htyping Hvalue Hbase Hfind
      Hargs) as [body_end [_ Hframe]]. exact Hframe. }
  split.
  - intros new_snapshot Hnew mode location Hcolor.
    unfold advance_frozen_caller_snapshots in Hnew.
    apply in_map_iff in Hnew.
    destruct Hnew as [old_slot [Heq Hold]].
    destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
    eapply (advance_frozen_caller_snapshot_runtime_mutable CT h callee
      old_snapshot.(frozen_snapshot_current_resume_exposure)); eauto.
    eapply (proj1 Hexposure); eauto.
  - split.
    + intros new_snapshot Hnew.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
      injection Heq as Heq. subst new_snapshot. simpl.
      exact (proj1 (frozen_caller_authority_closure_idempotent CT h callee
        old_snapshot.(frozen_snapshot_current_resume_exposure))).
    + split.
      * intros new_snapshot mode location Hnew Hcolor.
        unfold advance_frozen_caller_snapshots in Hnew.
        apply in_map_iff in Hnew.
        destruct Hnew as [old_slot [Heq Hold]].
        destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
        injection Heq as Heq. subst new_snapshot. simpl in Hcolor.
        eapply frozen_caller_authority_closure_dangerous; [|exact Hcolor].
        intros old_mode old_location Hold_color.
        eapply (proj1 (proj2 (proj2 Hexposure))) with
          (snapshot := old_snapshot); eauto.
      * split.
        -- intros new_snapshot Hnew state Hentry.
           unfold advance_frozen_caller_snapshots in Hnew.
           apply in_map_iff in Hnew.
           destruct Hnew as [old_slot [Heq Hold]].
           destruct old_slot as [old_snapshot|]; simpl in Heq;
             [|discriminate].
           injection Heq as Heq. subst new_snapshot. simpl in *.
           apply frozen_caller_authority_closure_contains.
           eapply (proj1 (proj2 (proj2 (proj2 Hexposure)))); eauto.
        -- intros new_snapshot root Hnew Hroot Hroot_runtime.
           unfold advance_frozen_caller_snapshots in Hnew.
           apply in_map_iff in Hnew.
           destruct Hnew as [old_slot [Heq Hold]].
           destruct old_slot as [old_snapshot|]; simpl in Heq;
             [|discriminate].
           injection Heq as Heq. subst new_snapshot. simpl in *.
           apply frozen_caller_authority_closure_contains.
           eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_resume_roots_safe :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_roots_safe CT h Z callee
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed
      [Hretain [Hdangerous [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs callee new_snapshot
    active_mode source exposure_mode target Hnew Hactive_mode Hactive Hsource
    Hexposure_mode Htarget Hprotected.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hcallee_color : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          (Empty_set authority_flow_state)))
      (active_mode, source).
  { eapply independent_active_authority_colors_in_executing. exact Hactive. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    (Empty_set authority_flow_state) Hwf Hsound
    (ltac:(intros mode location Hempty; inversion Hempty)) Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs active_mode source Hactive_mode
    Hcallee_color) as [old_mode [Hold_mode Hold_active]].
  have Hcallee_target : In authority_flow_state
      (executing_authority_color_set CT h callee
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          old_snapshot.(frozen_snapshot_current_resume_exposure)))
      (exposure_mode, target).
  { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
    - left. apply executing_authority_color_set_contains_incoming. exact Hseed.
    - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
  destruct (executing_authority_colors_enter_call_covered CT caller_authority
    sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
    old_snapshot.(frozen_snapshot_current_resume_exposure) Hwf Hsound
    ((proj1 Hexposure) old_snapshot Hold) Htyping Hscope Hgety Hvalue Hbase
    Hfind Hargs exposure_mode target Hexposure_mode Hcallee_target) as
    [old_exposure_mode [Hold_exposure_mode Hold_target]].
  destruct
    (executing_with_frozen_incoming_dangerous_covered_by_old_or_active CT h
      (mk_watched_frame caller_authority sGamma rGamma)
      old_snapshot.(frozen_snapshot_current_resume_exposure)
      old_exposure_mode target
      ((proj1 (proj2 Hexposure)) old_snapshot Hold)
      Hold_exposure_mode Hold_target) as
    [[snapshot_mode [Hsnapshot_mode Hsnapshot_target]] |
     [target_active_mode [Htarget_active_mode Htarget_active]]].
  - eapply Hresume with (snapshot := old_snapshot) (active_mode := old_mode)
      (source := source) (exposure_mode := snapshot_mode); eauto.
  - have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
    eapply Hmain_separated; [exact Htarget_active_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing.
    exact Htarget_active.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_resume_joins_safe :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs callee new_snapshot
    source_mode source Hnew Hsource_mode Hsource_color Hsource_root.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  assert (Hclassify : forall colors mode location,
      authority_colors_runtime_mutable h colors ->
      Included authority_flow_state
        (frozen_caller_authority_closure CT h
          (mk_watched_frame caller_authority sGamma rGamma) colors) colors ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee colors)
        (mode, location) ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state colors (old_mode, location)) \/
      (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h
            (mk_watched_frame caller_authority sGamma rGamma))
          (active_mode, location))).
  { intros colors mode location Hcolors_runtime Hcolors_closed Hmode Hcolor.
    have Hcallee_color : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) colors))
        (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
      - left. apply executing_authority_color_set_contains_incoming.
        exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT caller_authority
      sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
      colors Hwf Hsound Hcolors_runtime Htyping Hscope Hgety Hvalue Hbase
      Hfind Hargs mode location Hmode Hcallee_color) as
      [caller_mode [Hcaller_mode Hcaller_color]].
    exact
      (executing_with_frozen_incoming_dangerous_covered_by_old_or_active CT h
        (mk_watched_frame caller_authority sGamma rGamma) colors caller_mode
        location Hcolors_closed Hcaller_mode Hcaller_color). }
  have Hsource_cases := Hclassify
    old_snapshot.(frozen_snapshot_current_colors) source_mode source
    (Hruntime old_snapshot Hold) (Hclosed old_snapshot Hold) Hsource_mode
    Hsource_color.
  assert (Hclassify_target : forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee
          old_snapshot.(frozen_snapshot_current_resume_exposure))
        (exposure_mode, target) ->
      (exists old_exposure_mode,
        authority_mode_dangerous old_exposure_mode /\
        In authority_flow_state
          old_snapshot.(frozen_snapshot_current_resume_exposure)
          (old_exposure_mode, target)) \/
      (exists target_active_mode,
        authority_mode_dangerous target_active_mode /\
        In authority_flow_state
          (independent_active_authority_colors CT h
            (mk_watched_frame caller_authority sGamma rGamma))
          (target_active_mode, target))).
  { intros exposure_mode target Hexposure_mode Htarget.
    eapply Hclassify; eauto.
    - eapply (proj1 Hexposure); eauto.
    - eapply (proj1 (proj2 Hexposure)); eauto. }
  destruct Hsource_cases as
    [[old_source_mode [Hold_source_mode Hold_source]] |
     [active_source_mode [Hactive_source_mode Hactive_source]]].
  - destruct (Hjoins old_snapshot old_source_mode source Hold
      Hold_source_mode Hold_source Hsource_root) as
      [[entry_mode [Hentry_mode Hentry]] | Hsafe].
    + left. exists entry_mode. split; assumption.
    + right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
      destruct (Hclassify_target exposure_mode target Hexposure_mode Htarget) as
        [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
         [target_active_mode [Htarget_active_mode Htarget_active]]].
      * exact (Hsafe old_exposure_mode target Hold_exposure_mode Hold_target
          Hprotected).
      * eapply Hmain_separated; [exact Htarget_active_mode| |exact Hprotected].
        eapply independent_active_authority_colors_in_executing.
        exact Htarget_active.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    destruct (Hclassify_target exposure_mode target Hexposure_mode Htarget) as
      [[old_exposure_mode [Hold_exposure_mode Hold_target]] |
       [target_active_mode [Htarget_active_mode Htarget_active]]].
    + eapply Hresume with (snapshot := old_snapshot)
        (active_mode := active_source_mode) (source := source)
        (exposure_mode := old_exposure_mode); eauto.
    + eapply Hmain_separated; [exact Htarget_active_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing.
      exact Htarget_active.
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_nested_resume_safe Z snapshots ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hfrozen Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hnested callee.
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (exceptional := independent_active_authority_colors CT h caller).
  assert (Hclassify : forall colors mode location,
      authority_colors_runtime_mutable h colors ->
      Included authority_flow_state
        (frozen_caller_authority_closure CT h caller colors) colors ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h callee colors)
        (mode, location) ->
      (exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state colors (old_mode, location)) \/
      (exists active_mode,
        authority_mode_dangerous active_mode /\
        In authority_flow_state exceptional (active_mode, location))).
  { intros colors mode location Hcolors_runtime Hcolors_closed Hmode Hcolor.
    have Hcallee_color : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h caller colors))
        (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
      - left. apply executing_authority_color_set_contains_incoming.
        exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT
      caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
      runtime_mdef Ty colors Hwf Hsound Hcolors_runtime Htyping Hscope Hgety
      Hvalue Hbase Hfind Hargs mode location Hmode Hcallee_color) as
      [caller_mode [Hcaller_mode Hcaller_color]].
    unfold caller, exceptional.
    eapply executing_with_frozen_incoming_dangerous_covered_by_old_or_active;
      eauto. }
  eapply frozen_caller_snapshots_nested_resume_safe_after_classified_advance
    with (exceptional := exceptional).
  - exact Hnested.
  - unfold exceptional, caller. exact Hresume.
  - intros active_mode location Hactive_mode Hactive Hprotected.
    eapply Hmain_separated; [exact Hactive_mode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hactive.
  - intros snapshot older mode location Hsnapshot _ Hmode Hcolor _.
    eapply Hclassify; eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor _.
    eapply Hclassify; eauto using (proj1 Hexposure),
      (proj1 (proj2 Hexposure)).
Qed.

Lemma frozen_completed_colors_resume_safe_after_safe_call_entry :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming)
      snapshots ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors := executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h callee caller_colors)
      (advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    Hfrozen Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hcompleted
    caller caller_colors callee.
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
    proj1 (proj2 (proj2 Hmain)).
  have Hmain_separated := proj1 (proj2 (proj2 (proj2 Hmain))).
  intros new_snapshot source_mode source Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in *.
  destruct (executing_authority_colors_enter_call_covered CT
    caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
    runtime_mdef Ty incoming Hwf Hsound Hincoming_runtime Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode Hsource) as
    [caller_mode [Hcaller_mode Hcaller_source]].
  destruct (Hcompleted old_snapshot caller_mode source Hold Hcaller_mode
    Hcaller_source Hroot) as
    [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. exists entry_mode. split; assumption.
  - right. intros exposure_mode target Hexposure_mode Htarget Hprotected.
    have Hcallee_target : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h caller
            old_snapshot.(frozen_snapshot_current_resume_exposure)))
        (exposure_mode, target).
    { destruct Htarget as [seed [Hseed Hpath]]. exists seed. split.
      - left. apply executing_authority_color_set_contains_incoming.
        exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT
      caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
      runtime_mdef Ty old_snapshot.(frozen_snapshot_current_resume_exposure)
      Hwf Hsound ((proj1 Hexposure) old_snapshot Hold) Htyping Hscope Hgety
      Hvalue Hbase Hfind Hargs exposure_mode target Hexposure_mode
      Hcallee_target) as [caller_target_mode [Hcaller_target_mode Hcaller_target]].
    destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h caller old_snapshot.(frozen_snapshot_current_resume_exposure)
      caller_target_mode target ((proj1 (proj2 Hexposure)) old_snapshot Hold)
      Hcaller_target_mode Hcaller_target) as
      [[old_target_mode [Hold_target_mode Hold_target]] |
       [active_target_mode [Hactive_target_mode Hactive_target]]].
    + exact (Hsafe old_target_mode target Hold_target_mode Hold_target
        Hprotected).
    + eapply Hmain_separated; [exact Hactive_target_mode| |exact Hprotected].
      eapply independent_active_authority_colors_in_executing.
      exact Hactive_target.
Qed.

Lemma frozen_caller_snapshots_after_safe_call_entry_entry_exposure_covered :
  forall CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_frozen_authority_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let caller_colors :=
      executing_authority_color_set CT h caller incoming in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_entry_exposure_covered
      (enter_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots).
Proof.
  intros CT P Z cutoff caller_authority sGamma rGamma h stack incoming
    snapshots mt x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs caller caller_colors callee
    snapshot source_mode source Hsnapshot Hsource_mode Hsource_color
    Hsource_root.
  unfold enter_frozen_caller_snapshots in Hsnapshot.
  simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
  - injection Heq as Heq. subst snapshot. simpl in *.
    have Hwf : wf_r_config CT sGamma rGamma h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hsound : authority_context_sound h rGamma caller_authority :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
    have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
      proj1 (proj2 (proj2 Hmain)).
    have Hcallee_color : In authority_flow_state
        (executing_authority_color_set CT h callee
          (executing_authority_color_set CT h caller incoming))
        (source_mode, source).
    { destruct Hsource_color as [seed [[Hseed Hseed_mode] Hpath]].
      exists seed. split; [left; exact Hseed|].
      eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_enter_call_covered CT
      caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
      runtime_mdef Ty incoming Hwf Hsound Hincoming_runtime Htyping Hscope
      Hgety Hvalue Hbase Hfind Hargs source_mode source Hsource_mode
      Hcallee_color) as [caller_mode [Hcaller_mode Hcaller_source]].
    apply frozen_caller_authority_closure_monotone.
    intros exposure_state Hexposure_state. split.
    + eapply frame_resume_exposure_colors_in_executing_from_dangerous_rdm_root
        with (source_mode := caller_mode) (source := source); eauto.
    + destruct exposure_state as [exposure_mode exposure_location].
      eapply frame_resume_exposure_colors_dangerous. exact Hexposure_state.
  - eapply (advance_frozen_caller_snapshots_entry_exposure_covered
      CT h callee snapshots Hentry_covered); eauto.
Qed.

Lemma principled_phased_authority_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      principled_phased_authority_live_history_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty Hstate Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs.
  destruct Hstate as [Hcontains Hstate].
  destruct Hstate as [Hconfined Hstate].
  destruct Hstate as [Hincoming_runtime Hstate].
  destruct Hstate as [Hphased Hstate].
  destruct Hstate as [Hframes Hstate].
  destruct Hstate as [Hsound Hstate].
  destruct Hstate as [Hcutoff Hstate].
  destruct Hstate as [Hzone [Hchain Hcutoffs]].
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee_senv := mreceiver (msignature runtime_mdef) ::
    mparams (msignature runtime_mdef)).
  set (callee_renv := mkr_env (Iot ly :: vals)).
  set (callee := mk_watched_frame
    (call_authority caller_authority (sqtype Ty)) callee_senv callee_renv).
  set (callee_incoming := executing_authority_color_set CT h caller incoming).
  have Hwf : wf_r_config CT sGamma rGamma h := proj1 Hframes.
  set (origins := Build_call_boundary_origins caller (sqtype Ty)
    callee_senv callee_renv
    (safe_call_rdm_roots_reflect_through_view CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef Ty Hwf Htyping Hscope
      Hgety Hvalue Hbase Hfind Hargs)
    (safe_call_capability_roots_reflect_through_view CT caller_authority
      sGamma mt rGamma h x method y args sGamma' vals ly cy runtime_mdef Ty
      Hwf Htyping Hscope Hgety Hvalue Hbase Hfind Hargs)).
  assert (Hdestination : exists destination_type,
      static_getType sGamma x = Some destination_type).
  { inversion Htyping; subst; eauto. }
  destruct Hdestination as [destination_type Hdestination].
  set (boundary := mk_watched_call_boundary caller callee_senv callee_renv
    (sqtype Ty) (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  have Hcallee_wf : wf_r_config CT callee_senv callee_renv h.
  { unfold callee_senv, callee_renv.
    destruct (typed_call_has_wf_callee_frame CT sGamma mt rGamma h x method
      y args sGamma' vals ly cy runtime_mdef Hwf Htyping Hvalue Hbase Hfind
      Hargs) as [body_end [_ Hframe]]. exact Hframe. }
  have Hcallee_confined : state_is_confined P cutoff callee_renv h.
  { destruct Hconfined as [Hcaller_env Hheap]. split; [|exact Hheap].
    intros variable location Hcallee_value. unfold callee_renv in *.
    destruct variable as [|index].
    - simpl in Hcallee_value. injection Hcallee_value as <-.
      eapply Hcaller_env; eauto.
    - simpl in Hcallee_value.
      destruct (runtime_lookup_list_nth_zs rGamma args vals index
        (Iot location) Hargs Hcallee_value) as
        [argument [Hargument_index Hargument_value]].
      eapply Hcaller_env; eauto. }
  have Hcaller_sound : authority_context_sound h rGamma caller_authority :=
    proj1 Hsound.
  have Hcallee_sound : authority_context_sound h callee_renv
      (call_authority caller_authority (sqtype Ty)).
  { intros Hcallee_authority. exists ly. split; [reflexivity|].
    have Hnotbot := wf_config_nonnull_variable_not_bot CT sGamma rGamma h y
      Ty ly Hwf Hgety Hvalue.
    have Hreceiver_capability : capability_in_context caller_authority
        (sqtype Ty).
    { eapply safe_call_receiver_authority_reflects; [exact Hnotbot|].
      unfold capability_in_context. right. split; [reflexivity|].
      exact Hcallee_authority. }
    eapply frame_capability_root_runtime_mutable with (frame := caller).
    - exact Hwf.
    - exact Hcaller_sound.
    - exists y, Ty. repeat split; try assumption. }
  have Hcallee_frames : live_frames_wf CT h callee (boundary :: stack).
  { split; [exact Hcallee_wf|]. constructor; [exact Hwf|exact (proj2 Hframes)]. }
  have Hcallee_sounds : live_frames_authority_sound h callee
      (boundary :: stack).
  { split; [exact Hcallee_sound|].
    constructor; [exact Hcaller_sound|exact (proj2 Hsound)]. }
  have Hcallee_incoming_runtime : authority_colors_runtime_mutable h
      callee_incoming.
  { unfold callee_incoming, caller.
    eapply executing_authority_colors_runtime_mutable; eauto. }
  have Hcallee_phased : executing_authority_colors_separated CT h Z callee
      callee_incoming.
  { unfold callee, callee_senv, callee_renv, callee_incoming, caller.
    eapply executing_authority_colors_enter_call; eauto. }
  exists origins, destination_type. split; [exact Hdestination|].
  refine (conj Hcontains (conj Hcallee_confined _)).
  refine (conj Hcallee_incoming_runtime (conj Hcallee_phased _)).
  refine (conj Hcallee_frames (conj Hcallee_sounds (conj Hcutoff
    (conj Hzone (conj _ _))))).
  - unfold callee, boundary. simpl. split; [reflexivity|exact Hchain].
  - unfold boundary. constructor; [simpl; lia|exact Hcutoffs].
Qed.

(** A frozen caller color advanced through a safe callee is either still
    represented by the caller snapshot or has acquired the snapshot's
    root-scoped resume-origin witness.  The only interesting callee step is
    an RDM frame join.  Its roots reflect through class-bounded adaptation to
    caller [Mut], [Imm], or [RDM] roots: [Mut] is independently caller-owned,
    [Imm] contradicts the runtime mutability of the source color, and [RDM]
    is the corresponding caller-frame join. *)
Lemma safe_call_frozen_step_covered_by_old_or_resume_origin :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty snapshot (fallback : Prop) source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame caller_authority sGamma rGamma)
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall snapshot_mode active_mode location,
      authority_mode_dangerous snapshot_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (snapshot_mode, location) ->
      (In authority_flow_state
         (independent_active_authority_colors CT h
           (mk_watched_frame caller_authority sGamma rGamma))
         (active_mode, location) \/
       typed_root RDM sGamma rGamma location) ->
      fallback) ->
    frozen_state_covered_by_old_or snapshot fallback source ->
    frozen_caller_authority_step CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    frozen_state_covered_by_old_or snapshot fallback target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty snapshot fallback source target Hwf Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Horigins Hsource Hstep
    Htarget_mode.
  have Hsource_mode : authority_mode_dangerous (fst source).
  { inversion Hstep; subst; simpl;
      first [left; reflexivity | right; reflexivity]. }
  destruct (Hsource Hsource_mode) as
    [[old_mode [Hold_mode Hold_color]] | Horigin];
    [|right; exact Horigin].
  inversion Hstep; subst; simpl in *.
  - left. exists old_mode. split; [exact Hold_mode|].
    eapply frozen_caller_color_dangerous_retained; eauto.
  - left. exists old_mode. split; [exact Hold_mode|].
    eapply frozen_caller_color_dangerous_retained; eauto.
  - left. exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
  - left. exists FlowProspective. split; [right; reflexivity|].
    eapply frozen_caller_color_dangerous_reverse_rdm; eauto.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef left Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H) as
      [left_T [Hleft_get [Hleft_shape Hleft_root]]].
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef right Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H0) as
      [right_T [Hright_get [Hright_shape Hright_root]]].
    assert (left_T = Ty) by congruence.
    assert (right_T = Ty) by congruence. subst left_T right_T.
    destruct Hleft_shape as [Hmut | [Himm | Hrdm]].
    + right. apply (Horigins old_mode FlowPowered left Hold_mode
        (or_introl eq_refl) Hold_color).
      left. unfold independent_active_authority_colors.
      eapply executing_authority_typed_mut_root_is_powered.
      rewrite Hmut in Hleft_root. exact Hleft_root.
    + have Hmutable := Hruntime old_mode left Hold_color.
      have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma h
        left Hwf (ltac:(rewrite Himm in Hleft_root; exact Hleft_root)).
      congruence.
    + left. exists FlowProspective. split; [right; reflexivity|].
      apply Hclosed. exists (old_mode, left). split; [exact Hold_color|].
      apply rt_step. destruct Hold_mode as [-> | ->].
      * apply frozen_caller_powered_frame_join.
        -- rewrite Hrdm in Hleft_root. exact Hleft_root.
        -- rewrite Hrdm in Hright_root. exact Hright_root.
      * apply frozen_caller_prospective_frame_join.
        -- rewrite Hrdm in Hleft_root. exact Hleft_root.
        -- rewrite Hrdm in Hright_root. exact Hright_root.
  - destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef left Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H) as
      [left_T [Hleft_get [Hleft_shape Hleft_root]]].
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef right Hwf Htyping Hscope
      Hvalue Hbase Hfind Hargs H0) as
      [right_T [Hright_get [Hright_shape Hright_root]]].
    assert (left_T = Ty) by congruence.
    assert (right_T = Ty) by congruence. subst left_T right_T.
    destruct Hleft_shape as [Hmut | [Himm | Hrdm]].
    + right. apply (Horigins old_mode FlowPowered left Hold_mode
        (or_introl eq_refl) Hold_color).
      left. unfold independent_active_authority_colors.
      eapply executing_authority_typed_mut_root_is_powered.
      rewrite Hmut in Hleft_root. exact Hleft_root.
    + have Hmutable := Hruntime old_mode left Hold_color.
      have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma h
        left Hwf (ltac:(rewrite Himm in Hleft_root; exact Hleft_root)).
      congruence.
    + left. exists FlowProspective. split; [right; reflexivity|].
      apply Hclosed. exists (old_mode, left). split; [exact Hold_color|].
      apply rt_step. destruct Hold_mode as [-> | ->].
      * apply frozen_caller_powered_frame_join.
        -- rewrite Hrdm in Hleft_root. exact Hleft_root.
        -- rewrite Hrdm in Hright_root. exact Hright_root.
      * apply frozen_caller_prospective_frame_join.
        -- rewrite Hrdm in Hleft_root. exact Hleft_root.
        -- rewrite Hrdm in Hright_root. exact Hright_root.
  - left. exists FlowProspective. split; [right; reflexivity|].
    destruct Hold_mode as [-> | ->].
    + apply Hclosed. exists (FlowPowered, location).
      split; [exact Hold_color|]. apply rt_step.
      apply frozen_caller_mark_prospective.
    + exact Hold_color.
Qed.

Lemma safe_call_frozen_connected_covered_by_old_or_resume_origin :
  forall CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty snapshot (fallback : Prop) source target,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_colors_runtime_mutable h
      snapshot.(frozen_snapshot_current_colors) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h
        (mk_watched_frame caller_authority sGamma rGamma)
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall snapshot_mode active_mode location,
      authority_mode_dangerous snapshot_mode ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (snapshot_mode, location) ->
      (In authority_flow_state
         (independent_active_authority_colors CT h
           (mk_watched_frame caller_authority sGamma rGamma))
         (active_mode, location) \/
       typed_root RDM sGamma rGamma location) ->
      fallback) ->
    frozen_state_covered_by_old_or snapshot fallback source ->
    frozen_caller_authority_connected CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals))) source target ->
    frozen_state_covered_by_old_or snapshot fallback target.
Proof.
  intros CT caller_authority sGamma mt rGamma h x method y args sGamma'
    vals ly cy runtime_mdef Ty snapshot fallback source target Hwf Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hruntime Hclosed Horigins Hsource
    Hconnected.
  induction Hconnected.
  - eapply safe_call_frozen_step_covered_by_old_or_resume_origin; eauto.
  - exact Hsource.
  - apply IHHconnected2. apply IHHconnected1. exact Hsource.
Qed.

(** Root-scoped overlap provenance is stable across an ordinary safe call
    entry.  A dangerous color independently owned by the callee reflects to
    independently owned caller authority.  A callee RDM root reflects to a
    caller [Mut], [Imm], or [RDM] root; the immutable case contradicts the
    runtime-mutability of frozen colors, while the other two cases are
    precisely the triggers recorded by the caller certificate. *)
Lemma frozen_caller_snapshots_active_resume_origins_after_safe_call_entry :
  forall CT caller_authority sGamma mt rGamma h snapshots x method y args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma caller_authority ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    frozen_caller_snapshots_runtime_mutable h snapshots ->
    frozen_caller_snapshots_closed CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_active_resume_origins CT h
      (mk_watched_frame caller_authority sGamma rGamma) snapshots ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    frozen_caller_snapshots_active_resume_origins CT h callee
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
Proof.
  intros CT caller_authority sGamma mt rGamma h snapshots x method y args
    sGamma' vals ly cy runtime_mdef Ty Hwf Hsound Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hruntime Hclosed Horigins callee new_snapshot
    snapshot_mode active_mode location Hnew Hsnapshot_mode Hactive_mode
    Hsnapshot_color Htrigger.
  simpl in Hnew. destruct Hnew as [Hnone | Hnew]; [discriminate|].
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [old_slot [Heq Hold]].
  destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as <-. simpl in Hsnapshot_color.
  destruct Hsnapshot_color as
    [[seed_mode seed_location] [Hseed Hpath]].
  have Hcovered :=
    safe_call_frozen_connected_covered_by_old_or_resume_origin CT
      caller_authority sGamma mt rGamma h x method y args sGamma' vals ly cy
      runtime_mdef Ty old_snapshot
      (frozen_snapshot_has_resume_origin old_snapshot)
      (seed_mode, seed_location) (snapshot_mode, location) Hwf Htyping Hscope
      Hgety Hvalue Hbase Hfind Hargs (Hruntime old_snapshot Hold)
      (Hclosed old_snapshot Hold)
      (fun old_mode caller_mode old_location Hold_mode Hcaller_mode
        Hold_color Hcaller_trigger =>
        Horigins old_snapshot old_mode caller_mode old_location Hold
          Hold_mode Hcaller_mode Hold_color Hcaller_trigger)
      (ltac:(unfold frozen_state_covered_by_old_or; simpl; intros Hmode;
        left; exists seed_mode; repeat split; assumption)) Hpath.
  destruct (Hcovered Hsnapshot_mode) as
    [[old_mode [Hold_mode Hold_color]] | Hold_origin].
  - destruct Htrigger as [Hactive | Hrdm].
    + have Hcallee_color : In authority_flow_state
          (executing_authority_color_set CT h callee
            (executing_authority_color_set CT h
              (mk_watched_frame caller_authority sGamma rGamma)
              (Empty_set authority_flow_state)))
          (active_mode, location).
      { destruct Hactive as [[source_mode source_location] [Hsource Hactive]].
        exists (source_mode, source_location). split.
        - inversion Hsource; subst.
          + inversion H.
          + right. exact H.
        - exact Hactive. }
      destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty (Empty_set authority_flow_state) Hwf Hsound
        (ltac:(intros mode root Hempty; inversion Hempty)) Htyping Hscope
        Hgety Hvalue Hbase Hfind Hargs active_mode location Hactive_mode
        Hcallee_color) as [caller_mode [Hcaller_mode Hcaller_color]].
      destruct (Horigins old_snapshot old_mode caller_mode location Hold
        Hold_mode Hcaller_mode Hold_color (or_introl Hcaller_color)) as
        [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
      exists root_mode, root. repeat split; try assumption.
      apply frozen_caller_authority_closure_contains. exact Hroot_color.
    + destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
        method y args sGamma' vals ly cy runtime_mdef location Hwf Htyping
        Hscope Hvalue Hbase Hfind Hargs Hrdm) as
        [caller_T [Hcaller_type [Hshape Hcaller_root]]].
      assert (caller_T = Ty) by congruence. subst caller_T.
      destruct Hshape as [Hmut | [Himm | Hcaller_rdm]].
      * have Hcaller_color : In authority_flow_state
            (independent_active_authority_colors CT h
              (mk_watched_frame caller_authority sGamma rGamma))
            (FlowPowered, location).
        { unfold independent_active_authority_colors.
          eapply executing_authority_typed_mut_root_is_powered.
          rewrite Hmut in Hcaller_root. exact Hcaller_root. }
        destruct (Horigins old_snapshot old_mode FlowPowered location Hold
          Hold_mode (or_introl eq_refl) Hold_color (or_introl Hcaller_color))
          as [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
        exists root_mode, root. repeat split; try assumption.
        apply frozen_caller_authority_closure_contains. exact Hroot_color.
      * have Hmutable := Hruntime old_snapshot Hold old_mode location
          Hold_color.
        have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma
          h location Hwf
          (ltac:(rewrite Himm in Hcaller_root; exact Hcaller_root)).
        congruence.
      * destruct (Horigins old_snapshot old_mode active_mode location Hold
          Hold_mode Hactive_mode Hold_color
          (or_intror (ltac:(rewrite Hcaller_rdm in Hcaller_root;
            exact Hcaller_root)))) as
          [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
        exists root_mode, root. repeat split; try assumption.
        apply frozen_caller_authority_closure_contains. exact Hroot_color.
  - destruct Hold_origin as
      [root_mode [root [Hroot_mode [Hroot_color Hroot]]]].
    exists root_mode, root. repeat split; try assumption.
    apply frozen_caller_authority_closure_contains. exact Hroot_color.
Qed.

(** Untracked nested-call entry for the private statement induction.  The
    head [None] records that this boundary needs no exceptional-return
    snapshot; all older snapshots are advanced through the callee phase and
    retain their stack-aligned age certificates. *)
Lemma private_frozen_statement_enter_call_untracked :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty,
    private_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      private_frozen_statement_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming)
        (None :: advance_frozen_caller_snapshots CT h
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals))) snapshots) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hfrozen [Horigins [Hbefore [Hcovered [Hnested Hcompleted]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind
    Hargs.
  have Hfrozen_copy := Hfrozen.
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  destruct (principled_phased_authority_history_enter_call CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming x method y args
    sGamma' vals ly cy runtime_mdef Ty Hmain Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs) as
    [origins [destination_type [Hdestination Hcallee_main]]].
  have Hcallee_frozen : principled_frozen_authority_history_state CT P Z
      cutoff
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
        (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority sGamma rGamma) incoming)
      (None :: advance_frozen_caller_snapshots CT h
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals))) snapshots) h.
  { eapply principled_frozen_authority_enter_untracked.
    - exact Hcallee_main.
    - exact Haligned.
    - exact Hruntime.
    - exact Hretain.
    - exact Hdangerous.
    - eapply frozen_caller_snapshots_after_safe_call_entry_avoid_protected;
        eauto.
    - eapply frozen_caller_snapshots_after_safe_call_entry_roots_in_heap.
      exact Hroots.
    - eapply frozen_caller_snapshots_after_safe_call_entry_exposures_wf;
        eauto.
    - eapply frozen_caller_snapshots_after_safe_call_entry_resume_roots_safe;
        eauto.
    - eapply frozen_caller_snapshots_after_safe_call_entry_resume_joins_safe;
        eauto.
    - eapply advance_frozen_caller_snapshots_entry_exposure_covered.
      exact Hentry_covered.
    - eapply advance_frozen_caller_snapshots_cover_phase_incoming.
      exact Hphase_covered. }
  have Hcallee_parts := Hcallee_frozen.
  destruct Hcallee_parts as
    [_ [_ [_ [_ [Hcallee_retain [_ [_ [_ [_ [_
      [Hcallee_joins [_ _]]]]]]]]]]]].
  exists origins, destination_type. split; [exact Hdestination|]. split.
  - exact Hcallee_frozen.
  - split.
    + eapply frozen_resume_joins_and_retain_imply_active_resume_justified;
        eauto.
    + split.
      * constructor.
        -- exact I.
        -- eapply advance_frozen_caller_snapshots_before_boundaries.
           exact Hbefore.
      * simpl. split.
        -- apply advance_frozen_caller_snapshots_nested_covered.
           exact Hcovered.
        -- split.
           ++ eapply frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry;
                eauto.
           ++ intros snapshot source_mode source Hsnapshot.
              simpl in Hsnapshot. destruct Hsnapshot as [Hbad | Htail].
              ** discriminate.
              ** eapply frozen_completed_colors_resume_safe_after_safe_call_entry;
                   eauto.
Qed.

Lemma private_fresh_frozen_statement_enter_call_untracked :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty,
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      private_fresh_frozen_statement_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming)
        (None :: advance_frozen_caller_snapshots CT h
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals))) snapshots) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hprivate [Hcomponents [Hprospective Hafter]]] Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs.
  have Hmain := proj1 Hprivate.
  have Hstate := proj1 Hmain.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Hsound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
  destruct (private_frozen_statement_enter_call_untracked CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming snapshots x method y
    args sGamma' vals ly cy runtime_mdef Ty Hprivate Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs) as
    [origins [destination_type [Hdestination Hentry]]].
  have Hentry_state := proj1 (proj1 Hentry).
  have Hcallee_wf : wf_r_config CT
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hentry_state))))).
  exists origins, destination_type. split; [exact Hdestination|]. split.
  - exact Hentry.
  - split.
    + set (boundary := mk_watched_call_boundary
      (mk_watched_frame caller_authority sGamma rGamma)
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) (sqtype Ty)
      (mreturn (mbody runtime_mdef)) (sqtype destination_type)
      (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
    change (frozen_callee_side_mutable_components_after_boundaries CT h
      (mk_watched_frame
        (call_authority caller_authority (sqtype Ty))
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)))
      (None :: advance_frozen_caller_snapshots CT h
        (mk_watched_frame
          (call_authority caller_authority (sqtype Ty))
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals))) snapshots) (boundary :: stack)).
      eapply (frozen_callee_side_components_enter_untracked_safe_call CT h
        caller_authority sGamma mt rGamma stack snapshots x method y args
        sGamma' vals ly cy runtime_mdef Ty boundary); eauto.
    + split.
      * set (boundary := mk_watched_call_boundary
          (mk_watched_frame caller_authority sGamma rGamma)
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) (sqtype Ty)
          (mreturn (mbody runtime_mdef)) (sqtype destination_type)
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
        eapply
          (frozen_callee_side_prospective_components_enter_untracked_safe_call
            CT h caller_authority sGamma mt rGamma stack snapshots x method y
            args sGamma' vals ly cy runtime_mdef Ty boundary); eauto.
      * constructor; [exact I|].
        eapply advance_snapshot_boundaries_after_cutoff. exact Hafter.
Qed.

(** Tracked entry for the exceptional flexible-return shape.  Channel
    freedom is derived from the safe dynamic signature and the absence of
    non-null dynamic RDM roots; it is not a dispatch premise. *)
Lemma private_frozen_statement_enter_call_channel_free :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty,
    private_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    signature_has_no_mutable_roots (msignature runtime_mdef) ->
    (forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) root) ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      private_frozen_statement_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming)
        (enter_nested_frozen_caller_snapshots CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals)))
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) incoming)
          snapshots) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hfrozen [Horigins [Hbefore [Hcovered [Hnested Hcompleted]]]]]
    Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
    Hsignature_safe Hno_rdm.
  have Hfrozen_copy := Hfrozen.
  destruct Hfrozen as
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous [Havoid
      [Hroots [Hexposure [Hresume [Hjoins
        [Hentry_covered Hphase_covered]]]]]]]]]]]].
  destruct (principled_phased_authority_history_enter_call CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming x method y args
    sGamma' vals ly cy runtime_mdef Ty Hmain Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs) as
    [origins [destination_type [Hdestination Hcallee_main]]].
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee := mk_watched_frame
    (call_authority caller_authority (sqtype Ty))
    (mreceiver (msignature runtime_mdef) ::
      mparams (msignature runtime_mdef))
    (mkr_env (Iot ly :: vals))).
  set (caller_colors := executing_authority_color_set CT h caller incoming).
  set (boundary := mk_watched_call_boundary caller
    (mreceiver (msignature runtime_mdef) ::
      mparams (msignature runtime_mdef))
    (mkr_env (Iot ly :: vals)) (sqtype Ty)
    (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  have Hfree : entry_ownership_channel_free boundary.
  { unfold boundary, caller.
    eapply channel_free_boundary_from_safe_signature_without_rdm; eauto. }
  have Hcaller_colors_runtime : authority_colors_runtime_mutable h caller_colors.
  { unfold caller_colors, caller.
    eapply executing_authority_colors_runtime_mutable.
    - exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
    - exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain))))))).
    - exact (proj1 (proj2 (proj2 Hmain))). }
  exists origins, destination_type. split; [exact Hdestination|].
  change (private_frozen_statement_state CT P Z cutoff callee
    (boundary :: stack) caller_colors
    (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors snapshots)
    h).
  have Hcallee_frozen : principled_frozen_authority_history_state CT P Z
      cutoff callee (boundary :: stack) caller_colors
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) h.
  { eapply principled_frozen_authority_enter_nested_channel_free with
      (boundary := boundary) (stack := stack) (h := h)
      (caller_colors := caller_colors) (snapshots := snapshots).
    + exact Hcallee_main.
    + exact Haligned.
    + exact Hruntime.
    + exact Hclosed.
    + exact Hretain.
    + exact Hdangerous.
    + exact Havoid.
    + exact Hcaller_colors_runtime.
    + unfold caller_colors.
      apply executing_authority_color_set_frozen_closed.
    + exact Hfree.
    + eapply frozen_caller_snapshots_after_safe_call_entry_avoid_protected;
        eauto.
    + eapply frozen_caller_snapshots_after_safe_call_entry_roots_in_heap.
      exact Hroots.
    + eapply frozen_caller_snapshots_after_safe_call_entry_exposures_wf;
        eauto.
    + eapply frozen_caller_snapshots_after_safe_call_entry_resume_roots_safe;
        eauto.
    + eapply frozen_caller_snapshots_after_safe_call_entry_resume_joins_safe;
        eauto.
    + eapply frozen_caller_snapshots_after_safe_call_entry_entry_exposure_covered;
        eauto.
    + eapply enter_frozen_caller_snapshots_cover_phase_incoming.
      exact Hphase_covered. }
  have Hcallee_parts := Hcallee_frozen.
  destruct Hcallee_parts as
    [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hcallee_joins _]]]]]]]]]]].
  split; [exact Hcallee_frozen|].
  split.
    + apply frozen_active_resume_origins_imply_justified.
      exact (channel_free_entry_has_active_resume_origins CT h boundary
        (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
          snapshots) Hfree).
    + split.
      * eapply enter_nested_frozen_caller_snapshots_before_boundaries.
        -- unfold boundary. simpl. reflexivity.
        -- exact Hcaller_colors_runtime.
        -- exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
        -- exact Hbefore.
      * split.
        -- apply enter_nested_frozen_caller_snapshots_nested_covered.
           exact Hcovered.
        -- split.
              ** unfold enter_nested_frozen_caller_snapshots. simpl. split.
                 --- eapply nested_frozen_call_head_resume_safe_against_advanced_tail
                   with (boundary := boundary).
                     +++ exact Hfree.
                     +++ unfold caller_colors.
                     apply executing_authority_color_set_frozen_closed.
                     +++ exact Hclosed.
                     +++ exact Hcovered.
                     +++ exact Hnested.
                     +++ exact Hjoins.
                     +++ exact Hcompleted.
                     +++ intros old_snapshot exposure_mode target Hold
                       Hexposure_mode Htarget Hold_safe.
                     have Hwf : wf_r_config CT sGamma rGamma h :=
                       proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
                     have Hsound : authority_context_sound h rGamma
                         caller_authority :=
                       proj1 (proj1 (proj2 (proj2 (proj2 (proj2
                         (proj2 Hmain)))))).
                     have Hcallee_target : In authority_flow_state
                         (executing_authority_color_set CT h callee
                           (executing_authority_color_set CT h caller
                             old_snapshot.(frozen_snapshot_current_resume_exposure)))
                         (exposure_mode, target).
                     { destruct Htarget as [seed [Hseed Hpath]]. exists seed.
                       split.
                       - left.
                         apply executing_authority_color_set_contains_incoming.
                         exact Hseed.
                       - eapply frozen_caller_authority_connected_is_phased.
                         exact Hpath. }
                     destruct (executing_authority_colors_enter_call_covered
                       CT caller_authority sGamma mt rGamma h x method y args
                       sGamma' vals ly cy runtime_mdef Ty
                       old_snapshot.(frozen_snapshot_current_resume_exposure)
                       Hwf Hsound ((proj1 Hexposure) old_snapshot Hold)
                       Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
                       exposure_mode target Hexposure_mode Hcallee_target) as
                       [caller_mode [Hcaller_mode Hcaller_target]].
                     destruct
                       (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
                         CT h caller
                         old_snapshot.(frozen_snapshot_current_resume_exposure)
                         caller_mode target
                         ((proj1 (proj2 Hexposure)) old_snapshot Hold)
                         Hcaller_mode Hcaller_target) as
                       [[old_mode [Hold_mode Hold_target]] |
                        [active_mode [Hactive_mode Hactive_target]]].
                         *** exact (Hold_safe old_mode Hold_mode Hold_target).
                         *** intros Hprotected.
                         eapply (proj1 (proj2 (proj2 (proj2 Hmain))));
                           [exact Hactive_mode| |exact Hprotected].
                         eapply independent_active_authority_colors_in_executing.
                         exact Hactive_target.
                 --- eapply frozen_caller_snapshots_nested_resume_safe_after_safe_call_entry;
                   eauto.
              ** have Htail_completed :=
                frozen_completed_colors_resume_safe_after_safe_call_entry CT
                  P Z cutoff caller_authority sGamma rGamma h stack incoming
                  snapshots mt x method y args sGamma' vals ly cy runtime_mdef
                  Ty Hfrozen_copy Htyping Hscope Hgety Hvalue Hbase Hfind
                  Hargs Hcompleted.
              intros new_snapshot source_mode source Hnew Hsource_mode
                Hsource Hsource_root.
              unfold enter_nested_frozen_caller_snapshots in Hnew.
              simpl in Hnew. destruct Hnew as [Hhead | Htail].
                 --- injection Hhead as Heq. subst new_snapshot. simpl in *.
                 have Hwf : wf_r_config CT sGamma rGamma h :=
                   proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
                 have Hsound : authority_context_sound h rGamma
                     caller_authority :=
                   proj1 (proj1 (proj2 (proj2 (proj2 (proj2
                     (proj2 Hmain)))))).
                 have Hincoming_runtime : authority_colors_runtime_mutable h
                     incoming := proj1 (proj2 (proj2 Hmain)).
                 destruct (executing_authority_colors_enter_call_covered CT
                   caller_authority sGamma mt rGamma h x method y args
                   sGamma' vals ly cy runtime_mdef Ty incoming Hwf Hsound
                   Hincoming_runtime Htyping Hscope Hgety Hvalue Hbase Hfind
                   Hargs source_mode source Hsource_mode Hsource) as
                   [caller_mode [Hcaller_mode Hcaller_source]].
                 eapply Hcallee_joins with
                   (snapshot := nested_frozen_call_head CT h caller callee
                     caller_colors snapshots) (source_mode := caller_mode)
                   (source := source).
                     +++ simpl. left. reflexivity.
                     +++ exact Hcaller_mode.
                     +++ apply frozen_caller_authority_closure_contains.
                     left. split; assumption.
                     +++ exact Hsource_root.
                 --- eapply Htail_completed; eauto.
Qed.

Lemma private_fresh_frozen_statement_enter_call_channel_free :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty,
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    signature_has_no_mutable_roots (msignature runtime_mdef) ->
    (forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) root) ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      private_fresh_frozen_statement_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming)
        (enter_nested_frozen_caller_snapshots CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals)))
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) incoming)
          snapshots) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hprivate [Hcomponents [Hprospective Hafter]]] Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hsignature_safe Hno_rdm.
  have Hphase_state := proj1 (proj1 Hprivate).
  have Hcutoff_bound : cutoff <= dom h :=
    proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hphase_state)))))).
  destruct (private_frozen_statement_enter_call_channel_free CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming snapshots x method y
    args sGamma' vals ly cy runtime_mdef Ty Hprivate Htyping Hscope Hgety
    Hvalue Hbase Hfind Hargs Hsignature_safe Hno_rdm) as
    [origins [destination_type [Hdestination Hentry]]].
  exists origins, destination_type. split; [exact Hdestination|]. split.
  - exact Hentry.
  - split.
    + set (caller := mk_watched_frame caller_authority sGamma rGamma).
    set (callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals))).
    set (caller_colors := executing_authority_color_set CT h caller incoming).
    set (boundary := mk_watched_call_boundary caller
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) (sqtype Ty)
      (mreturn (mbody runtime_mdef)) (sqtype destination_type)
      (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
    change (frozen_callee_side_mutable_components_after_boundaries CT h callee
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) (boundary :: stack)).
    eapply frozen_callee_side_components_enter_nested_without_authority.
    * reflexivity.
    * eapply no_capability_or_rdm_root_has_no_mutable_authority_root.
      -- intros root Hroot. unfold callee.
        eapply safe_signature_without_rdm_has_no_capability_root; eauto.
      -- unfold callee. simpl. exact Hno_rdm.
    * exact Hcomponents.
    + split.
      * eapply
          frozen_callee_side_prospective_components_enter_nested_without_authority.
        -- reflexivity.
        -- eapply no_capability_or_rdm_root_has_no_mutable_authority_root.
           ++ intros root Hroot.
              eapply safe_signature_without_rdm_has_no_capability_root; eauto.
           ++ simpl. exact Hno_rdm.
        -- exact Hprospective.
      * eapply tracked_snapshot_boundaries_after_cutoff_push.
        -- exact Hcutoff_bound.
        -- exact Hafter.
Qed.

(** Synchronized tracked call entry for the eventual strengthened statement
    induction.  The public and private entry lemmas compute the same runtime
    boundary data.  Their proof-valued origin records are identified only by
    proof irrelevance; no semantic equality or dispatch condition is assumed. *)
Lemma private_statement_enter_call_channel_free :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack h ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    signature_has_no_mutable_roots (msignature runtime_mdef) ->
    (forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) root) ->
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        h /\
      private_fresh_frozen_statement_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming)
        (enter_nested_frozen_caller_snapshots CT h
          (mk_watched_frame caller_authority sGamma rGamma)
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals)))
          (executing_authority_color_set CT h
            (mk_watched_frame caller_authority sGamma rGamma) incoming)
          snapshots) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty Hpotential
    Hprivate Htyping Hscope Hgety Hvalue Hbase Hfind Hargs Hsignature Hno_rdm.
  destruct (potential_history_enter_call CT P Z cutoff caller_authority
    sGamma mt rGamma h stack x method y args sGamma' vals ly cy runtime_mdef
    Ty Hpotential Htyping Hscope Hgety Hvalue Hbase Hfind Hargs) as
    [public_origins [public_destination
      [Hpublic_destination Hpublic_entry]]].
  destruct (private_fresh_frozen_statement_enter_call_channel_free CT P Z
    cutoff caller_authority sGamma mt rGamma h stack incoming snapshots x
    method y args sGamma' vals ly cy runtime_mdef Ty Hprivate Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hsignature Hno_rdm) as
    [private_origins [private_destination
      [Hprivate_destination Hprivate_entry]]].
  assert (Hdestination : private_destination = public_destination) by
    congruence.
  subst public_destination.
  assert (Horigins : private_origins = public_origins) by
    apply proof_irrelevance.
  subst public_origins.
  exists private_origins, private_destination.
  split; [exact Hprivate_destination|].
  split; [exact Hpublic_entry|exact Hprivate_entry].
Qed.

(** Synchronized untracked entry for calls whose return does not require the
    exceptional flexible-return classifier.  The [None] head is nevertheless
    stack-aligned, so a nested body cannot accidentally consume an older
    tracked snapshot when it returns. *)
Lemma private_statement_enter_call_untracked :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty,
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    potential_live_history_state CT P Z cutoff caller stack h ->
    private_fresh_frozen_statement_state CT P Z cutoff caller stack incoming
      snapshots h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      let boundary := mk_watched_call_boundary caller
        (mreceiver (msignature runtime_mdef) ::
          mparams (msignature runtime_mdef))
        (mkr_env (Iot ly :: vals)) (sqtype Ty)
        (mreturn (mbody runtime_mdef)) (sqtype destination_type)
        (sqtype (mret (msignature runtime_mdef))) (dom h) origins in
      potential_live_history_state CT P Z cutoff callee (boundary :: stack)
        h /\
      private_fresh_frozen_statement_state CT P Z cutoff callee
        (boundary :: stack)
        (executing_authority_color_set CT h caller incoming)
        (None :: advance_frozen_caller_snapshots CT h callee snapshots) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots x method y args sGamma' vals ly cy runtime_mdef Ty caller callee
    Hpotential Hprivate Htyping Hscope Hgety Hvalue Hbase Hfind Hargs.
  destruct (potential_history_enter_call CT P Z cutoff caller_authority
    sGamma mt rGamma h stack x method y args sGamma' vals ly cy runtime_mdef
    Ty Hpotential Htyping Hscope Hgety Hvalue Hbase Hfind Hargs) as
    [public_origins [public_destination
      [Hpublic_destination Hpublic_entry]]].
  destruct (private_fresh_frozen_statement_enter_call_untracked CT P Z
    cutoff caller_authority sGamma mt rGamma h stack incoming snapshots x
    method y args sGamma' vals ly cy runtime_mdef Ty Hprivate Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs) as
    [private_origins [private_destination
      [Hprivate_destination Hprivate_entry]]].
  assert (Hdestination : private_destination = public_destination) by
    congruence.
  subst public_destination.
  assert (Horigins : private_origins = public_origins) by
    apply proof_irrelevance.
  subst public_origins.
  exists private_origins, private_destination.
  split; [exact Hprivate_destination|].
  split; [exact Hpublic_entry|exact Hprivate_entry].
Qed.

Lemma flexible_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    flexible_live_history_state CT P Z cutoff
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
      flexible_live_history_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack x method
    y args sGamma' vals ly cy runtime_mdef Ty [incoming Hstate] Htyping
    Hscope Hgety Hvalue Hbase Hfind Hargs.
  destruct (principled_phased_authority_history_enter_call CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming x method y args
    sGamma' vals ly cy runtime_mdef Ty Hstate Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs) as
    [origins [destination_type [Hdestination Hentry]]].
  exists origins, destination_type. split; [exact Hdestination|].
  exists (executing_authority_color_set CT h
    (mk_watched_frame caller_authority sGamma rGamma) incoming).
  exact Hentry.
Qed.

(** Entry wrapper for the exceptional flexible-return branch.  The absence
    of dynamic RDM roots is derived there from signature refinement; it is
    not a dispatch premise and does not appear in the public theorem. *)
Lemma principled_local_mutable_rdm_history_enter_call_without_rdm :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    (forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) root) ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      principled_local_mutable_rdm_history_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty Hstate Htyping Hscope
    Hgety Hvalue Hbase Hfind Hargs Hno_rdm.
  destruct (principled_phased_authority_history_enter_call CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming x method y args
    sGamma' vals ly cy runtime_mdef Ty Hstate Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs) as [origins [destination_type [Hdestination Hentry]]].
  exists origins, destination_type. split; [exact Hdestination|].
  split; [exact Hentry|].
  apply no_active_rdm_roots_have_old_mutable_components. exact Hno_rdm.
Qed.

Lemma principled_live_mutable_rdm_history_enter_call_without_rdm :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_live_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    (forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot ly :: vals)) root) ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      principled_live_mutable_rdm_history_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hstate Hcomponents] Htyping Hscope Hgety Hvalue Hbase Hfind Hargs
    Hno_rdm.
  destruct (principled_phased_authority_history_enter_call CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming x method y args
    sGamma' vals ly cy runtime_mdef Ty Hstate Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs) as [origins [destination_type [Hdestination Hentry]]].
  exists origins, destination_type. split; [exact Hdestination|].
  split; [exact Hentry|].
  eapply live_mutable_rdm_components_push_without_active_rdm.
  - reflexivity.
  - exact Hno_rdm.
  - exact Hcomponents.
Qed.

(** General nested-call entry for the private mutable-RDM component package.
    A callee RDM root reflects to a caller root through ordinary viewpoint
    adaptation.  A reflected [Mut] root is caller-owned, a reflected [Imm]
    root cannot have mutable runtime representation, and a reflected [RDM]
    root is covered by the caller's existing component invariant. *)
Lemma principled_live_mutable_rdm_history_enter_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty,
    principled_live_mutable_rdm_history_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    exists origins destination_type,
      static_getType sGamma x = Some destination_type /\
      principled_live_mutable_rdm_history_state CT P Z cutoff
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
          (sqtype (mret (msignature runtime_mdef))) (dom h) origins :: stack)
        (executing_authority_color_set CT h
          (mk_watched_frame caller_authority sGamma rGamma) incoming) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    x method y args sGamma' vals ly cy runtime_mdef Ty
    [Hstate Hcomponents] Htyping Hscope Hgety Hvalue Hbase Hfind Hargs.
  destruct (principled_phased_authority_history_enter_call CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming x method y args
    sGamma' vals ly cy runtime_mdef Ty Hstate Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs) as [origins [destination_type [Hdestination Hentry]]].
  exists origins, destination_type. split; [exact Hdestination|].
  split; [exact Hentry|].
  intros frame root target Hlive Hroot Hroot_runtime Hreachable.
  inversion Hlive; subst.
  - have Hcaller_wf : wf_r_config CT sGamma rGamma h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x
      method y args sGamma' vals ly cy runtime_mdef root Hcaller_wf Htyping
      Hscope Hvalue Hbase Hfind Hargs Hroot) as
      [caller_T [Hcaller_get [Hshape Hcaller_root]]].
    assert (caller_T = Ty) by congruence. subst caller_T.
    destruct Hshape as [Hmut | [Himm | Hrdm]].
    + eapply principled_phased_frame_owned_is_after_cutoff with
        (frame := mk_watched_frame caller_authority sGamma rGamma)
        (stack := stack) (incoming := incoming).
      * exact Hstate.
      * exists root. split.
        -- destruct Hcaller_root as
             [variable [T [Htype [Hroot_value Hqualifier]]]].
           exists variable, T. repeat split; try assumption.
           unfold capability_in_context. left.
           rewrite Hmut in Hqualifier. exact Hqualifier.
        -- eapply mutable_reachable_is_retained. exact Hreachable.
    + have Himmutable := typed_imm_root_runtime_immutable CT sGamma rGamma h
        root Hcaller_wf (ltac:(rewrite Himm in Hcaller_root;
          exact Hcaller_root)).
      congruence.
    + eapply Hcomponents.
      * constructor.
      * rewrite Hrdm in Hcaller_root. exact Hcaller_root.
      * exact Hroot_runtime.
      * exact Hreachable.
  - simpl in H. destruct H as [Heq | Hin].
    + subst. eapply Hcomponents; eauto. constructor.
    + eapply Hcomponents; eauto. constructor. exact Hin.
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

(** A dangerous color created independently by the active frame belongs to
    the prospective component of one of that frame's mutable-authority
    roots.  Promotions are handled by restarting at the frame-owned anchor,
    then projecting the remaining frozen path prospectively. *)
Lemma independent_active_dangerous_has_prospective_root :
  forall CT h active mode target,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv)
      active.(frame_authority) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (independent_active_authority_colors CT h active) (mode, target) ->
    exists root,
      mutable_authority_root active h root /\
      frozen_caller_authority_connected CT h active
        (FlowProspective, root) (FlowProspective, target).
Proof.
  intros CT h active mode target Hwf Hsound Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    active seed (mode, target) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Howned Hfrozen]]].
  - inversion Hseed; subst.
    + inversion H.
    + destruct H as [anchor [Heq Howned]]. inversion Heq; subst.
      destruct Howned as [root [Hroot Hroot_anchor]].
      exists root. split.
      * have Hruntime : r_muttype h root = Some Mut_r.
        { eapply frame_capability_root_runtime_mutable; eauto. }
        destruct Hroot as
          [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
        -- left. exists variable, T. repeat split; assumption.
        -- right. split.
           ++ exists variable, T. repeat split; assumption.
           ++ exact Hruntime.
      * eapply rt_trans.
        -- eapply frozen_caller_prospective_retained_forward.
           exact Hroot_anchor.
        -- exact (frozen_caller_connected_as_prospective CT h active
             (FlowPowered, anchor) (mode, target) Hfrozen).
  - destruct Howned as [root [Hroot Hroot_anchor]].
    exists root. split.
    + have Hruntime : r_muttype h root = Some Mut_r.
      { eapply frame_capability_root_runtime_mutable; eauto. }
      destruct Hroot as
        [variable [T [Htype [Hvalue [Hmut | [Hrdm Hauthority]]]]]].
      * left. exists variable, T. repeat split; assumption.
      * right. split.
        -- exists variable, T. repeat split; assumption.
        -- exact Hruntime.
    + eapply rt_trans.
      * eapply frozen_caller_prospective_retained_forward.
        exact Hroot_anchor.
      * exact (frozen_caller_connected_as_prospective CT h active
          (FlowPowered, anchor) (mode, target) Hfrozen).
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

Lemma frozen_callee_side_prospective_components_after_safe_field_update :
  forall CT P Z cutoff active stack incoming snapshots h lx old field written,
    principled_phased_authority_live_history_state CT P Z cutoff
      active stack incoming h ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    runtime_getObj h lx = Some old ->
    authority_safe_field_endpoints CT h active lx written ->
    frozen_callee_side_prospective_components_after_boundaries CT
      (update_field h lx field (Iot written)) active
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) active snapshots) stack.
Proof.
  intros CT P Z cutoff active stack incoming snapshots h lx old field written
    Hstate Hold Hobj Hendpoints snapshot boundary above below Hpartition.
  destruct (advance_frozen_snapshot_live_partition_reflects CT
    (update_field h lx field (Iot written)) active snapshots stack snapshot
    boundary above below Hpartition) as [old_snapshot Hold_partition].
  have Hold_components := Hold old_snapshot boundary above below
    Hold_partition.
  have Hframes := proj1 (proj2 (proj2 (proj2 (proj2 Hstate)))).
  have Hsounds := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Habove_frames := live_call_partition_above_frames_wf CT h active stack
    boundary above below (frozen_snapshot_live_partition_is_live_call
      snapshots stack old_snapshot boundary above below active Hold_partition)
    Hframes.
  have Habove_sounds := live_call_partition_above_frames_authority_sound h
    active stack boundary above below
    (frozen_snapshot_live_partition_is_live_call snapshots stack old_snapshot
      boundary above below active Hold_partition) Hsounds.
  eapply live_prospective_mutable_authority_components_after_safe_field_update;
    eauto.
Qed.

Lemma private_fresh_frozen_statement_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h',
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma' rGamma') stack incoming
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h'
    [Hprivate [Hcomponents [Hprospective Hafter]]] Htyping Hscope Heval.
  have Hfrozen := proj1 Hprivate.
  have Hmain := proj1 Hfrozen.
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Heffect := typed_field_write_component_effect CT authority sGamma mt
    rGamma h x field y sGamma' rGamma' h' Hwf Htyping Hscope Heval.
  have Hpost := private_frozen_statement_after_field_write CT P Z cutoff
    authority sGamma mt rGamma h stack incoming snapshots x field y sGamma'
    rGamma' h' Hprivate Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'. split; [exact Hpost|].
  destruct Heffect as
    [[Hruntimes [Hmutable [Hretained Howned]]] |
     [lx [old [written [Hheap [Hobj Hendpoints]]]]]].
  - split.
    + eapply frozen_callee_side_components_after_graph_reflection; eauto.
    + split.
      * eapply frozen_callee_side_prospective_components_after_graph_reflection;
          eauto.
      * eapply advance_snapshot_boundaries_after_cutoff. exact Hafter.
  - subst h'.
    split.
    + eapply frozen_callee_side_components_after_safe_field_update; eauto.
    + split.
      * eapply frozen_callee_side_prospective_components_after_safe_field_update;
          eauto.
      * eapply advance_snapshot_boundaries_after_cutoff. exact Hafter.
Qed.

Lemma private_statement_preservation_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    private_statement_preservation_result CT P Z cutoff authority sGamma'
      rGamma' stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h' Hpotential Hprivate Htyping Hscope Heval.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Heffect := typed_field_write_component_effect CT authority sGamma mt
    rGamma h x field y sGamma' rGamma' h' Hwf Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  have Hind_runtime : authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h
        (mk_watched_frame authority sGamma rGamma)).
  { eapply executing_authority_colors_runtime_mutable.
    - exact Hwf.
    - exact (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Hmain))))))).
    - intros mode location Hempty. inversion Hempty. }
  have Hind_safe : forall active_mode location,
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma))
        (active_mode, location) ->
      ~ In Loc Z location.
  { intros active_mode location Hmode Hcolor Hprotected.
    eapply (proj1 (proj2 (proj2 (proj2 Hmain))));
      [exact Hmode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  unfold private_statement_preservation_result. split.
  - eapply principled_phased_authority_history_after_field_write; eauto.
  - split.
    + eapply private_fresh_frozen_statement_after_field_write; eauto.
    + split.
      * apply advance_frozen_caller_snapshots_metadata_eq.
      * destruct Heffect as
          [[Hruntimes [Hmutable [Hretained Howned]]] |
           [lx [old [written [Hheap [Hobj Hendpoints]]]]]].
        -- eapply
             frozen_snapshot_list_resume_exposure_reflected_after_graph_reflection;
             eauto.
        -- subst h'.
           eapply
             frozen_snapshot_list_resume_exposure_reflected_after_safe_field_update;
             eauto.
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

Lemma resumed_caller_incoming_has_frozen_origin :
  forall CT h caller caller_incoming state,
    authority_mode_dangerous (fst state) ->
    In authority_flow_state caller_incoming state ->
    resumed_caller_frozen_origin CT h caller caller_incoming state.
Proof.
  intros CT h caller caller_incoming state Hmode Hincoming.
  exists state. split.
  - left. split; assumption.
  - apply rt_refl.
Qed.

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

(** Root-scoped pop classification for a harmless frozen/active overlap.
    The overlap itself may be fresh and is therefore not forbidden.  Its
    captured resume-root witness is classified by the snapshot's pairwise
    join certificate; the requested old caller target is already present in
    the frozen resume-exposure set. *)
Lemma tracked_active_overlap_join_has_class_from_resume_origin :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    (exists root_mode root,
      authority_mode_dangerous root_mode /\
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (root_mode, root) /\
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) target ->
    r_muttype h target = Some Mut_r ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (FlowProspective, target).
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming target Hfull
    [root_mode [root [Hroot_mode [Hroot_color Hroot]]]]
    Htarget Htarget_runtime.
  destruct Hfull as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
      Hphase_covered).
  have Hsnapshot : List.In (Some snapshot) (Some snapshot :: snapshots) by
    (simpl; auto).
  have Htarget_exposure : In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure)
      (FlowProspective, target).
  { eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto. }
  destruct (Hjoins snapshot root_mode root Hsnapshot Hroot_mode Hroot_color
    Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hsafe].
  - left. eapply (Hentry_covered snapshot entry_mode root Hsnapshot
      Hentry_mode Hentry Hroot). exact Htarget_exposure.
  - right. right. split; [exact Htarget_exposure|].
    intros mode location Hmode Hcolor. eapply Hsafe; eauto.
Qed.

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

Lemma frozen_nonjoin_step_is_phased :
  forall CT h frame source target,
    frozen_caller_authority_nonjoin_step CT h source target ->
    phased_authority_frame_step CT h frame source target.
Proof.
  intros CT h frame source target Hstep. inversion Hstep; subst.
  - apply phased_authority_retained. exact H.
  - apply phased_authority_prospective_retained. exact H.
  - apply phased_authority_prospective_rdm_backward. exact H.
  - apply phased_authority_reverse_rdm. exact H.
  - apply phased_authority_mark_prospective.
Qed.

Lemma frozen_nonjoin_step_location_effect :
  forall CT h source target,
    frozen_caller_authority_nonjoin_step CT h source target ->
    snd source = snd target \/
    retained_mut_edge CT h (snd source) (snd target) \/
    mutable_edge CT h (snd target) (snd source).
Proof.
  intros CT h source target Hstep. inversion Hstep; subst; simpl.
  - right. left. exact H.
  - right. left. exact H.
  - right. right. exact H.
  - right. right. exact H.
  - left. reflexivity.
Qed.

Lemma frozen_nonjoin_step_preserves_dangerous :
  forall CT h source target,
    authority_mode_dangerous (fst source) ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    authority_mode_dangerous (fst target).
Proof.
  intros CT h source target Hmode Hstep. inversion Hstep; subst; simpl in *;
    try exact Hmode; right; reflexivity.
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

(** Relational structural measure for the lossless provenance object.  The
    derivation remains proof-irrelevant in [Prop]; recording its height as a
    second proposition nevertheless permits well-founded induction when a
    fresh-return path is rerouted through a strictly smaller predecessor. *)
Inductive tracked_resume_frozen_color_derivation_has_height
  CT h Z callee callee_incoming caller caller_incoming snapshot :
  forall state,
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot state -> nat -> Prop :=
| tracked_resume_snapshot_height : forall state Hsnapshot Hincoming Horigin,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot state
      (tracked_resume_from_snapshot CT h Z callee callee_incoming caller
        caller_incoming snapshot state Hsnapshot Hincoming Horigin) 1
| tracked_resume_owned_height : forall anchor Howned Hcallee,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (FlowPowered, anchor)
      (tracked_resume_from_caller_owned CT h Z callee callee_incoming caller
        caller_incoming snapshot anchor Howned Hcallee) 1
| tracked_resume_nonjoin_height : forall source target previous Hstep n,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot source previous n ->
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot target
      (tracked_resume_by_nonjoin CT h Z callee callee_incoming caller
        caller_incoming snapshot source target previous Hstep) (S n)
| tracked_resume_join_height : forall mode left right Hmode previous
    Hleft Hright n,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot (mode, left) previous n ->
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot (FlowProspective, right)
      (tracked_resume_by_frame_join CT h Z callee callee_incoming caller
        caller_incoming snapshot mode left right Hmode previous Hleft Hright)
      (S n).

Lemma tracked_resume_frozen_color_derivation_has_some_height :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot state
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot state),
    exists height,
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot state derivation height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot.
  fix IH 2. intros state derivation. destruct derivation.
  - exists 1. constructor.
  - exists 1. constructor.
  - destruct (IH source derivation) as [height Hheight]. exists (S height).
    constructor. exact Hheight.
  - destruct (IH (mode, left) derivation) as [height Hheight].
    exists (S height).
    constructor. exact Hheight.
Qed.

(** Older frozen slots carried beneath a nested tracked call have a
    different provenance shape from the immediate caller.  Their colors are
    genuine frozen bases, but need not occur in the immediate caller's
    incoming set and therefore must not be given a fabricated
    [resumed_caller_frozen_origin].  This separate derivation records exactly
    the caller-frame flow followed while the nested call is popped. *)
Inductive nested_frozen_pop_derivation
  (CT : class_table) (h : heap)
  (caller : watched_frame) (snapshot : frozen_caller_color_snapshot) :
  authority_flow_state -> Prop :=
| nested_pop_from_snapshot : forall state,
    In authority_flow_state snapshot.(frozen_snapshot_current_colors) state ->
    nested_frozen_pop_derivation CT h caller snapshot state
| nested_pop_by_nonjoin : forall source target,
    nested_frozen_pop_derivation CT h caller snapshot source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    nested_frozen_pop_derivation CT h caller snapshot target
| nested_pop_by_frame_join : forall mode left right,
    authority_mode_dangerous mode ->
    nested_frozen_pop_derivation CT h caller snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    nested_frozen_pop_derivation CT h caller snapshot
      (FlowProspective, right).

Inductive nested_frozen_pop_derivation_has_height CT h caller snapshot :
  forall state,
    nested_frozen_pop_derivation CT h caller snapshot state -> nat -> Prop :=
| nested_pop_snapshot_height : forall state Hsnapshot,
    nested_frozen_pop_derivation_has_height CT h caller snapshot state
      (nested_pop_from_snapshot CT h caller snapshot state Hsnapshot) 1
| nested_pop_nonjoin_height : forall source target previous Hstep n,
    nested_frozen_pop_derivation_has_height CT h caller snapshot source
      previous n ->
    nested_frozen_pop_derivation_has_height CT h caller snapshot target
      (nested_pop_by_nonjoin CT h caller snapshot source target previous Hstep)
      (S n)
| nested_pop_join_height : forall mode left right Hmode previous Hleft Hright n,
    nested_frozen_pop_derivation_has_height CT h caller snapshot (mode, left)
      previous n ->
    nested_frozen_pop_derivation_has_height CT h caller snapshot
      (FlowProspective, right)
      (nested_pop_by_frame_join CT h caller snapshot mode left right Hmode
        previous Hleft Hright) (S n).

Lemma nested_frozen_pop_derivation_has_some_height :
  forall CT h caller snapshot state
    (derivation : nested_frozen_pop_derivation CT h caller snapshot state),
    exists height,
      nested_frozen_pop_derivation_has_height CT h caller snapshot state
        derivation height.
Proof.
  intros CT h caller snapshot. fix IH 2. intros state derivation.
  destruct derivation.
  - exists 1. constructor.
  - destruct (IH source derivation) as [height Hheight].
    exists (S height). constructor. exact Hheight.
  - destruct (IH (mode, left) derivation) as [height Hheight].
    exists (S height). constructor. exact Hheight.
Qed.

Lemma nested_frozen_pop_step_derives :
  forall CT h caller snapshot source target,
    authority_mode_dangerous (fst source) ->
    nested_frozen_pop_derivation CT h caller snapshot source ->
    frozen_caller_authority_step CT h caller source target ->
    nested_frozen_pop_derivation CT h caller snapshot target.
Proof.
  intros CT h caller snapshot source target Hmode Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply nested_pop_by_nonjoin; eauto.
    apply frozen_nonjoin_retained. exact H.
  - eapply nested_pop_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_retained. exact H.
  - eapply nested_pop_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_rdm_backward. exact H.
  - eapply nested_pop_by_nonjoin; eauto.
    apply frozen_nonjoin_reverse_rdm. exact H.
  - eapply nested_pop_by_frame_join; eauto.
  - eapply nested_pop_by_frame_join; eauto.
  - eapply nested_pop_by_nonjoin; eauto.
    apply frozen_nonjoin_mark_prospective.
Qed.

Lemma nested_frozen_pop_connected_derives :
  forall CT h caller snapshot source target,
    authority_mode_dangerous (fst source) ->
    nested_frozen_pop_derivation CT h caller snapshot source ->
    frozen_caller_authority_connected CT h caller source target ->
    nested_frozen_pop_derivation CT h caller snapshot target.
Proof.
  intros CT h caller snapshot source target Hmode Hsource Hconnected.
  induction Hconnected.
  - eapply nested_frozen_pop_step_derives; eauto.
  - exact Hsource.
  - have Hmiddle_mode : authority_mode_dangerous (fst y).
    { eapply frozen_caller_authority_connected_preserves_dangerous; eauto. }
    have Hmiddle := IHHconnected1 Hmode Hsource.
    exact (IHHconnected2 Hmiddle_mode Hmiddle).
Qed.

(** Second-order provenance for advancing an older snapshot's resume
    exposure across a nested return.  This is intentionally distinct from
    [nested_frozen_pop_derivation]: exposure membership is not ordinary
    frozen-color membership, and conflating the two would silently assume
    the very nested-pop fact that must be proved. *)
Inductive nested_resume_exposure_pop_derivation
  (CT : class_table) (h : heap) (caller : watched_frame)
  (exposure : Ensemble authority_flow_state) :
  authority_flow_state -> Prop :=
| nested_exposure_from_base : forall state,
    In authority_flow_state exposure state ->
    nested_resume_exposure_pop_derivation CT h caller exposure state
| nested_exposure_by_nonjoin : forall source target,
    nested_resume_exposure_pop_derivation CT h caller exposure source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    nested_resume_exposure_pop_derivation CT h caller exposure target
| nested_exposure_by_frame_join : forall mode left right,
    authority_mode_dangerous mode ->
    nested_resume_exposure_pop_derivation CT h caller exposure (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    nested_resume_exposure_pop_derivation CT h caller exposure
      (FlowProspective, right).

Inductive nested_resume_exposure_pop_derivation_has_height
  CT h caller exposure :
  forall state,
    nested_resume_exposure_pop_derivation CT h caller exposure state ->
    nat -> Prop :=
| nested_exposure_base_height : forall state Hbase,
    nested_resume_exposure_pop_derivation_has_height CT h caller exposure
      state
      (nested_exposure_from_base CT h caller exposure state Hbase) 1
| nested_exposure_nonjoin_height : forall source target previous Hstep n,
    nested_resume_exposure_pop_derivation_has_height CT h caller exposure
      source previous n ->
    nested_resume_exposure_pop_derivation_has_height CT h caller exposure
      target
      (nested_exposure_by_nonjoin CT h caller exposure source target previous
        Hstep) (S n)
| nested_exposure_join_height : forall mode left right Hmode previous
    Hleft Hright n,
    nested_resume_exposure_pop_derivation_has_height CT h caller exposure
      (mode, left) previous n ->
    nested_resume_exposure_pop_derivation_has_height CT h caller exposure
      (FlowProspective, right)
      (nested_exposure_by_frame_join CT h caller exposure mode left right
        Hmode previous Hleft Hright) (S n).

Lemma nested_resume_exposure_pop_derivation_has_some_height :
  forall CT h caller exposure state
    (derivation : nested_resume_exposure_pop_derivation CT h caller exposure
      state),
    exists height,
      nested_resume_exposure_pop_derivation_has_height CT h caller exposure
        state derivation height.
Proof.
  intros CT h caller exposure.
  fix IH 2. intros state derivation. destruct derivation.
  - exists 1. constructor.
  - destruct (IH source derivation) as [height Hheight].
    exists (S height). constructor. exact Hheight.
  - destruct (IH (mode, left) derivation) as [height Hheight].
    exists (S height). constructor. exact Hheight.
Qed.

Lemma nested_resume_exposure_pop_step_derives :
  forall CT h caller exposure source target,
    authority_mode_dangerous (fst source) ->
    nested_resume_exposure_pop_derivation CT h caller exposure source ->
    frozen_caller_authority_step CT h caller source target ->
    nested_resume_exposure_pop_derivation CT h caller exposure target.
Proof.
  intros CT h caller exposure source target Hmode Hsource Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_retained. exact H.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_retained. exact H.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_prospective_rdm_backward. exact H.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_reverse_rdm. exact H.
  - eapply nested_exposure_by_frame_join; eauto.
  - eapply nested_exposure_by_frame_join; eauto.
  - eapply nested_exposure_by_nonjoin; eauto.
    apply frozen_nonjoin_mark_prospective.
Qed.

Lemma nested_resume_exposure_pop_connected_derives :
  forall CT h caller exposure source target,
    authority_mode_dangerous (fst source) ->
    nested_resume_exposure_pop_derivation CT h caller exposure source ->
    frozen_caller_authority_connected CT h caller source target ->
    nested_resume_exposure_pop_derivation CT h caller exposure target.
Proof.
  intros CT h caller exposure source target Hmode Hsource Hconnected.
  induction Hconnected.
  - eapply nested_resume_exposure_pop_step_derives; eauto.
  - exact Hsource.
  - have Hmiddle_mode : authority_mode_dangerous (fst y).
    { eapply frozen_caller_authority_connected_preserves_dangerous; eauto. }
    have Hmiddle := IHHconnected1 Hmode Hsource.
    exact (IHHconnected2 Hmiddle_mode Hmiddle).
Qed.

Lemma nested_resume_exposure_derivation_has_base_path :
  forall CT h caller exposure state,
    nested_resume_exposure_pop_derivation CT h caller exposure state ->
    exists base,
      In authority_flow_state exposure base /\
      frozen_caller_authority_connected CT h caller base state.
Proof.
  intros CT h caller exposure state Hderivation.
  induction Hderivation as
    [state Hbase
    |source target Hsource IH Hstep
    |mode left right Hmode Hsource IH Hleft Hright].
  - exists state. split; [exact Hbase|apply rt_refl].
  - destruct IH as [base [Hbase Hpath]]. exists base. split; [exact Hbase|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    eapply frozen_nonjoin_step_in_frame. exact Hstep.
  - destruct IH as [base [Hbase Hpath]]. exists base. split; [exact Hbase|].
    eapply rt_trans; [exact Hpath|]. apply rt_step.
    destruct Hmode as [-> | ->].
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

Lemma nested_resume_exposure_derivation_preserves_dangerous :
  forall CT h caller exposure state,
    (forall mode location,
      In authority_flow_state exposure (mode, location) ->
      authority_mode_dangerous mode) ->
    nested_resume_exposure_pop_derivation CT h caller exposure state ->
    authority_mode_dangerous (fst state).
Proof.
  intros CT h caller exposure state Hdangerous Hderivation.
  destruct (nested_resume_exposure_derivation_has_base_path CT h caller
    exposure state Hderivation) as [base [Hbase Hpath]].
  eapply frozen_caller_authority_connected_preserves_dangerous;
    [|exact Hpath].
  destruct base as [mode location]. simpl. eapply Hdangerous. exact Hbase.
Qed.

Lemma nested_resume_exposure_closure_derives :
  forall CT h caller exposure state,
    (forall mode location,
      In authority_flow_state exposure (mode, location) ->
      authority_mode_dangerous mode) ->
    In authority_flow_state
      (frozen_caller_authority_closure CT h caller exposure) state ->
    nested_resume_exposure_pop_derivation CT h caller exposure state.
Proof.
  intros CT h caller exposure state Hdangerous
    [source [Hsource Hconnected]].
  have Hsource_mode : authority_mode_dangerous (fst source).
  { destruct source as [mode location]. simpl in *.
    eapply Hdangerous. exact Hsource. }
  eapply nested_resume_exposure_pop_connected_derives; eauto.
  apply nested_exposure_from_base. exact Hsource.
Qed.

Lemma advanced_snapshot_resume_exposure_has_pop_derivation :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    caller old_snapshot state,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    List.In (Some old_snapshot) snapshots ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot).(
        frozen_snapshot_current_resume_exposure) state ->
    nested_resume_exposure_pop_derivation CT h caller
      old_snapshot.(frozen_snapshot_current_resume_exposure) state.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h
    caller old_snapshot state Hfull Hold Hstate.
  destruct Hfull as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  unfold advance_frozen_caller_snapshot in Hstate. simpl in Hstate.
  eapply nested_resume_exposure_closure_derives; [|exact Hstate].
  intros mode location Hcolor.
  eapply (proj1 (proj2 (proj2 Hexposure))) with
    (snapshot := old_snapshot).
  - simpl. right. exact Hold.
  - exact Hcolor.
Qed.

Lemma nested_resume_exposure_derivation_maps_to_frozen :
  forall CT h caller exposure head state,
    Included authority_flow_state exposure
      head.(frozen_snapshot_current_colors) ->
    nested_resume_exposure_pop_derivation CT h caller exposure state ->
    nested_frozen_pop_derivation CT h caller head state.
Proof.
  intros CT h caller exposure head state Hincluded Hderivation.
  induction Hderivation.
  - apply nested_pop_from_snapshot. apply Hincluded. exact H.
  - eapply nested_pop_by_nonjoin; eauto.
  - eapply nested_pop_by_frame_join; eauto.
Qed.

Lemma nested_entry_origin_exposure_included_in_head :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    older source_mode source,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    frozen_caller_snapshots_nested_covered (Some head :: snapshots) ->
    List.In (Some older) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state older.(frozen_snapshot_entry_colors)
      (source_mode, source) ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) source ->
    Included authority_flow_state
      older.(frozen_snapshot_current_resume_exposure)
      head.(frozen_snapshot_current_colors).
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h older
    source_mode source Hfull Hnested Hold Hmode Hentry_color Hroot.
  destruct Hfull as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  simpl in Hnested. destruct Hnested as [Hhead_covers Htail_nested].
  intros state Hstate.
  eapply Hhead_covers; [exact Hold|].
  eapply Hentry with (snapshot := older) (source_mode := source_mode)
    (source := source).
  - simpl. right. exact Hold.
  - exact Hmode.
  - exact Hentry_color.
  - exact Hroot.
  - exact Hstate.
Qed.

Lemma nested_entry_origin_exposure_derivation_maps_to_head :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    older source_mode source caller state,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    frozen_caller_snapshots_nested_covered (Some head :: snapshots) ->
    List.In (Some older) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state older.(frozen_snapshot_entry_colors)
      (source_mode, source) ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) source ->
    nested_resume_exposure_pop_derivation CT h caller
      older.(frozen_snapshot_current_resume_exposure) state ->
    nested_frozen_pop_derivation CT h caller head state.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h older
    source_mode source caller state Hfull Hnested Hold Hmode Hentry Hroot
    Hderivation.
  eapply nested_resume_exposure_derivation_maps_to_frozen; [|exact Hderivation].
  eapply nested_entry_origin_exposure_included_in_head; eauto.
Qed.

(** Classification used only to transport older frozen slots across the
    immediate pop.  Unlike [tracked_resume_frozen_color_class], the completed
    callee alternative deliberately carries no immediate-caller origin: an
    older frozen base does not in general have one. *)
Definition nested_frozen_pop_color_class
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (callee_incoming : Ensemble authority_flow_state)
  (snapshot : frozen_caller_color_snapshot)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state snapshot.(frozen_snapshot_current_colors) state \/
  In authority_flow_state
    (executing_authority_color_set CT h callee callee_incoming) state \/
  (In authority_flow_state
      snapshot.(frozen_snapshot_current_resume_exposure) state /\
   forall mode location,
     authority_mode_dangerous mode ->
     In authority_flow_state
       snapshot.(frozen_snapshot_current_resume_exposure) (mode, location) ->
     ~ In Loc Z location).

(** Second-order class for an older resume-exposure image.  Existing
    exposure membership remains latent; only colors introduced while the
    immediate caller resumes are classified through the tracked head. *)
Definition nested_resume_exposure_pop_color_class
  (CT : class_table) (h : heap) (Z : Ensemble Loc)
  (callee : watched_frame) (callee_incoming : Ensemble authority_flow_state)
  (head older : frozen_caller_color_snapshot)
  (state : authority_flow_state) : Prop :=
  In authority_flow_state
    older.(frozen_snapshot_current_resume_exposure) state \/
  nested_frozen_pop_color_class CT h Z callee callee_incoming head state.

Lemma nested_frozen_pop_color_class_runtime_mutable :
  forall CT P Z cutoff callee boundary stack incoming head snapshots h state,
    principled_frozen_authority_history_state CT P Z cutoff callee
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    nested_frozen_pop_color_class CT h Z callee incoming head state ->
    r_muttype h (snd state) = Some Mut_r.
Proof.
  intros CT P Z cutoff callee boundary stack incoming head snapshots h
    [mode location] Hstate Hclass. simpl in *.
  destruct Hstate as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  destruct Hclass as [Hfrozen | [Hcallee | [Hexposure_color _]]].
  - eapply Hruntime; [simpl; auto|exact Hfrozen].
  - have Hcallee_wf : wf_r_config CT callee.(frame_senv)
        callee.(frame_renv) h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hcallee_sound : authority_context_sound h callee.(frame_renv)
        callee.(frame_authority) :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
    have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
      proj1 (proj2 (proj2 Hmain)).
    eapply executing_authority_colors_runtime_mutable; eauto.
  - eapply (proj1 Hexposure); [simpl; auto|exact Hexposure_color].
Qed.

Lemma nested_frozen_pop_color_class_avoids_protected :
  forall CT P Z cutoff callee boundary stack incoming head snapshots h
    mode location,
    principled_frozen_authority_history_state CT P Z cutoff callee
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    authority_mode_dangerous mode ->
    nested_frozen_pop_color_class CT h Z callee incoming head
      (mode, location) ->
    ~ In Loc Z location.
Proof.
  intros CT P Z cutoff callee boundary stack incoming head snapshots h
    mode location Hstate Hmode Hclass.
  destruct Hstate as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  destruct Hclass as [Hfrozen | [Hcallee | [Hexposure_color Hsafe]]].
  - eapply Havoid; [simpl; auto|exact Hmode|exact Hfrozen].
  - have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
    eapply Hseparated; eauto.
  - eapply Hsafe; eauto.
Qed.

Lemma nested_resume_exposure_pop_color_class_avoids_protected :
  forall CT P Z cutoff callee boundary stack incoming head snapshots h older
    mode location,
    principled_frozen_authority_history_state CT P Z cutoff callee
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    frozen_snapshot_resume_exposure_avoids Z older ->
    authority_mode_dangerous mode ->
    nested_resume_exposure_pop_color_class CT h Z callee incoming head older
      (mode, location) ->
    ~ In Loc Z location.
Proof.
  intros CT P Z cutoff callee boundary stack incoming head snapshots h older
    mode location Hfull Hold_safe Hmode [Hold | Hnested].
  - eapply Hold_safe; eauto.
  - eapply nested_frozen_pop_color_class_avoids_protected; eauto.
Qed.

(** A tracked derivation that has not crossed a caller-frame RDM join is
    still represented by the frozen snapshot.  Caller-owned bases are folded
    into the same set by the exceptional channel-free pop argument, and
    non-join steps remain there because the snapshot is closed under the
    completed callee phase.  Otherwise the first alternative exposes a
    concrete join predecessor with a strictly smaller derivation. *)
Lemma tracked_derivation_is_snapshot_or_has_frame_join_predecessor :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot state
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot state)
    derivation_height,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot state derivation
      derivation_height ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h callee
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors) state \/
    exists predecessor_mode predecessor_location predecessor
      predecessor_height,
      authority_mode_dangerous predecessor_mode /\
      tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
        caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) /\
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) predecessor
        predecessor_height /\
      typed_root RDM caller.(frame_senv) caller.(frame_renv)
        predecessor_location /\
      S predecessor_height <= derivation_height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot state
    derivation derivation_height Hheight Hclosed Howned_snapshot.
  induction Hheight as
    [state Hsnapshot Hincoming Horigin
    |anchor Howned Hcallee
    |source target previous Hstep n Hprevious_height IH
    |mode left right Hmode previous Hleft Hright n Hprevious_height IH].
  - left. exact Hsnapshot.
  - left. eapply Howned_snapshot; eauto.
  - destruct IH as [Hsource_snapshot | Hjoin].
    + left. eapply Hclosed. exists source. split; [exact Hsource_snapshot|].
      apply rt_step. eapply frozen_nonjoin_step_in_frame. exact Hstep.
    + right. destruct Hjoin as
        [predecessor_mode [predecessor_location [predecessor
          [predecessor_height
            [Hpredecessor_mode [Hpredecessor
              [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
      exists predecessor_mode, predecessor_location, predecessor,
        predecessor_height. repeat split; try assumption. lia.
  - right. exists mode, left, previous, n.
    repeat split; try assumption. lia.
Qed.

Lemma nested_frozen_pop_derivation_is_snapshot_or_has_join_predecessor :
  forall CT h callee caller snapshot state
    (derivation : nested_frozen_pop_derivation CT h caller snapshot state)
    derivation_height,
    nested_frozen_pop_derivation_has_height CT h caller snapshot state
      derivation derivation_height ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h callee
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors) state \/
    exists predecessor_mode predecessor_location predecessor
      predecessor_height,
      authority_mode_dangerous predecessor_mode /\
      nested_frozen_pop_derivation CT h caller snapshot
        (predecessor_mode, predecessor_location) /\
      nested_frozen_pop_derivation_has_height CT h caller snapshot
        (predecessor_mode, predecessor_location) predecessor
        predecessor_height /\
      typed_root RDM caller.(frame_senv) caller.(frame_renv)
        predecessor_location /\
      S predecessor_height <= derivation_height.
Proof.
  intros CT h callee caller snapshot state derivation derivation_height
    Hheight Hclosed.
  induction Hheight as
    [state Hsnapshot
    |source target previous Hstep n Hprevious_height IH
    |mode left right Hmode previous Hleft Hright n Hprevious_height IH].
  - left. exact Hsnapshot.
  - destruct IH as [Hsource_snapshot | Hjoin].
    + left. eapply Hclosed. exists source. split; [exact Hsource_snapshot|].
      apply rt_step. eapply frozen_nonjoin_step_in_frame. exact Hstep.
    + right. destruct Hjoin as
        [predecessor_mode [predecessor_location [predecessor
          [predecessor_height
            [Hpredecessor_mode [Hpredecessor
              [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
      exists predecessor_mode, predecessor_location, predecessor,
        predecessor_height. repeat split; try assumption. lia.
  - right. exists mode, left, previous, n.
    repeat split; try assumption. lia.
Qed.

(** At an exceptional channel-free return, it is enough to know that the
    returned location itself cannot carry a dangerous frozen caller color.
    The preceding decomposition then rules out its snapshot alternative and
    yields the join predecessor needed for directional rerouting.  Requiring
    disjointness for every callee-owned location would be unnecessarily
    stronger than this argument. *)
Lemma tracked_return_derivation_has_frame_join_predecessor :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    return_mode return_location
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (return_mode, return_location))
    derivation_height,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (return_mode, return_location) derivation derivation_height ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h callee
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    (forall mode,
      authority_mode_dangerous mode ->
      ~ In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (mode, return_location)) ->
    authority_mode_dangerous return_mode ->
    exists predecessor_mode predecessor_location predecessor
      predecessor_height,
      authority_mode_dangerous predecessor_mode /\
      tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
        caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) /\
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) predecessor
        predecessor_height /\
      typed_root RDM caller.(frame_senv) caller.(frame_renv)
        predecessor_location /\
      S predecessor_height <= derivation_height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    return_mode return_location derivation derivation_height Hheight Hclosed
    Howned_snapshot Hseparated Hreturn_mode.
  destruct (tracked_derivation_is_snapshot_or_has_frame_join_predecessor CT
    h Z callee callee_incoming caller caller_incoming snapshot
    (return_mode, return_location) derivation derivation_height Hheight
    Hclosed Howned_snapshot) as [Hreturn_snapshot | Hpredecessor].
  - exfalso. eapply Hseparated; eauto.
  - exact Hpredecessor.
Qed.

Lemma tracked_resume_frozen_derivation_has_origin_before_pop :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot state,
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot state ->
    resumed_caller_frozen_origin CT h caller caller_incoming state.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot state
    Hderivation.
  induction Hderivation.
  - exact H1.
  - eapply resumed_caller_owned_has_frozen_origin. exact H.
  - eapply resumed_caller_frozen_origin_connected; [exact IHHderivation|].
    apply rt_step. eapply frozen_nonjoin_step_in_frame. exact H.
  - eapply resumed_caller_frozen_origin_connected; [exact IHHderivation|].
    apply rt_step. destruct H as [-> | ->].
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

(** Root-scoped replacement for the obsolete global-disjointness rerouting
    argument.  If the return-root derivation is already represented by the
    frozen snapshot, the active-overlap origin certificate classifies every
    captured caller RDM target directly.  Otherwise the derivation exposes a
    strictly smaller caller-frame-join predecessor, from which the target is
    rerouted.  No symmetry of prospective connectivity is used. *)
Lemma tracked_separated_return_derivation_reroutes :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    return_mode return_location
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (return_mode, return_location))
    derivation_height target,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (return_mode, return_location) derivation derivation_height ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h callee
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    (forall separated_mode,
      authority_mode_dangerous separated_mode ->
      ~ In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (separated_mode, return_location)) ->
    authority_mode_dangerous return_mode ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) target ->
    exists rerouted rerouted_height,
      rerouted_height < S derivation_height /\
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot
        (FlowProspective, target) rerouted rerouted_height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    return_mode return_location derivation derivation_height target Hheight
    Hclosed Howned_snapshot Hseparated Hreturn_mode Htarget.
  destruct (tracked_return_derivation_has_frame_join_predecessor CT h Z
    callee callee_incoming caller caller_incoming snapshot return_mode
    return_location derivation derivation_height Hheight Hclosed
    Howned_snapshot Hseparated Hreturn_mode) as
    [predecessor_mode [predecessor_location [predecessor
      [predecessor_height
        [Hpredecessor_mode [Hpredecessor
          [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
  exists (tracked_resume_by_frame_join CT h Z callee callee_incoming caller
    caller_incoming snapshot predecessor_mode predecessor_location target
    Hpredecessor_mode predecessor Hpredecessor_root Htarget),
    (S predecessor_height).
  split; [lia|]. constructor. exact Hpredecessor_height.
Qed.

(** Overlap-aware counterpart of the preceding rerouting lemma.  A frozen
    color may harmlessly overlap the returned object.  The proof-local
    resume-origin certificate maps that overlap to a captured caller root,
    whose existing resume certificate classifies the old target directly.
    With no such overlap, the lossless derivation exposes the usual strictly
    smaller join predecessor. *)
Lemma tracked_return_source_join_has_class_from_overlap_justification :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming return_location target source_height
    mode
    (source_derivation : tracked_resume_frozen_color_derivation CT h Z active
      active_incoming caller caller_incoming snapshot
      (mode, return_location)),
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    frozen_caller_snapshots_active_overlap_justified CT h Z active
      (Some snapshot :: snapshots) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    frame_owned_location CT h active return_location ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) target ->
    tracked_resume_frozen_color_derivation_has_height CT h Z active
      active_incoming caller caller_incoming snapshot
      (mode, return_location) source_derivation source_height ->
    authority_mode_dangerous mode ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) return_location ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) target ->
    (forall state
      (derivation : tracked_resume_frozen_color_derivation CT h Z active
        active_incoming caller caller_incoming snapshot state)
      derivation_height,
      derivation_height < S source_height ->
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller caller_incoming snapshot state derivation
        derivation_height ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot state) ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (FlowProspective, target).
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming return_location target source_height
    mode source_derivation Hfull Hoverlap Howned_snapshot Hcaller_wf
    Hreturn_owned Htarget_root Hheight Hmode Hreturn_root Htarget_typed
    Hsmaller.
  have Hsnapshot_in : List.In (Some snapshot)
      (Some snapshot :: snapshots) by (simpl; auto).
  destruct (tracked_derivation_is_snapshot_or_has_frame_join_predecessor CT
    h Z active active_incoming caller caller_incoming snapshot
    (mode, return_location) source_derivation source_height Hheight
    ((proj1 (proj2 (proj2 (proj2 Hfull)))) snapshot Hsnapshot_in)
    Howned_snapshot) as
    [Hreturn_snapshot | Hpredecessor].
  - have Hreturn_independent : In authority_flow_state
        (independent_active_authority_colors CT h active)
        (FlowPowered, return_location).
    { unfold independent_active_authority_colors.
      eapply executing_authority_owned_is_powered. exact Hreturn_owned. }
    have Hoverlap_result := Hoverlap snapshot mode FlowPowered return_location
      Hsnapshot_in Hmode (or_introl eq_refl) Hreturn_snapshot
      (or_introl Hreturn_independent).
    have Hreturn_runtime : r_muttype h return_location = Some Mut_r.
    { have Hmain := proj1 Hfull.
      have Hactive_wf : wf_r_config CT active.(frame_senv)
          active.(frame_renv) h :=
        proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
      have Hactive_sound : authority_context_sound h active.(frame_renv)
          active.(frame_authority) :=
        proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
      have Hincoming_runtime : authority_colors_runtime_mutable h
          active_incoming := proj1 (proj2 (proj2 Hmain)).
      have Hexecuting_runtime := executing_authority_colors_runtime_mutable
        CT h active active_incoming Hactive_wf Hactive_sound
        Hincoming_runtime.
      eapply Hexecuting_runtime.
      eapply executing_authority_owned_is_powered. exact Hreturn_owned. }
    destruct (active_rdm_roots_share_runtime_context CT
      caller.(frame_senv) caller.(frame_renv) h return_location target
      Hcaller_wf Hreturn_root Htarget_typed) as
      [runtime_q [Hreturn_context Htarget_context]].
    rewrite Hreturn_runtime in Hreturn_context.
    injection Hreturn_context as <-.
    destruct Hoverlap_result as [Horigin | Hsafe].
    + eapply tracked_active_overlap_join_has_class_from_resume_origin; eauto.
    + right. right. split; [|exact Hsafe].
      have Hexposure := proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 (proj2 (proj2 (proj2 Hfull)))))))).
      eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto.
  - destruct Hpredecessor as
      [predecessor_mode [predecessor_location [predecessor
        [predecessor_height
          [Hpredecessor_mode [Hpredecessor
            [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
    set (rerouted := tracked_resume_by_frame_join CT h Z active
      active_incoming caller caller_incoming snapshot predecessor_mode
      predecessor_location target Hpredecessor_mode predecessor
      Hpredecessor_root Htarget_typed).
    eapply Hsmaller with (derivation := rerouted)
      (derivation_height := S predecessor_height).
    + lia.
    + unfold rerouted. constructor. exact Hpredecessor_height.
Qed.

(** Abstract normalization used by the fresh-return proof.  If derivation
    bases predate [boundary_cutoff] and a non-join step cannot enter the fresh
    suffix from an old source, then any derivation ending in that suffix must
    contain a caller-frame RDM join.  The derivation immediately before that
    join is short enough that joining it directly to another caller RDM root
    is a strictly smaller replacement for one more outer join. *)
Lemma tracked_fresh_derivation_has_frame_join_predecessor :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    boundary_cutoff state
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot state)
    derivation_height,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot state derivation
      derivation_height ->
    (forall mode location,
      In authority_flow_state caller_incoming (mode, location) ->
      location < boundary_cutoff) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary_cutoff) ->
    (forall source target
        (source_derivation : tracked_resume_frozen_color_derivation CT h Z
          callee callee_incoming caller caller_incoming snapshot source)
        source_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot source
        source_derivation source_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    boundary_cutoff <= snd state ->
    exists predecessor_mode predecessor_location predecessor
      predecessor_height,
      authority_mode_dangerous predecessor_mode /\
      tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
        caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) /\
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot
        (predecessor_mode, predecessor_location) predecessor
        predecessor_height /\
      typed_root RDM caller.(frame_senv) caller.(frame_renv)
        predecessor_location /\
      S predecessor_height <= derivation_height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    boundary_cutoff state derivation derivation_height Hheight Hincoming_old
    Howned_old Hnonjoin_back Hfresh.
  induction Hheight as
    [state Hsnapshot Hincoming Horigin
    |anchor Howned Hcallee
    |source target previous Hstep n Hprevious_height IH
    |mode left right Hmode previous Hleft Hright n Hprevious_height IH].
  - destruct state as [mode location]. simpl in *.
    have Hold := Hincoming_old mode location Hincoming. lia.
  - have Hold := Howned_old anchor Howned Hcallee. simpl in Hfresh. lia.
  - have Hsource_fresh := Hnonjoin_back source target previous n
      Hprevious_height Hstep Hfresh.
    destruct (IH Hsource_fresh) as
      [predecessor_mode [predecessor_location [predecessor
        [predecessor_height
          [Hpredecessor_mode [Hpredecessor
            [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
    exists predecessor_mode, predecessor_location, predecessor,
      predecessor_height. repeat split; try assumption. lia.
  - destruct (le_lt_dec boundary_cutoff left) as [Hleft_fresh | Hleft_old].
    + destruct (IH Hleft_fresh) as
        [predecessor_mode [predecessor_location [predecessor
          [predecessor_height
            [Hpredecessor_mode [Hpredecessor
              [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
      exists predecessor_mode, predecessor_location, predecessor,
        predecessor_height. repeat split; try assumption. lia.
    + exists mode, left, previous, n. repeat split; try assumption. lia.
Qed.

Lemma tracked_fresh_return_derivation_reroutes :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    boundary_cutoff return_location mode
    (derivation : tracked_resume_frozen_color_derivation CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (mode, return_location))
    derivation_height target,
    tracked_resume_frozen_color_derivation_has_height CT h Z callee
      callee_incoming caller caller_incoming snapshot
      (mode, return_location) derivation derivation_height ->
    (forall incoming_mode location,
      In authority_flow_state caller_incoming (incoming_mode, location) ->
      location < boundary_cutoff) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h callee callee_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary_cutoff) ->
    (forall source target_state
        (source_derivation : tracked_resume_frozen_color_derivation CT h Z
          callee callee_incoming caller caller_incoming snapshot source)
        source_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot source
        source_derivation source_height ->
      frozen_caller_authority_nonjoin_step CT h source target_state ->
      boundary_cutoff <= snd target_state ->
      boundary_cutoff <= snd source) ->
    boundary_cutoff <= return_location ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) target ->
    exists rerouted rerouted_height,
      rerouted_height < S derivation_height /\
      tracked_resume_frozen_color_derivation_has_height CT h Z callee
        callee_incoming caller caller_incoming snapshot
        (FlowProspective, target) rerouted rerouted_height.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    boundary_cutoff return_location mode derivation derivation_height target
    Hheight Hincoming_old Howned_old Hnonjoin_back Hreturn_fresh Htarget.
  destruct (tracked_fresh_derivation_has_frame_join_predecessor CT h Z
    callee callee_incoming caller caller_incoming snapshot boundary_cutoff
    (mode, return_location) derivation derivation_height Hheight Hincoming_old
    Howned_old Hnonjoin_back Hreturn_fresh) as
    [predecessor_mode [predecessor_location [predecessor
      [predecessor_height
        [Hpredecessor_mode [Hpredecessor
          [Hpredecessor_height [Hpredecessor_root Hbound]]]]]]]].
  exists (tracked_resume_by_frame_join CT h Z callee callee_incoming caller
    caller_incoming snapshot predecessor_mode predecessor_location target
    Hpredecessor_mode predecessor Hpredecessor_root Htarget),
    (S predecessor_height).
  split; [lia|]. constructor. exact Hpredecessor_height.
Qed.

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

Lemma tracked_resume_frozen_connected_derives :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot
    source target,
    authority_mode_dangerous (fst source) ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot source ->
    frozen_caller_authority_connected CT h caller source target ->
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot target.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot
    source target Hmode Hsource Hconnected.
  induction Hconnected.
  - eapply tracked_resume_frozen_step_derives; eauto.
  - exact Hsource.
  - have Hmiddle_mode : authority_mode_dangerous (fst y).
    { eapply frozen_caller_authority_connected_preserves_dangerous; eauto. }
    have Hmiddle := IHHconnected1 Hmode Hsource.
    exact (IHHconnected2 Hmiddle_mode Hmiddle).
Qed.

Lemma tracked_resume_frozen_derivation_has_origin :
  forall CT h Z callee callee_incoming caller caller_incoming snapshot state,
    tracked_resume_frozen_color_derivation CT h Z callee callee_incoming
      caller caller_incoming snapshot state ->
    resumed_caller_frozen_origin CT h caller caller_incoming state.
Proof.
  intros CT h Z callee callee_incoming caller caller_incoming snapshot state
    Hderivation.
  induction Hderivation.
  - exact H1.
  - eapply resumed_caller_owned_has_frozen_origin. exact H.
  - eapply resumed_caller_frozen_origin_connected; [exact IHHderivation|].
    apply rt_step. eapply frozen_nonjoin_step_in_frame. exact H.
  - eapply resumed_caller_frozen_origin_connected; [exact IHHderivation|].
    apply rt_step. destruct H as [Hmode | Hmode]; subst mode.
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

(** A caller-frame RDM join may target any location whose dangerous
    authority is already represented by the completed callee.  The target
    need not be a statically [Mut] root: this is the branch used when an RDM
    return retained its entry-derived authority color.  The caller-origin
    half is obtained from the strictly smaller source derivation, so this is
    provenance, not a dispatch assumption. *)
Lemma tracked_join_to_callee_colored_root_has_class :
  forall CT h Z active incoming caller caller_incoming snapshot mode left
    right target_mode,
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    authority_mode_dangerous target_mode ->
    In authority_flow_state
      (executing_authority_color_set CT h active incoming)
      (target_mode, right) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active incoming caller caller_incoming snapshot mode left
    right target_mode Hmode Hderivation Hleft Hright Htarget_mode Htarget.
  right. left. split.
  - destruct Htarget_mode as [Hpowered | Hprospective].
    + subst target_mode. destruct Htarget as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|].
      apply rt_step. apply phased_authority_mark_prospective.
    + subst target_mode. exact Htarget.
  - have Horigin := tracked_resume_frozen_derivation_has_origin CT h Z active
      incoming caller caller_incoming snapshot (mode, left) Hderivation.
    eapply resumed_caller_frozen_origin_connected; [exact Horigin|].
    apply rt_step. destruct Hmode as [Hpowered | Hprospective]; subst mode.
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

Lemma tracked_join_to_active_mut_root_has_class :
  forall CT h Z active incoming caller caller_incoming snapshot mode left right,
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    typed_root Mut active.(frame_senv) active.(frame_renv) right ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active incoming caller caller_incoming snapshot mode left
    right Hmode Hderivation Hleft Hright Hmut.
  eapply tracked_join_to_callee_colored_root_has_class with
    (target_mode := FlowPowered); eauto.
  - left. reflexivity.
  - eapply executing_authority_typed_mut_root_is_powered. exact Hmut.
Qed.

Lemma tracked_join_under_mutable_caller_has_class :
  forall CT h Z active incoming caller_senv caller_renv caller_incoming
    snapshot mode left right,
    let caller := mk_watched_frame Mut_r caller_senv caller_renv in
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller_senv caller_renv left ->
    typed_root RDM caller_senv caller_renv right ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (FlowPowered, location)) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active incoming caller_senv caller_renv caller_incoming
    snapshot mode left right caller Hmode Hderivation Hleft Hright Howned.
  have Hright_owned : frame_owned_location CT h caller right.
  { apply frame_owned_location_iff_active_live.
    eapply typed_rdm_root_is_live_under_mut_authority. exact Hright. }
  right. left. split.
  - have Hpowered := Howned right Hright_owned.
    destruct Hpowered as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|].
    apply rt_step. apply phased_authority_mark_prospective.
  - have Horigin := tracked_resume_frozen_derivation_has_origin CT h Z active
      incoming caller caller_incoming snapshot (mode, left) Hderivation.
    eapply resumed_caller_frozen_origin_connected; [exact Horigin|].
    apply rt_step. destruct Hmode as [Hmode | Hmode]; subst mode.
    + apply frozen_caller_powered_frame_join; assumption.
    + apply frozen_caller_prospective_frame_join; assumption.
Qed.

Lemma tracked_join_under_mutable_authority_has_class :
  forall CT h Z active incoming caller caller_incoming snapshot mode left right,
    caller.(frame_authority) = Mut_r ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (FlowPowered, location)) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active incoming [authority caller_senv caller_renv]
    caller_incoming snapshot mode left right Hauthority Hmode Hderivation
    Hleft Hright Howned. simpl in *. subst authority.
  eapply tracked_join_under_mutable_caller_has_class; eauto.
Qed.

Lemma tracked_snapshot_call_color_has_derivation :
  forall CT h Z active active_incoming snapshot caller caller_incoming
    mode location,
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state caller_incoming
        (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    (forall owned,
      frame_owned_location CT h caller owned ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, owned)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (mode, location) ->
    tracked_resume_frozen_color_derivation CT h Z active active_incoming
      caller caller_incoming snapshot (mode, location).
Proof.
  intros CT h Z active active_incoming snapshot caller caller_incoming
    mode location Hincoming Howned Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    caller seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Hanchor_owned Hfrozen]]].
  - have Hseed_derivation :
      tracked_resume_frozen_color_derivation CT h Z active active_incoming
        caller caller_incoming snapshot seed.
    { inversion Hseed; subst.
      - apply tracked_resume_from_snapshot.
        destruct seed as [seed_mode seed_location].
        eapply Hincoming; eauto.
        exact H.
        eapply resumed_caller_incoming_has_frozen_origin; eauto.
      - destruct H as [anchor [Heq Hanchor_owned]]. inversion Heq; subst.
        eapply tracked_resume_from_caller_owned; eauto. }
    eapply tracked_resume_frozen_connected_derives; eauto.
  - have Hanchor_derivation :
      tracked_resume_frozen_color_derivation CT h Z active active_incoming
        caller caller_incoming snapshot (FlowPowered, anchor).
    { eapply tracked_resume_from_caller_owned; eauto. }
    eapply tracked_resume_frozen_connected_derives; eauto.
    left. reflexivity.
Qed.

Lemma tracked_resume_frozen_color_class_runtime_mutable :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (mode, location) ->
    r_muttype h location = Some Mut_r.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location
    (Hstate & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
      Hphase_covered)
    [Hsnapshot | [[Hcallee Horigin] | [Hexposure_color Hexposure_safe]]].
  - eapply Hruntime; [simpl; auto|exact Hsnapshot].
  - have Hactive_wf :
        wf_r_config CT active.(frame_senv) active.(frame_renv) h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
    have Hactive_sound :
        authority_context_sound h active.(frame_renv)
          active.(frame_authority) :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
    have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
      proj1 (proj2 (proj2 Hstate)).
    eapply executing_authority_colors_runtime_mutable; eauto.
  - eapply (proj1 Hexposure); [simpl; auto|exact Hexposure_color].
Qed.

Lemma tracked_resume_frozen_color_class_not_typed_immutable :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (mode, location) ->
    ~ typed_root Imm active.(frame_senv) active.(frame_renv) location.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location Hstate Hclass Himmutable.
  have Hmutable := tracked_resume_frozen_color_class_runtime_mutable CT P Z
    cutoff active boundary stack incoming snapshot snapshots h caller
    caller_incoming mode location Hstate Hclass.
  have Hactive_wf :
      wf_r_config CT active.(frame_senv) active.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 Hstate)))))).
  have Himmutable_runtime := typed_imm_root_runtime_immutable CT
    active.(frame_senv) active.(frame_renv) h location Hactive_wf Himmutable.
  rewrite Hmutable in Himmutable_runtime. discriminate.
Qed.

Lemma tracked_rdm_join_cannot_target_active_immutable :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    typed_root Imm active.(frame_senv) active.(frame_renv) right ->
    False.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right Hstate Hcaller_wf Hclass Hleft
    Hright Himmutable.
  have Hleft_runtime := tracked_resume_frozen_color_class_runtime_mutable CT
    P Z cutoff active boundary stack incoming snapshot snapshots h caller
    caller_incoming mode left Hstate Hclass.
  destruct (active_rdm_roots_share_runtime_context CT caller.(frame_senv)
    caller.(frame_renv) h left right Hcaller_wf Hleft Hright) as
    [context [Hleft_context Hright_context]].
  rewrite Hleft_runtime in Hleft_context. injection Hleft_context as <-.
  have Hright_runtime : r_muttype h right = Some Mut_r := Hright_context.
  have Hactive_wf :
      wf_r_config CT active.(frame_senv) active.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 Hstate)))))).
  have Himmutable_runtime := typed_imm_root_runtime_immutable CT
    active.(frame_senv) active.(frame_renv) h right Hactive_wf Himmutable.
  rewrite Hright_runtime in Himmutable_runtime. discriminate.
Qed.

Lemma tracked_return_join_with_active_immutable_is_impossible :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right return_location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    typed_root Imm active.(frame_senv) active.(frame_renv) return_location ->
    (left = return_location \/ right = return_location) ->
    False.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right return_location Hstate Hcaller_wf
    Hclass Hleft Hright Himmutable [Hleft_return | Hright_return].
  - subst left. eapply tracked_resume_frozen_color_class_not_typed_immutable;
      eauto.
  - subst right. eapply tracked_rdm_join_cannot_target_active_immutable;
      eauto.
Qed.

Lemma tracked_immutable_return_join_has_class :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right return_location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    typed_root Imm active.(frame_senv) active.(frame_renv) return_location ->
    (left = return_location \/ right = return_location) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros. exfalso.
  eapply tracked_return_join_with_active_immutable_is_impossible; eauto.
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

Lemma tracked_resume_nonjoin_step_preserves_class :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot source ->
    frozen_caller_authority_step CT h caller source target ->
    frozen_caller_authority_step CT h active source target ->
    phased_authority_frame_step CT h active source target ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot target.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry_covered Hphase_covered]]]]]]]]]]]]
    [Hsnapshot | [Hcallee | [Hexposure_color Hexposure_safe]]]
    Hcaller_frozen Hfrozen Hphased.
  - left. eapply Hclosed.
    + simpl. left. reflexivity.
    + exists source. split; [exact Hsnapshot|].
      apply rt_step. exact Hfrozen.
  - right. left. destruct Hcallee as [Hcallee Horigin]. split.
    + destruct Hcallee as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|]. apply rt_step. exact Hphased.
    + destruct Horigin as [seed [Hseed Hpath]].
      exists seed. split; [exact Hseed|].
      eapply rt_trans; [exact Hpath|].
      apply rt_step. exact Hcaller_frozen.
  - right. right. split; [|exact Hexposure_safe].
    eapply (proj1 (proj2 Hexposure)).
    + simpl. left. reflexivity.
    + exists source. split; [exact Hexposure_color|].
      apply rt_step. exact Hfrozen.
Qed.

Lemma tracked_resume_frozen_step_preserves_class_given_joins :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_class CT h Z active incoming caller
        caller_incoming snapshot
        (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      tracked_resume_frozen_color_class CT h Z active incoming caller
        caller_incoming snapshot
        (FlowProspective, right)) ->
    authority_mode_dangerous (fst source) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot source ->
    frozen_caller_authority_step CT h caller source target ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot target.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target Hstate Hjoin Hsource_mode Hsource
    Hstep.
  inversion Hstep; subst; simpl in *.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + apply frozen_caller_retained. exact H.
    + apply phased_authority_retained. exact H.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + apply frozen_caller_prospective_retained. exact H.
    + apply phased_authority_prospective_retained. exact H.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + apply frozen_caller_prospective_rdm_backward. exact H.
    + apply phased_authority_prospective_rdm_backward. exact H.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + apply frozen_caller_reverse_rdm. exact H.
    + apply phased_authority_reverse_rdm. exact H.
  - eapply Hjoin; eauto.
  - eapply Hjoin; eauto.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + apply frozen_caller_mark_prospective.
    + apply phased_authority_mark_prospective.
Qed.

Lemma tracked_resume_frozen_connected_preserves_class_given_joins :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_class CT h Z active incoming caller
        caller_incoming snapshot
        (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      tracked_resume_frozen_color_class CT h Z active incoming caller
        caller_incoming snapshot
        (FlowProspective, right)) ->
    authority_mode_dangerous (fst source) ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot source ->
    frozen_caller_authority_connected CT h caller source target ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot target.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming source target Hstate Hjoin Hsource_mode Hsource
    Hconnected.
  induction Hconnected.
  - eapply tracked_resume_frozen_step_preserves_class_given_joins; eauto.
  - exact Hsource.
  - have Hmiddle_mode : authority_mode_dangerous (fst y).
    { eapply frozen_caller_authority_connected_preserves_dangerous; eauto. }
    have Hmiddle := IHHconnected1 Hsource_mode Hsource.
    exact (IHHconnected2 Hmiddle_mode Hmiddle).
Qed.

Lemma tracked_old_resume_join_preserves_class :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot
      (mode, left) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) left ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) right ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot
      (FlowProspective, right).
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode left right
    Hfull
    Hcaller_wf Hincoming_covered Hmode Hclass Hleft_root Hright_root Hleft
    Hright.
  have Hfull_copy := Hfull.
  destruct Hfull as
    (Hstate & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
      Hphase_covered).
  have Hsnapshot_in : List.In (Some snapshot) (Some snapshot :: snapshots) by
    (simpl; auto).
  have Hactive_wf : wf_r_config CT active.(frame_senv) active.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Hactive_sound :
      authority_context_sound h active.(frame_renv) active.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
  have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
    proj1 (proj2 (proj2 Hstate)).
  have Hcallee_runtime : authority_colors_runtime_mutable h
      (executing_authority_color_set CT h active incoming) :=
    executing_authority_colors_runtime_mutable CT h active incoming
      Hactive_wf Hactive_sound Hincoming_runtime.
  have Hleft_runtime : r_muttype h left = Some Mut_r.
  { destruct Hclass as
      [Hsnapshot_color | [Hcallee_color | [Hexposure_color Hsafe]]].
    - eapply Hruntime; eauto.
    - eapply Hcallee_runtime; exact (proj1 Hcallee_color).
    - eapply (proj1 Hexposure); eauto. }
  have Hright_runtime : r_muttype h right = Some Mut_r.
  { destruct (active_rdm_roots_share_runtime_context CT caller.(frame_senv)
      caller.(frame_renv) h left right Hcaller_wf Hleft Hright) as
      [context [Hleft_context Hright_context]].
    rewrite Hleft_runtime in Hleft_context. injection Hleft_context as <-.
    exact Hright_context. }
  assert (Hexposure_safe : forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        snapshot.(frozen_snapshot_current_resume_exposure)
        (exposure_mode, target) ->
      ~ In Loc Z target).
  { intros exposure_mode target Hexposure_mode Htarget.
    destruct Hclass as
      [Hsnapshot_color | [Hcallee_color | [Hexposure_color Hsafe]]].
    - exact (tracked_snapshot_resume_exposure_avoids_protected CT P Z cutoff
        active boundary stack incoming snapshot snapshots h mode left
        exposure_mode target Hfull_copy Hmode Hsnapshot_color Hleft_root
        Hexposure_mode Htarget).
    - destruct
        (executing_dangerous_covered_by_frozen_or_independent CT h active
          incoming snapshot.(frozen_snapshot_current_colors) mode left
          (Hclosed snapshot Hsnapshot_in) Hincoming_covered Hmode
          (proj1 Hcallee_color)) as
        [[snapshot_mode [Hsnapshot_mode Hsnapshot_color]] |
         [active_mode [Hactive_mode Hactive_color]]].
      + exact (tracked_snapshot_resume_exposure_avoids_protected CT P Z cutoff
          active boundary stack incoming snapshot snapshots h snapshot_mode
          left exposure_mode target Hfull_copy Hsnapshot_mode Hsnapshot_color
          Hleft_root Hexposure_mode Htarget).
      + exact
          (tracked_snapshot_active_resume_exposure_avoids_protected CT P Z
            cutoff active boundary stack incoming snapshot snapshots h
            active_mode left exposure_mode target Hfull_copy Hactive_mode
            Hactive_color Hleft_root Hexposure_mode Htarget).
    - eapply Hsafe; eauto. }
  right. right. split; [|exact Hexposure_safe].
  eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto.
Qed.

Lemma nested_frozen_pop_nonjoin_preserves_class :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    source target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    nested_frozen_pop_color_class CT h Z active incoming head source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    nested_frozen_pop_color_class CT h Z active incoming head target.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h
    source target
    [Hmain [Haligned [Hruntime [Hclosed [Hretain [Hdangerous
      [Havoid [Hroots [Hexposure
        [Hresume [Hjoins [Hentry Hphase]]]]]]]]]]]] Hclass Hstep.
  have Hactive_frozen : frozen_caller_authority_step CT h active source target
    := frozen_nonjoin_step_in_frame CT h active source target Hstep.
  have Hactive_phased : phased_authority_frame_step CT h active source target
    := frozen_nonjoin_step_is_phased CT h active source target Hstep.
  destruct Hclass as [Hsnapshot | [Hcallee | [Hexposure_color Hsafe]]].
  - left. eapply Hclosed; [simpl; auto|].
    exists source. split; [exact Hsnapshot|].
    apply rt_step. exact Hactive_frozen.
  - right. left. destruct Hcallee as [seed [Hseed Hpath]].
    exists seed. split; [exact Hseed|].
    eapply rt_trans; [exact Hpath|]. apply rt_step. exact Hactive_phased.
  - right. right. split; [|exact Hsafe].
    eapply (proj1 (proj2 Hexposure)); [simpl; auto|].
    exists source. split; [exact Hexposure_color|].
    apply rt_step. exact Hactive_frozen.
Qed.

Lemma nested_resume_exposure_nonjoin_preserves_class :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    older source target,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    List.In (Some older) snapshots ->
    nested_resume_exposure_pop_color_class CT h Z active incoming head older
      source ->
    frozen_caller_authority_nonjoin_step CT h source target ->
    nested_resume_exposure_pop_color_class CT h Z active incoming head older
      target.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h older
    source target Hfull Hold Hclass Hstep.
  destruct Hclass as [Hexposure_color | Hnested_class].
  - left. destruct Hfull as
      (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
        Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
    eapply (proj1 (proj2 Hexposure)) with (snapshot := older).
    + simpl. right. exact Hold.
    + exists source. split; [exact Hexposure_color|].
      apply rt_step. eapply frozen_nonjoin_step_in_frame. exact Hstep.
  - right. eapply nested_frozen_pop_nonjoin_preserves_class; eauto.
Qed.

(** Well-founded second-order classifier.  The callback is proof-local and
    is later discharged by the same old-root/fresh-return split as the main
    tracked classifier.  Abstracting it here prevents the recursive
    predecessor argument from becoming a public theorem premise. *)
Lemma nested_resume_exposure_derivation_implies_class_well_founded :
  forall CT P Z cutoff active boundary stack incoming head snapshots h older
    caller state
    (derivation : nested_resume_exposure_pop_derivation CT h caller
      older.(frozen_snapshot_current_resume_exposure) state)
    derivation_height,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    List.In (Some older) snapshots ->
    nested_resume_exposure_pop_derivation_has_height CT h caller
      older.(frozen_snapshot_current_resume_exposure) state derivation
      derivation_height ->
    (forall source_height mode left right
      (source_derivation : nested_resume_exposure_pop_derivation CT h caller
        older.(frozen_snapshot_current_resume_exposure) (mode, left)),
      nested_resume_exposure_pop_derivation_has_height CT h caller
        older.(frozen_snapshot_current_resume_exposure) (mode, left)
        source_derivation source_height ->
      authority_mode_dangerous mode ->
      nested_resume_exposure_pop_color_class CT h Z active incoming head older
        (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      (forall next_state
        (next_derivation : nested_resume_exposure_pop_derivation CT h caller
          older.(frozen_snapshot_current_resume_exposure) next_state)
        next_height,
        next_height < S source_height ->
        nested_resume_exposure_pop_derivation_has_height CT h caller
          older.(frozen_snapshot_current_resume_exposure) next_state
          next_derivation next_height ->
        nested_resume_exposure_pop_color_class CT h Z active incoming head
          older next_state) ->
      nested_resume_exposure_pop_color_class CT h Z active incoming head older
        (FlowProspective, right)) ->
    nested_resume_exposure_pop_color_class CT h Z active incoming head older
      state.
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h older
    caller state derivation derivation_height Hfull Hold Hheight Hjoin.
  revert state derivation Hheight.
  induction derivation_height as [derivation_height IHheight]
    using lt_wf_ind; intros state derivation Hheight.
  destruct Hheight as
    [state Hbase
    |source target previous Hstep n Hprevious_height
    |mode left right Hmode previous Hleft Hright n Hprevious_height].
  - left. exact Hbase.
  - have Hsource_class := IHheight n (ltac:(lia)) source previous
      Hprevious_height.
    eapply nested_resume_exposure_nonjoin_preserves_class; eauto.
  - have Hsource_class := IHheight n (ltac:(lia)) (mode, left) previous
      Hprevious_height.
    eapply Hjoin with (source_height := n) (source_derivation := previous).
    + exact Hprevious_height.
    + exact Hmode.
    + exact Hsource_class.
    + exact Hleft.
    + exact Hright.
    + intros next_state next_derivation next_height Hbound Hnext_height.
      eapply IHheight; eauto.
Qed.

(** Joins between roots already present before the immediate call are
    classified using the captured resume certificate.  This proof is the
    older-slot analogue of [tracked_old_resume_join_preserves_class]; it does
    not assert that a frozen base originated in the immediate caller. *)
Lemma nested_frozen_pop_old_join_preserves_class :
  forall CT P Z cutoff active boundary stack incoming head snapshots h
    caller mode left right,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      In authority_flow_state head.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    authority_mode_dangerous mode ->
    nested_frozen_pop_color_class CT h Z active incoming head (mode, left) ->
    In Loc head.(frozen_snapshot_resume_rdm_roots) left ->
    In Loc head.(frozen_snapshot_resume_rdm_roots) right ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    nested_frozen_pop_color_class CT h Z active incoming head
      (FlowProspective, right).
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h
    caller mode left right Hfull Hcaller_wf Hincoming_covered Hmode Hclass
    Hleft_root Hright_root Hleft Hright.
  have Hfull_copy := Hfull.
  destruct Hfull as
    (Hstate & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
      Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hhead_in : List.In (Some head) (Some head :: snapshots) by
    (simpl; auto).
  have Hactive_wf : wf_r_config CT active.(frame_senv) active.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hstate))))).
  have Hactive_sound : authority_context_sound h active.(frame_renv)
      active.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hstate)))))).
  have Hincoming_runtime : authority_colors_runtime_mutable h incoming :=
    proj1 (proj2 (proj2 Hstate)).
  have Hcallee_runtime : authority_colors_runtime_mutable h
      (executing_authority_color_set CT h active incoming) :=
    executing_authority_colors_runtime_mutable CT h active incoming
      Hactive_wf Hactive_sound Hincoming_runtime.
  have Hleft_runtime : r_muttype h left = Some Mut_r.
  { destruct Hclass as [Hsnapshot | [Hcallee | [Hexposure_color Hsafe]]].
    - eapply Hruntime; eauto.
    - eapply Hcallee_runtime. exact Hcallee.
    - eapply (proj1 Hexposure); eauto. }
  have Hright_runtime : r_muttype h right = Some Mut_r.
  { destruct (active_rdm_roots_share_runtime_context CT caller.(frame_senv)
      caller.(frame_renv) h left right Hcaller_wf Hleft Hright) as
      [context [Hleft_context Hright_context]].
    rewrite Hleft_runtime in Hleft_context. injection Hleft_context as <-.
    exact Hright_context. }
  assert (Hexposure_safe : forall exposure_mode target,
      authority_mode_dangerous exposure_mode ->
      In authority_flow_state
        head.(frozen_snapshot_current_resume_exposure)
        (exposure_mode, target) ->
      ~ In Loc Z target).
  { intros exposure_mode target Hexposure_mode Htarget.
    destruct Hclass as [Hsnapshot | [Hcallee | [Hexposure_color Hsafe]]].
    - exact (tracked_snapshot_resume_exposure_avoids_protected CT P Z cutoff
        active boundary stack incoming head snapshots h mode left
        exposure_mode target Hfull_copy Hmode Hsnapshot Hleft_root
        Hexposure_mode Htarget).
    - destruct
        (executing_dangerous_covered_by_frozen_or_independent CT h active
          incoming head.(frozen_snapshot_current_colors) mode left
          (Hclosed head Hhead_in) Hincoming_covered Hmode Hcallee) as
        [[snapshot_mode [Hsnapshot_mode Hsnapshot_color]] |
         [active_mode [Hactive_mode Hactive_color]]].
      + exact (tracked_snapshot_resume_exposure_avoids_protected CT P Z cutoff
          active boundary stack incoming head snapshots h snapshot_mode left
          exposure_mode target Hfull_copy Hsnapshot_mode Hsnapshot_color
          Hleft_root Hexposure_mode Htarget).
      + exact
          (tracked_snapshot_active_resume_exposure_avoids_protected CT P Z
            cutoff active boundary stack incoming head snapshots h
            active_mode left exposure_mode target Hfull_copy Hactive_mode
            Hactive_color Hleft_root Hexposure_mode Htarget).
    - eapply Hsafe; eauto. }
  right. right. split; [|exact Hexposure_safe].
  eapply (proj2 (proj2 (proj2 (proj2 Hexposure)))); eauto.
Qed.

Lemma tracked_captured_resume_derivation_implies_class :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming state,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state incoming (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    (forall root,
      typed_root RDM caller.(frame_senv) caller.(frame_renv) root ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) ->
    tracked_resume_frozen_color_derivation CT h Z active incoming caller
      caller_incoming snapshot state ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot state.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming state Hfull Hcaller_wf Hincoming_covered
    Hcaptured Hderivation.
  induction Hderivation.
  - left. exact H.
  - right. left. split; [exact H0|].
    eapply resumed_caller_owned_has_frozen_origin. exact H.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_is_phased. exact H.
  - eapply tracked_old_resume_join_preserves_class with
      (caller := caller) (caller_incoming := caller_incoming); eauto.
Qed.

Lemma tracked_resume_frozen_class_implies_pop_safe :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot
      (mode, location) ->
    (exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active incoming)
        (callee_mode, location)) \/
    ~ In Loc Z location.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location Hfull Hmode
    [Hsnapshot | [Hcallee | [Hexposure Hexposure_safe]]].
  - right. intros Hprotected.
    destruct Hfull as
      (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
        Havoid & Hroots & Hexposure_wf & Hresume & Hjoins & Hentry_covered &
        Hphase_covered).
    eapply Havoid; [simpl; auto|exact Hmode|exact Hsnapshot|exact Hprotected].
  - left. exists mode. split; [exact Hmode|exact (proj1 Hcallee)].
  - right. eapply Hexposure_safe; eauto.
Qed.

(** Every tracked dangerous caller color avoids the protected set.  The
    class eliminator above leaves a completed-callee-color alternative for
    use by pop; the executing-state separation invariant discharges that
    alternative when only non-membership is needed. *)
Lemma tracked_resume_frozen_class_avoids_protected :
  forall CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) incoming (Some snapshot :: snapshots) h ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active incoming caller
      caller_incoming snapshot (mode, location) ->
    ~ In Loc Z location.
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshot snapshots h
    caller caller_incoming mode location Hfull Hmode Hclass.
  have Hpop := tracked_resume_frozen_class_implies_pop_safe CT P Z cutoff
    active boundary stack incoming snapshot snapshots h caller
    caller_incoming mode location Hfull Hmode Hclass.
  destruct Hpop as
    [[callee_mode [Hcallee_mode Hcallee_color]] | Hsafe]; [|exact Hsafe].
  have Hmain := proj1 Hfull.
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
  eapply Hseparated; eauto.
Qed.

Lemma tracked_captured_snapshot_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state active_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall root,
      typed_root RDM caller.(frame_senv) caller.(frame_renv) root ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) root) ->
    executing_authority_call_pop_safe CT h Z active active_incoming caller
      caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming Hfull Hcaller_wf Hincoming
    Hactive_incoming Howned Hcaptured mode location Hmode Hcolor.
  have Hderivation := tracked_snapshot_call_color_has_derivation CT h Z
    active active_incoming snapshot caller caller_incoming mode location
    Hincoming Howned Hmode Hcolor.
  have Hclass := tracked_captured_resume_derivation_implies_class CT P Z
    cutoff active boundary stack active_incoming snapshot snapshots h caller
    caller_incoming (mode, location) Hfull Hcaller_wf Hactive_incoming Hcaptured
    Hderivation.
  eapply tracked_resume_frozen_class_implies_pop_safe; eauto.
Qed.

Lemma tracked_snapshot_call_pop_safe_given_join_classification :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot (mode, left) ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
      typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot (FlowProspective, right)) ->
    executing_authority_call_pop_safe CT h Z active active_incoming caller
      caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller caller_incoming Hfull Hcaller_incoming Howned Hjoin
    mode location Hmode [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    caller seed (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Hanchor_owned Hfrozen]]].
  - have Hseed_class : tracked_resume_frozen_color_class CT h Z active
        active_incoming caller caller_incoming snapshot seed.
    { inversion Hseed; subst.
      - left. destruct seed as [seed_mode seed_location].
        eapply Hcaller_incoming; eauto.
      - right. left. destruct H as [owned [Heq Howned_seed]].
        inversion Heq; subst. split.
        + eapply Howned. exact Howned_seed.
        + exists (FlowPowered, owned). split.
          * right. exists owned. split; [reflexivity|exact Howned_seed].
          * apply rt_refl. }
    have Htarget_class :=
      tracked_resume_frozen_connected_preserves_class_given_joins CT P Z
        cutoff active boundary stack active_incoming snapshot snapshots h
        caller caller_incoming seed (mode, location) Hfull Hjoin Hseed_mode Hseed_class
        Hfrozen.
    exact (tracked_resume_frozen_class_implies_pop_safe CT P Z cutoff active
      boundary stack active_incoming snapshot snapshots h caller caller_incoming
      mode location Hfull
      Hmode Htarget_class).
  - have Hanchor_class : tracked_resume_frozen_color_class CT h Z active
        active_incoming caller caller_incoming snapshot (FlowPowered, anchor).
    { right. left. split.
      - eapply Howned. exact Hanchor_owned.
      - exists (FlowPowered, anchor). split.
        + right. exists anchor. split; [reflexivity|exact Hanchor_owned].
        + apply rt_refl. }
    have Htarget_class :=
      tracked_resume_frozen_connected_preserves_class_given_joins CT P Z
        cutoff active boundary stack active_incoming snapshot snapshots h
        caller caller_incoming (FlowPowered, anchor) (mode, location) Hfull Hjoin
        (or_introl eq_refl) Hanchor_class Hfrozen.
    exact (tracked_resume_frozen_class_implies_pop_safe CT P Z cutoff active
      boundary stack active_incoming snapshot snapshots h caller caller_incoming
      mode location Hfull
      Hmode Htarget_class).
Qed.

(** A caller environment update can add only the returned location to its
    RDM roots.  This wrapper separates the already-proved old/old join from
    the genuinely call-specific cases involving that new root. *)
Lemma tracked_post_update_join_preserves_class :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming mode left right,
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall return_mode return_left return_right,
      authority_mode_dangerous return_mode ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        caller_incoming snapshot
        (return_mode, return_left) ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        return_left ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        return_right ->
      (return_left = return_location \/ return_right = return_location) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        caller_incoming snapshot
        (FlowProspective, return_right)) ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active active_incoming
      (mk_watched_frame boundary.(boundary_caller).(frame_authority)
        caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      caller_incoming snapshot
      (mode, left) ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) left ->
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) right ->
    tracked_resume_frozen_color_class CT h Z active active_incoming
      (mk_watched_frame boundary.(boundary_caller).(frame_authority)
        caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      caller_incoming snapshot
      (FlowProspective, right).
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming mode left right Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots_match Hincoming_match Hreturn Hmode
    Hclass Hleft Hright.
  destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
    destination destination_type return_location left Hcaller_wf Hdestination
    Hleft) as [Hleft_old | [Hleft_return Hdestination_rdm_left]];
  destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
    destination destination_type return_location right Hcaller_wf Hdestination
    Hright) as [Hright_old | [Hright_return Hdestination_rdm_right]].
  - have Hsnapshot_in : List.In (Some snapshot)
      (Some snapshot :: snapshots) by (simpl; auto).
    have Hincoming_covered : forall incoming_mode incoming_location,
        authority_mode_dangerous incoming_mode ->
        In authority_flow_state active_incoming
          (incoming_mode, incoming_location) ->
        In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (incoming_mode, incoming_location).
    { intros incoming_mode incoming_location Hincoming_mode Hincoming_color.
      destruct Hfull as
        (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
          Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
          Hphase_covered).
      eapply Hphase_covered; [exact Hsnapshot_in|exact Hincoming_mode|].
      eapply (proj1 Hincoming_match). exact Hincoming_color. }
    eapply tracked_old_resume_join_preserves_class with
      (caller := mk_watched_frame
        boundary.(boundary_caller).(frame_authority) caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      (caller_incoming := caller_incoming);
      eauto.
    + eapply (proj2 Hroots_match). exact Hleft_old.
    + eapply (proj2 Hroots_match). exact Hright_old.
  - eapply Hreturn; eauto.
  - eapply Hreturn; eauto.
  - eapply Hreturn; eauto.
Qed.

(** Derivation-indexed post-update elimination.  All joins between captured
    caller roots are discharged here.  The private return callback receives
    the strictly smaller derivation of the join source, which is the measure
    needed by the directional return-root argument. *)
Lemma tracked_post_update_derivation_implies_class :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming state,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowPowered, anchor)) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_derivation CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        left ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        right ->
      (left = return_location \/ right = return_location) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowProspective, right)) ->
    tracked_resume_frozen_color_derivation CT h Z active active_incoming
      caller_post caller_incoming snapshot state ->
    tracked_resume_frozen_color_class CT h Z active active_incoming
      caller_post caller_incoming snapshot state.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming state caller_post Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots_match Hincoming_match Howned_base
    Hreturn Hderivation.
  induction Hderivation.
  - left. exact H.
  - eapply Howned_base; eauto.
  - eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_in_frame. exact H.
    + eapply frozen_nonjoin_step_is_phased. exact H.
  - destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
      destination destination_type return_location left Hcaller_wf
      Hdestination H0) as [Hleft_old | [Hleft_return Hleft_rdm]];
    destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
      destination destination_type return_location right Hcaller_wf
      Hdestination H1) as [Hright_old | [Hright_return Hright_rdm]].
    + have Hsnapshot_in : List.In (Some snapshot)
          (Some snapshot :: snapshots) by (simpl; auto).
      have Hincoming_covered : forall incoming_mode incoming_location,
          authority_mode_dangerous incoming_mode ->
          In authority_flow_state active_incoming
            (incoming_mode, incoming_location) ->
          In authority_flow_state snapshot.(frozen_snapshot_current_colors)
            (incoming_mode, incoming_location).
      { intros incoming_mode incoming_location Hincoming_mode Hincoming_color.
        destruct Hfull as
          (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
            Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
            Hphase_covered).
        eapply Hphase_covered; [exact Hsnapshot_in|exact Hincoming_mode|].
        eapply (proj1 Hincoming_match). exact Hincoming_color. }
      eapply tracked_old_resume_join_preserves_class with
        (caller := caller_post) (caller_incoming := caller_incoming); eauto.
      * eapply (proj2 Hroots_match). exact Hleft_old.
      * eapply (proj2 Hroots_match). exact Hright_old.
    + eapply Hreturn; eauto.
    + eapply Hreturn; eauto.
    + eapply Hreturn; eauto.
Qed.

(** Well-founded counterpart of the preceding eliminator.  Its return-root
    callback receives a classifier for every strictly smaller derivation.
    This is exactly the induction principle needed to reroute

        old root -> fresh return root -> old root

    to the shorter direct caller-frame join.  The measure and callback are
    proof-local and disappear before the public preservation theorem. *)
Lemma tracked_post_update_derivation_implies_class_well_founded :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowPowered, anchor)) ->
    (forall source_height mode left right
      (source_derivation : tracked_resume_frozen_color_derivation CT h Z
        active active_incoming caller_post caller_incoming snapshot
        (mode, left)),
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller_post caller_incoming snapshot (mode, left)
        source_derivation source_height ->
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        left ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        right ->
      (left = return_location \/ right = return_location) ->
      (forall state
        (derivation : tracked_resume_frozen_color_derivation CT h Z active
          active_incoming caller_post caller_incoming snapshot state)
        derivation_height,
        derivation_height < S source_height ->
        tracked_resume_frozen_color_derivation_has_height CT h Z active
          active_incoming caller_post caller_incoming snapshot state derivation
          derivation_height ->
        tracked_resume_frozen_color_class CT h Z active active_incoming
          caller_post caller_incoming snapshot state) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowProspective, right)) ->
    forall state
      (derivation : tracked_resume_frozen_color_derivation CT h Z active
        active_incoming caller_post caller_incoming snapshot state)
      derivation_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller_post caller_incoming snapshot state derivation
        derivation_height ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot state.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming caller_post Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots_match Hincoming_match Howned_base
    Hreturn.
  intros state derivation derivation_height Hheight.
  revert state derivation Hheight.
  induction derivation_height as [derivation_height IHheight]
    using lt_wf_ind; intros state derivation Hheight.
  destruct Hheight as
    [state Hsnapshot Hincoming Horigin
    |anchor Howned Hcallee
    |source target previous Hstep n Hprevious_height
    |mode left right Hmode previous Hleft Hright n Hprevious_height].
  - left. assumption.
  - eapply Howned_base; eauto.
  - have Hsource_class := IHheight n (ltac:(lia)) source previous
      Hprevious_height.
    eapply tracked_resume_nonjoin_step_preserves_class; eauto.
    + eapply frozen_nonjoin_step_in_frame. exact Hstep.
    + eapply frozen_nonjoin_step_in_frame. exact Hstep.
    + eapply frozen_nonjoin_step_is_phased. exact Hstep.
  - have Hsource_class := IHheight n (ltac:(lia)) (mode, left) previous
      Hprevious_height.
    destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
      destination destination_type return_location left Hcaller_wf
      Hdestination Hleft) as [Hleft_old | [Hleft_return Hleft_rdm]];
    destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
      destination destination_type return_location right Hcaller_wf
      Hdestination Hright) as [Hright_old | [Hright_return Hright_rdm]].
    + have Hsnapshot_in : List.In (Some snapshot)
          (Some snapshot :: snapshots) by (simpl; auto).
      have Hincoming_covered : forall incoming_mode incoming_location,
          authority_mode_dangerous incoming_mode ->
          In authority_flow_state active_incoming
            (incoming_mode, incoming_location) ->
          In authority_flow_state snapshot.(frozen_snapshot_current_colors)
            (incoming_mode, incoming_location).
      { intros incoming_mode incoming_location Hincoming_mode Hincoming_color.
        destruct Hfull as
          (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous &
            Havoid & Hroots & Hexposure & Hresume & Hjoins & Hentry_covered &
            Hphase_covered).
        eapply Hphase_covered; [exact Hsnapshot_in|exact Hincoming_mode|].
        eapply (proj1 Hincoming_match). exact Hincoming_color. }
      eapply tracked_old_resume_join_preserves_class with
        (caller := caller_post) (caller_incoming := caller_incoming); eauto.
      * eapply (proj2 Hroots_match). exact Hleft_old.
      * eapply (proj2 Hroots_match). exact Hright_old.
    + eapply Hreturn with (source_height := n) (source_derivation := previous);
        [exact Hprevious_height|exact Hmode|exact Hsource_class|exact Hleft
        |exact Hright|right; exact Hright_return|].
      intros smaller_state smaller_derivation smaller_height Hsmaller
        Hsmaller_height.
      eapply IHheight; [exact Hsmaller|exact Hsmaller_height].
    + eapply Hreturn with (source_height := n) (source_derivation := previous);
        [exact Hprevious_height|exact Hmode|exact Hsource_class|exact Hleft
        |exact Hright|left; exact Hleft_return|].
      intros smaller_state smaller_derivation smaller_height Hsmaller
        Hsmaller_height.
      eapply IHheight; [exact Hsmaller|exact Hsmaller_height].
    + eapply Hreturn with (source_height := n) (source_derivation := previous);
        [exact Hprevious_height|exact Hmode|exact Hsource_class|exact Hleft
        |exact Hright|left; exact Hleft_return|].
      intros smaller_state smaller_derivation smaller_height Hsmaller
        Hsmaller_height.
      eapply IHheight; [exact Hsmaller|exact Hsmaller_height].
Qed.

(** Generic return-root callback for the well-founded eliminator.  Entering
    the return root is justified by a completed-callee color.  Leaving it is
    justified only by a derivation that the body-local provenance proof has
    rerouted below the current source height. *)
Lemma tracked_return_join_has_class_from_coloring_and_rerouting :
  forall CT h Z active active_incoming caller caller_incoming snapshot
    return_location source_height mode left right
    (source_derivation : tracked_resume_frozen_color_derivation CT h Z active
      active_incoming caller caller_incoming snapshot (mode, left)),
    tracked_resume_frozen_color_derivation_has_height CT h Z active
      active_incoming caller caller_incoming snapshot (mode, left)
      source_derivation source_height ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    (left = return_location \/ right = return_location) ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    (left = return_location -> right <> return_location ->
      exists rerouted rerouted_height,
        rerouted_height < S source_height /\
        tracked_resume_frozen_color_derivation_has_height CT h Z active
          active_incoming caller caller_incoming snapshot
          (FlowProspective, right) rerouted rerouted_height) ->
    (forall state
      (derivation : tracked_resume_frozen_color_derivation CT h Z active
        active_incoming caller caller_incoming snapshot state)
      derivation_height,
      derivation_height < S source_height ->
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller caller_incoming snapshot state derivation
        derivation_height ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot state) ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active active_incoming caller caller_incoming snapshot
    return_location source_height mode left right source_derivation Hheight
    Hmode Hsource Hleft Hright Hreturn
    [return_mode [Hreturn_mode Hreturn_color]] Hreroute Hsmaller.
  destruct (Nat.eq_dec right return_location) as [Hright_return | Hright_not].
  - subst right. eapply tracked_join_to_callee_colored_root_has_class with
      (target_mode := return_mode).
    + exact Hmode.
    + exact source_derivation.
    + exact Hleft.
    + exact Hright.
    + exact Hreturn_mode.
    + exact Hreturn_color.
  - destruct Hreturn as [Hleft_return | Hright_return]; [|congruence].
    destruct (Hreroute Hleft_return Hright_not) as
      [rerouted [rerouted_height [Hrerouted_lt Hrerouted_height]]].
    eapply Hsmaller; eauto.
Qed.

(** Instantiation of the generic return callback for a return allocated in
    the current call.  The three age facts are proof-local semantic
    consequences supplied by the body evaluation: derivation bases are old,
    a tracked non-join crossing has a fresh source, and the returned location
    lies in the fresh suffix.  Normalization then constructs the strictly
    smaller rerouted join consumed by the recursive classifier. *)
Lemma tracked_fresh_return_join_has_class :
  forall CT h Z active active_incoming caller caller_incoming snapshot
    boundary_cutoff return_location source_height mode left right
    (source_derivation : tracked_resume_frozen_color_derivation CT h Z active
      active_incoming caller caller_incoming snapshot (mode, left)),
    tracked_resume_frozen_color_derivation_has_height CT h Z active
      active_incoming caller caller_incoming snapshot (mode, left)
      source_derivation source_height ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    (left = return_location \/ right = return_location) ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    (forall incoming_mode location,
      In authority_flow_state caller_incoming (incoming_mode, location) ->
      location < boundary_cutoff) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary_cutoff) ->
    (forall source target
        (derivation : tracked_resume_frozen_color_derivation CT h Z active
          active_incoming caller caller_incoming snapshot source)
        derivation_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller caller_incoming snapshot source derivation
        derivation_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    boundary_cutoff <= return_location ->
    (forall state
      (derivation : tracked_resume_frozen_color_derivation CT h Z active
        active_incoming caller caller_incoming snapshot state)
      derivation_height,
      derivation_height < S source_height ->
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller caller_incoming snapshot state derivation
        derivation_height ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot state) ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active active_incoming caller caller_incoming snapshot
    boundary_cutoff return_location source_height mode left right
    source_derivation Hheight Hmode Hsource_class Hleft Hright Hreturn
    Hreturn_color Hincoming_old Howned_old Hnonjoin_back Hreturn_fresh
    Hsmaller.
  eapply tracked_return_join_has_class_from_coloring_and_rerouting with
    (source_derivation := source_derivation); eauto.
  intros Hleft_return Hright_not.
  subst left.
  eapply tracked_fresh_return_derivation_reroutes with
    (boundary_cutoff := boundary_cutoff); eauto.
Qed.

(** Preferred exceptional-return callback.  Unlike the older age-based
    normalization above, this formulation does not assume that arbitrary
    non-join heap steps preserve the allocation boundary.  It uses the exact
    semantic fact established for a channel-free body: frozen caller colors
    are closed under the completed phase yet remain disjoint from locations
    independently owned by that callee. *)
Lemma tracked_separated_return_join_has_class :
  forall CT h Z active active_incoming caller caller_incoming snapshot
    return_location source_height mode left right
    (source_derivation : tracked_resume_frozen_color_derivation CT h Z active
      active_incoming caller caller_incoming snapshot (mode, left)),
    tracked_resume_frozen_color_derivation_has_height CT h Z active
      active_incoming caller caller_incoming snapshot (mode, left)
      source_derivation source_height ->
    authority_mode_dangerous mode ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (mode, left) ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) left ->
    typed_root RDM caller.(frame_senv) caller.(frame_renv) right ->
    (left = return_location \/ right = return_location) ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    Included authority_flow_state
      (frozen_caller_authority_closure CT h active
        snapshot.(frozen_snapshot_current_colors))
      snapshot.(frozen_snapshot_current_colors) ->
    (forall anchor,
      frame_owned_location CT h caller anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    (forall separated_mode,
      authority_mode_dangerous separated_mode ->
      ~ In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (separated_mode, return_location)) ->
    (forall state
      (derivation : tracked_resume_frozen_color_derivation CT h Z active
        active_incoming caller caller_incoming snapshot state)
      derivation_height,
      derivation_height < S source_height ->
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller caller_incoming snapshot state derivation
        derivation_height ->
      tracked_resume_frozen_color_class CT h Z active active_incoming caller
        caller_incoming snapshot state) ->
    tracked_resume_frozen_color_class CT h Z active active_incoming caller
      caller_incoming snapshot (FlowProspective, right).
Proof.
  intros CT h Z active active_incoming caller caller_incoming snapshot
    return_location source_height mode left right source_derivation Hheight
    Hmode Hsource_class Hleft Hright Hreturn Hreturn_color Hclosed
    Howned_snapshot Hseparated Hsmaller.
  eapply tracked_return_join_has_class_from_coloring_and_rerouting with
    (source_derivation := source_derivation); eauto.
  intros Hleft_return Hright_not. subst left.
  eapply tracked_separated_return_derivation_reroutes; eauto.
Qed.

Lemma tracked_post_update_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall mode left right,
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_derivation CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        left ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        right ->
      (left = return_location \/ right = return_location) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowProspective, right)) ->
    executing_authority_call_pop_safe CT h Z active active_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming caller_post Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots_match Hincoming_match
    Hcaller_incoming Howned Hreturn mode location Hmode Hcolor.
  have Hderivation := tracked_snapshot_call_color_has_derivation CT h Z
    active active_incoming snapshot caller_post caller_incoming mode location
    Hcaller_incoming Howned Hmode Hcolor.
  have Howned_base : forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowPowered, anchor).
  { intros anchor Hcaller_owned Hcallee_color. right. left. split.
    - exact Hcallee_color.
    - eapply resumed_caller_owned_has_frozen_origin. exact Hcaller_owned. }
  have Hclass := tracked_post_update_derivation_implies_class CT P Z cutoff
    active boundary stack active_incoming snapshot snapshots h caller_senv
    caller_renv destination destination_type return_location caller_incoming
    (mode, location) Hfull Hcaller_wf Hcaller_post_wf Hdestination
    Hroots_match Hincoming_match Howned_base Hreturn Hderivation.
  eapply tracked_resume_frozen_class_implies_pop_safe; eauto.
Qed.

(** Pop-safety wrapper for the well-founded return classifier.  The
    derivation height is obtained existentially from the proof-local
    provenance tree, used to classify the resumed color, and then discarded.
    Consequently neither the height nor the recursive callback can escape to
    the public preservation theorem. *)
Lemma tracked_post_update_call_pop_safe_well_founded :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall source_height mode left right
      (source_derivation : tracked_resume_frozen_color_derivation CT h Z
        active active_incoming caller_post caller_incoming snapshot
        (mode, left)),
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller_post caller_incoming snapshot (mode, left)
        source_derivation source_height ->
      authority_mode_dangerous mode ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, left) ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        left ->
      typed_root RDM caller_senv
        (update_r_env_value caller_renv destination (Iot return_location))
        right ->
      (left = return_location \/ right = return_location) ->
      (forall state
        (derivation : tracked_resume_frozen_color_derivation CT h Z active
          active_incoming caller_post caller_incoming snapshot state)
        derivation_height,
        derivation_height < S source_height ->
        tracked_resume_frozen_color_derivation_has_height CT h Z active
          active_incoming caller_post caller_incoming snapshot state derivation
          derivation_height ->
        tracked_resume_frozen_color_class CT h Z active active_incoming
          caller_post caller_incoming snapshot state) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowProspective, right)) ->
    executing_authority_call_pop_safe CT h Z active active_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming caller_post Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots_match Hincoming_match
    Hcaller_incoming Howned Hreturn mode location Hmode Hcolor.
  have Hderivation := tracked_snapshot_call_color_has_derivation CT h Z
    active active_incoming snapshot caller_post caller_incoming mode location
    Hcaller_incoming Howned Hmode Hcolor.
  destruct (tracked_resume_frozen_color_derivation_has_some_height CT h Z
    active active_incoming caller_post caller_incoming snapshot
    (mode, location) Hderivation) as [derivation_height Hheight].
  have Howned_base : forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowPowered, anchor).
  { intros anchor Hcaller_owned Hcallee_color. right. left. split.
    - exact Hcallee_color.
    - eapply resumed_caller_owned_has_frozen_origin. exact Hcaller_owned. }
  have Hclass :=
    tracked_post_update_derivation_implies_class_well_founded CT P Z cutoff
      active boundary stack active_incoming snapshot snapshots h caller_senv
      caller_renv destination destination_type return_location
      caller_incoming Hfull Hcaller_wf Hcaller_post_wf Hdestination
      Hroots_match Hincoming_match Howned_base Hreturn
      (mode, location) Hderivation derivation_height Hheight.
  eapply tracked_resume_frozen_class_implies_pop_safe; eauto.
Qed.

(** Lossless color classification for the exceptional overlap-aware return.
    The pop-safety theorem below is only its protected-zone projection; this
    stronger form is also used to advance older policy witnesses. *)
Lemma tracked_overlap_post_update_color_has_class :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    frozen_caller_snapshots_active_overlap_justified CT h Z active
      (Some snapshot :: snapshots) ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    frame_owned_location CT h active return_location ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller_post caller_incoming)
        (mode, location) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (mode, location).
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming caller_post Hfull Hoverlap Hcaller_wf
    Hcaller_post_wf Hdestination Hroots Hincoming Hcaller_incoming Howned
    Howned_snapshot Hreturn_owned Hreturn_color mode location Hmode Hcolor.
  have Hderivation := tracked_snapshot_call_color_has_derivation CT h Z
    active active_incoming snapshot caller_post caller_incoming mode location
    Hcaller_incoming Howned Hmode Hcolor.
  destruct (tracked_resume_frozen_color_derivation_has_some_height CT h Z
    active active_incoming caller_post caller_incoming snapshot
    (mode, location) Hderivation) as [derivation_height Hheight].
  have Howned_base : forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming snapshot (FlowPowered, anchor).
  { intros anchor Hcaller_owned Hcallee_color. right. left. split.
    - exact Hcallee_color.
    - eapply resumed_caller_owned_has_frozen_origin. exact Hcaller_owned. }
  eapply tracked_post_update_derivation_implies_class_well_founded with
    (derivation := Hderivation) (derivation_height := derivation_height);
    eauto.
  intros source_height source_mode left right source_derivation
    Hsource_height Hsource_mode Hsource_class Hleft Hright Hreturn Hsmaller.
  destruct (Nat.eq_dec right return_location) as
    [Hright_return | Hright_not].
  - subst right.
    destruct Hreturn_color as [return_mode [Hreturn_mode Hreturn_color]].
    eapply tracked_join_to_callee_colored_root_has_class with
      (target_mode := return_mode); eauto.
  - destruct Hreturn as [Hleft_return | Hright_return]; [|congruence].
    subst left.
    have Hright_old : typed_root RDM caller_senv caller_renv right.
    { destruct (caller_post_rdm_root_origin CT caller_senv caller_renv h
        destination destination_type return_location right Hcaller_wf
        Hdestination Hright) as [Hright_old | [Hright_return _]].
      - exact Hright_old.
      - congruence. }
    have Hright_captured : In Loc
        snapshot.(frozen_snapshot_resume_rdm_roots) right.
    { eapply (proj2 Hroots). exact Hright_old. }
    eapply tracked_return_source_join_has_class_from_overlap_justification with
      (source_derivation := source_derivation); eauto.
Qed.

(** Exceptional-return pop using the root-scoped overlap certificate.  The
    return may be a dangerous completed-callee color and may overlap frozen
    caller colors.  A join into the return is classified by the completed
    callee; a join out of it is handled by
    [tracked_return_source_join_has_class_from_overlap_justification]. *)
Lemma tracked_overlap_post_update_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    frozen_caller_snapshots_active_overlap_justified CT h Z active
      (Some snapshot :: snapshots) ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    frame_owned_location CT h active return_location ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    executing_authority_call_pop_safe CT h Z active active_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming caller_post Hfull Hoverlap Hcaller_wf
    Hcaller_post_wf Hdestination Hroots Hincoming Hcaller_incoming Howned
    Howned_snapshot Hreturn_owned Hreturn_color mode location Hmode Hcolor.
  have Hclass := tracked_overlap_post_update_color_has_class CT P Z cutoff
    active boundary stack active_incoming snapshot snapshots h caller_senv
    caller_renv destination destination_type return_location caller_incoming
    Hfull Hoverlap Hcaller_wf Hcaller_post_wf Hdestination Hroots Hincoming
    Hcaller_incoming Howned Howned_snapshot Hreturn_owned Hreturn_color mode
    location Hmode Hcolor.
  eapply tracked_resume_frozen_class_implies_pop_safe; eauto.
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

Lemma advanced_tail_resume_exposure_protected_reflected_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming slot snapshots h
    caller old_snapshot new_snapshot,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    new_snapshot = advance_frozen_caller_snapshot CT h caller old_snapshot ->
    frozen_snapshot_resume_exposure_protected_reflected Z new_snapshot
      old_snapshot.
Proof.
  intros CT P Z cutoff active boundary stack incoming slot snapshots h
    caller old_snapshot new_snapshot Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hold Heq mode location Hmode Htarget Hprotected.
  subst caller.
  subst new_snapshot. simpl in Htarget.
  destruct Htarget as [source [Hsource Hpath]].
  destruct source as [source_mode source_location]. simpl in *.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hclass := pop_resume_exposure_state_class_connected CT h active
    boundary.(boundary_caller)
    old_snapshot.(frozen_snapshot_current_resume_exposure)
    (source_mode, source_location)
    (mode, location) Hcaller_wf Hcaller_sound
    ((proj1 Hexposure) old_snapshot (ltac:(simpl; right; exact Hold)))
    ((proj1 (proj2 Hexposure)) old_snapshot
      (ltac:(simpl; right; exact Hold))) (or_introl Hsource) Hpath.
  destruct Hclass as [Hold_target | [_
    [root [Hroot Hroot_path]]]].
  - exists mode. split; assumption.
  - exfalso. eapply (private_head_slot_prospective_component_avoids_older_protected
      CT P Z cutoff active slot snapshots boundary stack incoming h
      old_snapshot root location Hprivate Hold).
    split; [exact Hroot|exact Hroot_path].
    exact Hprotected.
Qed.

Lemma frozen_snapshot_list_resume_exposure_reflected_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h caller snapshots) snapshots.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hcaller Hcaller_wf Hcaller_sound.
  assert (Hmap : forall remaining,
    (forall old_snapshot, List.In (Some old_snapshot) remaining ->
      List.In (Some old_snapshot) snapshots) ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h caller remaining) remaining).
  { induction remaining as [|slot tail IH]; intros Hin; simpl.
    - constructor.
    - constructor.
      + destruct slot as [old_snapshot|]; simpl; [|exact I].
        eapply advanced_tail_resume_exposure_protected_reflected_after_tracked_pop;
          eauto.
        apply Hin. simpl. left. reflexivity.
      + apply IH. intros old_snapshot Hsnapshot.
        apply Hin. simpl. right. exact Hsnapshot. }
  apply Hmap. intros old_snapshot Hsnapshot. exact Hsnapshot.
Qed.

Lemma frozen_snapshot_resume_exposure_avoids_after_reflection :
  forall Z final initial,
    frozen_snapshot_resume_exposure_protected_reflected Z final initial ->
    frozen_snapshot_resume_exposure_avoids Z initial ->
    frozen_snapshot_resume_exposure_avoids Z final.
Proof.
  intros Z final initial Hreflection Hsafe mode location Hmode Hcolor
    Hprotected.
  destruct (Hreflection mode location Hmode Hcolor Hprotected) as
    [initial_mode [Hinitial_mode Hinitial_color]].
  exact (Hsafe initial_mode location Hinitial_mode Hinitial_color Hprotected).
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

Lemma private_tracked_head_prospective_component_disjoint_older_resume_root :
  forall CT P Z cutoff active head snapshots boundary stack incoming h older
    root target,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h
      boundary.(boundary_caller) root target ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) target ->
    False.
Proof.
  intros CT P Z cutoff active head snapshots boundary stack incoming h older
    root target Hprivate Hold Hreachable Htarget_root.
  destruct Hprivate as
    [[Hfull [_ [Hbefore _]]] [_ [Hprospective _]]].
  have Haligned := proj1 (proj2 Hfull).
  destruct (frozen_snapshot_in_tail_has_partition_below_head head snapshots
    boundary stack older Haligned Hold) as
    [older_boundary [above [below Hpartition]]].
  have Hfresh : older_boundary.(boundary_entry_cutoff) <= target.
  { eapply Hprospective with (snapshot := older)
      (above := boundary :: above) (below := below) (root := root).
    - exact Hpartition.
    - apply live_frame_suspended with (boundary := boundary). simpl. auto.
    - exact Hreachable. }
  have Hold_slot := frozen_snapshot_live_partition_before_boundary
    (Some head :: snapshots) (boundary :: stack) older older_boundary
    (boundary :: above) below Hbefore Hpartition.
  simpl in Hold_slot. have Hold_target := (proj2 Hold_slot) target Htarget_root.
  lia.
Qed.

(** Tail version of the preceding component/age contradiction.  The proof
    uses only stack alignment and the older tracked slot; the top slot may be
    [None]. *)
Lemma private_head_slot_prospective_component_disjoint_older_resume_root :
  forall CT P Z cutoff active slot snapshots boundary stack incoming h older
    root target,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (slot :: snapshots) h ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h
      boundary.(boundary_caller) root target ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) target ->
    False.
Proof.
  intros CT P Z cutoff active slot snapshots boundary stack incoming h older
    root target Hprivate Hold Hreachable Htarget_root.
  destruct Hprivate as
    [[Hfull [_ [Hbefore _]]] [_ [Hprospective _]]].
  have Haligned := proj1 (proj2 Hfull).
  destruct (frozen_snapshot_in_tail_has_partition_below_slot slot snapshots
    boundary stack older Haligned Hold) as
    [older_boundary [above [below Hpartition]]].
  have Hfresh : older_boundary.(boundary_entry_cutoff) <= target.
  { eapply Hprospective with (snapshot := older)
      (above := boundary :: above) (below := below) (root := root).
    - exact Hpartition.
    - apply live_frame_suspended with (boundary := boundary). simpl. auto.
    - exact Hreachable. }
  have Hold_slot := frozen_snapshot_live_partition_before_boundary
    (slot :: snapshots) (boundary :: stack) older older_boundary
    (boundary :: above) below Hbefore Hpartition.
  simpl in Hold_slot. have Hold_target := (proj2 Hold_slot) target Htarget_root.
  lia.
Qed.

Lemma active_prospective_component_disjoint_frozen_resume_root :
  forall CT h active snapshots stack older root target,
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h active root target ->
    In Loc older.(frozen_snapshot_resume_rdm_roots) target ->
    False.
Proof.
  intros CT h active snapshots stack older root target Haligned Hcomponents
    Hbefore Hold Hreachable Htarget_root.
  destruct (frozen_snapshot_in_has_live_partition snapshots stack older
    Haligned Hold) as [boundary [above [below Hpartition]]].
  have Hfresh : boundary.(boundary_entry_cutoff) <= target.
  { eapply Hcomponents with (snapshot := older) (boundary := boundary)
      (above := above) (below := below) (root := root).
    - exact Hpartition.
    - constructor.
    - exact Hreachable. }
  have Hold_slot := frozen_snapshot_live_partition_before_boundary snapshots
    stack older boundary above below Hbefore Hpartition.
  simpl in Hold_slot. have Hold_target := (proj2 Hold_slot) target Htarget_root.
  lia.
Qed.

Lemma nested_frozen_call_head_resume_exposure_disjoint_advanced_tail :
  forall CT h boundary caller_colors snapshots stack older new_older,
    let caller := boundary.(boundary_caller) in
    let callee := mk_watched_frame
      (call_authority caller.(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) in
    entry_ownership_channel_free boundary ->
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      snapshots stack ->
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    List.In (Some older) snapshots ->
    new_older = advance_frozen_caller_snapshot CT h callee older ->
    frozen_snapshot_resume_exposure_disjoint_from
      (nested_frozen_call_head CT h caller callee caller_colors snapshots)
      new_older.
Proof.
  intros CT h boundary caller_colors snapshots stack older new_older caller
    callee Hfree Haligned Hcomponents Hbefore Hold Heq mode location Hcolor
    Hroot.
  subst new_older. simpl in Hroot.
  unfold nested_frozen_call_head in Hcolor. simpl in Hcolor.
  destruct Hcolor as [caller_state [Hcaller_state Hcallee_path]].
  unfold frame_resume_exposure_colors in Hcaller_state.
  destruct Hcaller_state as [seed [Hseed Hcaller_path]].
  unfold frame_resume_exposure_seeds in Hseed.
  destruct Hseed as [root [Hrdm [Hruntime Heq]]]. subst seed.
  have Hcallee_reflected : frozen_caller_authority_connected CT h caller
      (FlowProspective, root) (mode, location).
  { eapply rt_trans; [exact Hcaller_path|].
    eapply channel_free_entry_frozen_connected_reflects; eauto. }
  have Hprospective_path := frozen_caller_connected_as_prospective CT h caller
    (FlowProspective, root) (mode, location) Hcallee_reflected.
  simpl in Hprospective_path.
  eapply active_prospective_component_disjoint_frozen_resume_root with
    (older := older) (root := root); eauto.
  split.
  - right. split; assumption.
  - exact Hprospective_path.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance :
  forall CT h active snapshots,
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    (forall newer older mode location,
      List.In (Some newer) snapshots ->
      List.In (Some older) snapshots ->
      In authority_flow_state
        (frozen_caller_authority_closure CT h active
          newer.(frozen_snapshot_current_resume_exposure)) (mode, location) ->
      In Loc older.(frozen_snapshot_resume_rdm_roots) location ->
      exists old_mode,
        In authority_flow_state
          newer.(frozen_snapshot_current_resume_exposure)
          (old_mode, location)) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h active snapshots).
Proof.
  intros CT h active snapshots Hdisjoint Hreflect.
  induction snapshots as [|slot tail IH]; simpl in *; [exact I|].
  destruct slot as [head|].
  - destruct Hdisjoint as [Hhead Htail]. split.
    + intros new_older Hnew mode location Hcolor Hroot.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [old_slot [Heq Hold]].
      destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
      injection Heq as Heq. subst new_older. simpl in Hroot.
      destruct (Hreflect head old_older mode location (ltac:(simpl; auto))
        (ltac:(simpl; right; exact Hold)) Hcolor Hroot) as
        [old_mode Hold_color].
      eapply (Hhead old_older Hold old_mode location); eauto.
    + apply IH.
      * exact Htail.
      * intros newer older mode location Hnewer Holder.
        eapply Hreflect; simpl; right; eauto.
  - apply IH.
    + exact Hdisjoint.
    + intros newer older mode location Hnewer Holder.
      eapply Hreflect; simpl; right; eauto.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_enter_channel_free :
  forall CT P Z cutoff caller stack incoming snapshots h boundary callee
    caller_colors,
    private_fresh_frozen_statement_state CT P Z cutoff caller stack incoming
      snapshots h ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    boundary.(boundary_caller) = caller ->
    callee = mk_watched_frame
      (call_authority caller.(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) ->
    entry_ownership_channel_free boundary ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots).
Proof.
  intros CT P Z cutoff caller stack incoming snapshots h boundary callee
    caller_colors Hprivate Hdisjoint Hboundary Hcallee Hfree.
  subst caller. subst callee.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hprivate_state := proj2 (proj1 Hprivate).
  destruct Hprivate_state as
    (Horigins & Hbefore & Hcovered & Hnested & Hcompleted).
  have Hprospective := proj1 (proj2 (proj2 Hprivate)).
  unfold enter_nested_frozen_caller_snapshots. simpl. split.
  - intros new_older Hnew.
    unfold advance_frozen_caller_snapshots in Hnew.
    apply in_map_iff in Hnew.
    destruct Hnew as [old_slot [Heq Hold]].
    destruct old_slot as [old_older|]; simpl in Heq; [|discriminate].
    injection Heq as Heq. subst new_older.
    eapply nested_frozen_call_head_resume_exposure_disjoint_advanced_tail;
      eauto.
  - eapply
      frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
    + exact Hdisjoint.
    + intros newer older mode location Hnewer Holder Hcolor Hroot.
      exists mode.
      eapply (proj1 (proj2 Hexposure)); [exact Hnewer|].
      destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split;
        [exact Hseed|].
      eapply channel_free_entry_frozen_connected_reflects; eauto.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_active_descent :
  forall CT h authority old_senv old_renv new_senv new_renv snapshots,
    rdm_roots_descend_from CT h old_senv old_renv new_senv new_renv ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority old_senv old_renv) snapshots ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority new_senv new_renv) snapshots).
Proof.
  intros CT h authority old_senv old_renv new_senv new_renv snapshots
    Hdescend Hexposure Hdisjoint.
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
  - exact Hdisjoint.
  - intros newer older mode location Hnewer Holder
      [seed [Hseed Hpath]] Hroot.
    exists mode. eapply (proj1 (proj2 Hexposure)); [exact Hnewer|].
    exists seed. split; [exact Hseed|].
    eapply frozen_caller_connected_after_descent_reflects; eauto.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_graph_reflection :
  forall CT old_h new_h active snapshots,
    (forall left right,
      retained_mut_edge CT new_h left right ->
      retained_mut_edge CT old_h left right) ->
    (forall left right,
      mutable_edge CT new_h left right ->
      mutable_edge CT old_h left right) ->
    frozen_caller_snapshots_resume_exposures_wf CT old_h active snapshots ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT new_h active snapshots).
Proof.
  intros CT old_h new_h active snapshots Hretained Hmutable Hexposure
    Hdisjoint.
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
  - exact Hdisjoint.
  - intros newer older mode location Hnewer Holder Hcolor Hroot.
    exists mode.
    eapply frozen_caller_closure_after_graph_reflection_included; eauto.
    eapply (proj1 (proj2 Hexposure)); eauto.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_safe_field_update :
  forall CT h active snapshots stack lx old field written,
    wf_r_config CT active.(frame_senv) active.(frame_renv) h ->
    authority_context_sound h active.(frame_renv) active.(frame_authority) ->
    runtime_getObj h lx = Some old ->
    frozen_caller_snapshots_resume_exposures_wf CT h active snapshots ->
    authority_colors_runtime_mutable h
      (independent_active_authority_colors CT h active) ->
    authority_safe_field_endpoints CT h active lx written ->
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT
        (update_field h lx field (Iot written)) active snapshots).
Proof.
  intros CT h active snapshots stack lx old field written Hwf Hsound Hobj
    Hexposure Hactive_runtime Hendpoints Haligned Hprospective Hbefore
    Hdisjoint.
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
  - exact Hdisjoint.
  - intros newer older mode location Hnewer Holder
      [seed [Hseed Hpath]] Hroot.
    destruct seed as [seed_mode seed_location]. simpl in *.
    have Hseed_dangerous := (proj1 (proj2 (proj2 Hexposure))) newer
      seed_mode seed_location Hnewer Hseed.
    have Htarget_mode :=
      frozen_caller_authority_connected_preserves_dangerous CT
        (update_field h lx field (Iot written)) active
        (seed_mode, seed_location) (mode, location)
        Hseed_dangerous Hpath.
    have Hcovered :=
      frozen_caller_connected_after_safe_field_update_covered_by_old_or_active
        CT h active newer.(frozen_snapshot_current_resume_exposure) lx old
        field written (seed_mode, seed_location) (mode, location) Hobj
        ((proj1 Hexposure) newer Hnewer)
        ((proj1 (proj2 Hexposure)) newer Hnewer) Hactive_runtime Hendpoints
        (ltac:(intros _; left; exists seed_mode; split; assumption)) Hpath.
    destruct (Hcovered Htarget_mode) as
      [[old_mode [Hold_mode Hold_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + exists old_mode. exact Hold_color.
    + destruct (independent_active_dangerous_has_prospective_root CT h active
        active_mode location Hwf Hsound Hactive_mode Hactive_color) as
        [active_root [Hactive_root Hactive_path]].
      exfalso. eapply
        (active_prospective_component_disjoint_frozen_resume_root CT h active
          snapshots stack older active_root location Haligned Hprospective
          Hbefore Holder).
      * split; assumption.
      * exact Hroot.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_new :
  forall CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority snapshots stack,
    wf_r_config CT sGamma rGamma h ->
    wf_r_config CT sGamma'
      (update_r_env_value rGamma x (Iot (dom h)))
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) ->
    authority_context_sound h rGamma authority ->
    authority_context_sound
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (update_r_env_value rGamma x (Iot (dom h))) authority ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    vpa_mutability_object_creation qreceiver qc = qruntime ->
    frozen_caller_snapshots_resume_roots_in_heap h snapshots ->
    frozen_caller_snapshots_resume_exposures_wf CT h
      (mk_watched_frame authority sGamma rGamma) snapshots ->
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      (mk_watched_frame authority sGamma rGamma) snapshots stack ->
    frozen_caller_snapshots_before_boundaries snapshots stack ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h)))) snapshots).
Proof.
  intros CT sGamma mt rGamma h x qc C args sGamma' vals qreceiver qruntime
    authority snapshots stack Hwf Hpost_wf Hsound Hpost_sound Htyping Hvals
    Hadapt Hroots Hexposure Haligned Hprospective Hbefore Hdisjoint.
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
  - exact Hdisjoint.
  - intros newer older mode location Hnewer Holder Hcolor Hroot.
    have Hlocation_old : location < dom h.
    { eapply Hroots; eauto. }
    have Hmode : authority_mode_dangerous mode.
    { destruct Hcolor as [seed [Hseed Hpath]].
      destruct seed as [seed_mode seed_location]. simpl in *.
      have Hseed_mode := (proj1 (proj2 (proj2 Hexposure))) newer seed_mode
        seed_location Hnewer Hseed.
      exact (frozen_caller_authority_connected_preserves_dangerous CT
        (h ++ [mkObj (mkruntime_type qruntime C) vals])
        (mk_watched_frame authority sGamma'
          (update_r_env_value rGamma x (Iot (dom h))))
        (seed_mode, seed_location) (mode, location) Hseed_mode Hpath). }
    have Hpost_color : In authority_flow_state
        (executing_authority_color_set CT
          (h ++ [mkObj (mkruntime_type qruntime C) vals])
          (mk_watched_frame authority sGamma'
            (update_r_env_value rGamma x (Iot (dom h))))
          newer.(frozen_snapshot_current_resume_exposure))
        (mode, location).
    { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
      - left. exact Hseed.
      - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
    destruct (executing_authority_colors_after_new_covered CT sGamma mt
      rGamma h x qc C args sGamma' vals qreceiver qruntime authority
      newer.(frozen_snapshot_current_resume_exposure) Hwf Hpost_wf Hsound
      Hpost_sound ((proj1 Hexposure) newer Hnewer) Htyping Hvals Hadapt mode
      location Hmode Hpost_color Hlocation_old) as
      [old_mode [Hold_mode Hold_executing]].
    destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
      CT h (mk_watched_frame authority sGamma rGamma)
      newer.(frozen_snapshot_current_resume_exposure) old_mode location
      ((proj1 (proj2 Hexposure)) newer Hnewer) Hold_mode Hold_executing) as
      [[snapshot_mode [Hsnapshot_mode Hsnapshot_color]] |
       [active_mode [Hactive_mode Hactive_color]]].
    + exists snapshot_mode. exact Hsnapshot_color.
    + destruct (independent_active_dangerous_has_prospective_root CT h
        (mk_watched_frame authority sGamma rGamma) active_mode location Hwf
        Hsound Hactive_mode Hactive_color) as
        [active_root [Hactive_root Hactive_path]].
      exfalso. eapply
        (active_prospective_component_disjoint_frozen_resume_root CT h
          (mk_watched_frame authority sGamma rGamma) snapshots stack older
          active_root location Haligned Hprospective Hbefore Holder).
      * split; assumption.
      * exact Hroot.
Qed.

Lemma advanced_tail_resume_exposure_at_any_older_root_reflected_after_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    exposure_snapshot root_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some exposure_snapshot) snapshots ->
    List.In (Some root_snapshot) snapshots ->
    In authority_flow_state
      (frozen_caller_authority_closure CT h caller
        exposure_snapshot.(frozen_snapshot_current_resume_exposure))
      (mode, location) ->
    In Loc root_snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    exists old_mode,
      In authority_flow_state
        exposure_snapshot.(frozen_snapshot_current_resume_exposure)
        (old_mode, location).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    exposure_snapshot root_snapshot mode location Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hexposure_slot Hroot_slot Hcolor Hresume_root.
  destruct Hcolor as [seed [Hseed Hpath]].
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hclass := pop_resume_exposure_state_class_connected CT h active caller
    exposure_snapshot.(frozen_snapshot_current_resume_exposure) seed
    (mode, location) Hcaller_wf Hcaller_sound
    ((proj1 Hexposure) exposure_snapshot
      (ltac:(simpl; right; exact Hexposure_slot)))
    ((proj1 (proj2 Hexposure)) exposure_snapshot
      (ltac:(simpl; right; exact Hexposure_slot))) (or_introl Hseed) Hpath.
  destruct Hclass as [Hold | [Hmode Hcovered]].
  - exists mode. exact Hold.
  - change (mode = FlowProspective) in Hmode. subst mode.
    destruct Hcovered as [root [Hroot Hroot_path]]. exfalso.
    eapply
      (private_head_slot_prospective_component_disjoint_older_resume_root
        CT P Z cutoff active head_slot snapshots boundary stack incoming h
        root_snapshot root location Hprivate Hroot_slot).
    + rewrite <- Hcaller. split; [exact Hroot|exact Hroot_path].
    + exact Hresume_root.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hdisjoint Hcaller Hcaller_wf Hcaller_sound.
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
  - exact Hdisjoint.
  - intros newer older mode location Hnewer Holder Hcolor Hroot.
    eapply advanced_tail_resume_exposure_at_any_older_root_reflected_after_pop;
      eauto.
Qed.

Lemma advanced_tail_current_color_class_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot state,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    new_snapshot = advance_frozen_caller_snapshot CT h caller old_snapshot ->
    In authority_flow_state new_snapshot.(frozen_snapshot_current_colors)
      state ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_colors) state.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot state Hprivate Hcaller Hcaller_wf Hcaller_sound
    Hold Heq Hstate.
  subst new_snapshot. simpl in Hstate. destruct Hstate as [source [Hsource Hpath]].
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  eapply pop_resume_exposure_state_class_connected with (active := active);
    eauto.
  - eapply Hruntime. simpl. right. exact Hold.
  - eapply Hclosed. simpl. right. exact Hold.
  - left. exact Hsource.
Qed.

Lemma advanced_tail_current_color_at_resume_root_reflected_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    new_snapshot = advance_frozen_caller_snapshot CT h caller old_snapshot ->
    authority_mode_dangerous mode ->
    In authority_flow_state new_snapshot.(frozen_snapshot_current_colors)
      (mode, location) ->
    In Loc new_snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    In authority_flow_state old_snapshot.(frozen_snapshot_current_colors)
      (mode, location).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    old_snapshot new_snapshot mode location Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hold Heq Hmode Hcolor Hresume_root.
  have Hclass := advanced_tail_current_color_class_after_tracked_pop CT P Z
    cutoff active boundary stack incoming head_slot snapshots h caller old_snapshot
    new_snapshot (mode, location) Hprivate Hcaller Hcaller_wf Hcaller_sound
    Hold Heq Hcolor.
  destruct Hclass as [Hold_color | [Hprospective Hcovered]].
  - exact Hold_color.
  - subst new_snapshot. simpl in Hresume_root.
    change (mode = FlowProspective) in Hprospective. subst mode.
    destruct Hcovered as [root [Hauthority_root Hpath]].
    exfalso. eapply
      (private_head_slot_prospective_component_disjoint_older_resume_root
        CT P Z cutoff active head_slot snapshots boundary stack incoming h
        old_snapshot root location Hprivate Hold).
    + rewrite <- Hcaller. split; [exact Hauthority_root|exact Hpath].
    + exact Hresume_root.
Qed.

(** Dropping a tracked head preserves protected-zone avoidance for every
    older slot.  A post-pop color is either an old frozen color, handled by
    the carried avoidance invariant, or lies in a prospective component of
    the resumed caller.  The stack-aligned component-age certificate places
    the latter beyond the older boundary, hence beyond the protected zone. *)
Lemma frozen_caller_snapshots_avoid_protected_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_caller_snapshots_avoid_protected Z
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hcaller Hcaller_wf Hcaller_sound new_snapshot mode location Hnew
    Hmode Hcolor Hprotected.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  have Hclass := advanced_tail_current_color_class_after_tracked_pop CT P Z
    cutoff active boundary stack incoming head_slot snapshots h caller old_snapshot
    (advance_frozen_caller_snapshot CT h caller old_snapshot)
    (mode, location) Hprivate Hcaller Hcaller_wf Hcaller_sound Hslot eq_refl
    Hcolor.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  destruct Hclass as [Hold_color | [Hprospective Hcovered]].
  - eapply Havoid; [simpl; right; exact Hslot|exact Hmode|exact Hold_color|].
    exact Hprotected.
  - change (mode = FlowProspective) in Hprospective. subst mode.
    destruct Hcovered as [root [Hroot Hpath]].
    have Hparts := proj2 Hprivate.
    destruct Hparts as [Hcomponents [Hprospective_components Hafter]].
    have Hzone := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (proj2 Hmain))))))).
    eapply head_slot_prospective_component_avoids_older_protected with
      (active := active) (slot := head_slot) (snapshots := snapshots)
      (boundary := boundary) (stack := stack) (older := old_snapshot)
      (root := root).
    + exact Haligned.
    + exact Hprospective_components.
    + exact Hafter.
    + exact Hzone.
    + exact Hslot.
    + split.
      * rewrite <- Hcaller. exact Hroot.
      * rewrite <- Hcaller. exact Hpath.
    + exact Hprotected.
Qed.

Lemma independent_active_authority_avoids_older_resume_roots_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    forall snapshot active_mode source,
      List.In (Some snapshot)
        (advance_frozen_caller_snapshots CT h caller snapshots) ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h caller)
        (active_mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      False.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hcaller Hcaller_wf Hcaller_sound snapshot active_mode source
    Hsnapshot Hactive_mode Hactive Hroot.
  unfold advance_frozen_caller_snapshots in Hsnapshot.
  apply in_map_iff in Hsnapshot.
  destruct Hsnapshot as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst snapshot. simpl in Hroot.
  destruct (independent_active_dangerous_has_prospective_root CT h caller
    active_mode source Hcaller_wf Hcaller_sound Hactive_mode Hactive) as
    [root [Hauthority_root Hpath]].
  eapply private_head_slot_prospective_component_disjoint_older_resume_root
    with (older := old_snapshot) (root := root) (target := source); eauto.
  rewrite <- Hcaller. split; assumption.
Qed.

Lemma frozen_caller_snapshots_resume_roots_safe_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_caller_snapshots_resume_roots_safe CT h Z caller
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hcaller Hcaller_wf Hcaller_sound snapshot active_mode source
    exposure_mode target Hsnapshot Hactive_mode Hactive Hroot.
  exfalso.
  eapply independent_active_authority_avoids_older_resume_roots_after_tracked_pop;
    eauto.
Qed.

Lemma resumed_completed_color_at_older_root_reflects_to_tracked_head :
  forall CT P Z cutoff active boundary stack incoming head snapshots h caller
    caller_incoming mode source,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    Included authority_flow_state caller_incoming
      head.(frozen_snapshot_current_colors) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h caller caller_incoming)
      (mode, source) ->
    (exists older,
      List.In (Some older) snapshots /\
      In Loc older.(frozen_snapshot_resume_rdm_roots) source) ->
    exists head_mode,
      authority_mode_dangerous head_mode /\
      In authority_flow_state head.(frozen_snapshot_current_colors)
        (head_mode, source).
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h caller
    caller_incoming mode source Hprivate Hcaller Hcaller_wf Hcaller_sound
    Hhead_incoming Hmode [seed [Hseed Hpath]]
    [older [Holder Hsource_root]].
  subst caller.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT h
    boundary.(boundary_caller) seed (mode, source) Hmode Hpath) as
    [[Hseed_mode Hfrozen_path] | [anchor [Hanchor_owned Hfrozen_path]]].
  - inversion Hseed; subst.
    + have Hclass := pop_resume_exposure_state_class_connected CT h active
        boundary.(boundary_caller) head.(frozen_snapshot_current_colors)
        seed (mode, source)
        Hcaller_wf Hcaller_sound (Hruntime head (ltac:(simpl; auto)))
        (Hclosed head (ltac:(simpl; auto)))
        (or_introl (Hhead_incoming seed H)) Hfrozen_path.
      destruct Hclass as [Hhead | [Hprospective Hcovered]].
      * exists mode. split; assumption.
      * change (mode = FlowProspective) in Hprospective. subst mode.
        destruct Hcovered as [root [Hroot Hroot_path]]. exfalso.
        eapply
          (private_tracked_head_prospective_component_disjoint_older_resume_root
            CT P Z cutoff active head snapshots boundary stack incoming h
            older root source Hprivate Holder).
        -- split; assumption.
        -- exact Hsource_root.
    + destruct H as [anchor [Heq Howned]]. inversion Heq; subst.
      have Hindependent : In authority_flow_state
          (independent_active_authority_colors CT h
            boundary.(boundary_caller)) (mode, source).
      { exists (FlowPowered, anchor). split.
        - right. exists anchor. split; [reflexivity|exact Howned].
        - eapply frozen_caller_authority_connected_is_phased.
          exact Hfrozen_path. }
      exfalso.
      eapply independent_active_authority_avoids_older_resume_roots_after_tracked_pop
        with (snapshot := advance_frozen_caller_snapshot CT h
          boundary.(boundary_caller) older)
          (active_mode := mode) (source := source); eauto.
      unfold advance_frozen_caller_snapshots. apply in_map_iff.
      exists (Some older). split; [reflexivity|exact Holder].
  - have Hindependent : In authority_flow_state
        (independent_active_authority_colors CT h boundary.(boundary_caller))
        (mode, source).
    { exists (FlowPowered, anchor). split.
      - right. exists anchor. split; [reflexivity|exact Hanchor_owned].
      - eapply frozen_caller_authority_connected_is_phased.
        exact Hfrozen_path. }
    exfalso.
    eapply independent_active_authority_avoids_older_resume_roots_after_tracked_pop
      with (snapshot := advance_frozen_caller_snapshot CT h
        boundary.(boundary_caller) older)
        (active_mode := mode) (source := source); eauto.
    unfold advance_frozen_caller_snapshots. apply in_map_iff.
    exists (Some older). split; [reflexivity|exact Holder].
Qed.

Lemma frozen_completed_colors_resume_safe_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head snapshots h caller
    caller_incoming,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    Included authority_flow_state caller_incoming
      head.(frozen_snapshot_current_colors) ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h caller caller_incoming)
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h caller
    caller_incoming Hprivate Hcaller Hcaller_wf Hcaller_sound Hhead_incoming
    new_snapshot source_mode source Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in Hroot.
  destruct (resumed_completed_color_at_older_root_reflects_to_tracked_head
    CT P Z cutoff active boundary stack incoming head snapshots h caller
    caller_incoming source_mode source Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hhead_incoming Hsource_mode Hsource
    (ltac:(exists old_snapshot; split; assumption))) as
    [head_mode [Hhead_mode Hhead_color]].
  have Hcertificates := proj2 (proj1 Hprivate).
  destruct Hcertificates as
    (Horigins & Hbefore & Hcovered & Hnested & Hcompleted).
  simpl in Hnested. destruct Hnested as [Hhead_safe Htail_safe].
  destruct (Hhead_safe old_snapshot Hslot head_mode source Hhead_mode
    Hhead_color Hroot) as [[entry_mode [Hentry_mode Hentry_color]] | Hsafe].
  - left. exists entry_mode. simpl. split; assumption.
  - right. eapply frozen_snapshot_resume_exposure_avoids_after_reflection.
    + eapply advanced_tail_resume_exposure_protected_reflected_after_tracked_pop
        with (old_snapshot := old_snapshot); eauto.
    + exact Hsafe.
Qed.

Lemma frozen_caller_snapshots_resume_joins_safe_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hcaller Hcaller_wf Hcaller_sound new_snapshot source_mode source
    Hnew Hsource_mode Hsource Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot.
  have Hold_color :=
    advanced_tail_current_color_at_resume_root_reflected_after_tracked_pop
      CT P Z cutoff active boundary stack incoming head_slot snapshots h
      caller
      old_snapshot (advance_frozen_caller_snapshot CT h caller old_snapshot)
      source_mode source Hprivate Hcaller Hcaller_wf Hcaller_sound Hslot
      eq_refl Hsource_mode Hsource Hroot.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  specialize (Hjoins old_snapshot source_mode source
    (ltac:(simpl; right; exact Hslot)) Hsource_mode Hold_color).
  simpl in Hroot. specialize (Hjoins Hroot).
  destruct Hjoins as [[entry_mode [Hentry_mode Hentry_color]] | Hsafe].
  - left. exists entry_mode. simpl. split; assumption.
  - right. eapply frozen_snapshot_resume_exposure_avoids_after_reflection.
    + eapply advanced_tail_resume_exposure_protected_reflected_after_tracked_pop
        with (old_snapshot := old_snapshot); eauto.
    + exact Hsafe.
Qed.

Lemma advanced_tail_current_color_at_any_older_resume_root_reflected :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    color_snapshot root_snapshot new_color_snapshot new_root_snapshot mode
    location,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some color_snapshot) snapshots ->
    List.In (Some root_snapshot) snapshots ->
    new_color_snapshot =
      advance_frozen_caller_snapshot CT h caller color_snapshot ->
    new_root_snapshot =
      advance_frozen_caller_snapshot CT h caller root_snapshot ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      new_color_snapshot.(frozen_snapshot_current_colors) (mode, location) ->
    In Loc new_root_snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    In authority_flow_state color_snapshot.(frozen_snapshot_current_colors)
      (mode, location).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    color_snapshot root_snapshot new_color_snapshot new_root_snapshot mode
    location Hprivate Hcaller Hcaller_wf Hcaller_sound Hcolor_slot Hroot_slot
    Hnew_color Hnew_root Hmode Hcolor Hresume_root.
  have Hclass := advanced_tail_current_color_class_after_tracked_pop CT P Z
    cutoff active boundary stack incoming head_slot snapshots h caller color_snapshot
    new_color_snapshot (mode, location) Hprivate Hcaller Hcaller_wf
    Hcaller_sound Hcolor_slot Hnew_color Hcolor.
  destruct Hclass as [Hold_color | [Hprospective Hcovered]].
  - exact Hold_color.
  - subst new_root_snapshot. simpl in Hresume_root.
    change (mode = FlowProspective) in Hprospective. subst mode.
    destruct Hcovered as [root [Hauthority_root Hpath]]. exfalso.
    eapply
      (private_head_slot_prospective_component_disjoint_older_resume_root
        CT P Z cutoff active head_slot snapshots boundary stack incoming h
        root_snapshot root location Hprivate Hroot_slot).
    + rewrite <- Hcaller. split; [exact Hauthority_root|exact Hpath].
    + exact Hresume_root.
Qed.

Lemma frozen_caller_snapshots_nested_resume_safe_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_caller_snapshots_nested_resume_safe Z
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    Hprivate Hcaller Hcaller_wf Hcaller_sound.
  have Hfrozen := proj1 (proj1 Hprivate).
  have Hprivate_state := proj2 (proj1 Hprivate).
  destruct Hprivate_state as
    (Horigins & Hbefore & Hcovered & Hnested & Hcompleted).
  eapply frozen_caller_snapshots_nested_resume_safe_after_classified_advance
    with (exceptional := Empty_set authority_flow_state).
  - eapply frozen_caller_snapshots_nested_resume_safe_tail. exact Hnested.
  - intros snapshot active_mode source exposure_mode target Hsnapshot
      Hactive_mode Hempty. inversion Hempty.
  - intros active_mode location Hactive_mode Hempty. inversion Hempty.
  - intros color_snapshot root_snapshot mode location Hcolor_slot Hroot_slot
      Hmode Hcolor Hroot.
    left. exists mode. split; [exact Hmode|].
    eapply advanced_tail_current_color_at_any_older_resume_root_reflected
      with (new_color_snapshot :=
        advance_frozen_caller_snapshot CT h caller color_snapshot)
        (new_root_snapshot :=
          advance_frozen_caller_snapshot CT h caller root_snapshot); eauto.
  - intros snapshot mode location Hsnapshot Hmode Hcolor Hprotected.
    have Hreflection :=
      advanced_tail_resume_exposure_protected_reflected_after_tracked_pop
        CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
        snapshot (advance_frozen_caller_snapshot CT h caller snapshot)
        Hprivate Hcaller Hcaller_wf Hcaller_sound Hsnapshot eq_refl.
    destruct (Hreflection mode location Hmode Hcolor Hprotected) as
      [old_mode [Hold_mode Hold_color]].
    left. exists old_mode. split; assumption.
Qed.

Lemma private_frozen_snapshot_return_safety_after_tracked_pop :
  forall CT P Z cutoff active boundary stack incoming head snapshots h caller
    caller_incoming,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (Some head :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    Included authority_flow_state caller_incoming
      head.(frozen_snapshot_current_colors) ->
    private_frozen_snapshot_return_safety CT h Z caller caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming head snapshots h caller
    caller_incoming Hprivate Hcaller Hcaller_wf Hcaller_sound Hhead_incoming.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hpost_retain : frozen_caller_snapshots_retain_entry
      (advance_frozen_caller_snapshots CT h caller snapshots).
  { eapply advance_frozen_caller_snapshots_retain_entry.
    intros snapshot Hsnapshot. eapply Hretain. simpl. right. exact Hsnapshot. }
  have Hpost_joins : frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h caller snapshots).
  { eapply frozen_caller_snapshots_resume_joins_safe_after_tracked_pop
      with (active := active) (boundary := boundary) (stack := stack)
        (incoming := incoming) (head_slot := Some head); eauto. }
  have Hpost_entry : frozen_caller_snapshots_entry_exposure_covered
      (advance_frozen_caller_snapshots CT h caller snapshots).
  { eapply advance_frozen_caller_snapshots_entry_exposure_covered.
    intros snapshot source_mode source Hsnapshot.
    eapply Hentry. simpl. right. exact Hsnapshot. }
  unfold private_frozen_snapshot_return_safety.
  split.
  - eapply frozen_resume_joins_and_retain_imply_active_resume_justified;
      eauto.
  - split.
    + eapply frozen_caller_snapshots_avoid_protected_after_tracked_pop
        with (active := active) (boundary := boundary) (stack := stack)
          (incoming := incoming) (head_slot := Some head); eauto.
    + split.
      * eapply frozen_caller_snapshots_nested_resume_safe_after_tracked_pop
          with (active := active) (boundary := boundary) (stack := stack)
            (incoming := incoming) (head_slot := Some head); eauto.
      * split.
        -- eapply frozen_caller_snapshots_resume_roots_safe_after_tracked_pop
             with (active := active) (boundary := boundary) (stack := stack)
               (incoming := incoming) (head_slot := Some head); eauto.
        -- split.
           ++ exact Hpost_joins.
           ++ eapply frozen_completed_colors_resume_safe_after_tracked_pop;
             eauto.
Qed.

(** For an untracked immediate caller, all tail certificates are reconstructed
    exactly as for a tracked pop.  The only information not represented by a
    [None] head is the completed-color certificate for the resumed caller;
    the policy-aware call proof supplies that proof-local fact separately. *)
Lemma private_frozen_snapshot_return_safety_after_untracked_pop_from_completed :
  forall CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (None :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h caller caller_incoming)
      (advance_frozen_caller_snapshots CT h caller snapshots) ->
    private_frozen_snapshot_return_safety CT h Z caller caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming Hprivate Hcaller Hcaller_wf Hcaller_sound Hcompleted.
  have Hfrozen := proj1 (proj1 Hprivate).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hpost_retain : frozen_caller_snapshots_retain_entry
      (advance_frozen_caller_snapshots CT h caller snapshots).
  { eapply advance_frozen_caller_snapshots_retain_entry.
    intros snapshot Hsnapshot. eapply Hretain. simpl. right. exact Hsnapshot. }
  have Hpost_joins : frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h caller snapshots).
  { eapply frozen_caller_snapshots_resume_joins_safe_after_tracked_pop
      with (active := active) (boundary := boundary) (stack := stack)
        (incoming := incoming) (head_slot := None); eauto. }
  unfold private_frozen_snapshot_return_safety.
  split.
  - eapply frozen_resume_joins_and_retain_imply_active_resume_justified;
      eauto.
  - split.
    + eapply frozen_caller_snapshots_avoid_protected_after_tracked_pop
        with (active := active) (boundary := boundary) (stack := stack)
          (incoming := incoming) (head_slot := None); eauto.
    + split.
      * eapply frozen_caller_snapshots_nested_resume_safe_after_tracked_pop
          with (active := active) (boundary := boundary) (stack := stack)
            (incoming := incoming) (head_slot := None); eauto.
      * split.
        -- eapply frozen_caller_snapshots_resume_roots_safe_after_tracked_pop
             with (active := active) (boundary := boundary) (stack := stack)
               (incoming := incoming) (head_slot := None); eauto.
        -- split.
           ++ exact Hpost_joins.
           ++ exact Hcompleted.
Qed.

(** Root-focused semantic transport for an untracked pop.  It is sufficient
    to reflect a resumed caller color only when it coincides with an older
    frozen resume root; the completed callee certificate then supplies the
    required entry-color-or-safe-exposure alternative. *)
Lemma frozen_completed_colors_resume_safe_after_untracked_pop_from_callee_roots :
  forall CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (None :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h active incoming)
          (callee_mode, source)) ->
    frozen_completed_colors_resume_safe Z
      (executing_authority_color_set CT h caller caller_incoming)
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming Hprivate Hcaller Hcaller_wf Hcaller_sound Hreflect
    new_snapshot mode source Hnew Hmode Hcolor Hroot.
  unfold advance_frozen_caller_snapshots in Hnew.
  apply in_map_iff in Hnew.
  destruct Hnew as [slot [Heq Hslot]].
  destruct slot as [old_snapshot|]; simpl in Heq; [|discriminate].
  injection Heq as Heq. subst new_snapshot. simpl in Hroot.
  destruct (Hreflect old_snapshot mode source Hslot Hmode Hcolor Hroot) as
    [callee_mode [Hcallee_mode Hcallee_color]].
  have Hcertificates := proj2 (proj1 Hprivate).
  destruct Hcertificates as
    (Horigins & Hbefore & Hcovered & Hnested & Hcompleted).
  destruct (Hcompleted old_snapshot callee_mode source
    (ltac:(simpl; right; exact Hslot)) Hcallee_mode Hcallee_color Hroot) as
    [[entry_mode [Hentry_mode Hentry_color]] | Hsafe].
  - left. exists entry_mode. simpl. split; assumption.
  - right. eapply frozen_snapshot_resume_exposure_avoids_after_reflection.
    + eapply advanced_tail_resume_exposure_protected_reflected_after_tracked_pop
        with (old_snapshot := old_snapshot) (slot := None); eauto.
    + exact Hsafe.
Qed.

Lemma private_frozen_snapshot_return_safety_after_untracked_pop_from_callee_roots :
  forall CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming,
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (None :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h active incoming)
          (callee_mode, source)) ->
    private_frozen_snapshot_return_safety CT h Z caller caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots).
Proof.
  intros CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming Hprivate Hcaller Hcaller_wf Hcaller_sound Hreflect.
  eapply private_frozen_snapshot_return_safety_after_untracked_pop_from_completed;
    eauto.
  eapply frozen_completed_colors_resume_safe_after_untracked_pop_from_callee_roots;
    eauto.
Qed.

(** A prospective component of the resumed active frame lies on the callee
    side of every older frozen boundary.  Consequently it cannot reach the
    protected prefix.  This is the post-update counterpart of the head-slot
    age argument: it consumes the independently reconstructed tail
    partitions, so it does not identify the resumed frame with the saved
    pre-call frame. *)
Lemma active_prospective_component_avoids_frozen_protected :
  forall CT h Z cutoff active snapshots stack older root target,
    frozen_caller_snapshots_aligned snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h active
      snapshots stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff snapshots stack ->
    protected_zone_before_cutoff Z cutoff ->
    List.In (Some older) snapshots ->
    prospective_mutable_authority_reachable CT h active root target ->
    ~ In Loc Z target.
Proof.
  intros CT h Z cutoff active snapshots stack older root target Haligned
    Hcomponents Hafter Hzone Holder Hreachable Hprotected.
  destruct (frozen_snapshot_in_has_live_partition snapshots stack older
    Haligned Holder) as [boundary [above [below Hpartition]]].
  have Hfresh : boundary.(boundary_entry_cutoff) <= target.
  { eapply Hcomponents with (snapshot := older) (above := above)
      (below := below) (root := root).
    - exact Hpartition.
    - constructor.
    - exact Hreachable. }
  have Hboundary_after : cutoff <= boundary.(boundary_entry_cutoff).
  { eapply frozen_snapshot_partition_boundary_after_cutoff; eauto. }
  have Hprotected_before := Hzone target Hprotected. lia.
Qed.

(** Classify a color added while an older tail snapshot is closed under the
    post-return caller.  The old snapshot remains closed under the completed
    callee, which is exactly the premise required by the generic connected
    classifier; no equality between the pre- and post-update callers is
    needed. *)
Lemma advanced_tail_color_class_after_return :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot)
        .(frozen_snapshot_current_colors) (mode, location) ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_colors) (mode, location).
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location Hbody Hcaller_wf Hcaller_sound Holder
    [source [Hsource Hpath]].
  have Hfrozen := proj1 (proj1 Hbody).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  eapply pop_resume_exposure_state_class_connected with (active := callee);
    eauto.
  - eapply Hruntime. simpl. right. exact Holder.
  - eapply Hclosed. simpl. right. exact Holder.
  - left. exact Hsource.
Qed.

Lemma advanced_tail_exposure_class_after_return :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some old_snapshot) snapshots ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller old_snapshot)
        .(frozen_snapshot_current_resume_exposure) (mode, location) ->
    pop_resume_exposure_state_class CT h caller
      old_snapshot.(frozen_snapshot_current_resume_exposure) (mode, location).
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller old_snapshot mode location Hbody Hcaller_wf Hcaller_sound Holder
    [source [Hsource Hpath]].
  have Hfrozen := proj1 (proj1 Hbody).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  eapply pop_resume_exposure_state_class_connected with (active := callee);
    eauto.
  - eapply (proj1 Hexposure). simpl. right. exact Holder.
  - eapply (proj1 (proj2 Hexposure)). simpl. right. exact Holder.
  - left. exact Hsource.
Qed.

(** At a root captured by any retained snapshot, advancing another retained
    snapshot through the resumed caller introduces no new dangerous color.
    A prospective-component alternative would connect a post-boundary root
    to a pre-boundary captured root, contradicting the stack-aligned age
    certificate.  This is the reusable form of the color-reflection argument
    formerly local to the untracked-return reconstruction. *)
Lemma advanced_tail_current_color_at_any_older_root_reflected_after_return :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller color_snapshot root_snapshot mode location,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    private_frozen_snapshot_structural_state CT h caller
      (advance_frozen_caller_snapshots CT h caller snapshots) stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      (advance_frozen_caller_snapshots CT h caller snapshots) stack ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    List.In (Some color_snapshot) snapshots ->
    List.In (Some root_snapshot) snapshots ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (advance_frozen_caller_snapshot CT h caller color_snapshot).(
        frozen_snapshot_current_colors) (mode, location) ->
    In Loc root_snapshot.(frozen_snapshot_resume_rdm_roots) location ->
    In authority_flow_state color_snapshot.(frozen_snapshot_current_colors)
      (mode, location).
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller color_snapshot root_snapshot mode location Hbody Hstructural
    Hprospective Hcaller_wf Hcaller_sound Hcolor_slot Hroot_slot Hmode Hcolor
    Hroot.
  destruct Hstructural as
    (Hpost_aligned & Hpost_runtime & Hpost_closed & Hpost_retain &
      Hpost_dangerous & Hpost_roots & Hpost_exposure & Hpost_before &
      Hpost_covered & Hpost_entry & Hpost_phase).
  have Hclass := advanced_tail_color_class_after_return CT P Z cutoff callee
    boundary stack incoming head_slot snapshots h caller color_snapshot mode
    location Hbody Hcaller_wf Hcaller_sound Hcolor_slot Hcolor.
  destruct Hclass as [Hold | [Hprospective_mode Hcovered]]; [exact Hold|].
  change (mode = FlowProspective) in Hprospective_mode. subst mode.
  destruct Hcovered as [root [Hauthority_root Hpath]]. exfalso.
  eapply active_prospective_component_disjoint_frozen_resume_root with
    (active := caller)
    (snapshots := advance_frozen_caller_snapshots CT h caller snapshots)
    (stack := stack)
    (older := advance_frozen_caller_snapshot CT h caller root_snapshot)
    (root := root) (target := location).
  - exact Hpost_aligned.
  - exact Hprospective.
  - exact Hpost_before.
  - unfold advance_frozen_caller_snapshots. apply in_map_iff.
    exists (Some root_snapshot). split; [reflexivity|exact Hroot_slot].
  - split; [exact Hauthority_root|exact Hpath].
  - simpl. exact Hroot.
Qed.

(** All semantic certificates needed after an untracked return are rebuilt
    against the actual post-update caller.  [Hstructural] and the two
    component-age facts are independently produced by the mechanical return
    lemmas.  The sole evaluation-sensitive input is root-scoped reflection
    from the resumed caller into the completed callee. *)
Lemma private_frozen_snapshot_return_safety_after_untracked_return_phase_parts :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller caller_incoming post_snapshots,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    principled_phased_authority_live_history_state CT P Z cutoff caller stack
      caller_incoming h ->
    post_snapshots = advance_frozen_caller_snapshots CT h caller snapshots ->
    private_frozen_snapshot_structural_state CT h caller post_snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      post_snapshots stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff post_snapshots stack ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists phase_mode,
        authority_mode_dangerous phase_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_phase_incoming)
          (phase_mode, source)) \/
      (exists callee_mode,
          authority_mode_dangerous callee_mode /\
          In authority_flow_state
            (executing_authority_color_set CT h callee incoming)
            (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot) ->
    private_frozen_snapshot_return_safety CT h Z caller caller_incoming
      post_snapshots.
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller caller_incoming post_snapshots Hbody Hpost Heq Hstructural
    Hprospective Hafter Hcaller_wf Hcaller_sound Hreflect.
  subst post_snapshots.
  have Hbody_frozen := proj1 (proj1 Hbody).
  destruct Hbody_frozen as
    (Hbody_main & Hbody_aligned & Hbody_runtime & Hbody_closed & Hbody_retain &
      Hbody_dangerous & Hbody_avoid & Hbody_roots & Hbody_exposure &
      Hbody_resume & Hbody_joins & Hbody_entry & Hbody_phase).
  have Hbody_private := proj2 (proj1 Hbody).
  destruct Hbody_private as
    (Hbody_origins & Hbody_before & Hbody_covered &
      Hbody_nested & Hbody_completed).
  destruct Hstructural as
    (Hpost_aligned & Hpost_runtime & Hpost_closed & Hpost_retain &
      Hpost_dangerous & Hpost_roots & Hpost_exposure & Hpost_before &
      Hpost_covered & Hpost_entry & Hpost_phase).
  have Hzone := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
    (proj2 Hpost))))))).
  have Hexposure_reflect : forall old_snapshot mode location,
      List.In (Some old_snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller old_snapshot)
          .(frozen_snapshot_current_resume_exposure) (mode, location) ->
      In Loc Z location ->
      exists old_mode,
        authority_mode_dangerous old_mode /\
        In authority_flow_state
          old_snapshot.(frozen_snapshot_current_resume_exposure)
          (old_mode, location).
  { intros old_snapshot mode location Holder Hmode Hcolor Hprotected.
    have Hclass := advanced_tail_exposure_class_after_return CT P Z cutoff
      callee boundary stack incoming head_slot snapshots h caller old_snapshot
      mode location Hbody Hcaller_wf Hcaller_sound Holder Hcolor.
    destruct Hclass as [Hold | [Hprospective_mode Hcovered]].
    - exists mode. split; assumption.
    - change (mode = FlowProspective) in Hprospective_mode. subst mode.
      destruct Hcovered as [root [Hroot Hpath]]. exfalso.
      eapply active_prospective_component_avoids_frozen_protected with
        (active := caller) (snapshots :=
          advance_frozen_caller_snapshots CT h caller snapshots)
        (stack := stack) (older :=
          advance_frozen_caller_snapshot CT h caller old_snapshot)
        (root := root).
      + exact Hpost_aligned.
      + exact Hprospective.
      + exact Hafter.
      + exact Hzone.
      + unfold advance_frozen_caller_snapshots. apply in_map_iff.
        exists (Some old_snapshot). split; [reflexivity|exact Holder].
      + split; [exact Hroot|exact Hpath].
      + exact Hprotected. }
  have Hcolor_at_root_reflect : forall color_snapshot root_snapshot mode source,
      List.In (Some color_snapshot) snapshots ->
      List.In (Some root_snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (advance_frozen_caller_snapshot CT h caller color_snapshot)
          .(frozen_snapshot_current_colors) (mode, source) ->
      In Loc root_snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      In authority_flow_state color_snapshot.(frozen_snapshot_current_colors)
        (mode, source).
  { intros color_snapshot root_snapshot mode source Hcolor_slot Hroot_slot
      Hmode Hcolor Hroot.
    have Hclass := advanced_tail_color_class_after_return CT P Z cutoff callee
      boundary stack incoming head_slot snapshots h caller color_snapshot mode
      source Hbody Hcaller_wf Hcaller_sound Hcolor_slot Hcolor.
    destruct Hclass as [Hold | [Hprospective_mode Hcovered]]; [exact Hold|].
    change (mode = FlowProspective) in Hprospective_mode. subst mode.
    destruct Hcovered as [root [Hauthority_root Hpath]]. exfalso.
    eapply active_prospective_component_disjoint_frozen_resume_root with
      (active := caller)
      (snapshots := advance_frozen_caller_snapshots CT h caller snapshots)
      (stack := stack)
      (older := advance_frozen_caller_snapshot CT h caller root_snapshot)
      (root := root) (target := source).
    - exact Hpost_aligned.
    - exact Hprospective.
    - exact Hpost_before.
    - unfold advance_frozen_caller_snapshots. apply in_map_iff.
      exists (Some root_snapshot). split; [reflexivity|exact Hroot_slot].
    - split; [exact Hauthority_root|exact Hpath].
    - simpl. exact Hroot. }
  have Hpost_joins : frozen_caller_snapshots_resume_joins_safe Z
      (advance_frozen_caller_snapshots CT h caller snapshots).
  { intros new_snapshot source_mode source Hnew Hmode Hcolor Hroot.
    unfold advance_frozen_caller_snapshots in Hnew.
    apply in_map_iff in Hnew.
    destruct Hnew as [slot [Hnew Hslot]]. destruct slot as [old_snapshot|];
      simpl in Hnew; [|discriminate]. injection Hnew as <-. simpl in Hroot.
    have Hold_color := Hcolor_at_root_reflect old_snapshot old_snapshot
      source_mode source Hslot Hslot Hmode Hcolor Hroot.
    destruct (Hbody_joins old_snapshot source_mode source
      (ltac:(simpl; right; exact Hslot)) Hmode Hold_color Hroot) as
      [[entry_mode [Hentry_mode Hentry_color]] | Hsafe].
    - left. exists entry_mode. simpl. split; assumption.
    - right. intros exposure_mode target Hexposure_mode Hexposure Hprotected.
      destruct (Hexposure_reflect old_snapshot exposure_mode target Hslot
        Hexposure_mode Hexposure Hprotected) as
        [old_mode [Hold_mode Hold_exposure]].
      eapply Hsafe; eauto. }
  unfold private_frozen_snapshot_return_safety.
  split.
  - eapply frozen_resume_joins_and_retain_imply_active_resume_justified;
      eauto.
  - split.
    + intros new_snapshot mode location Hnew Hmode Hcolor Hprotected.
      unfold advance_frozen_caller_snapshots in Hnew.
      apply in_map_iff in Hnew.
      destruct Hnew as [slot [Hnew Hslot]]. destruct slot as [old_snapshot|];
        simpl in Hnew; [|discriminate]. injection Hnew as <-.
      have Hclass := advanced_tail_color_class_after_return CT P Z cutoff
        callee boundary stack incoming head_slot snapshots h caller old_snapshot
        mode location Hbody Hcaller_wf Hcaller_sound Hslot Hcolor.
      destruct Hclass as [Hold | [Hprospective_mode Hcovered]].
      * eapply Hbody_avoid; eauto. simpl. right. exact Hslot.
      * change (mode = FlowProspective) in Hprospective_mode. subst mode.
        destruct Hcovered as [root [Hroot Hpath]].
        eapply active_prospective_component_avoids_frozen_protected with
          (active := caller)
          (snapshots := advance_frozen_caller_snapshots CT h caller snapshots)
          (stack := stack)
          (older := advance_frozen_caller_snapshot CT h caller old_snapshot)
          (root := root).
        -- exact Hpost_aligned.
        -- exact Hprospective.
        -- exact Hafter.
        -- exact Hzone.
        -- unfold advance_frozen_caller_snapshots. apply in_map_iff.
           exists (Some old_snapshot). split; [reflexivity|exact Hslot].
        -- split; [exact Hroot|exact Hpath].
        -- exact Hprotected.
    + split.
      * eapply frozen_caller_snapshots_nested_resume_safe_after_classified_advance
          with (exceptional := Empty_set authority_flow_state).
        -- eapply frozen_caller_snapshots_nested_resume_safe_tail.
           exact Hbody_nested.
        -- intros snapshot active_mode source exposure_mode target Hsnapshot
             Hactive_mode Hempty Hroot Hexposure_mode Hexposure Hprotected.
           inversion Hempty.
        -- intros active_mode location Hactive_mode Hempty Hprotected.
           inversion Hempty.
        -- intros snapshot older mode location Hsnapshot Holder Hmode Hcolor
             Hroot.
           left. exists mode. split; [exact Hmode|].
           eapply Hcolor_at_root_reflect; eauto.
        -- intros snapshot mode location Hsnapshot Hmode Hcolor Hprotected.
           left. eapply Hexposure_reflect; eauto.
      * split.
        -- intros new_snapshot active_mode source exposure_mode target Hnew
             Hactive_mode Hactive Hroot Hexposure_mode Hexposure Hprotected.
           unfold advance_frozen_caller_snapshots in Hnew.
           apply in_map_iff in Hnew.
           destruct Hnew as [slot [Hnew Hslot]].
           destruct slot as [old_snapshot|]; simpl in Hnew; [|discriminate].
           injection Hnew as <-. simpl in Hroot.
           destruct (independent_active_dangerous_has_prospective_root CT h
             caller active_mode source Hcaller_wf Hcaller_sound Hactive_mode
             Hactive) as [root [Hauthority_root Hpath]].
           exfalso. eapply active_prospective_component_disjoint_frozen_resume_root
             with (active := caller)
             (snapshots := advance_frozen_caller_snapshots CT h caller snapshots)
             (stack := stack)
             (older := advance_frozen_caller_snapshot CT h caller old_snapshot)
             (root := root) (target := source).
           ++ exact Hpost_aligned.
           ++ exact Hprospective.
           ++ exact Hpost_before.
           ++ unfold advance_frozen_caller_snapshots. apply in_map_iff.
              exists (Some old_snapshot). split; [reflexivity|exact Hslot].
           ++ split; [exact Hauthority_root|exact Hpath].
           ++ simpl. exact Hroot.
        -- split; [exact Hpost_joins|].
           intros new_snapshot mode source Hnew Hmode Hcolor Hroot.
           unfold advance_frozen_caller_snapshots in Hnew.
           apply in_map_iff in Hnew.
           destruct Hnew as [slot [Hnew Hslot]].
           destruct slot as [old_snapshot|]; simpl in Hnew; [|discriminate].
           injection Hnew as <-. simpl in Hroot.
           destruct (Hreflect old_snapshot mode source Hslot Hmode Hcolor
             Hroot) as
             [[phase_mode [Hphase_mode Hphase_color]] |
              [[callee_mode [Hcallee_mode Hcallee_color]] | Hsafe]].
           ++ have Hcurrent := Hbody_phase old_snapshot phase_mode source
                (ltac:(simpl; right; exact Hslot)) Hphase_mode Hphase_color.
              destruct (Hbody_joins old_snapshot phase_mode source
                (ltac:(simpl; right; exact Hslot)) Hphase_mode Hcurrent Hroot)
                as [[entry_mode [Hentry_mode Hentry]] | Hsafe'].
              ** left. exists entry_mode. simpl. split; assumption.
              ** right. intros exposure_mode target Hexposure_mode Hexposure
                   Hprotected.
                 destruct (Hexposure_reflect old_snapshot exposure_mode target
                   Hslot Hexposure_mode Hexposure Hprotected) as
                   [old_mode [Hold_mode Hold_exposure]].
                 eapply Hsafe'; eauto.
           ++ destruct (Hbody_completed old_snapshot callee_mode source
                (ltac:(simpl; right; exact Hslot)) Hcallee_mode Hcallee_color
                Hroot) as [[entry_mode [Hentry_mode Hentry]] | Hsafe'].
              ** left. exists entry_mode. simpl. split; assumption.
              ** right. intros exposure_mode target Hexposure_mode Hexposure
                   Hprotected.
                 destruct (Hexposure_reflect old_snapshot exposure_mode target
                   Hslot Hexposure_mode Hexposure Hprotected) as
                   [old_mode [Hold_mode Hold_exposure]].
                 eapply Hsafe'; eauto.
           ++ right. intros exposure_mode target Hexposure_mode Hexposure
                Hprotected.
              destruct (Hexposure_reflect old_snapshot exposure_mode target
                Hslot Hexposure_mode Hexposure Hprotected) as
                [old_mode [Hold_mode Hold_exposure]].
              eapply Hsafe; eauto.
Qed.

(** Compatibility corollary for callers that already establish exact
    completed-callee reflection. *)
Lemma private_frozen_snapshot_return_safety_after_untracked_return_parts :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller caller_incoming post_snapshots,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    principled_phased_authority_live_history_state CT P Z cutoff caller stack
      caller_incoming h ->
    post_snapshots = advance_frozen_caller_snapshots CT h caller snapshots ->
    private_frozen_snapshot_structural_state CT h caller post_snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      post_snapshots stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff post_snapshots stack ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h callee incoming)
          (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot) ->
    private_frozen_snapshot_return_safety CT h Z caller caller_incoming
      post_snapshots.
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller caller_incoming post_snapshots Hbody Hpost Heq Hstructural
    Hprospective Hafter Hcaller_wf Hcaller_sound Hreflect.
  eapply private_frozen_snapshot_return_safety_after_untracked_return_phase_parts;
    eauto.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_after_return_parts :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller post_snapshots,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    post_snapshots = advance_frozen_caller_snapshots CT h caller snapshots ->
    private_frozen_snapshot_structural_state CT h caller post_snapshots stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      post_snapshots stack ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint post_snapshots.
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller post_snapshots Hbody Hdisjoint Heq Hstructural Hprospective
    Hcaller_wf Hcaller_sound. subst post_snapshots.
  destruct Hstructural as
    (Hpost_aligned & Hpost_runtime & Hpost_closed & Hpost_retain &
      Hpost_dangerous & Hpost_roots & Hpost_exposure & Hpost_before &
      Hpost_covered & Hpost_entry & Hpost_phase).
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
  - exact Hdisjoint.
  - intros newer older mode location Hnewer Holder Hcolor Hroot.
    have Hclass := advanced_tail_exposure_class_after_return CT P Z cutoff
      callee boundary stack incoming head_slot snapshots h caller newer mode
      location Hbody Hcaller_wf Hcaller_sound Hnewer Hcolor.
    destruct Hclass as [Hold | [Hmode Hcovered]].
    + exists mode. exact Hold.
    + change (mode = FlowProspective) in Hmode. subst mode.
      destruct Hcovered as [root [Hauthority_root Hpath]]. exfalso.
      eapply active_prospective_component_disjoint_frozen_resume_root with
        (active := caller)
        (snapshots := advance_frozen_caller_snapshots CT h caller snapshots)
        (stack := stack)
        (older := advance_frozen_caller_snapshot CT h caller older)
        (root := root) (target := location).
      * exact Hpost_aligned.
      * exact Hprospective.
      * exact Hpost_before.
      * unfold advance_frozen_caller_snapshots. apply in_map_iff.
        exists (Some older). split; [reflexivity|exact Holder].
      * split; [exact Hauthority_root|exact Hpath].
      * simpl. exact Hroot.
Qed.

Lemma frozen_snapshot_current_root_makes_resume_exposure_safe :
  forall Z snapshots snapshot source_mode source,
    frozen_caller_snapshots_avoid_protected Z snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    frozen_caller_snapshots_entry_exposure_covered snapshots ->
    List.In (Some snapshot) snapshots ->
    authority_mode_dangerous source_mode ->
    In authority_flow_state snapshot.(frozen_snapshot_current_colors)
      (source_mode, source) ->
    In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
    frozen_snapshot_resume_exposure_avoids Z snapshot.
Proof.
  intros Z snapshots snapshot source_mode source Havoid Hjoins Hentry
    Hsnapshot Hsource_mode Hsource Hroot.
  destruct (Hjoins snapshot source_mode source Hsnapshot Hsource_mode Hsource
    Hroot) as [[entry_mode [Hentry_mode Hentry_color]] | Hsafe].
  - intros exposure_mode target Hexposure_mode Hexposure Hprotected.
    eapply (Havoid snapshot exposure_mode target Hsnapshot Hexposure_mode).
    + eapply (Hentry snapshot entry_mode source Hsnapshot Hentry_mode
        Hentry_color Hroot). exact Hexposure.
    + exact Hprotected.
  - exact Hsafe.
Qed.

Lemma frozen_completed_colors_resume_safe_from_snapshot_root_colors :
  forall Z completed snapshots,
    frozen_caller_snapshots_avoid_protected Z snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    frozen_caller_snapshots_entry_exposure_covered snapshots ->
    (forall snapshot source_mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous source_mode ->
      In authority_flow_state completed (source_mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists snapshot_mode,
        authority_mode_dangerous snapshot_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (snapshot_mode, source)) ->
    frozen_completed_colors_resume_safe Z completed snapshots.
Proof.
  intros Z completed snapshots Havoid Hjoins Hentry Hclass snapshot
    source_mode source Hsnapshot Hsource_mode Hsource Hroot.
  destruct (Hclass snapshot source_mode source Hsnapshot Hsource_mode Hsource
    Hroot) as [snapshot_mode [Hsnapshot_mode Hsnapshot_color]].
  have Hsafe := frozen_snapshot_current_root_makes_resume_exposure_safe Z
    snapshots snapshot snapshot_mode source Havoid Hjoins Hentry Hsnapshot
    Hsnapshot_mode Hsnapshot_color Hroot.
  right. exact Hsafe.
Qed.

Lemma frozen_caller_snapshots_resume_roots_safe_from_snapshot_root_colors :
  forall CT h Z active snapshots,
    frozen_caller_snapshots_avoid_protected Z snapshots ->
    frozen_caller_snapshots_resume_joins_safe Z snapshots ->
    frozen_caller_snapshots_entry_exposure_covered snapshots ->
    (forall snapshot active_mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous active_mode ->
      In authority_flow_state
        (independent_active_authority_colors CT h active)
        (active_mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists snapshot_mode,
        authority_mode_dangerous snapshot_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_current_colors)
          (snapshot_mode, source)) ->
    frozen_caller_snapshots_resume_roots_safe CT h Z active snapshots.
Proof.
  intros CT h Z active snapshots Havoid Hjoins Hentry Hclass snapshot
    active_mode source exposure_mode target Hsnapshot Hactive_mode Hactive
    Hroot Hexposure_mode Hexposure.
  destruct (Hclass snapshot active_mode source Hsnapshot Hactive_mode Hactive
    Hroot) as [snapshot_mode [Hsnapshot_mode Hsnapshot_color]].
  have Hsafe := frozen_snapshot_current_root_makes_resume_exposure_safe Z
    snapshots snapshot snapshot_mode source Havoid Hjoins Hentry Hsnapshot
    Hsnapshot_mode Hsnapshot_color Hroot.
  exact (Hsafe exposure_mode target Hexposure_mode Hexposure).
Qed.

(** Final strengthened induction state.  The disjointness conjunct is ghost
    state initialized by [None] slots at the public boundary; it is never a
    premise of the public preservation theorem. *)
Definition private_principled_statement_state
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (active : watched_frame) (stack : list watched_boundary)
  (incoming : Ensemble authority_flow_state)
  (snapshots : list frozen_caller_snapshot_slot) (h : heap) : Prop :=
  private_fresh_frozen_statement_state CT P Z cutoff active stack incoming
    snapshots h /\
  frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots.

Definition private_principled_statement_result
  (CT : class_table) (P Z : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (final_senv : s_env) (final_renv : r_env)
  (stack : list watched_boundary) (incoming : Ensemble authority_flow_state)
  (initial_snapshots final_snapshots : list frozen_caller_snapshot_slot)
  (final_h : heap) : Prop :=
  private_statement_preservation_result CT P Z cutoff authority final_senv
    final_renv stack incoming initial_snapshots final_snapshots final_h /\
  frozen_caller_snapshots_newer_resume_exposure_disjoint final_snapshots.

Lemma potential_live_history_starts_private_principled_statement :
  forall CT P Z cutoff authority sGamma rGamma stack h,
    potential_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack h ->
    private_principled_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack
      (Empty_set authority_flow_state) (repeat None (length stack)) h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack h Hstate. split.
  - eapply potential_live_history_starts_private_fresh_frozen_statement.
    exact Hstate.
  - apply repeat_none_snapshots_newer_resume_exposure_disjoint.
Qed.

Lemma private_principled_statement_result_refl :
  forall CT P Z cutoff authority sGamma rGamma stack incoming snapshots h,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_principled_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    private_principled_statement_result CT P Z cutoff authority sGamma rGamma
      stack incoming snapshots snapshots h.
Proof.
  intros CT P Z cutoff authority sGamma rGamma stack incoming snapshots h
    Hmain [Hprivate Hdisjoint]. split.
  - eapply private_statement_preservation_result_refl; eauto.
  - exact Hdisjoint.
Qed.

Lemma private_principled_statement_result_trans :
  forall CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots middle_h final_h,
    private_principled_statement_result CT P Z cutoff authority middle_senv
      middle_renv stack incoming initial_snapshots middle_snapshots middle_h ->
    private_principled_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming middle_snapshots final_snapshots final_h ->
    private_principled_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots final_h.
Proof.
  intros CT P Z cutoff authority middle_senv middle_renv final_senv
    final_renv stack incoming initial_snapshots middle_snapshots
    final_snapshots middle_h final_h [Hfirst _] [Hsecond Hdisjoint]. split.
  - eapply private_statement_preservation_result_trans; eauto.
  - exact Hdisjoint.
Qed.

Lemma private_principled_statement_after_assignment :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x expression old value,
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_principled_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    private_principled_statement_result CT P Z cutoff authority sGamma
      (update_r_env_value rGamma x value) stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma
          (update_r_env_value rGamma x value)) snapshots) h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x expression old value Hpotential [Hprivate Hdisjoint] Htyping Hscope
    Hvalue Heval. split.
  - eapply private_statement_preservation_after_assignment; eauto.
  - have Hfrozen := proj1 (proj1 Hprivate).
    destruct Hfrozen as
      (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
        Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
    have Hwf : wf_r_config CT sGamma rGamma h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hdescend := rdm_roots_descend_after_assignment CT sGamma mt rGamma h
      x expression old value Hwf Htyping Hscope Hvalue Heval.
    eapply
      frozen_caller_snapshots_newer_resume_exposure_disjoint_after_active_descent;
      eauto.
Qed.

Lemma private_principled_statement_after_local :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    T x sGamma',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_principled_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    private_principled_statement_result CT P Z cutoff authority sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])) stack incoming snapshots
      (advance_frozen_caller_snapshots CT h
        (mk_watched_frame authority sGamma'
          (set_vars rGamma (vars rGamma ++ [Null_a]))) snapshots) h.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    T x sGamma' Hpotential [Hprivate Hdisjoint] Htyping Hnone. split.
  - eapply private_statement_preservation_after_local; eauto.
  - have Hfrozen := proj1 (proj1 Hprivate).
    destruct Hfrozen as
      (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
        Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
    have Hwf : wf_r_config CT sGamma rGamma h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hdescend := rdm_roots_descend_after_local CT sGamma mt rGamma h T x
      sGamma' Hwf Htyping Hnone.
    eapply
      frozen_caller_snapshots_newer_resume_exposure_disjoint_after_active_descent;
      eauto.
Qed.

Lemma private_principled_statement_after_field_write :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_principled_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    private_principled_statement_result CT P Z cutoff authority sGamma'
      rGamma' stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x field y sGamma' rGamma' h' Hpotential [Hprivate Hdisjoint] Htyping
    Hscope Heval.
  have Hfrozen := proj1 (proj1 Hprivate).
  have Hprivate_certificates := proj2 (proj1 Hprivate).
  destruct Hprivate_certificates as
    (Horigins & Hbefore & Hcovered & Hnested & Hcompleted).
  destruct Hfrozen as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  have Hwf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h rGamma authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Heffect := typed_field_write_component_effect CT authority sGamma mt
    rGamma h x field y sGamma' rGamma' h' Hwf Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by
    (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by
    (inversion Heval; reflexivity).
  subst sGamma' rGamma'. split.
  - eapply private_statement_preservation_after_field_write; eauto.
  - have Hprivate_tail := proj2 Hprivate.
    destruct Hprivate_tail as [Hcomponents [Hprospective Hafter]].
    have Hind_runtime : authority_colors_runtime_mutable h
        (independent_active_authority_colors CT h
          (mk_watched_frame authority sGamma rGamma)).
    { eapply executing_authority_colors_runtime_mutable.
      - exact Hwf.
      - exact Hsound.
      - intros mode location Hempty. inversion Hempty. }
    destruct Heffect as
      [[Hretained_reflect [Hmutable_reflect [Hretained Howned]]] |
       [lx [old [written [Hheap [Hobj Hendpoints]]]]]].
    + exact
        (frozen_caller_snapshots_newer_resume_exposure_disjoint_after_graph_reflection
          CT h h' (mk_watched_frame authority sGamma rGamma) snapshots
          Hretained Hmutable_reflect Hexposure Hdisjoint).
    + subst h'.
      exact
        (frozen_caller_snapshots_newer_resume_exposure_disjoint_after_safe_field_update
          CT h (mk_watched_frame authority sGamma rGamma) snapshots stack lx
          old field written Hwf Hsound Hobj Hexposure Hind_runtime Hendpoints
          Haligned Hprospective Hbefore Hdisjoint).
Qed.

Lemma private_principled_statement_after_new :
  forall CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x qc C args sGamma' rGamma' h',
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming h ->
    private_principled_statement_state CT P Z cutoff
      (mk_watched_frame authority sGamma rGamma) stack incoming snapshots h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    private_principled_statement_result CT P Z cutoff authority sGamma'
      rGamma' stack incoming snapshots
      (advance_frozen_caller_snapshots CT h'
        (mk_watched_frame authority sGamma' rGamma') snapshots) h'.
Proof.
  intros CT P Z cutoff authority sGamma mt rGamma h stack incoming snapshots
    x qc C args sGamma' rGamma' h' Hpotential [Hprivate Hdisjoint] Htyping
    Heval. split.
  - eapply private_statement_preservation_after_new; eauto.
  - have Hfrozen := proj1 (proj1 Hprivate).
    have Hprivate_certificates := proj2 (proj1 Hprivate).
    destruct Hprivate_certificates as
      (Horigins & Hbefore & Hcovered & Hnested & Hcompleted).
    destruct Hfrozen as
      (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
        Hroots & Hexposure & Hresume & Hjoins & Hentry & Hphase).
    have Hwf : wf_r_config CT sGamma rGamma h :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hsound : authority_context_sound h rGamma authority :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
    have Hprivate_post := private_fresh_frozen_statement_after_new CT P Z
      cutoff authority sGamma mt rGamma h stack incoming snapshots x qc C args
      sGamma' rGamma' h' Hprivate Htyping Heval.
    have Hpost_main := proj1 (proj1 (proj1 Hprivate_post)).
    have Hpost_wf : wf_r_config CT sGamma' rGamma' h' :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hpost_main))))).
    have Hpost_sound : authority_context_sound h' rGamma' authority :=
      proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpost_main)))))).
    have Hprivate_tail := proj2 Hprivate.
    destruct Hprivate_tail as [Hcomponents [Hprospective Hafter]].
    inversion Heval; subst.
    assert (Hupdate :
        set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
        update_r_env_value rGamma x (Iot (dom h))).
    { destruct rGamma. reflexivity. }
    rewrite Hupdate in Hpost_wf, Hpost_sound |- *.
    set (new_runtime := vpa_mutability_object_creation qthisr qc) in *.
    eapply frozen_caller_snapshots_newer_resume_exposure_disjoint_after_new
      with (qreceiver := qthisr) (qruntime := new_runtime) (stack := stack);
      eauto.
Qed.

Lemma private_principled_statement_enter_channel_free_from_parts :
  forall CT P Z cutoff caller stack incoming snapshots h boundary callee
    caller_colors,
    private_principled_statement_state CT P Z cutoff caller stack incoming
      snapshots h ->
    boundary.(boundary_caller) = caller ->
    callee = mk_watched_frame
      (call_authority caller.(frame_authority)
        boundary.(boundary_receiver_view))
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) ->
    entry_ownership_channel_free boundary ->
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) caller_colors
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) h ->
    private_principled_statement_state CT P Z cutoff callee
      (boundary :: stack) caller_colors
      (enter_nested_frozen_caller_snapshots CT h caller callee caller_colors
        snapshots) h.
Proof.
  intros CT P Z cutoff caller stack incoming snapshots h boundary callee
    caller_colors [Hprivate Hdisjoint] Hboundary Hcallee Hfree Hentry.
  split; [exact Hentry|].
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_enter_channel_free;
    eauto.
Qed.

Lemma private_principled_statement_after_tracked_pop_from_parts :
  forall CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    caller_incoming,
    private_principled_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    private_fresh_frozen_statement_state CT P Z cutoff caller stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) h ->
    private_principled_statement_state CT P Z cutoff caller stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) h.
Proof.
  intros CT P Z cutoff active boundary stack incoming head_slot snapshots h caller
    caller_incoming [Hprivate Hdisjoint] Hcaller Hcaller_wf Hcaller_sound
    Hpost. split; [exact Hpost|].
  have Htail_disjoint :=
    frozen_caller_snapshots_newer_resume_exposure_disjoint_tail
      head_slot snapshots Hdisjoint.
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_tracked_pop;
    eauto.
Qed.

(** The explicit untracked specialization documents the [None] boundary
    used by general calls.  Its proof is the same slot-polymorphic pop rule;
    no snapshot is fabricated for the immediate caller. *)
Lemma private_principled_statement_after_untracked_pop_from_parts :
  forall CT P Z cutoff active boundary stack incoming snapshots h caller
    caller_incoming,
    private_principled_statement_state CT P Z cutoff active
      (boundary :: stack) incoming (None :: snapshots) h ->
    caller = boundary.(boundary_caller) ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    private_fresh_frozen_statement_state CT P Z cutoff caller stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) h ->
    private_principled_statement_state CT P Z cutoff caller stack
      caller_incoming
      (advance_frozen_caller_snapshots CT h caller snapshots) h.
Proof.
  intros. eapply private_principled_statement_after_tracked_pop_from_parts;
    eauto.
Qed.

Lemma frozen_caller_snapshots_newer_resume_exposure_disjoint_enter_untracked :
  forall CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots h,
    private_fresh_frozen_statement_state CT P Z cutoff old_active stack
      old_incoming snapshots h ->
    private_fresh_frozen_statement_state CT P Z cutoff new_active
      (boundary :: stack) new_incoming
      (None :: advance_frozen_caller_snapshots CT h new_active snapshots) h ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint snapshots ->
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    authority_context_sound h new_active.(frame_renv)
      new_active.(frame_authority) ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (advance_frozen_caller_snapshots CT h new_active snapshots).
Proof.
  intros CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots h Hold Hpost Hdisjoint Hnew_wf Hnew_sound.
  have Hold_frozen := proj1 (proj1 Hold).
  destruct Hold_frozen as
    (Hold_main & Hold_aligned & Hold_runtime & Hold_closed & Hold_retain &
      Hold_dangerous & Hold_avoid & Hold_roots & Hold_exposure & Hold_resume &
      Hold_joins & Hold_entry & Hold_phase).
  have Hpost_frozen := proj1 (proj1 Hpost).
  destruct Hpost_frozen as
    (Hpost_main & Hpost_aligned & Hpost_runtime & Hpost_closed & Hpost_retain &
      Hpost_dangerous & Hpost_avoid & Hpost_roots & Hpost_exposure &
      Hpost_resume & Hpost_joins & Hpost_entry & Hpost_phase).
  have Hpost_certificates := proj2 (proj1 Hpost).
  destruct Hpost_certificates as
    (Hpost_origins & Hpost_before & Hpost_covered &
      Hpost_nested & Hpost_completed).
  have Hpost_tail := proj2 Hpost.
  destruct Hpost_tail as
    [Hpost_components [Hpost_prospective Hpost_after]].
  eapply
    frozen_caller_snapshots_newer_resume_exposure_disjoint_after_reflected_advance.
  - exact Hdisjoint.
  - intros newer older mode location Hnewer Holder
      [seed [Hseed Hpath]] Hroot.
    have Hclass := pop_resume_exposure_state_class_connected CT h old_active
      new_active newer.(frozen_snapshot_current_resume_exposure) seed
      (mode, location) Hnew_wf Hnew_sound
      ((proj1 Hold_exposure) newer Hnewer)
      ((proj1 (proj2 Hold_exposure)) newer Hnewer) (or_introl Hseed) Hpath.
    destruct Hclass as [Hold_color | [Hmode Hcovered]].
    + exists mode. exact Hold_color.
    + change (mode = FlowProspective) in Hmode. subst mode.
      destruct Hcovered as [root [Hauthority_root Hroot_path]]. exfalso.
      set (new_older := advance_frozen_caller_snapshot CT h new_active older).
      have Hnew_older : List.In (Some new_older)
          (None :: advance_frozen_caller_snapshots CT h new_active snapshots).
      { simpl. right. unfold advance_frozen_caller_snapshots.
        apply in_map_iff. exists (Some older). split; [reflexivity|exact Holder]. }
      eapply
        (active_prospective_component_disjoint_frozen_resume_root CT h
          new_active
          (None :: advance_frozen_caller_snapshots CT h new_active snapshots)
          (boundary :: stack) new_older root location Hpost_aligned
          Hpost_prospective Hpost_before Hnew_older).
      * split; [exact Hauthority_root|exact Hroot_path].
      * unfold new_older. simpl. exact Hroot.
Qed.

Lemma private_principled_statement_enter_untracked_from_parts :
  forall CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots h,
    private_principled_statement_state CT P Z cutoff old_active stack
      old_incoming snapshots h ->
    private_fresh_frozen_statement_state CT P Z cutoff new_active
      (boundary :: stack) new_incoming
      (None :: advance_frozen_caller_snapshots CT h new_active snapshots) h ->
    wf_r_config CT new_active.(frame_senv) new_active.(frame_renv) h ->
    authority_context_sound h new_active.(frame_renv)
      new_active.(frame_authority) ->
    private_principled_statement_state CT P Z cutoff new_active
      (boundary :: stack) new_incoming
      (None :: advance_frozen_caller_snapshots CT h new_active snapshots) h.
Proof.
  intros CT P Z cutoff old_active new_active boundary stack old_incoming
    new_incoming snapshots h [Hold Hdisjoint] Hpost Hnew_wf Hnew_sound.
  split; [exact Hpost|]. simpl.
  eapply frozen_caller_snapshots_newer_resume_exposure_disjoint_enter_untracked;
    eauto.
Qed.

Lemma frozen_snapshot_lists_metadata_and_reflection_in :
  forall Z final initial final_snapshot,
    frozen_caller_snapshot_list_metadata_eq final initial ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z final initial ->
    List.In (Some final_snapshot) final ->
    exists initial_snapshot,
      List.In (Some initial_snapshot) initial /\
      frozen_caller_snapshot_metadata_eq final_snapshot initial_snapshot /\
      frozen_snapshot_resume_exposure_protected_reflected Z final_snapshot
        initial_snapshot.
Proof.
  intros Z final initial final_snapshot Hmetadata Hreflection Hfinal.
  induction Hmetadata; inversion Hreflection; subst; simpl in Hfinal.
  - contradiction.
  - destruct Hfinal as [Hhead | Htail].
    + subst x. destruct y as [initial_snapshot|]; simpl in H; try contradiction.
      exists initial_snapshot. split; [simpl; auto|]. split; assumption.
    + destruct (IHHmetadata H5 Htail) as
        [initial_snapshot [Hinitial [Hmeta Hreflect]]].
      exists initial_snapshot. split; [simpl; auto|]. split; assumption.
Qed.

(** Structural transport plus the first semantic pop obligation.  This is
    the reusable tail package consumed by the private statement induction;
    all hypotheses are derived from the tracked call entry and completed
    body. *)
(** Exceptional immutable-caller pop wrapper using root-scoped overlap
    provenance.  All additional arguments are private products of call
    entry, body preservation, and ordinary typing; none is exported through
    the public statement theorem. *)
Lemma tracked_mutable_post_update_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    boundary.(boundary_caller).(frame_authority) = Mut_r ->
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    executing_authority_call_pop_safe CT h Z active active_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming caller_post Hauthority Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots Hincoming Hcaller_incoming Howned.
  eapply tracked_post_update_call_pop_safe; eauto.
  intros mode left right Hmode Hderivation Hclass Hleft Hright Hreturn.
  eapply tracked_join_under_mutable_authority_has_class; eauto.
Qed.

Lemma null_update_rdm_root_is_old :
  forall caller_senv caller_renv destination root,
    typed_root RDM caller_senv
      (update_r_env_value caller_renv destination Null_a) root ->
    typed_root RDM caller_senv caller_renv root.
Proof.
  intros caller_senv caller_renv destination root
    [variable [T [Htype [Hvalue Hrdm]]]].
  destruct caller_renv as [caller_vars]. simpl in *.
  destruct (Nat.eq_dec variable destination) as [Heq | Hneq].
  - subst variable.
    have Hdom := runtime_getVal_dom _ _ _ Hvalue. simpl in Hdom.
    rewrite update_length in Hdom.
    have Hsame := runtime_getVal_update_same (mkr_env caller_vars)
      destination Null_a
      Hdom.
    rewrite Hvalue in Hsame. discriminate.
  - exists variable, T. repeat split; try assumption.
    have Hdiff := runtime_getVal_update_diff (mkr_env caller_vars)
      destination variable Null_a (ltac:(congruence)).
    rewrite Hvalue in Hdiff. symmetry. exact Hdiff.
Qed.

Lemma tracked_null_post_update_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination Null_a) in
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination Null_a) h ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    executing_authority_call_pop_safe CT h Z active active_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination caller_incoming
    caller_post Hfull Hcaller_post_wf Hroots Hincoming Hcaller_incoming
    Howned.
  have Hfull_parts := Hfull.
  destruct Hfull_parts as
    (Hmain & Haligned & Hruntime & Hclosed & Hretain & Hdangerous & Havoid &
      Hroots_in_heap & Hexposure & Hresume & Hjoins & Hentry & Hphase).
  eapply tracked_captured_snapshot_call_pop_safe; eauto.
  - intros mode location Hmode Hactive.
    have Hsnapshot_in : List.In (Some snapshot)
        (Some snapshot :: snapshots) by (simpl; auto).
    eapply Hphase; [exact Hsnapshot_in|exact Hmode|].
    eapply (proj1 Hincoming). exact Hactive.
  - intros root Hroot. eapply (proj2 Hroots).
    eapply null_update_rdm_root_is_old. exact Hroot.
Qed.

(** Immutable-caller counterpart of the preceding wrapper.  The four age
    hypotheses are private semantic products of tracked call entry and the
    completed channel-free body: restored incoming colors and independently
    owned caller anchors predate the boundary, non-join flow cannot enter the
    fresh suffix from an old source, and the mutable return lies in that
    suffix.  The well-founded classifier consumes all four; none can escape
    to the public theorem. *)
Lemma tracked_immutable_fresh_post_update_call_pop_safe :
  forall CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    boundary.(boundary_caller).(frame_authority) = Imm_r ->
    principled_frozen_authority_history_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some snapshot :: snapshots) h ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc snapshot.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      snapshot.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (mode, location)) ->
    (forall location,
      frame_owned_location CT h caller_post location ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, location)) ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    (forall incoming_mode location,
      In authority_flow_state caller_incoming (incoming_mode, location) ->
      location < boundary.(boundary_entry_cutoff)) ->
    (forall anchor,
      frame_owned_location CT h caller_post anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary.(boundary_entry_cutoff)) ->
    (forall source target
        (derivation : tracked_resume_frozen_color_derivation CT h Z active
          active_incoming caller_post caller_incoming snapshot source)
        derivation_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming caller_post caller_incoming snapshot source derivation
        derivation_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary.(boundary_entry_cutoff) <= snd target ->
      boundary.(boundary_entry_cutoff) <= snd source) ->
    boundary.(boundary_entry_cutoff) <= return_location ->
    executing_authority_call_pop_safe CT h Z active active_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff active boundary stack active_incoming snapshot
    snapshots h caller_senv caller_renv destination destination_type
    return_location caller_incoming caller_post Hauthority Hfull Hcaller_wf
    Hcaller_post_wf Hdestination Hroots Hincoming Hcaller_incoming Howned
    Hreturn_color Hincoming_old Howned_old Hnonjoin_back Hreturn_fresh.
  eapply tracked_post_update_call_pop_safe_well_founded; eauto.
  intros source_height mode left right source_derivation Hheight Hmode
    Hclass Hleft Hright Hreturn Hsmaller.
  eapply tracked_fresh_return_join_has_class with
    (source_derivation := source_derivation)
    (boundary_cutoff := boundary.(boundary_entry_cutoff)); eauto.
Qed.

(** Once the statement induction has produced its old-color summary, pop
    safety is immediate.  An old dangerous caller color is rejected by the
    caller's entry separation; a fresh location lies beyond every member of
    the protected zone.  This lemma is intentionally proof-internal: the
    reflection summary is derived recursively and is not a public premise. *)
Lemma executing_authority_call_pop_safe_from_old_colors_reflected :
  forall CT P Z cutoff caller_h caller stack caller_incoming callee_h
    caller_post callee callee_incoming,
    principled_phased_authority_live_history_state CT P Z cutoff
      caller stack caller_incoming caller_h ->
    executing_authority_old_colors_reflected CT caller_h caller
      caller_incoming callee_h caller_post caller_incoming ->
    executing_authority_call_pop_safe CT callee_h Z callee callee_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff caller_h caller stack caller_incoming callee_h
    caller_post callee callee_incoming Hcaller Hreflected mode location Hmode
    Hcolor.
  right. intros Hprotected.
  destruct (lt_dec location (dom caller_h)) as [Hold | Hfresh].
  - destruct (Hreflected mode location Hmode Hcolor Hold) as
      [old_mode [Hold_mode Hold_color]].
    have Hseparated := proj1 (proj2 (proj2 (proj2 Hcaller))).
    exact (Hseparated old_mode location Hold_mode Hold_color Hprotected).
  - have Hcutoff :=
      proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hcaller)))))).
    have Hzone := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (proj2 Hcaller))))))).
    have Hbound := Hzone location Hprotected. lia.
Qed.

(** The flexible-call statement summary permits one additional case: a
    dangerous old-location color may have arisen through benign read-only
    overlap, provided that location is outside the protected zone.  That is
    exactly the alternative needed by call-pop safety, so no stronger public
    invariant or symmetric connectivity argument is required. *)
Lemma executing_authority_call_pop_safe_from_old_colors_reflected_or_outside :
  forall CT P Z cutoff caller_h caller stack caller_incoming callee_h
    caller_post callee callee_incoming,
    principled_phased_authority_live_history_state CT P Z cutoff
      caller stack caller_incoming caller_h ->
    executing_authority_old_colors_reflected_or_outside CT Z caller_h caller
      caller_incoming callee_h caller_post caller_incoming ->
    executing_authority_call_pop_safe CT callee_h Z callee callee_incoming
      caller_post caller_incoming.
Proof.
  intros CT P Z cutoff caller_h caller stack caller_incoming callee_h
    caller_post callee callee_incoming Hcaller Hreflected mode location Hmode
    Hcolor.
  right. intros Hprotected.
  destruct (lt_dec location (dom caller_h)) as [Hold | Hfresh].
  - destruct (Hreflected mode location Hmode Hcolor Hold) as
      [[old_mode [Hold_mode Hold_color]] | Houtside].
    + have Hseparated := proj1 (proj2 (proj2 (proj2 Hcaller))).
      exact (Hseparated old_mode location Hold_mode Hold_color Hprotected).
    + exact (Houtside Hprotected).
  - have Hcutoff :=
      proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 Hcaller)))))).
    have Hzone := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
      (proj2 Hcaller))))))).
    have Hbound := Hzone location Hprotected. lia.
Qed.

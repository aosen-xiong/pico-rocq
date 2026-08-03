Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityTargetEntry.

From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

(** Recursive body reflection composed with the safe-call entry theorem.
    This is the directional replacement for reasoning backwards through
    undirected potential connectivity: final callee authority first reflects
    to its entry phase, then the entry phase reflects to the caller phase. *)
Lemma safe_call_body_old_colors_reflect_to_caller :
  forall CT caller_authority caller_senv caller_scope caller_renv caller_h
    destination method receiver args caller_final_senv vals receiver_location
    runtime_class runtime_mdef receiver_type caller_incoming callee_incoming
    final_h callee_final mode location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    authority_context_sound caller_h caller_renv caller_authority ->
    authority_colors_runtime_mutable caller_h caller_incoming ->
    stmt_typing CT caller_senv caller_scope
      (SCall destination method receiver args) caller_final_senv ->
    readonly_state_method_scope caller_scope ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    r_basetype caller_h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef ->
    runtime_lookup_list caller_renv args = Some vals ->
    let caller := mk_watched_frame caller_authority caller_senv caller_renv in
    let callee_entry := mk_watched_frame
      (call_authority caller_authority (sqtype receiver_type))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot receiver_location :: vals)) in
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    executing_authority_old_colors_reflected CT caller_h callee_entry
      callee_incoming final_h callee_final callee_incoming ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h callee_final callee_incoming)
      (mode, location) ->
    location < dom caller_h ->
    exists caller_mode,
      authority_mode_dangerous caller_mode /\
      In authority_flow_state
        (executing_authority_color_set CT caller_h caller caller_incoming)
        (caller_mode, location).
Proof.
  intros CT caller_authority caller_senv caller_scope caller_renv caller_h
    destination method receiver args caller_final_senv vals receiver_location
    runtime_class runtime_mdef receiver_type caller_incoming callee_incoming
    final_h callee_final mode location Hwf Hsound Hincoming Htyping Hscope
    Hreceiver_type Hreceiver_value Hbase Hfind Hargs caller callee_entry
    Hcallee_incoming Hbody Hmode Hcolor Hold.
  destruct (Hbody mode location Hmode Hcolor Hold) as
    [entry_mode [Hentry_mode Hentry_color]].
  rewrite Hcallee_incoming in Hentry_color.
  eapply executing_authority_colors_enter_call_covered; eauto.
Qed.

Lemma safe_call_body_old_colors_reflect_to_caller_or_outside :
  forall CT Z caller_authority caller_senv caller_scope caller_renv caller_h
    destination method receiver args caller_final_senv vals receiver_location
    runtime_class runtime_mdef receiver_type caller_incoming callee_incoming
    final_h callee_final mode location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    authority_context_sound caller_h caller_renv caller_authority ->
    authority_colors_runtime_mutable caller_h caller_incoming ->
    stmt_typing CT caller_senv caller_scope
      (SCall destination method receiver args) caller_final_senv ->
    readonly_state_method_scope caller_scope ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    r_basetype caller_h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef ->
    runtime_lookup_list caller_renv args = Some vals ->
    let caller := mk_watched_frame caller_authority caller_senv caller_renv in
    let callee_entry := mk_watched_frame
      (call_authority caller_authority (sqtype receiver_type))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot receiver_location :: vals)) in
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    executing_authority_old_colors_reflected_or_outside CT Z caller_h
      callee_entry callee_incoming final_h callee_final callee_incoming ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h callee_final callee_incoming)
      (mode, location) ->
    location < dom caller_h ->
    (exists caller_mode,
      authority_mode_dangerous caller_mode /\
      In authority_flow_state
        (executing_authority_color_set CT caller_h caller caller_incoming)
        (caller_mode, location)) \/
    ~ In Loc Z location.
Proof.
  intros CT Z caller_authority caller_senv caller_scope caller_renv caller_h
    destination method receiver args caller_final_senv vals receiver_location
    runtime_class runtime_mdef receiver_type caller_incoming callee_incoming
    final_h callee_final mode location Hwf Hsound Hincoming Htyping Hscope
    Hreceiver_type Hreceiver_value Hbase Hfind Hargs caller callee_entry
    Hcallee_incoming Hbody Hmode Hcolor Hold.
  destruct (Hbody mode location Hmode Hcolor Hold) as
    [[entry_mode [Hentry_mode Hentry_color]] | Houtside].
  - left. rewrite Hcallee_incoming in Hentry_color.
    eapply executing_authority_colors_enter_call_covered; eauto.
  - right. exact Houtside.
Qed.

(** A whole-call old-color summary simultaneously discharges the ordinary
    phased pop and the root-focused input of the policy-aware [None] pop.
    The latter only asks about older frozen roots, which are allocated before
    the call boundary and therefore fall within the old-color relation. *)
Lemma call_old_reflection_supplies_pop_obligations :
  forall CT P Z cutoff caller_h caller stack caller_incoming final_h
    caller_post callee callee_incoming snapshots,
    principled_phased_authority_live_history_state CT P Z cutoff caller stack
      caller_incoming caller_h ->
    frozen_caller_snapshots_resume_roots_in_heap caller_h snapshots ->
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    executing_authority_old_colors_reflected CT caller_h caller
      caller_incoming final_h caller_post caller_incoming ->
    executing_authority_call_pop_safe CT final_h Z callee callee_incoming
      caller_post caller_incoming /\
    (forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT final_h callee callee_incoming)
          (callee_mode, source)).
Proof.
  intros CT P Z cutoff caller_h caller stack caller_incoming final_h
    caller_post callee callee_incoming snapshots Hcaller Hroots Hincoming
    Hreflect. split.
  - eapply executing_authority_call_pop_safe_from_old_colors_reflected;
      eauto.
  - intros snapshot mode source Hsnapshot Hmode Hcolor Hroot.
    have Hold : source < dom caller_h.
    { eapply Hroots; eauto. }
    eapply call_old_reflection_supplies_completed_callee_color; eauto.
Qed.

(** A result-specific completed-callee classifier is the strongest useful
    return summary.  Composing it with the body's old-color reflection gives
    the whole-call reflection required by the recursive statement contract.
    This direction never reconstructs a caller path in the final heap: it
    first moves a post-call color into the completed callee and only then
    reflects an entry-old location through the recursive body summary. *)
Lemma completed_callee_classifier_implies_call_old_colors_reflected :
  forall CT caller_h caller caller_incoming final_h caller_post callee
    callee_incoming,
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h caller_post caller_incoming)
        (mode, location) ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT final_h callee callee_incoming)
          (callee_mode, location)) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (mode, location) ->
      location < dom caller_h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h caller caller_incoming)
          (caller_mode, location)) ->
    executing_authority_old_colors_reflected CT caller_h caller
      caller_incoming final_h caller_post caller_incoming.
Proof.
  intros CT caller_h caller caller_incoming final_h caller_post callee
    callee_incoming Hcompleted Hbody mode location Hmode Hpost Hold.
  destruct (Hcompleted mode location Hmode Hpost) as
    [callee_mode [Hcallee_mode Hcallee]].
  eapply Hbody; eauto.
Qed.

Lemma completed_callee_classifier_implies_call_old_colors_reflected_or_outside :
  forall CT Z caller_h caller caller_incoming final_h caller_post callee
    callee_incoming,
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h caller_post caller_incoming)
        (mode, location) ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT final_h callee callee_incoming)
          (callee_mode, location)) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (mode, location) ->
      location < dom caller_h ->
      (exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h caller caller_incoming)
          (caller_mode, location)) \/
      ~ In Loc Z location) ->
    executing_authority_old_colors_reflected_or_outside CT Z caller_h caller
      caller_incoming final_h caller_post caller_incoming.
Proof.
  intros CT Z caller_h caller caller_incoming final_h caller_post callee
    callee_incoming Hcompleted Hbody mode location Hmode Hpost Hold.
  destruct (Hcompleted mode location Hmode Hpost) as
    [callee_mode [Hcallee_mode Hcallee]].
  eapply Hbody; eauto.
Qed.

(** The same completed-callee classifier discharges the root-scoped input
    used when advancing every retained policy witness after pop. *)
Lemma completed_callee_classifier_supplies_resume_root_reflection :
  forall CT final_h caller_post caller_incoming callee callee_incoming
    snapshots,
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h caller_post caller_incoming)
        (mode, location) ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT final_h callee callee_incoming)
          (callee_mode, location)) ->
    forall snapshot mode source,
      List.In (Some snapshot) snapshots ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT final_h callee callee_incoming)
          (callee_mode, source).
Proof.
  intros CT final_h caller_post caller_incoming callee callee_incoming
    snapshots Hcompleted snapshot mode source _ Hmode Hpost _.
  eapply Hcompleted; eauto.
Qed.

Lemma caller_null_post_owned_is_completed_callee_powered :
  forall CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming
    location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming ->
    frame_owned_location CT final_h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) location ->
    In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming)
      (FlowPowered, location).
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming
    location Hwf Hdestination Hdestination_type Hincoming
    [root [Hroot Hreachable]].
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hwf)))).
  have Hold_root : frame_capability_root
      (mk_watched_frame caller_authority caller_senv caller_renv) root.
  { eapply caller_null_post_capability_root_is_old; eauto. }
  have Hold_owned : frame_owned_location CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv) root.
  { exists root. split; [exact Hold_root|constructor]. }
  have Hold_color : In authority_flow_state
      (executing_authority_color_set CT caller_h
        (mk_watched_frame caller_authority caller_senv caller_renv)
        caller_incoming) (FlowPowered, root).
  { eapply executing_authority_owned_is_powered. exact Hold_owned. }
  have Hcallee_root : In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming)
      (FlowPowered, root).
  { apply executing_authority_color_set_contains_incoming.
    rewrite Hincoming. exact Hold_color. }
  eapply executing_authority_dangerous_retained_reachable.
  - left. reflexivity.
  - exact Hcallee_root.
  - exact Hreachable.
Qed.

Lemma null_post_frozen_path_preserves_completed_color :
  forall CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming
    source target,
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (mode, location) ->
      location < dom caller_h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h
            (mk_watched_frame caller_authority caller_senv caller_renv)
            caller_incoming) (caller_mode, location)) ->
    authority_mode_dangerous (fst source) ->
    In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming)
      source ->
    frozen_caller_authority_connected CT final_h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a)) source target ->
    authority_mode_dangerous (fst target) /\
    In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming)
      target.
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming
    source target Hwf Hdestination Hdestination_type Hincoming Hreflect
    Hsource_mode Hsource Hpath.
  have Hlength : length caller_senv = length caller_renv.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hwf)))).
  induction Hpath as [left right Hstep | state | left middle right Hleft IHleft
    Hright IHright].
  - destruct left as [left_mode left_location].
    destruct right as [right_mode right_location]. simpl in *.
    inversion Hstep; subst.
    + split; [left; reflexivity|].
      eapply executing_authority_dangerous_retained; eauto.
    + split; [right; reflexivity|].
      eapply executing_authority_dangerous_retained; eauto.
    + split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
    + split; [right; reflexivity|].
      eapply executing_authority_dangerous_reverse_rdm; eauto.
    + have Hleft_old : typed_root RDM caller_senv caller_renv left_location.
      { eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hright_old : typed_root RDM caller_senv caller_renv right_location.
      { eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hleft_old_copy := Hleft_old.
      destruct Hleft_old_copy as
        [variable [T [Htype [Hvalue Hrdm]]]].
      have Hleft_dom := wf_config_value_dom CT caller_senv caller_renv
        caller_h variable left_location Hwf Hvalue.
      destruct (Hreflect FlowPowered left_location (or_introl eq_refl)
        Hsource Hleft_dom) as [caller_mode [Hcaller_mode Hcaller_color]].
      have Hcaller_target := executing_authority_dangerous_frame_join CT
        caller_h (mk_watched_frame caller_authority caller_senv caller_renv)
        caller_incoming caller_mode left_location right_location Hcaller_mode
        Hcaller_color Hleft_old Hright_old.
      split; [right; reflexivity|].
      apply executing_authority_color_set_contains_incoming.
      exact Hcaller_target.
    + have Hleft_old : typed_root RDM caller_senv caller_renv left_location.
      { eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hright_old : typed_root RDM caller_senv caller_renv right_location.
      { eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hleft_old_copy := Hleft_old.
      destruct Hleft_old_copy as
        [variable [T [Htype [Hvalue Hrdm]]]].
      have Hleft_dom := wf_config_value_dom CT caller_senv caller_renv
        caller_h variable left_location Hwf Hvalue.
      destruct (Hreflect FlowProspective left_location (or_intror eq_refl)
        Hsource Hleft_dom) as [caller_mode [Hcaller_mode Hcaller_color]].
      have Hcaller_target := executing_authority_dangerous_frame_join CT
        caller_h (mk_watched_frame caller_authority caller_senv caller_renv)
        caller_incoming caller_mode left_location right_location Hcaller_mode
        Hcaller_color Hleft_old Hright_old.
      split; [right; reflexivity|].
      apply executing_authority_color_set_contains_incoming.
      exact Hcaller_target.
    + split; [right; reflexivity|].
      destruct Hsource as [seed [Hseed Hpath]]. exists seed.
      split; [exact Hseed|]. eapply rt_trans; [exact Hpath|].
      apply rt_step. apply phased_authority_mark_prospective.
  - destruct state as [state_mode state_location].
    split; assumption.
  - destruct (IHleft Hsource_mode Hsource) as
      [Hmiddle_mode Hmiddle_color].
    eapply IHright; eauto.
Qed.

(** A dangerous color produced by the null-updated caller is already present
    in the completed callee phase.  The only possible dangerous origins are
    preserved incoming authority or caller-post owned roots; the latter are
    old caller roots because a null update introduces no fresh location. *)
Lemma null_post_dangerous_color_is_completed_callee_color :
  forall CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming
    mode location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming ->
    (forall source_mode source,
      authority_mode_dangerous source_mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (source_mode, source) ->
      source < dom caller_h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h
            (mk_watched_frame caller_authority caller_senv caller_renv)
            caller_incoming) (caller_mode, source)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination Null_a))
        caller_incoming) (mode, location) ->
    exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (callee_mode, location).
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming
    mode location Hwf Hdestination Hdestination_type Hincoming Hreflect
    Hmode Hcolor.
  unfold executing_authority_color_set in Hcolor.
  destruct Hcolor as [seed [Hseed Hpath]].
  destruct (phased_dangerous_path_has_frozen_origin_or_owned_promotion CT
    final_h
    (mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination Null_a)) seed
    (mode, location) Hmode Hpath) as
    [[Hseed_mode Hfrozen] | [anchor [Howned Hfrozen]]].
  - have Hseed_color : In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming) seed.
    { destruct Hseed as [seed Hseed | seed Hseed].
      - apply executing_authority_color_set_contains_incoming.
        rewrite Hincoming.
        apply executing_authority_color_set_contains_incoming.
        exact Hseed.
      - destruct Hseed as [owned [Heq Howned_seed]].
        inversion Heq; subst.
        eapply caller_null_post_owned_is_completed_callee_powered; eauto. }
    destruct (null_post_frozen_path_preserves_completed_color CT
      caller_authority caller_senv caller_renv caller_h final_h destination
      destination_type callee callee_incoming caller_incoming seed
      (mode, location) Hwf Hdestination Hdestination_type Hincoming Hreflect
      Hseed_mode Hseed_color Hfrozen) as [_ Htarget].
    exists mode. split; assumption.
  - have Hanchor_color : In authority_flow_state
      (executing_authority_color_set CT final_h callee callee_incoming)
      (FlowPowered, anchor).
    { eapply caller_null_post_owned_is_completed_callee_powered; eauto. }
    destruct (null_post_frozen_path_preserves_completed_color CT
      caller_authority caller_senv caller_renv caller_h final_h destination
      destination_type callee callee_incoming caller_incoming
      (FlowPowered, anchor) (mode, location) Hwf Hdestination
      Hdestination_type Hincoming Hreflect (or_introl eq_refl) Hanchor_color
      Hfrozen) as [_ Htarget].
    exists mode. split; assumption.
Qed.

Lemma null_call_old_colors_reflected :
  forall CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming,
    wf_r_config CT caller_senv caller_renv caller_h ->
    destination <> 0 ->
    static_getType caller_senv destination = Some destination_type ->
    callee_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (mode, location) ->
      location < dom caller_h ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h
            (mk_watched_frame caller_authority caller_senv caller_renv)
            caller_incoming) (caller_mode, location)) ->
    executing_authority_old_colors_reflected CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming final_h
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination Null_a))
      caller_incoming.
Proof.
  intros CT caller_authority caller_senv caller_renv caller_h final_h
    destination destination_type callee callee_incoming caller_incoming Hwf
    Hdestination Hdestination_type Hincoming Hreflect mode location Hmode
    Hcolor Hold.
  destruct (null_post_dangerous_color_is_completed_callee_color CT
    caller_authority caller_senv caller_renv caller_h final_h destination
    destination_type callee callee_incoming caller_incoming mode location Hwf
    Hdestination Hdestination_type Hincoming Hreflect Hmode Hcolor) as
    [callee_mode [Hcallee_mode Hcallee_color]].
  eapply Hreflect; eauto.
Qed.

(** Temporal reflection for the tail that is closed under the actual
    post-update caller.  New prospective exposure is on the callee side of
    every older boundary and therefore cannot occur in the protected prefix;
    every protected exposure consequently comes from the old tail slot. *)
Lemma frozen_snapshot_list_resume_exposure_reflected_after_return_parts :
  forall CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller,
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) incoming (head_slot :: snapshots) h ->
    frozen_caller_snapshots_aligned
      (advance_frozen_caller_snapshots CT h caller snapshots) stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h caller
      (advance_frozen_caller_snapshots CT h caller snapshots) stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff
      (advance_frozen_caller_snapshots CT h caller snapshots) stack ->
    protected_zone_before_cutoff Z cutoff ->
    wf_r_config CT caller.(frame_senv) caller.(frame_renv) h ->
    authority_context_sound h caller.(frame_renv) caller.(frame_authority) ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h caller snapshots) snapshots.
Proof.
  intros CT P Z cutoff callee boundary stack incoming head_slot snapshots h
    caller Hbody Haligned Hprospective Hafter Hzone Hcaller_wf
    Hcaller_sound.
  assert (Hmap : forall remaining,
    (forall old_snapshot, List.In (Some old_snapshot) remaining ->
      List.In (Some old_snapshot) snapshots) ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h caller remaining) remaining).
  { induction remaining as [|slot tail IH]; intros Hin; simpl.
    - constructor.
    - constructor.
      + destruct slot as [old_snapshot|]; simpl; [|exact I].
        intros mode location Hmode Hcolor Hprotected.
        have Holder : List.In (Some old_snapshot) snapshots.
        { apply Hin. simpl. left. reflexivity. }
        have Hclass := advanced_tail_exposure_class_after_return CT P Z cutoff
          callee boundary stack incoming head_slot snapshots h caller
          old_snapshot mode location Hbody Hcaller_wf Hcaller_sound Holder
          Hcolor.
        destruct Hclass as [Hold | [Hprospective_mode Hcovered]].
        * exists mode. split; assumption.
        * change (mode = FlowProspective) in Hprospective_mode.
          subst mode. destruct Hcovered as [root [Hroot Hpath]].
          exfalso.
          eapply active_prospective_component_avoids_frozen_protected with
            (active := caller)
            (snapshots := advance_frozen_caller_snapshots CT h caller snapshots)
            (stack := stack)
            (older := advance_frozen_caller_snapshot CT h caller old_snapshot)
            (root := root).
          -- exact Haligned.
          -- exact Hprospective.
          -- exact Hafter.
          -- exact Hzone.
          -- unfold advance_frozen_caller_snapshots. apply in_map_iff.
             exists (Some old_snapshot). split; [reflexivity|exact Holder].
          -- split; [exact Hroot|]. simpl. exact Hpath.
          -- exact Hprotected.
      + apply IH. intros old_snapshot Htail.
        apply Hin. simpl. right. exact Htail. }
  apply Hmap. intros old_snapshot Holder. exact Holder.
Qed.

Lemma advanced_snapshot_list_reflection_at_original_slot :
  forall CT h Z caller snapshots old,
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h caller snapshots) snapshots ->
    List.In (Some old) snapshots ->
    policy_pop_exposure_protected_reflects CT h Z caller old.
Proof.
  intros CT h Z caller snapshots.
  induction snapshots as [|slot tail IH]; intros old Hreflection Hold;
    simpl in Hold; [contradiction|].
  inversion Hreflection; subst.
  destruct Hold as [Hhead | Htail].
  - subst slot. simpl in H2. exact H2.
  - eapply IH; eauto.
Qed.

(** Exceptional non-null reconstruction for the policy-only witness tail.
    The ordinary call stack has an untracked [None] head, whereas the
    channel-free policy stack has a tracked [Some head].  The overlap-aware
    classifier mediates the latter pop, and the general return partition
    facts supply the two temporal reflection callbacks. *)
Lemma tracked_overlap_policy_witness_tail_safe_after_return :
  forall CT P Z cutoff active boundary stack active_incoming head tail h
    caller_senv caller_renv destination destination_type return_location
    caller_incoming,
    let caller_post := mk_watched_frame
      boundary.(boundary_caller).(frame_authority) caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) in
    private_fresh_frozen_statement_state CT P Z cutoff active
      (boundary :: stack) active_incoming (Some head :: tail) h ->
    frozen_caller_snapshots_newer_resume_exposure_disjoint
      (Some head :: tail) ->
    frozen_caller_snapshots_active_overlap_justified CT h Z active
      (Some head :: tail) ->
    wf_r_config CT caller_senv caller_renv h ->
    wf_r_config CT caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)) h ->
    authority_context_sound h
      (update_r_env_value caller_renv destination (Iot return_location))
      boundary.(boundary_caller).(frame_authority) ->
    static_getType caller_senv destination = Some destination_type ->
    Same_set Loc head.(frozen_snapshot_resume_rdm_roots)
      (frame_rdm_root_set
        (mk_watched_frame boundary.(boundary_caller).(frame_authority)
          caller_senv caller_renv)) ->
    Same_set authority_flow_state active_incoming
      head.(frozen_snapshot_phase_incoming) ->
    (forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state caller_incoming (mode, location) ->
      In authority_flow_state head.(frozen_snapshot_current_colors)
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
      In authority_flow_state head.(frozen_snapshot_current_colors)
        (FlowPowered, anchor)) ->
    frame_owned_location CT h active return_location ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    private_frozen_snapshot_structural_state CT h caller_post
      (advance_frozen_caller_snapshots CT h caller_post tail) stack ->
    frozen_callee_side_prospective_components_after_boundaries CT h
      caller_post (advance_frozen_caller_snapshots CT h caller_post tail)
      stack ->
    frozen_snapshot_boundaries_after_cutoff cutoff
      (advance_frozen_caller_snapshots CT h caller_post tail) stack ->
    protected_zone_before_cutoff Z cutoff ->
    private_resume_witness_stack_safe CT h Z caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h caller_post tail).
Proof.
  intros CT P Z cutoff active boundary stack active_incoming head tail h
    caller_senv caller_renv destination destination_type return_location
    caller_incoming caller_post Hbody Hdisjoint Hoverlap Hcaller_wf Hcaller_post_wf
    Hcaller_post_sound Hdestination Hroots Hincoming Hcaller_incoming Howned
    Howned_snapshot Hreturn_owned Hreturn_color Hstructural Hprospective
    Hafter Hzone.
  have Hstack_safe : private_resume_witness_stack_safe CT h Z active
      active_incoming (Some head :: tail) :=
    private_fresh_frozen_statement_state_has_resume_witness_stack_safe CT P Z
      cutoff active (boundary :: stack) active_incoming (Some head :: tail) h
      Hbody.
  have Hstack_structural : private_resume_witness_stack_structural CT h
      caller_post (advance_frozen_caller_snapshots CT h caller_post tail).
  { eapply private_resume_witness_stack_structural_after_pop_advance with
      (Z := Z) (old_active := active) (incoming := active_incoming)
      (head := Some head); eauto. }
  have Hclass : forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h caller_post caller_incoming)
        (mode, location) ->
      tracked_resume_frozen_color_class CT h Z active active_incoming
        caller_post caller_incoming head (mode, location).
  { intros mode location Hmode Hcolor.
    exact (tracked_overlap_post_update_color_has_class CT P Z cutoff active
      boundary stack active_incoming head tail h caller_senv caller_renv
      destination destination_type return_location caller_incoming
      (proj1 (proj1 Hbody)) Hoverlap Hcaller_wf Hcaller_post_wf Hdestination
      Hroots Hincoming Hcaller_incoming Howned Howned_snapshot Hreturn_owned
      Hreturn_color mode location Hmode Hcolor). }
  have Hexposure_list :
      frozen_snapshot_list_resume_exposure_protected_reflected Z
        (advance_frozen_caller_snapshots CT h caller_post tail) tail.
  { eapply frozen_snapshot_list_resume_exposure_reflected_after_return_parts
      with (callee := active) (boundary := boundary)
        (incoming := active_incoming) (head_slot := Some head); eauto.
    exact (proj1 Hstructural). }
  eapply private_resume_witness_stack_safe_after_tracked_policy_head_pop.
  - exact Hstack_structural.
  - exact Hstack_safe.
  - exact Hdisjoint.
  - intros mode location Hmode Hindependent. eapply Hclass; [exact Hmode|].
    eapply independent_active_authority_colors_in_executing.
    exact Hindependent.
  - exact Hclass.
  - intros old target mode location Hold Htarget Hmode Hcolor Hroot.
    eapply advanced_tail_current_color_at_any_older_root_reflected_after_return
      with (root_snapshot := target) (head_slot := Some head); eauto.
  - intros old Hold mode location Hmode Hcolor Hprotected.
    left. eapply advanced_snapshot_list_reflection_at_original_slot; eauto.
Qed.

Lemma frozen_snapshot_list_resume_exposure_reflected_after_safe_call_entry :
  forall CT P Z cutoff caller_authority caller_senv caller_scope caller_renv h
    stack caller_incoming snapshots destination method receiver args
    caller_final_senv vals receiver_location runtime_class runtime_mdef
    receiver_type,
    private_fresh_frozen_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv caller_renv) stack
      caller_incoming snapshots h ->
    stmt_typing CT caller_senv caller_scope
      (SCall destination method receiver args) caller_final_senv ->
    readonly_state_method_scope caller_scope ->
    static_getType caller_senv receiver = Some receiver_type ->
    runtime_getVal caller_renv receiver = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef ->
    runtime_lookup_list caller_renv args = Some vals ->
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype receiver_type))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot receiver_location :: vals)) in
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h callee snapshots) snapshots.
Proof.
  intros CT P Z cutoff caller_authority caller_senv caller_scope caller_renv h
    stack caller_incoming snapshots destination method receiver args
    caller_final_senv vals receiver_location runtime_class runtime_mdef
    receiver_type Hprivate Htyping Hscope Hreceiver_type Hreceiver_value
    Hbase Hfind Hargs callee.
  have Hfrozen := proj1 (proj1 Hprivate).
  have Hmain := proj1 Hfrozen.
  have Hwf : wf_r_config CT caller_senv caller_renv h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
  have Hsound : authority_context_sound h caller_renv caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hmain)))))).
  have Hseparated := proj1 (proj2 (proj2 (proj2 Hmain))).
  have Hfrozen_parts := Hfrozen.
  destruct Hfrozen_parts as
    (_ & _ & Hsnapshot_runtime & _ & _ & _ & _ & _ &
      Hsnapshot_exposure & _).
  assert (Hmap : forall remaining,
    (forall old_snapshot, List.In (Some old_snapshot) remaining ->
      List.In (Some old_snapshot) snapshots) ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT h callee remaining) remaining).
  { induction remaining as [|slot tail IH]; intros Hin; simpl.
    - constructor.
    - constructor.
      + destruct slot as [old_snapshot|]; simpl; [|exact I].
        intros mode location Hmode Hcolor Hprotected.
        have Holder : List.In (Some old_snapshot) snapshots.
        { apply Hin. simpl. left. reflexivity. }
        have Hcallee_color : In authority_flow_state
            (executing_authority_color_set CT h callee
              (executing_authority_color_set CT h
                (mk_watched_frame caller_authority caller_senv caller_renv)
                old_snapshot.(frozen_snapshot_current_resume_exposure)))
            (mode, location).
        { destruct Hcolor as [seed [Hseed Hpath]]. exists seed. split.
          - left. apply executing_authority_color_set_contains_incoming.
            exact Hseed.
          - eapply frozen_caller_authority_connected_is_phased. exact Hpath. }
        destruct (executing_authority_colors_enter_call_covered CT
          caller_authority caller_senv caller_scope caller_renv h destination
          method receiver args caller_final_senv vals receiver_location
          runtime_class runtime_mdef receiver_type
          old_snapshot.(frozen_snapshot_current_resume_exposure) Hwf Hsound
          ((proj1 Hsnapshot_exposure) old_snapshot Holder) Htyping Hscope
          Hreceiver_type Hreceiver_value Hbase Hfind Hargs mode location Hmode
          Hcallee_color) as
          [caller_mode [Hcaller_mode Hcaller_color]].
        destruct (executing_with_frozen_incoming_dangerous_covered_by_old_or_active
          CT h
          (mk_watched_frame caller_authority caller_senv caller_renv)
          old_snapshot.(frozen_snapshot_current_resume_exposure) caller_mode
          location ((proj1 (proj2 Hsnapshot_exposure)) old_snapshot Holder)
          Hcaller_mode Hcaller_color) as
          [[old_mode [Hold_mode Hold_color]] |
           [active_mode [Hactive_mode Hactive_color]]].
        * exists old_mode. split; assumption.
        * exfalso. eapply Hseparated; [exact Hactive_mode| |exact Hprotected].
          eapply independent_active_authority_colors_in_executing.
          exact Hactive_color.
      + apply IH. intros old_snapshot Htail.
        apply Hin. simpl. right. exact Htail. }
  apply Hmap. intros old_snapshot Holder. exact Holder.
Qed.

Lemma returned_untracked_tail_metadata_eq_initial :
  forall CT entry_h final_h entry caller initial tail,
    frozen_caller_snapshot_list_metadata_eq (None :: tail)
      (None :: advance_frozen_caller_snapshots CT entry_h entry initial) ->
    frozen_caller_snapshot_list_metadata_eq
      (advance_frozen_caller_snapshots CT final_h caller tail) initial.
Proof.
  intros CT entry_h final_h entry caller initial tail Hbody.
  inversion Hbody; subst.
  eapply frozen_caller_snapshot_list_metadata_eq_trans.
  - apply advance_frozen_caller_snapshots_metadata_eq.
  - eapply frozen_caller_snapshot_list_metadata_eq_trans.
    + exact H4.
    + apply advance_frozen_caller_snapshots_metadata_eq.
Qed.

Lemma returned_untracked_tail_exposure_reflected_initial :
  forall CT entry_h final_h Z entry caller initial tail,
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT final_h caller tail) tail ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z (None :: tail)
      (None :: advance_frozen_caller_snapshots CT entry_h entry initial) ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT entry_h entry initial) initial ->
    frozen_snapshot_list_resume_exposure_protected_reflected Z
      (advance_frozen_caller_snapshots CT final_h caller tail) initial.
Proof.
  intros CT entry_h final_h Z entry caller initial tail Hreturn Hbody Hentry.
  have Hbody_tail :=
    frozen_snapshot_list_resume_exposure_protected_reflected_tail Z None tail
      None (advance_frozen_caller_snapshots CT entry_h entry initial) Hbody.
  eapply frozen_snapshot_list_resume_exposure_protected_reflected_trans.
  - exact Hreturn.
  - eapply frozen_snapshot_list_resume_exposure_protected_reflected_trans;
      eauto.
Qed.

Lemma private_advancing_policy_statement_enter_untracked_safe_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack
    caller_incoming caller_snapshots caller_policies x method y args sGamma'
    vals ly cy runtime_mdef Ty boundary,
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack caller_incoming
      caller_snapshots caller_policies h ->
    stmt_typing CT sGamma mt (SCall x method y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    boundary.(boundary_caller) =
      mk_watched_frame caller_authority sGamma rGamma ->
    boundary.(boundary_receiver_view) = sqtype Ty ->
    boundary.(boundary_callee_entry_senv) =
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef)) ->
    boundary.(boundary_callee_entry_renv) = mkr_env (Iot ly :: vals) ->
    boundary.(boundary_entry_cutoff) = dom h ->
    let caller := mk_watched_frame caller_authority sGamma rGamma in
    let callee := mk_watched_frame
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) in
    let callee_incoming := executing_authority_color_set CT h caller
      caller_incoming in
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      h ->
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee
        caller_policies.(suspended_frame_resume_witnesses)) h ->
    private_advancing_policy_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      (enter_private_frame_join_policies_advanced CT h callee
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)))
        None
        caller_policies) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack
    caller_incoming caller_snapshots caller_policies x method y args sGamma'
    vals ly cy runtime_mdef Ty boundary Hadvancing Htyping Hscope Hgety Hvalue
    Hbase Hfind Hargs Hboundary Hboundary_view Hboundary_senv Hboundary_renv
    Hcutoff caller callee callee_incoming Hentry_fresh Hentry_witness_fresh.
  destruct Hadvancing as
    (Hold & Hcover & Hphase & Hroots_safe & Hnested_safe & Hcompleted_safe &
      Hwitness_stack_safe & Hwitness_before & Hwitness_temporal &
      Htarget_state).
  destruct Htarget_state as
    (Htarget_cover & Htarget_stack_safe & Htarget_phase_safe &
      Htarget_cross_phase & Htarget_nested_phase & Htarget_before &
      Htarget_support & Htarget_history & Htarget_temporal).
  have Htarget_stack := Htarget_stack_safe.
  have Hwitness_stack_parts := Hwitness_stack_safe.
  destruct Hwitness_stack_parts as
    (_ & _ & _ & _ & _ & Hwitness_exposure & _ & _ & _ & _ & _ & _).
  have Hcaller_main := private_policy_statement_state_main CT P Z cutoff
    caller stack caller_incoming caller_snapshots caller_policies h Hold.
  have Hcaller_wf : wf_r_config CT sGamma rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_main))))).
  have Hcaller_sound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2
      (proj2 Hcaller_main)))))).
  have Hcaller_fresh := proj1 (proj1 Hold).
  have Hcaller_frozen := proj1 Hcaller_fresh.
  have Hcaller_principled := proj1 Hcaller_frozen.
  pose proof Hcaller_principled as Hcaller_principled_copy.
  destruct Hcaller_principled as
    (Hmain & Hsnapshot_aligned & Hruntime & Hclosed & Hretain &
      Hdangerous & Havoid & Hroots & Hexposure & Hresume & Hjoins &
      Hentry_covered & Hphase_covered).
  have Hentry_main := proj1 (proj1 (proj1 Hentry_fresh)).
  have Hcallee_wf : wf_r_config CT callee.(frame_senv) callee.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hentry_main))))).
  have Hcallee_sound : authority_context_sound h callee.(frame_renv)
      callee.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hentry_main)))))).
  have Hcallee_incoming_runtime : authority_colors_runtime_mutable h
      callee_incoming := proj1 (proj2 (proj2 Hentry_main)).
  have Hcaller_independent_separated : executing_authority_colors_separated
      CT h Z caller (Empty_set authority_flow_state).
  { intros mode location Hmode Hcolor Hprotected.
    eapply (proj1 (proj2 (proj2 (proj2 Hcaller_main))));
      [exact Hmode| |exact Hprotected].
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Hcaller_executing_separated : executing_authority_colors_separated
      CT h Z caller caller_incoming.
  { exact (proj1 (proj2 (proj2 (proj2 Hcaller_main)))). }
  have Hfixed : private_policy_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      (enter_private_frame_join_policies_advanced CT h callee
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)))
        None
        caller_policies) h.
  { eapply private_policy_statement_enter_untracked_advanced_from_parts with
      (target_witness := Some (private_nested_target_call_head CT h caller
        callee callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)))
      (caller_witness := None); eauto. }
  have Hentry_target_cover_full : private_resume_witnesses_cover_snapshots Z
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses))
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots).
  { unfold private_nested_target_call_head.
    eapply private_resume_witnesses_cover_snapshots_enter_private_nested.
    exact Htarget_cover. }
  (** Target-phase decomposition for the aggregate target head. *)
  have Hentry_target_cover : True := I.
  have Hentry_target_stack : private_target_witness_stack_structural CT h
      callee
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses)).
  { eapply private_target_witness_stack_structural_enter_call; eauto. }
  have Hentry_target_tail_phase_safe :
      frozen_completed_colors_resume_phase_safe Z
        (executing_authority_color_set CT h callee callee_incoming)
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_target_witnesses)).
  { eapply
      frozen_completed_colors_resume_phase_safe_after_safe_call_entry_from_parts.
    - exact Hcaller_main.
    - exact Htyping.
    - exact Hscope.
    - exact Hgety.
    - exact Hvalue.
    - exact Hbase.
    - exact Hfind.
    - exact Hargs.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Htarget_stack)))))).
    - exact Htarget_phase_safe. }
  have Hentry_target_phase_safe :
      frozen_completed_colors_resume_phase_safe Z
        (executing_authority_color_set CT h callee callee_incoming)
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)) ::
         advance_frozen_caller_snapshots CT h callee
           caller_policies.(suspended_frame_target_witnesses)).
  { intros snapshot source_mode source Hsnapshot Hsource_mode Hsource Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    - injection Heq as <-. left.
      destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty caller_incoming Hcaller_wf Hcaller_sound
        (proj1 (proj2 (proj2 Hcaller_main))) Htyping Hscope Hgety Hvalue
        Hbase Hfind Hargs source_mode source Hsource_mode Hsource) as
        [caller_mode [Hcaller_mode Hcaller_source]].
      exists caller_mode. split; [exact Hcaller_mode|].
      unfold private_nested_target_call_head.
      destruct caller_authority; simpl; exact Hcaller_source.
    - eapply Hentry_target_tail_phase_safe; eauto. }
  have Hresume_completed_phase :
      frozen_completed_colors_resume_phase_safe Z
        (executing_authority_color_set CT h caller caller_incoming)
        caller_policies.(suspended_frame_resume_witnesses).
  { eapply target_phase_safe_transfers_to_resume_witnesses;
      eauto using Htarget_support, Htarget_phase_safe. }
  have Hresume_active_phase :
      frozen_completed_colors_resume_phase_safe Z
        (independent_active_authority_colors CT h caller)
        caller_policies.(suspended_frame_resume_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Hresume_completed_phase; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Htarget_active_phase :
      frozen_completed_colors_resume_phase_safe Z
        (independent_active_authority_colors CT h caller)
        caller_policies.(suspended_frame_target_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Htarget_phase_safe; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Hentry_target_tail_cross_phase :
      private_target_exposures_support_resume_phase Z
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_target_witnesses))
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_resume_witnesses)).
  { eapply
      private_target_exposures_support_resume_phase_after_safe_call_entry;
      eauto.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Htarget_stack)))))). }
  have Hentry_target_tail_nested_phase :
      frozen_target_snapshots_nested_resume_phase_safe CT h Z
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_target_witnesses)).
  { eapply frozen_target_nested_phase_safe_after_safe_call_entry; eauto.
    - exact (proj1 (proj2 Htarget_stack)).
    - exact (proj1 (proj2 (proj2 (proj2 Htarget_stack)))).
    - exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Htarget_stack)))))). }
  have Hentry_target_head_cross_phase :
      frozen_completed_colors_resume_phase_safe Z
        (private_nested_target_call_head CT h caller callee callee_incoming
          caller_snapshots
          caller_policies.(suspended_frame_target_witnesses))
          .(frozen_snapshot_current_resume_exposure)
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_resume_witnesses)).
  { unfold private_nested_target_call_head.
    eapply (private_nested_target_resume_exposure_phase_safe_at_call_entry
      CT P Z cutoff caller_authority sGamma mt rGamma h stack caller_incoming
      caller_snapshots caller_policies.(suspended_frame_target_witnesses)
      caller_policies.(suspended_frame_resume_witnesses)); eauto. }
  have Hentry_target_head_nested_phase :
      frozen_snapshot_resume_activated
        (private_nested_target_call_head CT h caller callee callee_incoming
          caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)) ->
      frozen_target_colors_resume_phase_safe CT h Z
        (private_nested_target_call_head CT h caller callee callee_incoming
          caller_snapshots
          caller_policies.(suspended_frame_target_witnesses))
          .(frozen_snapshot_current_resume_exposure)
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_target_witnesses)).
  { intros Hactivation. unfold frozen_target_colors_resume_phase_safe.
    unfold frozen_snapshot_resume_activated in Hactivation.
    unfold private_nested_target_call_head in Hactivation |- *.
    unfold private_nested_frozen_call_head, nested_frozen_call_head in
      Hactivation. simpl in Hactivation.
    eapply (private_nested_target_target_exposure_phase_safe_at_call_entry
      CT P Z cutoff caller_authority sGamma mt rGamma h stack caller_incoming
      caller_snapshots caller_policies.(suspended_frame_target_witnesses));
      eauto.
    exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Htarget_stack)))))). }
  have Hentry_target_cross_phase :
      private_target_exposures_support_resume_phase Z
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)) ::
         advance_frozen_caller_snapshots CT h callee
           caller_policies.(suspended_frame_target_witnesses))
        (None :: advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_resume_witnesses)).
  { simpl. split; assumption. }
  have Hentry_target_nested_phase :
      frozen_target_snapshots_nested_resume_phase_safe CT h Z
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)) ::
         advance_frozen_caller_snapshots CT h callee
           caller_policies.(suspended_frame_target_witnesses)).
  { simpl. split; assumption. }
  have Hentry_target_before : frozen_caller_snapshots_before_boundaries
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses))
      (boundary :: stack).
  { constructor.
    - eapply private_nested_target_call_head_before_boundary; eauto.
    - eapply advance_frozen_caller_snapshots_before_boundaries.
      exact Htarget_before. }
  have Hentry_target_support : private_target_supports_resume_witnesses
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses))
      (None :: advance_frozen_caller_snapshots CT h callee
        caller_policies.(suspended_frame_resume_witnesses)).
  { simpl. eapply private_target_supports_resume_witnesses_after_advance.
    exact Htarget_support. }
  have Hentry_target_tail_history :
      private_target_history_supports_resume_phase Z
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_target_witnesses))
        (advance_frozen_caller_snapshots CT h callee
          caller_policies.(suspended_frame_resume_witnesses)).
  { eapply private_target_history_supports_resume_phase_after_advance.
    - exact Htarget_history.
    - intros resume Hin_resume Hsafe.
      eapply (frozen_snapshot_resume_exposure_avoids_after_safe_call_entry CT
        Z caller_authority sGamma mt rGamma h caller_incoming resume x method
        y args sGamma' vals ly cy runtime_mdef Ty); eauto.
      + exact ((proj1 Hwitness_exposure) resume Hin_resume).
      + exact ((proj1 (proj2 Hwitness_exposure)) resume Hin_resume). }
  have Hentry_target_history : private_target_history_supports_resume_phase Z
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses))
      (None :: advance_frozen_caller_snapshots CT h callee
        caller_policies.(suspended_frame_resume_witnesses)).
  { simpl. exact Hentry_target_tail_history. }
  have Hentry_target_temporal : private_target_witness_temporal_state CT h Z
      cutoff callee (boundary :: stack)
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses)).
  { constructor.
    - simpl. rewrite Hcutoff.
      exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 (proj2 Hcaller_main))))))).
    - eapply advance_snapshot_boundaries_after_cutoff.
      exact Htarget_temporal. }
  have Hentry_target_state : private_target_witness_state CT h Z cutoff callee
      callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses))
      (None :: advance_frozen_caller_snapshots CT h callee
        caller_policies.(suspended_frame_resume_witnesses))
      (boundary :: stack).
  { unfold private_target_witness_state.
    split; [exact Hentry_target_cover_full|].
    split.
    - exact Hentry_target_stack.
    - split; [exact Hentry_target_phase_safe|].
      split; [exact Hentry_target_cross_phase|].
      split; [exact Hentry_target_nested_phase|].
      split; [exact Hentry_target_before|].
      split; [exact Hentry_target_support|].
      split; [exact Hentry_target_history|exact Hentry_target_temporal]. }
  have Hentry_stack :=
    private_fresh_frozen_statement_state_has_resume_witness_stack_safe CT P Z
      cutoff callee (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee
        caller_policies.(suspended_frame_resume_witnesses)) h
      Hentry_witness_fresh.
  pose proof Hentry_stack as Hentry_stack_copy.
  destruct Hentry_stack as
    (Hentry_witness_covered & Hentry_witness_runtime &
      Hentry_witness_dangerous & Hentry_witness_closed &
      Hentry_witness_roots & Hentry_witness_exposure &
      Hentry_witness_resume & Hentry_witness_joins &
      Hentry_witness_nested & Hentry_witness_completed &
      Hentry_witness_retain & Hentry_witness_incoming).
  have Hordinary_tail_none : forall snapshot,
      ~ List.In (Some snapshot)
        (advance_frozen_caller_snapshots CT h callee caller_snapshots).
  { intros snapshot Hnew.
    unfold advance_frozen_caller_snapshots in Hnew.
    apply in_map_iff in Hnew.
    destruct Hnew as [old_slot [Heq Hslot]].
    destruct old_slot as [old_snapshot|]; simpl in Heq; [|discriminate].
    injection Heq as <-.
    eapply (private_resume_witnesses_cover_snapshots_none Z
      caller_policies.(suspended_frame_resume_witnesses) caller_snapshots
      old_snapshot Hcover). exact Hslot. }
  split; [exact Hfixed|].
  split.
  - simpl. split.
    + intros older Holder. eapply Hordinary_tail_none. exact Holder.
    + eapply private_resume_witnesses_cover_snapshots_after_advance.
      exact Hcover.
  - split.
    + have Hold_phase := private_resume_witnesses_phase_wf_enter_nested CT h
        caller callee callee_incoming
        caller_policies.(suspended_frame_resume_witnesses) caller_snapshots
        Hcaller_wf Hcallee_wf Hcallee_incoming_runtime Hruntime Hdangerous
        Hroots Hexposure Hphase.
      simpl in Hold_phase |-*.
      destruct Hold_phase as
        [Hold_runtime [Hold_closed [Hold_roots [Hold_exposure Htail_phase]]]].
      refine (conj _ (conj _ (conj _ (conj _ Htail_phase)))).
      * intros snapshot Hsnapshot.
        destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
        exfalso. exact (Hordinary_tail_none snapshot Htail).
      * intros snapshot Hsnapshot.
        destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
        exfalso. exact (Hordinary_tail_none snapshot Htail).
      * intros snapshot root Hsnapshot Hroot.
        destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
        exfalso. exact (Hordinary_tail_none snapshot Htail).
      * repeat split.
        -- intros snapshot Hsnapshot.
           destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
           exfalso. exact (Hordinary_tail_none snapshot Htail).
        -- intros snapshot Hsnapshot.
           destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
           exfalso. exact (Hordinary_tail_none snapshot Htail).
        -- intros snapshot mode location Hsnapshot Hcolor.
           destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
           exfalso. exact (Hordinary_tail_none snapshot Htail).
        -- intros snapshot Hsnapshot state Hstate.
           destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
           exfalso. exact (Hordinary_tail_none snapshot Htail).
        -- intros snapshot root Hsnapshot Hroot Hruntime_root.
           destruct Hsnapshot as [Hbad | Htail]; [discriminate|].
           exfalso. exact (Hordinary_tail_none snapshot Htail).
    + split.
      * have Hold_roots := private_resume_witnesses_roots_safe_enter_nested
          CT Z caller_authority sGamma mt rGamma h callee_incoming
          caller_policies.(suspended_frame_resume_witnesses) caller_snapshots
          x method y args sGamma' vals ly cy runtime_mdef Ty
          Hcaller_wf Hcaller_sound Htyping Hscope Hgety Hvalue Hbase Hfind
          Hargs Hcaller_independent_separated Hexposure Hresume Hphase
          Hroots_safe.
        simpl in Hold_roots. destruct Hold_roots as [Hold_head Hold_tail].
        split.
        -- unfold frozen_caller_snapshots_active_resume_safe.
           intros snapshot active_mode source Hsnapshot Hactive_mode
             Hactive_source Hroot.
           destruct Hsnapshot as [Hbad | Htail_snapshot]; [discriminate|].
           exfalso. exact (Hordinary_tail_none snapshot Htail_snapshot).
        -- exact Hold_tail.
      * split.
        -- have Hold_nested :=
             private_resume_witnesses_nested_resume_safe_enter_nested
             CT P Z cutoff caller_authority sGamma rGamma h stack
             caller_incoming
             caller_policies.(suspended_frame_resume_witnesses)
             caller_snapshots mt x method y args sGamma' vals ly cy
             runtime_mdef Ty Hcaller_frozen Htyping Hscope Hgety Hvalue
             Hbase Hfind Hargs Hphase Hroots_safe Hnested_safe.
           simpl in Hold_nested.
           destruct Hold_nested as [[Hold_head_against Hold_ordinary_tail]
             Hold_policy_tail].
           split.
           ++ exact Hold_ordinary_tail.
           ++ exact Hold_policy_tail.
        -- split.
           ++ have Hold_completed :=
                private_resume_witnesses_completed_safe_enter_nested
                CT P Z cutoff caller_authority sGamma rGamma h stack
                caller_incoming
                caller_policies.(suspended_frame_resume_witnesses)
                caller_snapshots mt x method y args sGamma' vals ly cy
                runtime_mdef Ty Hcaller_frozen Htyping Hscope Hgety Hvalue
                Hbase Hfind Hargs Hphase Hcompleted_safe.
              simpl in Hold_completed.
              destruct Hold_completed as [Hold_completed_head
                Hold_completed_tail].
              split.
              ** intros snapshot source_mode source Hsnapshot Hsource_mode
                   Hsource Hroot.
                 destruct Hsnapshot as [Hbad | Htail_snapshot];
                   [discriminate|].
                 eapply Hold_completed_head;
                   [simpl; right; exact Htail_snapshot|exact Hsource_mode|
                    exact Hsource|exact Hroot].
              ** exact Hold_completed_tail.
           ++ split.
              ** exact Hentry_stack_copy.
              ** split.
                 --- constructor.
                     +++ exact I.
                     +++ eapply
                       advance_frozen_caller_snapshots_before_boundaries.
                       exact Hwitness_before.
                 --- split.
                     +++ unfold private_resume_witness_temporal_state.
                         exact
                           (private_fresh_frozen_statement_state_has_resume_temporal_state
                             CT P Z cutoff callee (boundary :: stack)
                             callee_incoming
                             (None :: advance_frozen_caller_snapshots CT h callee
                               caller_policies.(suspended_frame_resume_witnesses))
                             h Hentry_witness_fresh).
                     +++ exact Hentry_target_state.
                     (* old assembly retained below *)
                     (*
                     +++ constructor.
                         **** exact I.
                         **** eapply
                           advance_frozen_caller_snapshots_before_boundaries.
                         exact Hwitness_before.
                     +++ unfold private_resume_witness_temporal_state.
                     exact
                       (private_fresh_frozen_statement_state_has_resume_temporal_state
                         CT P Z cutoff callee (boundary :: stack)
                         callee_incoming
                         (None :: advance_frozen_caller_snapshots CT h callee
                           caller_policies.(suspended_frame_resume_witnesses))
                         h Hentry_witness_fresh).
                     *)
                     (* Obsolete conditional transport retained temporarily
                        while the untracked entry is brought back to a
                        compiling checkpoint.
                     split.
                     +++ intros snapshot tracked_boundary above below
                           Hpartition Hfree.
                         simpl in Hpartition.
                         inversion Hpartition; subst.
                         *** have Hnoauthority : forall root,
                               ~ mutable_authority_root callee h root.
                             { unfold entry_ownership_channel_free in Hfree.
                               rewrite Hboundary in Hfree.
                               rewrite Hboundary_view in Hfree.
                               rewrite Hboundary_senv in Hfree.
                               rewrite Hboundary_renv in Hfree.
                               eapply
                                 no_capability_or_rdm_root_has_no_mutable_authority_root.
                               - exact (proj1 Hfree).
                               - exact (proj2 Hfree). }
                             intros frame root target Hlive Hreachable.
                             inversion Hlive; subst.
                             ---- exfalso. eapply Hnoauthority.
                                  eapply mutable_authority_reachable_has_root.
                                  exact Hreachable.
                             ---- inversion H.
                         *** destruct
                               (advance_frozen_snapshot_live_partition_reflects
                                 CT h callee
                                 caller_policies.(
                                   suspended_frame_resume_witnesses)
                                 stack snapshot tracked_boundary above0 below
                                 H7) as [old_snapshot Hold_partition].
                             have Hold_components := Hpolicy_components
                               old_snapshot tracked_boundary above0 below
                               Hold_partition Hfree.
                             unfold callee.
                             exact
                               (live_mutable_authority_components_enter_safe_call
                                 CT tracked_boundary.(boundary_entry_cutoff)
                                 caller_authority sGamma mt rGamma h above0 x
                                 method y args sGamma' vals ly cy runtime_mdef
                                 Ty boundary Hcaller_wf Htyping Hscope Hgety
                                 Hvalue Hbase Hfind Hargs Hboundary
                                 Hold_components).
                     +++ split.
                         *** intros snapshot tracked_boundary above below
                               Hpartition Hfree.
                             simpl in Hpartition.
                             inversion Hpartition; subst.
                             ---- have Hnoauthority : forall root,
                                   ~ mutable_authority_root callee h root.
                                  { unfold entry_ownership_channel_free in Hfree.
                                    rewrite Hboundary in Hfree.
                                    rewrite Hboundary_view in Hfree.
                                    rewrite Hboundary_senv in Hfree.
                                    rewrite Hboundary_renv in Hfree.
                                    eapply
                                      no_capability_or_rdm_root_has_no_mutable_authority_root.
                                    + exact (proj1 Hfree).
                                    + exact (proj2 Hfree). }
                                  intros frame root target Hlive
                                    [Hroot Hpath].
                                  inversion Hlive; subst.
                                  ++++ exfalso. exact (Hnoauthority root Hroot).
                                  ++++ inversion H.
                             ---- destruct
                                   (advance_frozen_snapshot_live_partition_reflects
                                     CT h callee
                                     caller_policies.(
                                       suspended_frame_resume_witnesses)
                                     stack snapshot tracked_boundary above0
                                     below H7) as
                                   [old_snapshot Hold_partition].
                                  have Hold_components := Hpolicy_prospective
                                    old_snapshot tracked_boundary above0 below
                                    Hold_partition Hfree.
                                  unfold callee.
                                  exact
                                    (live_prospective_mutable_authority_components_enter_safe_call
                                      CT tracked_boundary.(boundary_entry_cutoff)
                                      caller_authority sGamma mt rGamma h
                                      above0 x method y args sGamma' vals ly cy
                                      runtime_mdef Ty boundary Hcaller_wf
                                      Hcaller_sound Hcallee_wf Htyping Hscope
                                      Hgety Hvalue Hbase Hfind Hargs Hboundary
                                      Hold_components).
                         *** constructor.
                             ---- have Hglobal_cutoff : cutoff <= dom h :=
                                    proj1 (proj2 (proj2 (proj2 (proj2
                                      (proj2 (proj2 Hcaller_main)))))).
                                  simpl. rewrite Hcutoff. exact Hglobal_cutoff.
                             ---- eapply
                                  advance_snapshot_boundaries_after_cutoff.
                                  exact Hpolicy_after.
                     *)
Qed.

(** Channel-free entry is the sole place where the policy-only stack installs
    a tracked [Some] witness.  The ordinary operational snapshot remains
    [None].  Once the policy stack itself is a mature frozen stack, coverage
    implies all four mixed policy/ordinary relations, so no separate semantic
    premise is needed here or in the public theorem. *)
Lemma private_advancing_policy_statement_enter_channel_free_from_parts :
  forall CT P Z cutoff caller callee boundary stack caller_incoming
    callee_incoming caller_snapshots caller_policies h,
    private_advancing_policy_statement_state CT P Z cutoff caller stack
      caller_incoming caller_snapshots caller_policies h ->
    boundary.(boundary_caller) = caller ->
    boundary.(boundary_entry_cutoff) = dom h ->
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      h ->
    private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_resume_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_resume_witnesses)) h ->
    private_target_witness_state CT h Z cutoff callee callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_target_witnesses))
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_resume_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_resume_witnesses))
      (boundary :: stack) ->
    wf_r_config CT callee.(frame_senv) callee.(frame_renv) h ->
    authority_context_sound h callee.(frame_renv) callee.(frame_authority) ->
    private_advancing_policy_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      (enter_private_frame_join_policies_advanced CT h callee
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)))
        (Some (private_nested_frozen_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_resume_witnesses)))
        caller_policies) h.
Proof.
  intros CT P Z cutoff caller callee boundary stack caller_incoming
    callee_incoming caller_snapshots caller_policies h Hcaller Hboundary
    Hcutoff Hordinary_entry Hwitness_entry Htarget_entry Hcallee_wf
    Hcallee_sound.
  have Hfixed : private_policy_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
      (enter_private_frame_join_policies_advanced CT h callee
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_target_witnesses)))
        (Some (private_nested_frozen_call_head CT h caller callee
          callee_incoming caller_snapshots
          caller_policies.(suspended_frame_resume_witnesses)))
        caller_policies) h.
  { eapply private_policy_statement_enter_untracked_advanced_from_parts with
      (target_witness := Some (private_nested_target_call_head CT h caller
        callee callee_incoming caller_snapshots
        caller_policies.(suspended_frame_target_witnesses)))
      (caller_witness := Some (private_nested_frozen_call_head CT h caller
        callee callee_incoming caller_snapshots
        caller_policies.(suspended_frame_resume_witnesses))).
    - exact (proj1 Hcaller).
    - exact Hboundary.
    - exact Hcutoff.
    - exact Hordinary_entry.
    - exact Hcallee_wf.
    - exact Hcallee_sound. }
  have Hcaller_cover := proj1 (proj2 Hcaller).
  have Hentry_cover : private_resume_witnesses_cover_snapshots Z
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_resume_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_resume_witnesses))
      (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots).
  { eapply private_resume_witnesses_cover_snapshots_enter_private_nested.
    exact Hcaller_cover. }
  have Hentry_stack :=
    private_fresh_frozen_statement_state_has_resume_witness_stack_safe CT P Z
      cutoff callee (boundary :: stack) callee_incoming
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming caller_snapshots
        caller_policies.(suspended_frame_resume_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         caller_policies.(suspended_frame_resume_witnesses)) h
      Hwitness_entry.
  destruct (private_resume_witness_relations_from_stack_safe CT h Z callee
    callee_incoming
    (Some (private_nested_frozen_call_head CT h caller callee callee_incoming
      caller_snapshots caller_policies.(suspended_frame_resume_witnesses)) ::
     advance_frozen_caller_snapshots CT h callee
       caller_policies.(suspended_frame_resume_witnesses))
    (None :: advance_frozen_caller_snapshots CT h callee caller_snapshots)
    Hentry_cover Hentry_stack) as
    (Hentry_phase & Hentry_roots & Hentry_nested & Hentry_completed).
  split; [exact Hfixed|].
  split; [exact Hentry_cover|].
  split; [exact Hentry_phase|].
  split; [exact Hentry_roots|].
  split; [exact Hentry_nested|].
  split; [exact Hentry_completed|].
  split; [exact Hentry_stack|].
  split.
  - exact (proj1 (proj2 (proj2 (proj1 Hwitness_entry)))).
  - split.
    + eapply private_fresh_frozen_statement_state_has_resume_temporal_state.
      exact Hwitness_entry.
    + exact Htarget_entry.
Qed.

(** Behavioral subtyping itself identifies the exceptional channel-free
    shape.  A statically [RDM] result refined to a dynamically [Mut] body
    result forces the dynamic receiver to [RO]; contravariant parameters
    then rule out every non-null dynamic [RDM] argument. *)
Lemma refined_mut_return_call_has_channel_free_entry_shape :
  forall CT sGamma mt rGamma h x method receiver args vals
    receiver_location receiver_type destination_type body_return_type
    runtime_mdef static_mdef,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x method receiver args) sGamma ->
    readonly_state_method_scope mt ->
    static_getType sGamma receiver = Some receiver_type ->
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    runtime_lookup_list rGamma args = Some vals ->
    FindMethodWithName CT (sctype receiver_type) method static_mdef ->
    qualified_type_subtype CT body_return_type
      (mret (msignature runtime_mdef)) ->
    method_signature_refinement CT
      (msignature runtime_mdef) (msignature static_mdef) ->
    qualified_type_subtype CT
      (vpa_mutability_tt_readonly_state receiver_type
        (mret (msignature static_mdef)))
      destination_type ->
    sqtype receiver_type <> Bot ->
    sqtype destination_type = RDM ->
    sqtype body_return_type = Mut ->
    qualified_type_subtype CT receiver_type
      (vpa_mutability_tt_readonly_state receiver_type
        (mreceiver (msignature static_mdef))) ->
    signature_has_no_mutable_roots (msignature runtime_mdef) ->
    sqtype (mreceiver (msignature runtime_mdef)) = RO /\
    (forall root,
      ~ typed_root RDM
          (mreceiver (msignature runtime_mdef) ::
            mparams (msignature runtime_mdef))
          (mkr_env (Iot receiver_location :: vals)) root).
Proof.
  intros CT sGamma mt rGamma h x method receiver args vals
    receiver_location receiver_type destination_type body_return_type
    runtime_mdef static_mdef
    Hwf Htyping Hscope Hreceiver_type Hreceiver_value Hargs Hfind_static
    Hbody_sub Hrefine Hresult_sub Hreceiver_nonbottom
    Hdestination_rdm Hbody_mut Hreceiver_sub Hsignature_safe.
  destruct (refined_call_rdm_result_classifies_body_return CT receiver_type
    body_return_type (msignature runtime_mdef) (msignature static_mdef)
    destination_type Hbody_sub Hrefine Hresult_sub Hreceiver_nonbottom
    (ltac:(rewrite Hbody_mut; discriminate)) Hdestination_rdm) as
    [Hreceiver_rdm _].
  destruct (refined_call_rdm_mut_body_signature_shape CT receiver_type
    body_return_type (msignature runtime_mdef) (msignature static_mdef)
    destination_type Hbody_sub Hrefine Hresult_sub Hreceiver_nonbottom
    Hdestination_rdm Hbody_mut) as [Hstatic_return Hruntime_return].
  have Hstatic_receiver :
      sqtype (mreceiver (msignature static_mdef)) = RDM \/
      sqtype (mreceiver (msignature static_mdef)) = RO.
  { eapply readonly_rdm_call_receiver_signature.
    - exact Hreceiver_rdm.
    - exact Hreceiver_sub. }
  have Hruntime_receiver :
      sqtype (mreceiver (msignature runtime_mdef)) = RO.
  { eapply method_signature_refinement_mut_from_rdm_has_ro_receiver; eauto. }
  split; [exact Hruntime_receiver|].
  intros root.
  eapply refined_mut_return_call_entry_has_no_rdm_roots with
    (receiver_type := receiver_type) (runtime_mdef := runtime_mdef)
    (static_mdef := static_mdef); eauto.
Qed.

(** Typed channel-free call entry with the two ghost channels synchronized.
    The operational snapshot channel pushes [None].  The policy-only channel
    pushes the aggregate tracked witness, and no other call shape may use
    this constructor. *)
Lemma private_advancing_policy_statement_enter_channel_free_call :
  forall CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots policies x method y args sGamma' vals ly cy runtime_mdef Ty,
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots policies h ->
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
      private_advancing_policy_statement_state CT P Z cutoff
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
            (mkr_env (Iot ly :: vals))) snapshots)
        (enter_private_frame_join_policies_advanced CT h
          (mk_watched_frame
            (call_authority caller_authority (sqtype Ty))
            (mreceiver (msignature runtime_mdef) ::
              mparams (msignature runtime_mdef))
            (mkr_env (Iot ly :: vals)))
          (Some (private_nested_target_call_head CT h
            (mk_watched_frame caller_authority sGamma rGamma)
            (mk_watched_frame
              (call_authority caller_authority (sqtype Ty))
              (mreceiver (msignature runtime_mdef) ::
                mparams (msignature runtime_mdef))
              (mkr_env (Iot ly :: vals)))
            (executing_authority_color_set CT h
              (mk_watched_frame caller_authority sGamma rGamma) incoming)
            snapshots policies.(suspended_frame_target_witnesses)))
          (Some (private_nested_frozen_call_head CT h
            (mk_watched_frame caller_authority sGamma rGamma)
            (mk_watched_frame
              (call_authority caller_authority (sqtype Ty))
              (mreceiver (msignature runtime_mdef) ::
                mparams (msignature runtime_mdef))
              (mkr_env (Iot ly :: vals)))
            (executing_authority_color_set CT h
              (mk_watched_frame caller_authority sGamma rGamma) incoming)
            snapshots policies.(suspended_frame_resume_witnesses)))
          policies) h.
Proof.
  intros CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
    snapshots policies x method y args sGamma' vals ly cy runtime_mdef Ty
    Hcaller Htyping Hscope Hreceiver_type Hreceiver_value Hbase Hfind Hargs
    Hsignature_safe Hno_rdm.
  pose proof Hcaller as Hcaller_parts.
  destruct Hcaller_parts as
    (Hcaller_policy & Hcaller_cover & Hcaller_phase & Hcaller_roots &
      Hcaller_nested & Hcaller_completed & Hcaller_witness_stack &
      Hcaller_witness_before & Hcaller_witness_temporal &
      Hcaller_target_state).
  have Hordinary_fresh := proj1 (proj1 (proj1 Hcaller)).
  have Hwitness_fresh :=
    private_advancing_policy_statement_witness_state_is_private_fresh CT P Z
      cutoff (mk_watched_frame caller_authority sGamma rGamma) stack incoming
      snapshots policies h Hcaller.
  destruct (private_fresh_frozen_statement_enter_call_untracked CT P Z cutoff
    caller_authority sGamma mt rGamma h stack incoming snapshots x method y
    args sGamma' vals ly cy runtime_mdef Ty Hordinary_fresh Htyping Hscope
    Hreceiver_type Hreceiver_value Hbase Hfind Hargs) as
    [origins [destination_type [Hdestination Hordinary_entry]]].
  destruct (private_fresh_frozen_statement_enter_call_channel_free CT P Z
    cutoff caller_authority sGamma mt rGamma h stack incoming
    policies.(suspended_frame_resume_witnesses) x method y args sGamma' vals
    ly cy runtime_mdef Ty Hwitness_fresh Htyping Hscope Hreceiver_type
    Hreceiver_value Hbase Hfind Hargs Hsignature_safe Hno_rdm) as
    [witness_origins
      [witness_destination_type [Hwitness_destination Hwitness_entry]]].
  assert (witness_destination_type = destination_type) by congruence.
  subst witness_destination_type.
  assert (witness_origins = origins) by apply proof_irrelevance.
  subst witness_origins.
  set (caller := mk_watched_frame caller_authority sGamma rGamma).
  set (callee := mk_watched_frame
    (call_authority caller_authority (sqtype Ty))
    (mreceiver (msignature runtime_mdef) ::
      mparams (msignature runtime_mdef))
    (mkr_env (Iot ly :: vals))).
  set (boundary := mk_watched_call_boundary caller
    (mreceiver (msignature runtime_mdef) ::
      mparams (msignature runtime_mdef))
    (mkr_env (Iot ly :: vals)) (sqtype Ty)
    (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  set (callee_incoming := executing_authority_color_set CT h caller incoming).
  have Hfree : entry_ownership_channel_free boundary.
  { unfold boundary, caller.
    eapply channel_free_boundary_from_safe_signature_without_rdm; eauto. }
  have Hnone : forall snapshot, ~ List.In (Some snapshot) snapshots.
  { intros snapshot. eapply private_resume_witnesses_cover_snapshots_none.
    exact (proj1 (proj2 Hcaller)). }
  have Hhead_eq : private_nested_frozen_call_head CT h caller callee
      callee_incoming snapshots policies.(suspended_frame_resume_witnesses) =
      nested_frozen_call_head CT h caller callee callee_incoming
        policies.(suspended_frame_resume_witnesses).
  { eapply private_nested_frozen_call_head_eq_witness_head. exact Hnone. }
  change (private_fresh_frozen_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming
      (enter_nested_frozen_caller_snapshots CT h caller callee callee_incoming
        policies.(suspended_frame_resume_witnesses)) h) in Hwitness_entry.
  unfold enter_nested_frozen_caller_snapshots in Hwitness_entry. simpl in
    Hwitness_entry.
  rewrite <- Hhead_eq in Hwitness_entry.
  have Hentry_main := proj1 (proj1 (proj1 Hordinary_entry)).
  have Hcallee_wf : wf_r_config CT callee.(frame_senv) callee.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hentry_main))))).
  have Hcallee_sound : authority_context_sound h callee.(frame_renv)
      callee.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hentry_main)))))).
  have Hcaller_main := private_policy_statement_state_main CT P Z cutoff
    caller stack incoming snapshots policies h (proj1 Hcaller).
  have Hcaller_wf : wf_r_config CT caller.(frame_senv) caller.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_main))))).
  have Hcaller_sound : authority_context_sound h caller.(frame_renv)
      caller.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hcaller_main)))))).
  have Hcaller_executing_separated : executing_authority_colors_separated
      CT h Z caller incoming := proj1 (proj2 (proj2 (proj2 Hcaller_main))).
  have Hcallee_incoming_runtime : authority_colors_runtime_mutable h
      callee_incoming := proj1 (proj2 (proj2 Hentry_main)).
  have Htarget_state := private_advancing_policy_statement_state_target CT P Z
    cutoff caller stack incoming snapshots policies h Hcaller.
  destruct Htarget_state as
    (Htarget_cover & Htarget_stack_safe & Htarget_phase_safe &
      Htarget_cross_phase & Htarget_nested_phase & Htarget_before &
      Htarget_support & Htarget_history & Htarget_temporal).
  have Htarget_stack := Htarget_stack_safe.
  have Hwitness_stack_parts := Hcaller_witness_stack.
  destruct Hwitness_stack_parts as
    (_ & _ & _ & _ & _ & Hwitness_exposure & _ & _ & _ & _ & _ & _).
  have Hentry_target_cover_full : private_resume_witnesses_cover_snapshots Z
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_target_witnesses))
      (None :: advance_frozen_caller_snapshots CT h callee snapshots).
  { unfold private_nested_target_call_head.
    eapply private_resume_witnesses_cover_snapshots_enter_private_nested.
    exact Htarget_cover. }
  (** Target-phase decomposition for the aggregate target head. *)
  have Hentry_target_cover : True := I.
  have Hentry_target_stack : private_target_witness_stack_structural CT h
      callee
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_target_witnesses)).
  { eapply private_target_witness_stack_structural_enter_call; eauto.
    exact (proj1 (proj1 Hordinary_fresh)). }
  have Hentry_target_tail_phase_safe :
      frozen_completed_colors_resume_phase_safe Z
        (executing_authority_color_set CT h callee callee_incoming)
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_target_witnesses)).
  { eapply
      frozen_completed_colors_resume_phase_safe_after_safe_call_entry_from_parts.
    - exact Hcaller_main.
    - exact Htyping.
    - exact Hscope.
    - exact Hreceiver_type.
    - exact Hreceiver_value.
    - exact Hbase.
    - exact Hfind.
    - exact Hargs.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Htarget_stack)))))).
    - exact Htarget_phase_safe. }
  have Hentry_target_phase_safe :
      frozen_completed_colors_resume_phase_safe Z
        (executing_authority_color_set CT h callee callee_incoming)
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming snapshots
          policies.(suspended_frame_target_witnesses)) ::
         advance_frozen_caller_snapshots CT h callee
           policies.(suspended_frame_target_witnesses)).
  { intros snapshot source_mode source Hsnapshot Hsource_mode Hsource Hroot.
    simpl in Hsnapshot. destruct Hsnapshot as [Heq | Htail].
    - injection Heq as <-. left.
      destruct (executing_authority_colors_enter_call_covered CT
        caller_authority sGamma mt rGamma h x method y args sGamma' vals ly
        cy runtime_mdef Ty incoming Hcaller_wf
        (proj1 (proj1 (proj2 (proj2 (proj2 (proj2
          (proj2 Hcaller_main)))))))
        (proj1 (proj2 (proj2 Hcaller_main))) Htyping Hscope Hreceiver_type
        Hreceiver_value Hbase Hfind Hargs source_mode source Hsource_mode
        Hsource) as [caller_mode [Hcaller_mode Hcaller_source]].
      exists caller_mode. split; [exact Hcaller_mode|].
      unfold private_nested_target_call_head.
      destruct caller_authority; simpl; exact Hcaller_source.
    - eapply Hentry_target_tail_phase_safe; eauto. }
  have Hcaller_snapshot_aligned :
      frozen_caller_snapshots_aligned snapshots stack :=
    proj1 (proj2 (proj1 (proj1 Hordinary_fresh))).
  have Hresume_completed_phase :
      frozen_completed_colors_resume_phase_safe Z
        (executing_authority_color_set CT h caller incoming)
        policies.(suspended_frame_resume_witnesses).
  { eapply target_phase_safe_transfers_to_resume_witnesses;
      eauto using Htarget_support, Htarget_phase_safe. }
  have Hresume_active_phase :
      frozen_completed_colors_resume_phase_safe Z
        (independent_active_authority_colors CT h caller)
        policies.(suspended_frame_resume_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Hresume_completed_phase; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Htarget_active_phase :
      frozen_completed_colors_resume_phase_safe Z
        (independent_active_authority_colors CT h caller)
        policies.(suspended_frame_target_witnesses).
  { intros snapshot source_mode source Hsnapshot Hmode Hcolor Hroot.
    eapply Htarget_phase_safe; eauto.
    eapply independent_active_authority_colors_in_executing. exact Hcolor. }
  have Hentry_target_tail_cross_phase :
      private_target_exposures_support_resume_phase Z
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_target_witnesses))
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_resume_witnesses)).
  { eapply
      private_target_exposures_support_resume_phase_after_safe_call_entry;
      eauto.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Htarget_stack)))))). }
  have Hentry_target_tail_nested_phase :
      frozen_target_snapshots_nested_resume_phase_safe CT h Z
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_target_witnesses)).
  { eapply (proj2 (frozen_target_nested_phase_safe_iff_legacy CT h Z _)).
    eapply
      frozen_caller_snapshots_nested_resume_phase_safe_after_safe_call_entry;
      eauto.
    - exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 Htarget_stack)))))).
    - eapply (proj1 (frozen_target_nested_phase_safe_iff_legacy CT h Z _)).
      exact Htarget_nested_phase. }
  have Hentry_target_head_cross_phase :
      frozen_completed_colors_resume_phase_safe Z
        (private_nested_target_call_head CT h caller callee callee_incoming
          snapshots policies.(suspended_frame_target_witnesses))
          .(frozen_snapshot_current_resume_exposure)
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_resume_witnesses)).
  { unfold private_nested_target_call_head.
    eapply (private_nested_target_resume_exposure_phase_safe_at_call_entry
      CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
      snapshots policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses)); eauto. }
  have Hentry_target_head_nested_phase :
      frozen_snapshot_resume_activated
        (private_nested_target_call_head CT h caller callee callee_incoming
          snapshots policies.(suspended_frame_target_witnesses)) ->
      frozen_target_colors_resume_phase_safe CT h Z
        (private_nested_target_call_head CT h caller callee callee_incoming
          snapshots policies.(suspended_frame_target_witnesses))
          .(frozen_snapshot_current_resume_exposure)
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_target_witnesses)).
  { intros Hactivation. unfold frozen_target_colors_resume_phase_safe.
    unfold frozen_snapshot_resume_activated in Hactivation.
    unfold private_nested_target_call_head in Hactivation |- *.
    unfold private_nested_frozen_call_head, nested_frozen_call_head in
      Hactivation. simpl in Hactivation.
    eapply (private_nested_target_target_exposure_phase_safe_at_call_entry
      CT P Z cutoff caller_authority sGamma mt rGamma h stack incoming
      snapshots policies.(suspended_frame_target_witnesses)); eauto.
    exact (proj1 (proj2 (proj2 (proj2 (proj2
      (proj2 Htarget_stack)))))). }
  have Hentry_target_cross_phase :
      private_target_exposures_support_resume_phase Z
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming snapshots
          policies.(suspended_frame_target_witnesses)) ::
         advance_frozen_caller_snapshots CT h callee
           policies.(suspended_frame_target_witnesses))
        (Some (private_nested_frozen_call_head CT h caller callee
          callee_incoming snapshots
          policies.(suspended_frame_resume_witnesses)) ::
         advance_frozen_caller_snapshots CT h callee
           policies.(suspended_frame_resume_witnesses)).
  { simpl. split; assumption. }
  have Hentry_target_nested_phase :
      frozen_target_snapshots_nested_resume_phase_safe CT h Z
        (Some (private_nested_target_call_head CT h caller callee
          callee_incoming snapshots
          policies.(suspended_frame_target_witnesses)) ::
         advance_frozen_caller_snapshots CT h callee
           policies.(suspended_frame_target_witnesses)).
  { simpl. split; assumption. }
  have Hentry_target_before : frozen_caller_snapshots_before_boundaries
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_target_witnesses))
      (boundary :: stack).
  { constructor.
    - eapply private_nested_target_call_head_before_boundary; eauto.
    - eapply advance_frozen_caller_snapshots_before_boundaries.
      exact Htarget_before. }
  have Hentry_target_support : private_target_supports_resume_witnesses
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_target_witnesses))
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_resume_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_resume_witnesses)).
  { simpl. unfold private_nested_target_call_head.
    destruct (private_nested_frozen_call_heads_support CT h caller
      callee callee_incoming snapshots
      policies.(suspended_frame_target_witnesses)
      policies.(suspended_frame_resume_witnesses)) as
      (Hhead_phase & Hhead_roots & Hhead_entry & Hhead_exposure).
    split; [exact Hhead_phase|]. split; [exact Hhead_roots|].
    split; [exact Hhead_entry|]. split; [exact Hhead_exposure|].
    eapply private_target_supports_resume_witnesses_after_advance.
    exact Htarget_support. }
  have Hentry_target_tail_history :
      private_target_history_supports_resume_phase Z
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_target_witnesses))
        (advance_frozen_caller_snapshots CT h callee
          policies.(suspended_frame_resume_witnesses)).
  { eapply private_target_history_supports_resume_phase_after_advance.
    - exact Htarget_history.
    - intros resume Hin_resume Hsafe.
      eapply (frozen_snapshot_resume_exposure_avoids_after_safe_call_entry CT
        Z caller_authority sGamma mt rGamma h incoming resume x method y args
        sGamma' vals ly cy runtime_mdef Ty); eauto.
      + exact ((proj1 Hwitness_exposure) resume Hin_resume).
      + exact ((proj1 (proj2 Hwitness_exposure)) resume Hin_resume). }
  have Hentry_target_history : private_target_history_supports_resume_phase Z
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_target_witnesses))
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_resume_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_resume_witnesses)).
  { simpl. split.
    - intros source_mode source Hmode Hphase Hroot. left.
      exists source_mode. split; [exact Hmode|exact Hphase].
    - exact Hentry_target_tail_history. }
  have Hentry_target_temporal : private_target_witness_temporal_state CT h Z
      cutoff callee (boundary :: stack)
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_target_witnesses)).
  { constructor.
    - unfold boundary. simpl.
      exact (proj1 (proj2 (proj2 (proj2 (proj2
        (proj2 (proj2 Hcaller_main))))))).
    - eapply advance_snapshot_boundaries_after_cutoff.
      exact Htarget_temporal. }
  have Hentry_target_state : private_target_witness_state CT h Z cutoff callee
      callee_incoming
      (None :: advance_frozen_caller_snapshots CT h callee snapshots)
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_target_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_target_witnesses))
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming snapshots policies.(suspended_frame_resume_witnesses)) ::
       advance_frozen_caller_snapshots CT h callee
         policies.(suspended_frame_resume_witnesses))
      (boundary :: stack).
  { unfold private_target_witness_state.
    split; [exact Hentry_target_cover_full|].
    split; [exact Hentry_target_stack|].
    split; [exact Hentry_target_phase_safe|].
    split; [exact Hentry_target_cross_phase|].
    split; [exact Hentry_target_nested_phase|].
    split; [exact Hentry_target_before|].
    split; [exact Hentry_target_support|].
    split; [exact Hentry_target_history|exact Hentry_target_temporal]. }
  exists origins, destination_type. split; [exact Hdestination|].
  change (private_advancing_policy_statement_state CT P Z cutoff callee
    (boundary :: stack) callee_incoming
    (None :: advance_frozen_caller_snapshots CT h callee snapshots)
    (enter_private_frame_join_policies_advanced CT h callee
      (Some (private_nested_target_call_head CT h caller callee
        callee_incoming snapshots
        policies.(suspended_frame_target_witnesses)))
      (Some (private_nested_frozen_call_head CT h caller callee
        callee_incoming snapshots
        policies.(suspended_frame_resume_witnesses))) policies) h).
  eapply private_advancing_policy_statement_enter_channel_free_from_parts.
  - exact Hcaller.
  - reflexivity.
  - reflexivity.
  - exact Hordinary_entry.
  - exact Hwitness_entry.
  - exact Hentry_target_state.
  - exact Hcallee_wf.
  - exact Hcallee_sound.
Qed.

(** Advancing-policy null-call case.  The recursive body returns evolved
    resume witnesses; the pop consumes the evolved head and retains its tail
    instead of pretending that call entry is an exact policy inverse. *)
Lemma private_advancing_policy_successful_null_call_case :
  forall P CT rGamma h destination method receiver args vals
    receiver_location runtime_class runtime_mdef body_renv h'
    caller_senv caller_scope caller_final_senv caller_authority stack Z cutoff
    caller_incoming caller_snapshots caller_policies,
    runtime_getVal rGamma receiver = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    eval_stmt CT (mkr_env (Iot receiver_location :: vals)) h
      (mbody_stmt (mbody runtime_mdef)) OK body_renv h' ->
    runtime_getVal body_renv (mreturn (mbody runtime_mdef)) = Some Null_a ->
    (forall entry_senv entry_scope final_senv callee_authority callee_stack
      incoming snapshots policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv
          (mkr_env (Iot receiver_location :: vals))) callee_stack incoming
        h ->
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv
          (mkr_env (Iot receiver_location :: vals))) callee_stack incoming
        snapshots policies h ->
      stmt_typing CT entry_senv entry_scope
        (mbody_stmt (mbody runtime_mdef)) final_senv ->
      readonly_state_method_scope entry_scope ->
      exists final_snapshots,
        private_advancing_policy_statement_result CT P Z cutoff callee_authority
          final_senv body_renv callee_stack incoming snapshots
          final_snapshots policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame callee_authority entry_senv
            (mkr_env (Iot receiver_location :: vals))) incoming h'
          (mk_watched_frame callee_authority final_senv body_renv) incoming) ->
    principled_phased_authority_live_history_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming h ->
    private_advancing_policy_statement_state CT P Z cutoff
      (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming caller_snapshots caller_policies h ->
    stmt_typing CT caller_senv caller_scope
      (SCall destination method receiver args) caller_final_senv ->
    readonly_state_method_scope caller_scope ->
    exists final_snapshots,
      private_advancing_policy_statement_result CT P Z cutoff caller_authority
        caller_final_senv (update_r_env_value rGamma destination Null_a) stack
        caller_incoming caller_snapshots final_snapshots
        caller_policies h' /\
      executing_authority_old_colors_reflected_or_outside CT Z h
        (mk_watched_frame caller_authority caller_senv rGamma) caller_incoming
        h' (mk_watched_frame caller_authority caller_final_senv
          (update_r_env_value rGamma destination Null_a)) caller_incoming.
Proof.
  intros P CT rGamma h destination method receiver args vals
    receiver_location runtime_class runtime_mdef body_renv h' caller_senv
    caller_scope caller_final_senv caller_authority stack Z cutoff
    caller_incoming caller_snapshots caller_policies Hreceiver_value Hbase
    Hfind Hargs Heval Hreturn IH Hpotential Hprivate Htyping Hscope.
  have Hcaller_main := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame caller_authority caller_senv rGamma) stack
    caller_incoming caller_snapshots caller_policies h (proj1 Hprivate).
  have Hcaller_wf : wf_r_config CT caller_senv rGamma h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_main))))).
  destruct (safe_typed_call_static_result CT caller_senv caller_scope rGamma h
    destination method receiver args caller_final_senv receiver_location
    runtime_class runtime_mdef Hcaller_wf Htyping Hscope Hreceiver_value Hbase
    Hfind) as
    [destination_type [receiver_type [static_mdef Hstatic]]].
  destruct Hstatic as
    [Hfinal_senv [Hdestination_receiver [Hdestination_type
      [Hreceiver_type [Hfind_static
        [Hsignature_refinement [Hresult_sub Hreceiver_sub]]]]]]].
  subst caller_final_senv.
  destruct (typed_call_target CT caller_senv caller_scope rGamma h destination
    method receiver args caller_senv vals receiver_location runtime_class
    runtime_mdef Hcaller_wf Htyping Hreceiver_value Hbase Hfind Hargs) as
    (declaring_class & declaring_def & body_end & Hruntime_sub & Hdeclaring &
      Hmember & Hmethod_wf & Hbody_typing & Hcallee_entry_wf).
  unfold wf_method in Hmethod_wf. simpl in Hmethod_wf.
  destruct Hmethod_wf as
    (_ & method_end & body_return_type & Hmethod_body_typing & Hreturn_dom &
      Hreturn_type & Hbody_sub & Hoverriding).
  have Hcallee_scope := safe_typed_call_target_method_safe CT caller_senv
    caller_scope rGamma h destination method receiver args caller_senv
    receiver_location runtime_class runtime_mdef Hcaller_wf Htyping Hscope
    Hreceiver_value Hbase Hfind.
  have Hcaller_fresh := proj1 (proj1 (proj1 Hprivate)).
  have Hcaller_witness_fresh :=
    private_advancing_policy_statement_witness_state_is_private_fresh CT P Z
      cutoff (mk_watched_frame caller_authority caller_senv rGamma) stack
      caller_incoming caller_snapshots caller_policies h Hprivate.
  destruct (private_fresh_frozen_statement_enter_call_untracked CT P Z cutoff
    caller_authority caller_senv caller_scope rGamma h stack caller_incoming
    caller_snapshots destination method receiver args caller_senv vals
    receiver_location runtime_class runtime_mdef receiver_type Hcaller_fresh
    Htyping Hscope Hreceiver_type Hreceiver_value Hbase Hfind Hargs) as
    [origins [entry_destination_type [Hentry_destination Hentry_fresh]]].
  assert (entry_destination_type = destination_type) by congruence.
  subst entry_destination_type.
  destruct (private_fresh_frozen_statement_enter_call_untracked CT P Z cutoff
    caller_authority caller_senv caller_scope rGamma h stack caller_incoming
    caller_policies.(suspended_frame_resume_witnesses) destination method
    receiver args caller_senv vals receiver_location runtime_class
    runtime_mdef receiver_type Hcaller_witness_fresh Htyping Hscope
    Hreceiver_type Hreceiver_value Hbase Hfind Hargs) as
    [witness_origins
      [witness_destination_type
        [Hwitness_destination Hentry_witness_fresh]]].
  assert (witness_destination_type = destination_type) by congruence.
  subst witness_destination_type.
  assert (witness_origins = origins) by apply proof_irrelevance.
  subst witness_origins.
  set (caller := mk_watched_frame caller_authority caller_senv rGamma).
  set (callee := mk_watched_frame
    (call_authority caller_authority (sqtype receiver_type))
    (mreceiver (msignature runtime_mdef) :: mparams (msignature runtime_mdef))
    (mkr_env (Iot receiver_location :: vals))).
  set (boundary := mk_watched_call_boundary caller
    (mreceiver (msignature runtime_mdef) :: mparams (msignature runtime_mdef))
    (mkr_env (Iot receiver_location :: vals)) (sqtype receiver_type)
    (mreturn (mbody runtime_mdef)) (sqtype destination_type)
    (sqtype (mret (msignature runtime_mdef))) (dom h) origins).
  set (callee_incoming := executing_authority_color_set CT h caller
    caller_incoming).
  set (entry_snapshots := None :: advance_frozen_caller_snapshots CT h callee
    caller_snapshots).
  set (entry_policies := enter_private_frame_join_policies_advanced CT h callee
    (Some (private_nested_target_call_head CT h caller callee callee_incoming
      caller_snapshots
      caller_policies.(suspended_frame_target_witnesses)))
    None
    caller_policies).
  have Hentry_main := proj1 (proj1 (proj1 Hentry_fresh)).
  have Hcallee_wf : wf_r_config CT callee.(frame_senv) callee.(frame_renv) h :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hentry_main))))).
  have Hcallee_sound : authority_context_sound h callee.(frame_renv)
      callee.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hentry_main)))))).
  have Hentry_policy : private_advancing_policy_statement_state CT P Z cutoff callee
      (boundary :: stack) callee_incoming entry_snapshots entry_policies h.
  { unfold caller, callee, boundary, callee_incoming, entry_snapshots,
      entry_policies in *.
    eapply private_advancing_policy_statement_enter_untracked_safe_call;
      eauto. }
  have Hbody := IH callee.(frame_senv) (mscope (msignature runtime_mdef))
    method_end callee.(frame_authority) (boundary :: stack) callee_incoming
    entry_snapshots entry_policies.
  unfold callee, boundary in Hbody.
  destruct (Hbody Hentry_main Hentry_policy Hmethod_body_typing Hcallee_scope)
    as [body_snapshots [Hbody_result Hbody_reflection]].
  destruct Hbody_result as
    [body_policies
      (Hbody_policy_metadata & Hbody_witness_growth & Hbody_fixed &
       Hbody_cover & Hbody_phase & Hbody_roots & Hbody_nested &
       Hbody_completed & Hbody_stack_safe & Hbody_before & Hbody_temporal &
       Hbody_target_state)].
  destruct Hbody_fixed as
    [Hbody_principled [Hpolicies_aligned
      [Hpolicies_valid Hbody_separated]]].
  destruct Hbody_principled as [Hbody_statement Hbody_disjoint].
  destruct Hbody_statement as
    [Hbody_potential [Hbody_fresh [Hbody_metadata Hbody_exposure]]].
  have Hbody_main := proj1 (proj1 (proj1 Hbody_fresh)).
  destruct (frozen_caller_snapshot_list_metadata_eq_head_none body_snapshots
    (advance_frozen_caller_snapshots CT h callee caller_snapshots)
    Hbody_metadata) as [body_tail [Hbody_snapshots Htail_metadata]].
  subst body_snapshots.
  have Hbody_target_witness_metadata :=
    proj1 (proj2 (proj2 Hbody_policy_metadata)).
  destruct (frozen_target_snapshot_list_metadata_le_head_some
    body_policies.(suspended_frame_target_witnesses)
    (private_nested_target_call_head CT h caller callee callee_incoming
      caller_snapshots
      caller_policies.(suspended_frame_target_witnesses))
    (advance_frozen_caller_snapshots CT h callee
      caller_policies.(suspended_frame_target_witnesses))
    Hbody_target_witness_metadata) as
    [body_target_witness [body_target_witness_tail
      [Hbody_target_witnesses
        [Hbody_target_head_metadata Hbody_target_witness_tail_metadata]]]].
  have Hbody_witness_metadata :=
    proj2 (proj2 (proj2 Hbody_policy_metadata)).
  destruct (frozen_caller_snapshot_list_metadata_eq_head_none
    body_policies.(suspended_frame_resume_witnesses)
    (advance_frozen_caller_snapshots CT h callee
      caller_policies.(suspended_frame_resume_witnesses))
    Hbody_witness_metadata) as
    [body_witness_tail
      [Hbody_witnesses Hbody_witness_tail_metadata]].
  set (caller_leave_policies := mk_private_frame_join_policies
    caller_policies.(active_frame_join_targets)
    caller_policies.(suspended_frame_join_targets)
    body_target_witness_tail
    body_witness_tail).
  set (caller_final_policies := activate_private_frame_targets_on_pop CT h'
    (mk_watched_frame caller_authority caller_senv
      (update_r_env_value rGamma destination Null_a))
    caller_incoming
    caller_leave_policies).
  have Hleave_policies :
      leave_private_frame_join_policies_advanced body_policies =
      Some caller_leave_policies.
  { unfold leave_private_frame_join_policies_advanced,
      caller_leave_policies.
    rewrite (proj1 (proj2 Hbody_policy_metadata)).
    unfold entry_policies, enter_private_frame_join_policies_advanced.
    simpl. rewrite Hbody_target_witnesses. rewrite Hbody_witnesses.
    reflexivity. }
  have Hcaller_final_policy_metadata :
      private_frame_join_policies_metadata_eq caller_final_policies
        caller_policies.
  { unfold private_frame_join_policies_metadata_eq,
      caller_final_policies, activate_private_frame_targets_on_pop,
      caller_leave_policies. simpl.
    split; [reflexivity|]. split; [reflexivity|]. split.
    - eapply frozen_target_snapshot_list_metadata_le_trans.
      + apply activate_frozen_target_snapshots_metadata_le.
      + eapply frozen_target_snapshot_list_metadata_le_trans.
        * exact Hbody_target_witness_tail_metadata.
        * apply frozen_caller_snapshot_list_metadata_eq_target_le.
          apply advance_frozen_caller_snapshots_metadata_eq.
    - eapply frozen_caller_snapshot_list_metadata_eq_trans.
      + apply advance_frozen_caller_snapshots_metadata_eq.
      + eapply frozen_caller_snapshot_list_metadata_eq_trans.
        * exact Hbody_witness_tail_metadata.
        * apply advance_frozen_caller_snapshots_metadata_eq. }
  set (callee_final := mk_watched_frame callee.(frame_authority) method_end
    body_renv).
  set (caller_post := mk_watched_frame caller_authority caller_senv
    (update_r_env_value rGamma destination Null_a)).
  destruct Hbody_target_state as
    (Hbody_target_cover & Hbody_target_stack_safe &
      Hbody_target_phase_safe_state & Hbody_target_cross_phase_state &
      Hbody_target_nested_phase_state & Hbody_target_before &
      Hbody_target_support & Hbody_target_history & Hbody_target_temporal).
  rewrite Hbody_target_witnesses in Hbody_target_stack_safe.
  have Hbody_target_stack := Hbody_target_stack_safe.
  have Hbody_target_phase_safe : frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h' callee_final callee_incoming)
      (Some body_target_witness :: body_target_witness_tail).
  { rewrite <- Hbody_target_witnesses.
    exact Hbody_target_phase_safe_state. }
  have Hbody_target_cross_phase :
      private_target_exposures_support_resume_phase Z
        (Some body_target_witness :: body_target_witness_tail)
        (None :: body_witness_tail).
  { rewrite <- Hbody_target_witnesses. rewrite <- Hbody_witnesses.
    exact Hbody_target_cross_phase_state. }
  have Hbody_target_head_in :
      List.In (Some body_target_witness)
      (Some body_target_witness :: body_target_witness_tail) by
    (simpl; auto).
  destruct Hbody_target_stack as
    (Hbody_target_covered & Hbody_target_runtime & Hbody_target_dangerous &
      Hbody_target_closed & Hbody_target_roots_in_heap &
      Hbody_target_exposure & Hbody_target_retain &
      Hbody_target_phase_stack).
  have Hbody_frames := proj1 (proj2 (proj2 (proj2 (proj2 Hbody_main)))).
  have Hbody_sounds := proj1 (proj2 (proj2 (proj2 (proj2
    (proj2 Hbody_main))))).
  have Hcaller_current_wf : wf_r_config CT caller_senv rGamma h'.
  { exact (Forall_inv (proj2 Hbody_frames)). }
  have Hcaller_current_sound : authority_context_sound h' rGamma
      caller_authority.
  { exact (Forall_inv (proj2 Hbody_sounds)). }
  have Hcaller_sound : authority_context_sound h rGamma caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hcaller_main)))))).
  have Hcaller_incoming_runtime : authority_colors_runtime_mutable h
      caller_incoming := proj1 (proj2 (proj2 Hcaller_main)).
  have Hcallee_to_caller : forall mode location,
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' callee_final callee_incoming)
        (mode, location) ->
      location < dom h ->
      (exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h caller caller_incoming)
          (caller_mode, location)) \/
      ~ In Loc Z location.
  { intros mode location Hmode Hcolor Hold.
    unfold caller, callee, callee_final, callee_incoming in *.
    eapply safe_call_body_old_colors_reflect_to_caller_or_outside; eauto. }
  have Hcallee_final_wf : wf_r_config CT callee_final.(frame_senv)
      callee_final.(frame_renv) h' :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hbody_main))))).
  have Hcallee_final_sound : authority_context_sound h'
      callee_final.(frame_renv) callee_final.(frame_authority) :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2
      (proj2 Hbody_main)))))).
  have Hcallee_incoming_runtime_final : authority_colors_runtime_mutable h'
      callee_incoming := proj1 (proj2 (proj2 Hbody_main)).
  have Hcallee_completed_runtime : authority_colors_runtime_mutable h'
      (executing_authority_color_set CT h' callee_final callee_incoming) :=
    executing_authority_colors_runtime_mutable CT h' callee_final
      callee_incoming Hcallee_final_wf Hcallee_final_sound
      Hcallee_incoming_runtime_final.
  have Hcaller_length : length caller_senv = length rGamma.(vars) :=
    proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_wf)))).
  have Htarget_join : forall source_mode left right,
      authority_mode_dangerous source_mode ->
      target_phase_pop_color_class CT h' Z callee_final callee_incoming
        body_target_witness (source_mode, left) ->
      typed_root RDM caller_post.(frame_senv) caller_post.(frame_renv) left ->
      typed_root RDM caller_post.(frame_senv) caller_post.(frame_renv) right ->
      target_phase_pop_color_class CT h' Z callee_final callee_incoming
        body_target_witness (FlowProspective, right).
  { intros source_mode left right Hsource_mode Hclass Hleft Hright.
    eapply target_phase_pop_join_preserves_class with (caller := caller_post).
    - intros phase_source_mode source Hphase_source_mode Hcompleted Hroot.
      eapply Hbody_target_phase_safe.
      + exact Hbody_target_head_in.
      + exact Hphase_source_mode.
      + exact Hcompleted.
      + exact Hroot.
    - intros root Hroot.
      have Hold_root : typed_root RDM caller_senv rGamma root.
      { unfold caller_post in Hroot. simpl in Hroot.
        eapply caller_null_post_rdm_root_is_old; eauto. }
      eapply (proj2 (proj1 (proj2 (proj2 (proj2
        Hbody_target_head_metadata))))).
      unfold private_nested_frozen_call_head, nested_frozen_call_head. simpl.
      exact Hold_root.
    - intros phase_mode Hphase_mode Hphase_color.
      have Hold_left : typed_root RDM caller_senv rGamma left.
      { unfold caller_post in Hleft. simpl in Hleft.
        eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hold_right : typed_root RDM caller_senv rGamma right.
      { unfold caller_post in Hright. simpl in Hright.
        eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hold_phase : In authority_flow_state callee_incoming
          (phase_mode, left).
      { admit. }
      have Hcaller_target : In authority_flow_state
          (executing_authority_color_set CT h caller caller_incoming)
          (FlowProspective, right).
      { unfold callee_incoming in Hold_phase. unfold caller in Hold_phase |- *.
        eapply executing_authority_dangerous_frame_join; eauto. }
      apply executing_authority_color_set_contains_incoming.
      exact Hcaller_target.
    - intros Hright_again.
      have Hold_left : typed_root RDM caller_senv rGamma left.
      { unfold caller_post in Hleft. simpl in Hleft.
        eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hold_right : typed_root RDM caller_senv rGamma right.
      { unfold caller_post in Hright_again. simpl in Hright_again.
        eapply caller_null_post_rdm_root_is_old; eauto. }
      have Hleft_runtime_final : r_muttype h' left = Some Mut_r.
      { destruct Hclass as [Hcompleted | [Hexposure _]].
        - eapply Hcallee_completed_runtime. exact Hcompleted.
        - eapply (proj1 Hbody_target_exposure); eauto. }
      have Hleft_dom : left < dom h.
      { destruct Hold_left as [variable [T [Htype [Hvalue _]]]].
        exact (wf_config_value_dom CT caller_senv rGamma h variable left
          Hcaller_wf Hvalue). }
      have Hleft_runtime : r_muttype h left = Some Mut_r.
      { eapply eval_stmt_preserves_r_muttype_backwards; eauto. }
      have Hright_runtime : r_muttype h right = Some Mut_r.
      { destruct (active_rdm_roots_share_runtime_context CT caller_senv rGamma
          h left right Hcaller_wf Hold_left Hold_right) as
          [context [Hleft_context Hright_context]].
        rewrite Hleft_runtime in Hleft_context. injection Hleft_context as <-.
        exact Hright_context. }
      have Hright_root : In Loc
          body_target_witness.(frozen_snapshot_resume_rdm_roots) right.
      { eapply (proj2 (proj1 (proj2 (proj2 (proj2
          Hbody_target_head_metadata))))).
        unfold private_nested_frozen_call_head, nested_frozen_call_head. simpl.
        exact Hold_right. }
      have Hright_dom : right < dom h.
      { destruct Hold_right as [variable [T [Htype [Hvalue _]]]].
        exact (wf_config_value_dom CT caller_senv rGamma h variable right
          Hcaller_wf Hvalue). }
      have Hright_runtime_final : r_muttype h' right = Some Mut_r.
      { eapply eval_stmt_preserves_r_muttype; eauto. }
      eapply (proj2 (proj2 (proj2 (proj2 Hbody_target_exposure)))); eauto.
    - exact Hsource_mode.
    - exact Hclass.
    - exact Hleft.
    - exact Hright. }
  have Hpop : executing_authority_call_pop_safe CT h' Z callee_final
      callee_incoming caller_post caller_incoming.
  { intros mode location Hmode Hcolor.
    eapply target_phase_pop_executing_color_is_completed_or_outside with
      (snapshot := body_target_witness) (caller := caller_post).
    - intros state Hstate. apply executing_authority_color_set_contains_incoming.
      unfold callee_incoming, caller. apply
        executing_authority_color_set_contains_incoming. exact Hstate.
    - intros owned Howned.
      unfold caller_post in Howned. simpl in Howned.
      eapply caller_null_post_owned_is_completed_callee_powered with
        (caller_authority := caller_authority) (caller_senv := caller_senv)
        (caller_renv := rGamma) (caller_h := h)
        (destination := destination) (destination_type := destination_type);
        eauto.
      unfold callee_incoming, caller. reflexivity.
    - eapply (proj1 (proj2 Hbody_target_exposure));
        exact Hbody_target_head_in.
    - exact Htarget_join.
    - exact Hmode.
    - exact Hcolor. }
  have Hwhole_reflection :
      executing_authority_old_colors_reflected_or_outside CT Z h
      caller caller_incoming h' caller_post caller_incoming.
  { intros mode location Hmode Hcolor Hold.
    destruct (Hpop mode location Hmode Hcolor) as
      [[callee_mode [Hcallee_mode Hcallee_color]] | Houtside].
    - eapply Hcallee_to_caller; eauto.
    - right. exact Houtside. }
  have Hbody_witness_fresh : private_fresh_frozen_statement_state CT P Z
      cutoff callee_final (boundary :: stack) callee_incoming
      (None :: body_witness_tail) h'.
  { eapply private_resume_witness_state_is_private_fresh.
    - exact Hbody_main.
    - unfold frozen_caller_snapshots_aligned.
      rewrite <- Hbody_witnesses.
      exact (proj2 (proj2 Hpolicies_aligned)).
    - rewrite <- Hbody_witnesses. exact Hbody_stack_safe.
    - rewrite <- Hbody_witnesses. exact Hbody_before.
    - rewrite <- Hbody_witnesses. exact Hbody_temporal. }
  have Heval_call_raw : eval_stmt CT rGamma h
      (SCall destination method receiver args) OK
      (set_vars rGamma (update destination Null_a rGamma.(vars))) h'.
  { econstructor; eauto. }
  assert (Hupdate : set_vars rGamma
      (update destination Null_a rGamma.(vars)) =
      update_r_env_value rGamma destination Null_a).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Heval_call_raw.
  have Hcaller_post_wf := preservation_pico CT caller_senv caller_scope
    rGamma h (SCall destination method receiver args)
    (update_r_env_value rGamma destination Null_a) h' caller_senv Hcaller_wf
    Htyping Heval_call_raw.
  have Hpost_main : principled_phased_authority_live_history_state CT P Z
      cutoff caller_post stack caller_incoming h'.
  { eapply principled_phased_authority_history_leave_call_null with
      (P := P) (Z := Z) (cutoff := cutoff) (caller := caller)
      (stack := stack) (caller_incoming := caller_incoming) (caller_h := h)
      (callee := callee_final) (boundary := boundary)
      (callee_renv := body_renv) (callee_incoming := callee_incoming)
      (destination := destination).
    - exact Hcaller_main.
    - unfold boundary. reflexivity.
    - unfold callee_final. reflexivity.
    - exact Hbody_main.
    - unfold callee_incoming. reflexivity.
    - exact Hdestination_receiver.
    - exact Hcaller_post_wf.
    - exact Hpop. }
  have Hbody_policy : private_policy_statement_state CT P Z cutoff
      callee_final (boundary :: stack) callee_incoming (None :: body_tail)
      body_policies h'.
  { split.
    - split; assumption.
    - split; [exact Hpolicies_aligned|].
      split; assumption. }
  have Hroots_reflect : forall snapshot mode source,
      List.In (Some snapshot) body_tail ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      exists callee_mode,
        authority_mode_dangerous callee_mode /\
        In authority_flow_state
          (executing_authority_color_set CT h' callee_final callee_incoming)
          (callee_mode, source).
  { intros snapshot mode source Hsnapshot.
    exfalso.
    eapply private_resume_witnesses_cover_snapshots_none with
      (witnesses := body_witness_tail) (snapshots := body_tail)
      (snapshot := snapshot).
    - have Hcover := Hbody_cover.
      rewrite Hbody_witnesses in Hcover. simpl in Hcover.
      exact (proj2 Hcover).
    - exact Hsnapshot. }
  have Hresumed_pop : executing_resumed_authority_call_pop_safe CT h' Z
      callee_final callee_incoming
      caller_leave_policies.(active_frame_join_targets) caller_post
      caller_incoming.
  { eapply executing_authority_call_pop_safe_implies_resumed. exact Hpop. }
  have Hcaller_post_sound : authority_context_sound h'
      (update_r_env_value rGamma destination Null_a) caller_authority :=
    proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 Hpost_main)))))).
  have Hroots_reflect_witness : forall snapshot mode source,
      List.In (Some snapshot) body_witness_tail ->
      authority_mode_dangerous mode ->
      In authority_flow_state
        (executing_authority_color_set CT h' caller_post caller_incoming)
        (mode, source) ->
      In Loc snapshot.(frozen_snapshot_resume_rdm_roots) source ->
      (exists phase_mode,
        authority_mode_dangerous phase_mode /\
        In authority_flow_state snapshot.(frozen_snapshot_phase_incoming)
          (phase_mode, source)) \/
      (exists callee_mode,
          authority_mode_dangerous callee_mode /\
          In authority_flow_state
            (executing_authority_color_set CT h' callee_final callee_incoming)
            (callee_mode, source)) \/
      frozen_snapshot_resume_exposure_avoids Z snapshot.
  { intros snapshot mode source Hsnapshot Hmode Hcolor Hroot.
    have Hclass : target_phase_pop_color_class CT h' Z callee_final
        callee_incoming body_target_witness (mode, source).
    { eapply target_phase_pop_executing_color_has_class with
        (caller := caller_post) (caller_incoming := caller_incoming).
      - intros state Hstate.
        apply executing_authority_color_set_contains_incoming.
        unfold callee_incoming, caller.
        apply executing_authority_color_set_contains_incoming. exact Hstate.
      - intros owned Howned.
        unfold caller_post in Howned. simpl in Howned.
        eapply caller_null_post_owned_is_completed_callee_powered with
          (caller_authority := caller_authority)
          (caller_senv := caller_senv) (caller_renv := rGamma)
          (caller_h := h) (destination := destination)
          (destination_type := destination_type); eauto.
        unfold callee_incoming, caller. reflexivity.
      - eapply (proj1 (proj2 Hbody_target_exposure));
          exact Hbody_target_head_in.
      - exact Htarget_join.
      - exact Hmode.
      - exact Hcolor. }
    destruct (target_phase_pop_head_class_at_older_root CT h' Z
      callee_final callee_incoming body_target_witness
      body_target_witness_tail None body_witness_tail snapshot mode source
      Hbody_target_cross_phase Hsnapshot Hmode Hroot Hclass) as
      [Hcompleted | [Hphase | Hsafe]].
    - right. left. exact Hcompleted.
    - left. exact Hphase.
    - right. right. exact Hsafe. }
  have Hpost_witness_structural : private_frozen_snapshot_structural_state CT
      h' caller_post
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      stack.
  { destruct (private_frozen_statement_advance_tail_structural_state CT P Z
      cutoff callee_final boundary stack callee_incoming None
      body_witness_tail h' caller_post (proj1 Hbody_witness_fresh)
      Hcaller_post_wf) as [Hstructural _].
    exact Hstructural. }
  have Hpost_witness_partitions :=
    private_fresh_return_partitions_after_null_pop CT P Z cutoff callee_final
      boundary stack callee_incoming None body_witness_tail h'
      caller_authority caller_senv rGamma destination destination_type
      Hbody_witness_fresh (ltac:(unfold boundary, caller; reflexivity))
      Hdestination_receiver Hcaller_current_wf Hcaller_current_sound
      Hdestination_type.
  destruct Hpost_witness_partitions as
    [Hpost_witness_components
      [Hpost_witness_prospective Hpost_witness_after]].
  have Hpost_witness_return_safety : private_frozen_snapshot_return_safety CT
      h' Z caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail).
  { eapply
      private_frozen_snapshot_return_safety_after_untracked_return_phase_parts
      with (callee := callee_final) (boundary := boundary)
        (incoming := callee_incoming) (head_slot := None); eauto. }
  have Hpost_witness_fresh : private_fresh_frozen_statement_state CT P Z
      cutoff caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) h'.
  { unfold caller_post, caller, callee_final in *.
    eapply private_fresh_frozen_statement_after_null_return_parts; eauto. }
  have Hpost_leave_policy : private_policy_statement_state CT P Z cutoff
      caller_post
      stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_tail)
      caller_leave_policies h'.
  { unfold caller, caller_post, callee_final in *.
    eapply private_policy_statement_after_untracked_null_pop with
      (active := mk_watched_frame
        (call_authority caller_authority (sqtype receiver_type)) method_end
        body_renv) (boundary := boundary) (destination_type := destination_type)
      (policies := body_policies); eauto. }
  have Hpost_policy : private_policy_statement_state CT P Z cutoff caller_post
      stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_tail)
      caller_final_policies h'.
  { destruct Hpost_leave_policy as
      [Hprincipled [Haligned [Hvalid Hseparated]]].
    split; [exact Hprincipled|]. split.
    - unfold private_frame_join_policies_aligned in *.
      unfold caller_final_policies, activate_private_frame_targets_on_pop,
        caller_leave_policies in *. simpl in *.
      destruct Haligned as [Hjoin [Htarget Hresume]].
      rewrite !length_map. repeat split; assumption.
    - split.
      + unfold private_frame_join_policies_valid in *.
        unfold caller_final_policies, activate_private_frame_targets_on_pop,
          caller_leave_policies in *. simpl in *. exact Hvalid.
      + unfold caller_final_policies, activate_private_frame_targets_on_pop,
          caller_leave_policies in *. simpl in *. exact Hseparated. }
  have Hentry_exposure :=
    frozen_snapshot_list_resume_exposure_reflected_after_safe_call_entry CT P
      Z cutoff caller_authority caller_senv caller_scope rGamma h stack
      caller_incoming caller_snapshots destination method receiver args
      caller_senv vals receiver_location runtime_class runtime_mdef
      receiver_type Hcaller_fresh Htyping Hscope Hreceiver_type
      Hreceiver_value Hbase Hfind Hargs.
  destruct Hpost_policy as
    [Hpost_principled [Hpost_aligned_policy
      [Hpost_valid_policy Hpost_separated_policy]]].
  destruct Hpost_principled as [Hpost_fresh Hpost_disjoint].
  have Hpost_fresh_copy := Hpost_fresh.
  destruct Hpost_fresh_copy as
    [Hpost_private [Hpost_components [Hpost_prospective Hpost_after]]].
  have Hpost_aligned := proj1 (proj2 (proj1 Hpost_private)).
  have Hreturn_exposure :=
    frozen_snapshot_list_resume_exposure_reflected_after_return_parts CT P Z
      cutoff callee_final boundary stack callee_incoming None body_tail h'
      caller_post Hbody_fresh Hpost_aligned Hpost_prospective Hpost_after
      (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
        (proj2 Hpost_main))))))))
      Hcaller_post_wf Hcaller_post_sound.
  have Hfinal_metadata := returned_untracked_tail_metadata_eq_initial CT h h'
    callee caller_post caller_snapshots body_tail Hbody_metadata.
  have Hfinal_exposure := returned_untracked_tail_exposure_reflected_initial
    CT h h' Z callee caller_post caller_snapshots body_tail Hreturn_exposure
    Hbody_exposure Hentry_exposure.
  have Hbody_witness_growth_shape := Hbody_witness_growth.
  rewrite Hbody_witnesses in Hbody_witness_growth_shape.
  unfold entry_policies, enter_private_frame_join_policies_advanced in
    Hbody_witness_growth_shape. simpl in Hbody_witness_growth_shape.
  have Hfinal_witness_growth :
      frozen_caller_snapshot_list_phase_images_grow
        (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
        caller_policies.(suspended_frame_resume_witnesses).
  { eapply returned_policy_tail_phase_images_grow_initial with
      (entry := callee) (entry_head := None) (final_head := None).
    exact Hbody_witness_growth_shape. }
  have Hbody_cover_shape := Hbody_cover.
  rewrite Hbody_witnesses in Hbody_cover_shape.
  have Hfinal_witness_cover : private_resume_witnesses_cover_snapshots Z
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      (advance_frozen_caller_snapshots CT h' caller_post body_tail).
  { eapply private_resume_witnesses_cover_snapshots_after_pop_advance.
    exact Hbody_cover_shape. }
  have Hfinal_witness_stack_safe : private_resume_witness_stack_safe CT h' Z
      caller_post caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) :=
    private_fresh_frozen_statement_state_has_resume_witness_stack_safe CT P Z
      cutoff caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) h'
      Hpost_witness_fresh.
  destruct (private_resume_witness_relations_from_stack_safe CT h' Z
    caller_post caller_incoming
    (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
    (advance_frozen_caller_snapshots CT h' caller_post body_tail)
    Hfinal_witness_cover Hfinal_witness_stack_safe) as
    (Hfinal_witness_phase & Hfinal_witness_roots & Hfinal_witness_nested &
      Hfinal_witness_completed).
  have Hfinal_witness_before : frozen_caller_snapshots_before_boundaries
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      stack := proj1 (proj2 (proj2 (proj1 Hpost_witness_fresh))).
  have Hfinal_witness_temporal : private_resume_witness_temporal_state CT h' Z
      cutoff caller_post stack
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) :=
    private_fresh_frozen_statement_state_has_resume_temporal_state CT P Z
      cutoff caller_post stack caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail) h'
      Hpost_witness_fresh.
  have Hbody_target_cover_shape := Hbody_target_cover.
  rewrite Hbody_target_witnesses in Hbody_target_cover_shape.
  have Hfinal_target_cover : private_resume_witnesses_cover_snapshots Z
      (activate_frozen_target_snapshots CT h' caller_post
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        body_target_witness_tail)
      (advance_frozen_caller_snapshots CT h' caller_post body_tail).
  { eapply private_resume_witnesses_cover_snapshots_after_pop_activate.
    exact Hbody_target_cover_shape. }
  have Hbody_target_before_shape := Hbody_target_before.
  rewrite Hbody_target_witnesses in Hbody_target_before_shape.
  simpl in Hbody_target_before_shape.
  have Hfinal_target_before : frozen_caller_snapshots_before_boundaries
      (activate_frozen_target_snapshots CT h' caller_post
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        body_target_witness_tail) stack.
  { eapply activate_frozen_target_snapshots_before_boundaries.
    inversion Hbody_target_before_shape; subst. assumption. }
  have Hbody_target_support_shape := Hbody_target_support.
  rewrite Hbody_target_witnesses in Hbody_target_support_shape.
  rewrite Hbody_witnesses in Hbody_target_support_shape.
  simpl in Hbody_target_support_shape.
  have Hfinal_target_support : private_target_supports_resume_witnesses
      (activate_frozen_target_snapshots CT h' caller_post
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        body_target_witness_tail)
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail).
  { eapply private_target_supports_resume_witnesses_after_target_activation.
    exact Hbody_target_support_shape. }
  have Hbody_target_history_shape := Hbody_target_history.
  rewrite Hbody_target_witnesses in Hbody_target_history_shape.
  rewrite Hbody_witnesses in Hbody_target_history_shape.
  simpl in Hbody_target_history_shape.
  have Hbody_resume_phase_safe : frozen_completed_colors_resume_phase_safe Z
      (executing_authority_color_set CT h' callee_final callee_incoming)
      (None :: body_witness_tail).
  { have Hsafe := target_phase_safe_transfers_to_resume_witnesses Z
      (executing_authority_color_set CT h' callee_final callee_incoming)
      body_policies.(suspended_frame_target_witnesses)
      body_policies.(suspended_frame_resume_witnesses)
      Hbody_target_support Hbody_target_history Hbody_target_phase_safe_state.
    rewrite Hbody_witnesses in Hsafe. exact Hsafe. }
  have Hreturn_witness_exposure :=
    frozen_snapshot_list_resume_exposure_reflected_after_return_parts CT P Z
      cutoff callee_final boundary stack callee_incoming None
      body_witness_tail h' caller_post Hbody_witness_fresh
      (proj1 Hpost_witness_structural) Hpost_witness_prospective
      Hpost_witness_after
      (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2
        (proj2 Hpost_main))))))))
      Hcaller_post_wf Hcaller_post_sound.
  have Hlift_body_witness_safe : forall resume,
      List.In (Some resume) body_witness_tail ->
      frozen_snapshot_resume_exposure_avoids Z resume ->
      frozen_snapshot_resume_exposure_avoids Z
        (advance_frozen_caller_snapshot CT h' caller_post resume).
  { intros resume Hresume Hsafe.
    eapply advance_resume_exposure_avoids_from_list_reflection; eauto. }
  have Hactual_final_witness_phase_safe :
      frozen_completed_colors_resume_phase_safe Z
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail).
  { intros final_resume source_mode source Hfinal Hmode Hcolor Hroot.
    unfold advance_frozen_caller_snapshots in Hfinal.
    apply in_map_iff in Hfinal.
    destruct Hfinal as [old_slot [Heq Hold]].
    destruct old_slot as [old_resume|]; simpl in Heq; [|discriminate].
    injection Heq as <-. simpl in *.
    destruct (Hroots_reflect_witness old_resume source_mode source Hold Hmode
      (proj1 Hcolor) Hroot) as [Hphase | [Hcompleted | Hsafe]].
    - left. exact Hphase.
    - destruct Hcompleted as [callee_mode [Hcallee_mode Hcallee_color]].
      have Hcompleted_result := Hbody_resume_phase_safe old_resume
        callee_mode source (ltac:(simpl; right; exact Hold))
        Hcallee_mode Hcallee_color Hroot.
      simpl in Hcompleted_result. destruct Hcompleted_result as
        [Hphase | Hsafe].
      + left. exact Hphase.
      + right. eapply Hlift_body_witness_safe; eauto.
    - right. eapply Hlift_body_witness_safe; eauto. }
  have Hfinal_target_history : private_target_history_supports_resume_phase Z
      (activate_frozen_target_snapshots CT h' caller_post
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        body_target_witness_tail)
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail).
  { eapply private_target_history_supports_resume_phase_after_target_activation.
    - exact Hbody_target_history_shape.
    - exact Hlift_body_witness_safe.
    - exact Hactual_final_witness_phase_safe. }
  have Hbody_target_temporal_shape := Hbody_target_temporal.
  rewrite Hbody_target_witnesses in Hbody_target_temporal_shape.
  have Hbody_target_after_tail : frozen_snapshot_boundaries_after_cutoff cutoff
      body_target_witness_tail stack.
  { inversion Hbody_target_temporal_shape; subst. assumption. }
  have Hfinal_target_temporal : private_target_witness_temporal_state CT h' Z
      cutoff caller_post stack
      (activate_frozen_target_snapshots CT h' caller_post
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        body_target_witness_tail).
  { eapply activate_target_snapshot_boundaries_after_cutoff.
    exact Hbody_target_after_tail. }
  have Hbody_target_tail_structural :
      private_target_witness_stack_structural CT h' callee_final
        body_target_witness_tail.
  { eapply private_target_witness_stack_structural_tail with
      (head := Some body_target_witness).
    unfold private_target_witness_stack_structural.
    exact (conj Hbody_target_covered (conj Hbody_target_runtime
      (conj Hbody_target_dangerous (conj Hbody_target_closed
        (conj Hbody_target_roots_in_heap (conj Hbody_target_exposure
          (conj Hbody_target_retain Hbody_target_phase_stack))))))). }
  have Hfinal_target_structural : private_target_witness_stack_structural CT
      h' caller_post
      (activate_frozen_target_snapshots CT h' caller_post
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        body_target_witness_tail).
  { eapply private_target_witness_stack_structural_after_activation
      with (old_active := callee_final); eauto.
    - intros mode location [Hcolor Hmode].
      eapply (executing_authority_colors_runtime_mutable CT h' caller_post
        caller_incoming Hcaller_post_wf Hcaller_post_sound
        (proj1 (proj2 (proj2 Hpost_main)))); exact Hcolor.
    - intros mode location [_ Hmode]. simpl in Hmode. exact Hmode. }
  (* Temporary proof hole used only to expose downstream return obligations.
     It must be discharged before the final assumption audit. *)
  have Hfinal_target_state : private_target_witness_state CT h' Z cutoff caller_post
      caller_incoming
      (advance_frozen_caller_snapshots CT h' caller_post body_tail)
      (activate_frozen_target_snapshots CT h' caller_post
        (dangerous_authority_colors
          (executing_authority_color_set CT h' caller_post caller_incoming))
        body_target_witness_tail)
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      stack.
  { unfold private_target_witness_state.
    split; [exact Hfinal_target_cover|].
    split; [exact Hfinal_target_structural|].
    split; [apply frozen_completed_colors_resume_phase_safe_after_self_activation|].
    split; [admit|].
    split; [admit|].
    split; [exact Hfinal_target_before|].
    split; [exact Hfinal_target_support|].
    split; [exact Hfinal_target_history|exact Hfinal_target_temporal]. }
  (* The former callback-based pop reconstruction is superseded by the
     mature untracked frozen-state return theorem above.
  have Hbody_phase_shape := Hbody_phase.
  rewrite Hbody_witnesses in Hbody_phase_shape.
  have Hfinal_witness_phase : private_resume_witnesses_phase_wf CT h'
      caller_post
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      (advance_frozen_caller_snapshots CT h' caller_post body_tail).
  { eapply private_resume_witnesses_phase_wf_after_pop_advance with
      (old_active := callee_final) (witness := Some body_witness)
      (snapshot := None); eauto. }
  have Hbody_before_shape := Hbody_before.
  rewrite Hbody_witnesses in Hbody_before_shape.
  have Hbody_before_tail : frozen_caller_snapshots_before_boundaries
      body_witness_tail stack.
  { inversion Hbody_before_shape; subst; assumption. }
  have Hfinal_witness_before : frozen_caller_snapshots_before_boundaries
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail)
      stack.
  { eapply advance_frozen_caller_snapshots_before_boundaries.
    exact Hbody_before_tail. }
  have Hbody_stack_shape := Hbody_stack_safe.
  rewrite Hbody_witnesses in Hbody_stack_shape.
  have Hfinal_witness_structural : private_resume_witness_stack_structural CT
      h' caller_post
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail).
  { eapply private_resume_witness_stack_structural_after_pop_advance with
      (Z := Z) (old_active := callee_final)
      (incoming := callee_incoming) (head := Some body_witness); eauto. }
  have Hbody_temporal_shape := Hbody_temporal.
  rewrite Hbody_witnesses in Hbody_temporal_shape.
  destruct Hbody_temporal_shape as
    (Hbody_policy_components & Hbody_policy_prospective & Hbody_policy_after).
  have Hbody_policy_after_tail : frozen_snapshot_boundaries_after_cutoff cutoff
      body_witness_tail stack.
  { inversion Hbody_policy_after; subst; assumption. }
  have Hfinal_witness_temporal : private_resume_witness_temporal_state CT h' Z
      cutoff caller_post stack
      (advance_frozen_caller_snapshots CT h' caller_post body_witness_tail).
  { split.
    - intros snapshot tracked_boundary above below Hpartition Hfree.
      destruct (advance_frozen_snapshot_live_partition_reflects CT h'
        caller_post body_witness_tail stack snapshot tracked_boundary above
        below Hpartition) as [old_snapshot Hold_partition].
      have Hinput_partition : frozen_snapshot_live_partition
          (Some body_witness :: body_witness_tail) (boundary :: stack)
          old_snapshot tracked_boundary (boundary :: above) below.
      { constructor. exact Hold_partition. }
      have Hinput_components := Hbody_policy_components old_snapshot
        tracked_boundary (boundary :: above) below Hinput_partition Hfree.
      unfold caller_post.
      eapply live_mutable_authority_components_after_null_return_pop with
        (active := callee_final) (boundary := boundary); eauto.
    - split.
      + intros snapshot tracked_boundary above below Hpartition Hfree.
        destruct (advance_frozen_snapshot_live_partition_reflects CT h'
          caller_post body_witness_tail stack snapshot tracked_boundary above
          below Hpartition) as [old_snapshot Hold_partition].
        have Hinput_partition : frozen_snapshot_live_partition
            (Some body_witness :: body_witness_tail) (boundary :: stack)
            old_snapshot tracked_boundary (boundary :: above) below.
        { constructor. exact Hold_partition. }
        have Hinput_components := Hbody_policy_prospective old_snapshot
          tracked_boundary (boundary :: above) below Hinput_partition Hfree.
        have Hcaller_components :
            live_prospective_mutable_authority_components_after_cutoff CT h'
              tracked_boundary.(boundary_entry_cutoff) caller above.
        { eapply live_prospective_components_after_plain_pop with
            (active := callee_final) (boundary := boundary).
          - unfold caller, boundary. reflexivity.
          - exact Hinput_components. }
        unfold caller_post, caller.
        have Hcaller_length : length caller_senv = length rGamma.(vars) :=
          proj1 (proj2 (proj2 (proj2 (proj2 Hcaller_current_wf)))).
        eapply live_prospective_mutable_authority_components_after_active_descent.
        * exact Hcaller_current_wf.
        * exact Hcaller_current_sound.
        * eapply caller_null_post_rdm_roots_descend;
            [exact Hdestination_receiver|exact Hdestination_type|
             exact Hcaller_length].
        * eapply caller_null_post_owned_is_old;
            [exact Hdestination_receiver|exact Hdestination_type|
             exact Hcaller_length].
        * exact Hcaller_components.
      + eapply advance_snapshot_boundaries_after_cutoff.
        exact Hbody_policy_after_tail. }
  *)
  exists (advance_frozen_caller_snapshots CT h' caller_post body_tail). split.
  - exists caller_final_policies. split.
    + exact Hcaller_final_policy_metadata.
    + split; [exact Hfinal_witness_growth|].
      split.
      * split.
        -- split.
           ++ unfold private_statement_preservation_result.
              split; [exact Hpost_main|].
              split; [exact Hpost_fresh|]. split; assumption.
           ++ exact Hpost_disjoint.
        -- split; [exact Hpost_aligned_policy|]. split; assumption.
      * split; [exact Hfinal_witness_cover|].
        split; [exact Hfinal_witness_phase|].
        split; [exact Hfinal_witness_roots|].
        split; [exact Hfinal_witness_nested|].
        split; [exact Hfinal_witness_completed|].
        split; [exact Hfinal_witness_stack_safe|].
        split; [exact Hfinal_witness_before|].
        split; [exact Hfinal_witness_temporal|exact Hfinal_target_state].
  - exact Hwhole_reflection.
Admitted.

(** A reflected dangerous representative may change between powered and
    prospective mode.  Every non-join step can nevertheless be replayed from
    either dangerous mode, possibly choosing the other dangerous mode at the
    target. *)
Lemma frozen_nonjoin_replays_from_dangerous_mode :
  forall CT h frame source target completed_mode,
    frozen_caller_authority_nonjoin_step CT h source target ->
    authority_mode_dangerous completed_mode ->
    exists target_mode,
      authority_mode_dangerous target_mode /\
      phased_authority_frame_connected CT h frame
        (completed_mode, snd source) (target_mode, snd target).
Proof.
  intros CT h frame source target completed_mode Hstep Hmode.
  destruct Hmode as [Hmode | Hmode]; subst completed_mode;
    inversion Hstep; subst; simpl.
  - exists FlowPowered. split; [left; reflexivity|].
    apply rt_step. apply phased_authority_retained. exact H.
  - exists FlowPowered. split; [left; reflexivity|].
    apply rt_step. apply phased_authority_retained. exact H.
  - exists FlowProspective. split; [right; reflexivity|].
    apply rt_step. apply phased_authority_reverse_rdm. exact H.
  - exists FlowProspective. split; [right; reflexivity|].
    apply rt_step. apply phased_authority_reverse_rdm. exact H.
  - exists FlowProspective. split; [right; reflexivity|].
    apply rt_step. apply phased_authority_mark_prospective.
  - exists FlowProspective. split; [right; reflexivity|].
    apply rt_step. apply phased_authority_prospective_retained. exact H.
  - exists FlowProspective. split; [right; reflexivity|].
    apply rt_step. apply phased_authority_prospective_retained. exact H.
  - exists FlowProspective. split; [right; reflexivity|].
    apply rt_step. apply phased_authority_prospective_rdm_backward. exact H.
  - exists FlowProspective. split; [right; reflexivity|].
    apply rt_step. apply phased_authority_prospective_rdm_backward. exact H.
  - exists FlowProspective. split; [right; reflexivity|]. apply rt_refl.
Qed.

(** Directional completion theorem for the tracked exceptional return.  The
    well-founded derivation is already part of the private pop machinery.
    Old-to-old caller joins are replayed in the pre-call caller and injected
    through the callee incoming set.  A join whose source is the separated
    return root is rerouted to the strictly smaller direct derivation. *)
Lemma tracked_derivation_is_completed_color_well_founded :
  forall CT h Z active active_incoming caller_authority caller_senv caller_renv
    caller_h caller_incoming snapshot destination destination_type
    return_location boundary_cutoff state
    (derivation : tracked_resume_frozen_color_derivation CT h Z active
      active_incoming
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      caller_incoming snapshot state)
    derivation_height,
    tracked_resume_frozen_color_derivation_has_height CT h Z active
      active_incoming
      (mk_watched_frame caller_authority caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      caller_incoming snapshot state derivation derivation_height ->
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    active_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming ->
    executing_authority_old_colors_reflected CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming h active active_incoming ->
    (forall incoming_mode location,
      In authority_flow_state caller_incoming (incoming_mode, location) ->
      location < boundary_cutoff) ->
    (forall anchor,
      frame_owned_location CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary_cutoff) ->
    (forall source target
        (source_derivation : tracked_resume_frozen_color_derivation CT h Z
          active active_incoming
          (mk_watched_frame caller_authority caller_senv
            (update_r_env_value caller_renv destination
              (Iot return_location)))
          caller_incoming snapshot source)
        source_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        caller_incoming snapshot source source_derivation source_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    boundary_cutoff <= return_location ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    authority_mode_dangerous (fst state) ->
    exists completed_mode,
      authority_mode_dangerous completed_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (completed_mode, snd state).
Proof.
  intros CT h Z active active_incoming caller_authority caller_senv caller_renv
    caller_h caller_incoming snapshot destination destination_type
    return_location boundary_cutoff state derivation derivation_height Hheight Hcaller_wf
    Hdestination Hentry_incoming Hbody_reflection Hincoming_old Howned_old
    Hnonjoin_back Hreturn_fresh Hreturn_color Hstate_mode.
  revert state derivation Hheight Hstate_mode.
  induction derivation_height as [derivation_height IH] using lt_wf_ind.
  intros state derivation Hheight Hstate_mode.
  dependent destruction Hheight.
  - destruct state as [mode location]. simpl in *.
    exists mode. split; [exact Hstate_mode|].
    apply executing_authority_color_set_contains_incoming.
    rewrite Hentry_incoming.
    apply executing_authority_color_set_contains_incoming.
    assumption.
  - exists FlowPowered. split; [left; reflexivity|exact Hcallee].
  - have Hsource_mode : authority_mode_dangerous (fst source) by
      (inversion Hstep; subst;
       [left; reflexivity | right; reflexivity | right; reflexivity
       | left; reflexivity | left; reflexivity]).
    destruct (IH n (ltac:(lia)) source previous Hheight Hsource_mode) as
      [completed_source_mode [Hcompleted_source_mode Hsource_color]].
    destruct (frozen_nonjoin_replays_from_dangerous_mode CT h active source
      target completed_source_mode Hstep Hcompleted_source_mode) as
      [completed_target_mode [Hcompleted_target_mode Hreplay]].
    exists completed_target_mode. split; [exact Hcompleted_target_mode|].
    destruct target as [target_mode target_location]. simpl in *.
      destruct Hsource_color as [seed [Hseed Hpath]]. exists seed.
      split; [exact Hseed|]. eapply rt_trans; [exact Hpath|].
      exact Hreplay.
  - destruct (caller_post_rdm_root_origin CT caller_senv caller_renv caller_h
      destination destination_type return_location left Hcaller_wf
      Hdestination Hleft) as [Hleft_old | [Hleft_return Hleft_rdm]];
    destruct (caller_post_rdm_root_origin CT caller_senv caller_renv caller_h
      destination destination_type return_location right Hcaller_wf
      Hdestination Hright) as [Hright_old | [Hright_return Hright_rdm]].
    + have Hleft_old_copy := Hleft_old.
      destruct Hleft_old_copy as
        [variable [T [Htype [Hvalue Hrdm]]]].
      have Hleft_dom := wf_config_value_dom CT caller_senv caller_renv caller_h
        variable left Hcaller_wf Hvalue.
      destruct (IH n (ltac:(lia)) (mode, left) previous Hheight Hmode) as
        [completed_mode [Hcompleted_mode Hcompleted_left]].
      destruct (Hbody_reflection completed_mode left Hcompleted_mode
        Hcompleted_left Hleft_dom) as
        [caller_mode [Hcaller_mode Hcaller_left]].
      have Hcaller_right := executing_authority_dangerous_frame_join CT
        caller_h
        (mk_watched_frame caller_authority caller_senv caller_renv)
        caller_incoming caller_mode left right Hcaller_mode Hcaller_left
        Hleft_old Hright_old.
      exists FlowProspective. split; [right; reflexivity|].
      apply executing_authority_color_set_contains_incoming.
      rewrite Hentry_incoming. exact Hcaller_right.
    + subst right. exact Hreturn_color.
    + subst left.
      destruct (tracked_fresh_return_derivation_reroutes CT h Z active
        active_incoming
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        caller_incoming snapshot boundary_cutoff return_location mode previous
        n right Hheight Hincoming_old Howned_old Hnonjoin_back Hreturn_fresh
        Hright) as
        [rerouted [rerouted_height [Hsmaller Hrerouted]]].
      eapply IH; eauto.
    + subst left right. exact Hreturn_color.
Qed.

(** Extensional wrapper around the well-founded proof.  The derivation and
    its height are reconstructed from an actual resumed-caller color and do
    not escape this private lemma. *)
Lemma tracked_post_dangerous_color_is_completed_color :
  forall CT h (Z : Ensemble Loc) active active_incoming caller_authority
    caller_senv caller_renv
    caller_h caller_incoming snapshot destination destination_type
    return_location boundary_cutoff mode location,
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    active_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming ->
    executing_authority_old_colors_reflected CT caller_h
      (mk_watched_frame caller_authority caller_senv caller_renv)
      caller_incoming h active active_incoming ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state caller_incoming
        (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    (forall anchor,
      frame_owned_location CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor)) ->
    (forall incoming_mode incoming_location,
      In authority_flow_state caller_incoming
        (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall anchor,
      frame_owned_location CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary_cutoff) ->
    (forall source target
        (source_derivation : tracked_resume_frozen_color_derivation CT h Z
          active active_incoming
          (mk_watched_frame caller_authority caller_senv
            (update_r_env_value caller_renv destination
              (Iot return_location)))
          caller_incoming snapshot source)
        source_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        caller_incoming snapshot source source_derivation source_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    boundary_cutoff <= return_location ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT h
        (mk_watched_frame caller_authority caller_senv
          (update_r_env_value caller_renv destination (Iot return_location)))
        caller_incoming) (mode, location) ->
    exists completed_mode,
      authority_mode_dangerous completed_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (completed_mode, location).
Proof.
  intros CT h Z active active_incoming caller_authority caller_senv caller_renv
    caller_h caller_incoming snapshot destination destination_type
    return_location boundary_cutoff mode location Hcaller_wf Hdestination
    Hentry_incoming Hbody_reflection Hincoming_snapshot Howned_callee
    Hincoming_old Howned_old Hnonjoin_back Hreturn_fresh Hreturn_color Hmode
    Hcolor.
  have Hderivation := tracked_snapshot_call_color_has_derivation CT h Z active
    active_incoming snapshot
    (mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)))
    caller_incoming mode location Hincoming_snapshot Howned_callee Hmode Hcolor.
  destruct (tracked_resume_frozen_color_derivation_has_some_height CT h Z
    active active_incoming
    (mk_watched_frame caller_authority caller_senv
      (update_r_env_value caller_renv destination (Iot return_location)))
    caller_incoming snapshot (mode, location) Hderivation) as
    [derivation_height Hheight].
  change (exists completed_mode,
    authority_mode_dangerous completed_mode /\
    In authority_flow_state
      (executing_authority_color_set CT h active active_incoming)
      (completed_mode, snd (mode, location))).
  eapply tracked_derivation_is_completed_color_well_founded; eauto.
Qed.

(** Policy-aware pop for an untracked [[None]] call boundary.

    The frozen statement stack deliberately has no immediate-caller slot in
    this case.  The policy stack separately retains the caller snapshot that
    was captured at entry.  The preceding well-founded classifier consumes
    that witness together with the recursive body's directional old-color
    summary.  Thus every dangerous color admitted by the resumed target
    policy is already a completed-callee color; neither a fabricated tracked
    slot nor an additional public premise is required. *)
Lemma untracked_immutable_resumed_call_pop_safe_from_witness :
  forall CT h (Z : Ensemble Loc) active active_incoming caller_senv
    caller_renv caller_h caller_incoming snapshot destination
    destination_type return_location boundary_cutoff eligible,
    wf_r_config CT caller_senv caller_renv caller_h ->
    static_getType caller_senv destination = Some destination_type ->
    active_incoming = executing_authority_color_set CT caller_h
      (mk_watched_frame Imm_r caller_senv caller_renv) caller_incoming ->
    executing_authority_old_colors_reflected CT caller_h
      (mk_watched_frame Imm_r caller_senv caller_renv) caller_incoming h
      active active_incoming ->
    (forall incoming_mode incoming_location,
      authority_mode_dangerous incoming_mode ->
      In authority_flow_state caller_incoming
        (incoming_mode, incoming_location) ->
      In authority_flow_state snapshot.(frozen_snapshot_current_colors)
        (incoming_mode, incoming_location)) ->
    (forall anchor,
      frame_owned_location CT h
        (mk_watched_frame Imm_r caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor)) ->
    (forall incoming_mode incoming_location,
      In authority_flow_state caller_incoming
        (incoming_mode, incoming_location) ->
      incoming_location < boundary_cutoff) ->
    (forall anchor,
      frame_owned_location CT h
        (mk_watched_frame Imm_r caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location))) anchor ->
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (FlowPowered, anchor) ->
      anchor < boundary_cutoff) ->
    (forall source target
        (source_derivation : tracked_resume_frozen_color_derivation CT h Z
          active active_incoming
          (mk_watched_frame Imm_r caller_senv
            (update_r_env_value caller_renv destination
              (Iot return_location)))
          caller_incoming snapshot source)
        source_height,
      tracked_resume_frozen_color_derivation_has_height CT h Z active
        active_incoming
        (mk_watched_frame Imm_r caller_senv
          (update_r_env_value caller_renv destination
            (Iot return_location)))
        caller_incoming snapshot source source_derivation source_height ->
      frozen_caller_authority_nonjoin_step CT h source target ->
      boundary_cutoff <= snd target ->
      boundary_cutoff <= snd source) ->
    boundary_cutoff <= return_location ->
    (exists return_mode,
      authority_mode_dangerous return_mode /\
      In authority_flow_state
        (executing_authority_color_set CT h active active_incoming)
        (return_mode, return_location)) ->
    executing_resumed_authority_call_pop_safe CT h Z active active_incoming
      eligible
      (mk_watched_frame Imm_r caller_senv
        (update_r_env_value caller_renv destination (Iot return_location)))
      caller_incoming.
Proof.
  intros CT h Z active active_incoming caller_senv caller_renv caller_h
    caller_incoming snapshot destination destination_type return_location
    boundary_cutoff eligible Hcaller_wf Hdestination Hentry_incoming
    Hbody_reflection Hincoming_snapshot Howned_callee Hincoming_old Howned_old
    Hnonjoin_back Hreturn_fresh Hreturn_color mode location Hmode Hcolor.
  left.
  eapply tracked_post_dangerous_color_is_completed_color; eauto.
  eapply executing_resumed_authority_color_set_in_phased. exact Hcolor.
Qed.

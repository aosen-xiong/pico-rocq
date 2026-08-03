Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityPolicy.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

(** Compositional active-color summaries.  These are the missing semantic
    payload for an untracked call: the [None] snapshot deliberately records
    no immediate caller, so the recursive body proof instead reports that
    every dangerous color at an entry-old location reflects to the entry
    phase. *)
Lemma assignment_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming x expression old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x expression) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h expression value OK rGamma h ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h
      (mk_watched_frame authority sGamma
        (update_r_env_value rGamma x value)) incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming x expression old value
    Hwf Htyping Hscope Hvalue Heval mode location Hmode Hcolor Hlocation.
  have Hdescend := rdm_roots_descend_after_assignment CT sGamma mt rGamma h
    x expression old value Hwf Htyping Hscope Hvalue Heval.
  eapply executing_authority_colors_after_active_descent_covered; eauto.
  intros owned Howned.
  apply frame_owned_location_iff_active_live.
  eapply assignment_live_reachability_is_old with
    (mt := mt) (x := x) (e := expression) (old := old) (value := value)
    (stack := []); eauto.
  apply frame_owned_location_iff_active_live. exact Howned.
Qed.

Lemma local_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h
      (mk_watched_frame authority sGamma'
        (set_vars rGamma (vars rGamma ++ [Null_a]))) incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming T x sGamma' Hwf Htyping
    Hnone mode location Hmode Hcolor Hlocation.
  have Hdescend := rdm_roots_descend_after_local CT sGamma mt rGamma h T x
    sGamma' Hwf Htyping Hnone.
  eapply executing_authority_colors_after_active_descent_covered; eauto.
  intros owned Howned.
  apply frame_owned_location_iff_active_live.
  eapply local_live_reachability_is_old with (stack := []); eauto.
  apply frame_owned_location_iff_active_live. exact Howned.
Qed.

Lemma field_write_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming x field y sGamma' rGamma'
    h',
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SFldWrite x field y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x field y) OK rGamma' h' ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h'
      (mk_watched_frame authority sGamma' rGamma') incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming x field y sGamma' rGamma'
    h' Hwf Hsound Hincoming Htyping Hscope Heval mode location Hmode Hcolor
    Hlocation.
  eapply executing_authority_colors_after_typed_field_write_covered; eauto.
  eapply executing_authority_colors_runtime_mutable; eauto.
Qed.

Lemma new_old_colors_reflected :
  forall CT authority sGamma mt rGamma h incoming x qc C args sGamma' rGamma'
    h',
    wf_r_config CT sGamma rGamma h ->
    wf_r_config CT sGamma' rGamma' h' ->
    authority_context_sound h rGamma authority ->
    authority_context_sound h' rGamma' authority ->
    authority_colors_runtime_mutable h incoming ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    executing_authority_old_colors_reflected CT h
      (mk_watched_frame authority sGamma rGamma) incoming h'
      (mk_watched_frame authority sGamma' rGamma') incoming.
Proof.
  intros CT authority sGamma mt rGamma h incoming x qc C args sGamma' rGamma'
    h' Hwf Hpost_wf Hsound Hpost_sound Hincoming Htyping Heval.
  inversion Heval; subst.
  assert (Hupdate :
      set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))).
  { destruct rGamma. reflexivity. }
  rewrite Hupdate in Hpost_wf, Hpost_sound |- *.
  intros mode location Hmode Hcolor Hlocation.
  eapply executing_authority_colors_after_new_covered; eauto.
Qed.

(** Composition bridge for a call body.  The recursive summary first maps a
    final callee color to the callee-entry phase; safe-call entry coverage
    then maps that entry color to the suspended caller phase. *)
Lemma call_body_old_color_reflects_to_caller_entry :
  forall CT caller_h caller caller_incoming callee_entry callee_incoming
    final_h callee_final mode location,
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    (forall entry_mode entry_location,
      authority_mode_dangerous entry_mode ->
      In authority_flow_state
        (executing_authority_color_set CT caller_h callee_entry
          callee_incoming) (entry_mode, entry_location) ->
      exists caller_mode,
        authority_mode_dangerous caller_mode /\
        In authority_flow_state
          (executing_authority_color_set CT caller_h caller caller_incoming)
          (caller_mode, entry_location)) ->
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
  intros CT caller_h caller caller_incoming callee_entry callee_incoming
    final_h callee_final mode location Hincoming Hentry Hbody Hmode Hcolor
    Hold.
  destruct (Hbody mode location Hmode Hcolor Hold) as
    [entry_mode [Hentry_mode Hentry_color]].
  eapply Hentry; eauto.
Qed.

(** If the whole call summary reflects a resumed caller color to the
    pre-call caller, that representative is present in the completed callee:
    caller colors are precisely the callee incoming colors and incoming
    colors are seeds of the final callee closure. *)
Lemma call_old_reflection_supplies_completed_callee_color :
  forall CT caller_h caller caller_incoming final_h caller_post callee
    callee_incoming mode location,
    callee_incoming = executing_authority_color_set CT caller_h caller
      caller_incoming ->
    executing_authority_old_colors_reflected CT caller_h caller
      caller_incoming final_h caller_post caller_incoming ->
    authority_mode_dangerous mode ->
    In authority_flow_state
      (executing_authority_color_set CT final_h caller_post caller_incoming)
      (mode, location) ->
    location < dom caller_h ->
    exists callee_mode,
      authority_mode_dangerous callee_mode /\
      In authority_flow_state
        (executing_authority_color_set CT final_h callee callee_incoming)
        (callee_mode, location).
Proof.
  intros CT caller_h caller caller_incoming final_h caller_post callee
    callee_incoming mode location Hincoming Hreflect Hmode Hcolor Hold.
  destruct (Hreflect mode location Hmode Hcolor Hold) as
    [caller_mode [Hcaller_mode Hcaller_color]].
  exists caller_mode. split; [exact Hcaller_mode|].
  apply executing_authority_color_set_contains_incoming.
  rewrite Hincoming. exact Hcaller_color.
Qed.

Lemma private_policy_eval_results_trans :
  forall CT P Z cutoff authority initial_senv initial_renv middle_senv
    middle_renv final_senv final_renv stack incoming initial_snapshots
    middle_snapshots final_snapshots policies initial_h middle_h final_h,
    dom initial_h <= dom middle_h ->
    private_policy_statement_result CT P Z cutoff authority middle_senv
      middle_renv stack incoming initial_snapshots middle_snapshots policies
      middle_h ->
    executing_authority_old_colors_reflected_or_outside CT Z initial_h
      (mk_watched_frame authority initial_senv initial_renv) incoming middle_h
      (mk_watched_frame authority middle_senv middle_renv) incoming ->
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming middle_snapshots final_snapshots policies
      final_h ->
    executing_authority_old_colors_reflected_or_outside CT Z middle_h
      (mk_watched_frame authority middle_senv middle_renv) incoming final_h
      (mk_watched_frame authority final_senv final_renv) incoming ->
    private_policy_statement_result CT P Z cutoff authority final_senv
      final_renv stack incoming initial_snapshots final_snapshots policies
      final_h /\
    executing_authority_old_colors_reflected_or_outside CT Z initial_h
      (mk_watched_frame authority initial_senv initial_renv) incoming final_h
      (mk_watched_frame authority final_senv final_renv) incoming.
Proof.
  intros CT P Z cutoff authority initial_senv initial_renv middle_senv
    middle_renv final_senv final_renv stack incoming initial_snapshots
    middle_snapshots final_snapshots policies initial_h middle_h final_h
    Hgrowth Hfirst Hfirst_reflect Hsecond Hsecond_reflect. split.
  - eapply private_policy_statement_result_trans; eauto.
  - eapply executing_authority_old_colors_reflected_or_outside_trans; eauto.
Qed.

(** Strengthened recursive contract.  The initial public history fact remains
    explicit because atomic preservation lemmas consume it; all additional
    data is proof-local and existentially hidden at the public wrapper. *)
Definition private_policy_eval_preserves : Prop :=
  forall P CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff incoming snapshots
      policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack incoming h ->
      private_policy_statement_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
        policies h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      exists final_snapshots,
        private_policy_statement_result CT P Z cutoff authority sGamma'
          rGamma' stack incoming snapshots final_snapshots policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame authority sGamma rGamma) incoming h'
          (mk_watched_frame authority sGamma' rGamma') incoming.

(** The single recursive rule consumed by the structural induction.  It is
    deliberately stated for the successful call constructor itself: all
    operational equalities remain available to the call proof, while the
    recursive body theorem is the only induction hypothesis supplied. *)
Definition private_policy_successful_call_rule : Prop :=
  forall P CT rGamma h x y method args vals receiver_location runtime_class
    runtime_mdef body statement return_var result h' entry_renv body_renv
    final_renv,
    runtime_getVal rGamma y = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef /\
      body = Syntax.mbody runtime_mdef ->
    statement = body.(mbody_stmt) ->
    return_var = body.(mreturn) ->
    runtime_lookup_list rGamma args = Some vals ->
    entry_renv = mkr_env (Iot receiver_location :: vals) ->
    eval_stmt CT entry_renv h statement OK body_renv h' ->
    runtime_getVal body_renv return_var = Some result ->
    final_renv = set_vars rGamma (update x result rGamma.(vars)) ->
    (forall entry_senv entry_scope final_senv callee_authority stack Z cutoff
      incoming snapshots policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv entry_renv) stack
        incoming h ->
      private_policy_statement_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv entry_renv) stack
        incoming snapshots policies h ->
      stmt_typing CT entry_senv entry_scope statement final_senv ->
      readonly_state_method_scope entry_scope ->
      exists final_snapshots,
        private_policy_statement_result CT P Z cutoff callee_authority
          final_senv body_renv stack incoming snapshots final_snapshots
          policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame callee_authority entry_senv entry_renv) incoming
          h' (mk_watched_frame callee_authority final_senv body_renv)
          incoming) ->
    forall caller_senv caller_scope caller_final_senv caller_authority stack Z
      cutoff caller_incoming caller_snapshots caller_policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame caller_authority caller_senv rGamma) stack
        caller_incoming h ->
      private_policy_statement_state CT P Z cutoff
        (mk_watched_frame caller_authority caller_senv rGamma) stack
        caller_incoming caller_snapshots caller_policies h ->
      stmt_typing CT caller_senv caller_scope
        (SCall x method y args) caller_final_senv ->
      readonly_state_method_scope caller_scope ->
      exists final_snapshots,
        private_policy_statement_result CT P Z cutoff caller_authority
          caller_final_senv final_renv stack caller_incoming caller_snapshots
          final_snapshots caller_policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame caller_authority caller_senv rGamma)
          caller_incoming h'
          (mk_watched_frame caller_authority caller_final_senv final_renv)
          caller_incoming.

(** Policy-evolving counterpart of the preceding recursive interfaces.
    Suspended resume witnesses are advanced by each phase and are therefore
    returned existentially; persistent target sets remain related to their
    entry values by [private_frame_join_policies_metadata_eq]. *)
Definition private_advancing_policy_eval_preserves : Prop :=
  forall P CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff incoming snapshots
      policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack incoming h ->
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
        policies h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      exists final_snapshots,
        private_advancing_policy_statement_result CT P Z cutoff authority
          sGamma' rGamma' stack incoming snapshots final_snapshots
          policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame authority sGamma rGamma) incoming h'
          (mk_watched_frame authority sGamma' rGamma') incoming.

Definition private_advancing_policy_successful_call_rule : Prop :=
  forall P CT rGamma h x y method args vals receiver_location runtime_class
    runtime_mdef body statement return_var result h' entry_renv body_renv
    final_renv,
    runtime_getVal rGamma y = Some (Iot receiver_location) ->
    r_basetype h receiver_location = Some runtime_class ->
    FindMethodWithName CT runtime_class method runtime_mdef /\
      body = Syntax.mbody runtime_mdef ->
    statement = body.(mbody_stmt) ->
    return_var = body.(mreturn) ->
    runtime_lookup_list rGamma args = Some vals ->
    entry_renv = mkr_env (Iot receiver_location :: vals) ->
    eval_stmt CT entry_renv h statement OK body_renv h' ->
    runtime_getVal body_renv return_var = Some result ->
    final_renv = set_vars rGamma (update x result rGamma.(vars)) ->
    (forall entry_senv entry_scope final_senv callee_authority stack Z cutoff
      incoming snapshots policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv entry_renv) stack
        incoming h ->
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame callee_authority entry_senv entry_renv) stack
        incoming snapshots policies h ->
      stmt_typing CT entry_senv entry_scope statement final_senv ->
      readonly_state_method_scope entry_scope ->
      exists final_snapshots,
        private_advancing_policy_statement_result CT P Z cutoff
          callee_authority final_senv body_renv stack incoming snapshots
          final_snapshots policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame callee_authority entry_senv entry_renv) incoming
          h' (mk_watched_frame callee_authority final_senv body_renv)
          incoming) ->
    forall caller_senv caller_scope caller_final_senv caller_authority stack Z
      cutoff caller_incoming caller_snapshots caller_policies,
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame caller_authority caller_senv rGamma) stack
        caller_incoming h ->
      private_advancing_policy_statement_state CT P Z cutoff
        (mk_watched_frame caller_authority caller_senv rGamma) stack
        caller_incoming caller_snapshots caller_policies h ->
      stmt_typing CT caller_senv caller_scope
        (SCall x method y args) caller_final_senv ->
      readonly_state_method_scope caller_scope ->
      exists final_snapshots,
        private_advancing_policy_statement_result CT P Z cutoff
          caller_authority caller_final_senv final_renv stack caller_incoming
          caller_snapshots final_snapshots caller_policies h' /\
        executing_authority_old_colors_reflected_or_outside CT Z h
          (mk_watched_frame caller_authority caller_senv rGamma)
          caller_incoming h'
          (mk_watched_frame caller_authority caller_final_senv final_renv)
          caller_incoming.

Lemma private_policy_eval_preserves_from_call_rule :
  private_policy_successful_call_rule -> private_policy_eval_preserves.
Proof.
  intros Hcall P CT rGamma h statement rGamma' h' Heval.
  revert P.
  dependent induction Heval; intros P sGamma mt sGamma' authority stack Z
    cutoff incoming snapshots policies Hpotential Hprivate Htyping Hscope.
  - inversion Htyping; subst. exists snapshots. split.
    + eapply private_policy_statement_result_refl; eauto.
    + apply executing_authority_old_colors_reflected_or_outside_refl.
  - eexists. split.
    + eapply private_policy_statement_after_local; eauto.
    + have Hmain := private_policy_statement_state_main CT P Z cutoff
        (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
        policies h Hprivate.
      have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
      apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply local_old_colors_reflected; eauto.
  - have Hmain := private_policy_statement_state_main CT P Z cutoff
      (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
      policies h Hprivate.
    have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hsound := proj1 (proj1 (proj2 (proj2 (proj2
      (proj2 (proj2 Hmain)))))).
    inversion Htyping; subst.
    assert (Hupdate : set_vars rΓ (update x v2 (vars rΓ)) =
        update_r_env_value rΓ x v2) by (destruct rΓ; reflexivity).
    rewrite Hupdate.
    eexists. split.
    + eapply private_policy_statement_after_assignment; eauto.
    + apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply assignment_old_colors_reflected; eauto.
  - have Heval_current : eval_stmt CT rΓ h (SFldWrite x f y) OK rΓ h'.
    { econstructor; eauto. }
    eexists. split.
    + eapply private_policy_statement_after_field_write; eauto.
    + have Hmain := private_policy_statement_state_main CT P Z cutoff
        (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
        policies h Hprivate.
      have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
      have Hsound := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 (proj2 Hmain)))))).
      have Hincoming_runtime := proj1 (proj2 (proj2 Hmain)).
      apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply field_write_old_colors_reflected; eauto.
  - have Heval_current : eval_stmt CT rΓ h (SNew x q_c c ys) OK rΓ' h'.
    { econstructor; eauto. }
    have Hnew_result := private_policy_statement_after_new CT P Z cutoff
      authority sGamma mt rΓ h stack incoming snapshots policies x q_c c ys
      sGamma' rΓ' h' Hpotential Hprivate Htyping Heval_current.
    exists (advance_frozen_caller_snapshots CT h'
      (mk_watched_frame authority sGamma' rΓ') snapshots). split.
    + exact Hnew_result.
    + have Hmain := private_policy_statement_state_main CT P Z cutoff
        (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
        policies h Hprivate.
      have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
      have Hsound := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 (proj2 Hmain)))))).
      have Hincoming_runtime := proj1 (proj2 (proj2 Hmain)).
      have Hpost_state := private_policy_statement_result_is_state CT P Z
        cutoff authority sGamma' rΓ' stack incoming snapshots
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma' rΓ') snapshots)
        policies h' Hnew_result.
      have Hpost_main := private_policy_statement_state_main CT P Z cutoff
        (mk_watched_frame authority sGamma' rΓ') stack incoming
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma' rΓ') snapshots)
        policies h' Hpost_state.
      have Hpost_wf := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 Hpost_main))))).
      have Hpost_sound := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 (proj2 Hpost_main)))))).
      apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply new_old_colors_reflected; eauto.
  - eapply Hcall; eauto.
  - inversion Htyping; subst.
    destruct (IHHeval1 eq_refl P sGamma mt sΓ' authority stack Z
      cutoff incoming snapshots policies Hpotential Hprivate Htype1 Hscope)
      as [middle_snapshots [Hfirst Hfirst_reflect]].
    have Hmiddle_private := private_policy_statement_result_is_state CT P Z
      cutoff authority sΓ' rΓ' stack incoming snapshots middle_snapshots
      policies h' Hfirst.
    have Hmiddle_potential := proj1 (proj1 (proj1 Hfirst)).
    destruct (IHHeval2 eq_refl P sΓ' mt sGamma' authority stack Z
      cutoff incoming middle_snapshots policies Hmiddle_potential
      Hmiddle_private Htype2 Hscope) as
      [final_snapshots [Hsecond Hsecond_reflect]].
    exists final_snapshots.
    have Hgrowth : dom h <= dom h'.
    { eapply eval_stmt_preserves_heap_domain_simple. exact Heval1. }
    exact (private_policy_eval_results_trans CT P Z cutoff authority sGamma
      rΓ sΓ' rΓ' sGamma' rΓ'' stack incoming snapshots middle_snapshots
      final_snapshots policies h h' h'' Hgrowth Hfirst Hfirst_reflect Hsecond
      Hsecond_reflect).
Qed.

(** Structural preservation with phase-current suspended witnesses. *)
Lemma private_advancing_policy_eval_preserves_from_call_rule :
  private_advancing_policy_successful_call_rule ->
  private_advancing_policy_eval_preserves.
Proof.
  intros Hcall P CT rGamma h statement rGamma' h' Heval.
  revert P.
  dependent induction Heval; intros P sGamma mt sGamma' authority stack Z
    cutoff incoming snapshots policies Hpotential Hprivate Htyping Hscope.
  all: have Hprivate_full := Hprivate.
  all: destruct Hprivate as
    (Hprivate & Hwitness_cover & Hwitness_phase & Hwitness_roots &
      Hwitness_nested & Hwitness_completed & Hwitness_stack_safe &
      Hwitness_before & Hwitness_temporal).
  - inversion Htyping; subst. exists snapshots. split.
    + eapply private_advancing_policy_statement_result_refl; eauto.
    + apply executing_authority_old_colors_reflected_or_outside_refl.
  - have Hmain := private_policy_statement_state_main CT P Z cutoff
      (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
      policies h Hprivate.
    have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hsound := proj1 (proj1 (proj2 (proj2 (proj2
      (proj2 (proj2 Hmain)))))).
    have Heval_current : eval_stmt CT rΓ h (SLocal T x) OK
        (set_vars rΓ (vars rΓ ++ [Null_a])) h.
    { econstructor; eauto. }
    have Hwitness_fresh :=
      private_advancing_policy_statement_witness_state_is_private_fresh
        CT P Z cutoff (mk_watched_frame authority sGamma rΓ) stack incoming
        snapshots policies h Hprivate_full.
    have Hnew_witness_fresh :
        private_fresh_frozen_statement_state CT P Z cutoff
          (mk_watched_frame authority sGamma'
            (set_vars rΓ (vars rΓ ++ [Null_a]))) stack incoming
          (advance_frozen_caller_snapshots CT h
            (mk_watched_frame authority sGamma'
              (set_vars rΓ (vars rΓ ++ [Null_a])))
            policies.(suspended_frame_resume_witnesses)) h.
    { eapply private_fresh_frozen_statement_after_local; eauto. }
    eexists. split.
    + eapply
        private_policy_statement_result_advance_witnesses_after_active_descent
        with (old_senv := sGamma) (old_renv := rΓ)
          (new_senv := sGamma')
          (new_renv := set_vars rΓ (vars rΓ ++ [Null_a])).
      * exact Hprivate_full.
      * eapply rdm_roots_descend_after_local; eauto.
      * intros location Hlocation.
        apply frame_owned_location_iff_active_live.
        eapply local_live_reachability_is_old with (stack := []); eauto.
        apply frame_owned_location_iff_active_live. exact Hlocation.
      * exact (preservation_pico CT sGamma mt rΓ h (SLocal T x)
          (set_vars rΓ (vars rΓ ++ [Null_a])) h sGamma' Hwf Htyping
          Heval_current).
      * eapply
          private_fresh_frozen_statement_state_has_resume_temporal_state.
        exact Hnew_witness_fresh.
      * eapply private_policy_statement_after_local; eauto.
    + apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply local_old_colors_reflected; eauto.
  - have Hmain := private_policy_statement_state_main CT P Z cutoff
      (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
      policies h Hprivate.
    have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
    have Hsound := proj1 (proj1 (proj2 (proj2 (proj2
      (proj2 (proj2 Hmain)))))).
    inversion Htyping; subst.
    assert (Hupdate : set_vars rΓ (update x v2 (vars rΓ)) =
        update_r_env_value rΓ x v2) by (destruct rΓ; reflexivity).
    have Heval_current : eval_stmt CT rΓ h (SVarAss x e) OK
        (set_vars rΓ (update x v2 (vars rΓ))) h.
    { econstructor; eauto. }
    rewrite Hupdate in Heval_current.
    rewrite Hupdate.
    have Hwitness_fresh :=
      private_advancing_policy_statement_witness_state_is_private_fresh
        CT P Z cutoff (mk_watched_frame authority sGamma' rΓ) stack incoming
        snapshots policies h Hprivate_full.
    have Hnew_witness_fresh :
        private_fresh_frozen_statement_state CT P Z cutoff
          (mk_watched_frame authority sGamma'
            (update_r_env_value rΓ x v2)) stack incoming
          (advance_frozen_caller_snapshots CT h
            (mk_watched_frame authority sGamma'
              (update_r_env_value rΓ x v2))
            policies.(suspended_frame_resume_witnesses)) h.
    { eapply private_fresh_frozen_statement_after_assignment; eauto. }
    eexists. split.
    + eapply
        private_policy_statement_result_advance_witnesses_after_active_descent
        with (old_senv := sGamma') (old_renv := rΓ)
          (new_senv := sGamma')
          (new_renv := update_r_env_value rΓ x v2).
      * exact Hprivate_full.
      * eapply rdm_roots_descend_after_assignment; eauto.
      * intros location Hlocation.
        apply frame_owned_location_iff_active_live.
        eapply assignment_live_reachability_is_old with
          (mt := mt) (x := x) (e := e) (value := v2) (stack := []); eauto.
        apply frame_owned_location_iff_active_live. exact Hlocation.
      * exact (preservation_pico CT sGamma' mt rΓ h (SVarAss x e)
          (update_r_env_value rΓ x v2) h sGamma' Hwf Htyping Heval_current).
      * eapply
          private_fresh_frozen_statement_state_has_resume_temporal_state.
        exact Hnew_witness_fresh.
      * eapply private_policy_statement_after_assignment; eauto.
    + apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply assignment_old_colors_reflected; eauto.
  - have Heval_current : eval_stmt CT rΓ h (SFldWrite x f y) OK rΓ h'.
    { econstructor; eauto. }
    eexists. split.
    + eapply private_advancing_policy_statement_after_field_write; eauto.
      eapply private_policy_statement_after_field_write; eauto.
    + have Hmain := private_policy_statement_state_main CT P Z cutoff
        (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
        policies h Hprivate.
      have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
      have Hsound := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 (proj2 Hmain)))))).
      have Hincoming_runtime := proj1 (proj2 (proj2 Hmain)).
      apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply field_write_old_colors_reflected; eauto.
  - have Heval_current : eval_stmt CT rΓ h (SNew x q_c c ys) OK rΓ' h'.
    { econstructor; eauto. }
    have Hnew_fixed := private_policy_statement_after_new CT P Z cutoff
      authority sGamma mt rΓ h stack incoming snapshots policies x q_c c ys
      sGamma' rΓ' h' Hpotential Hprivate Htyping Heval_current.
    have Hnew_advancing :=
      private_advancing_policy_statement_after_new CT P Z cutoff authority
        sGamma mt rΓ h stack incoming snapshots policies x q_c c ys
        sGamma' rΓ' h' Hpotential Hprivate_full Htyping Heval_current
        Hnew_fixed.
    exists (advance_frozen_caller_snapshots CT h'
      (mk_watched_frame authority sGamma' rΓ') snapshots). split.
    + exact Hnew_advancing.
    + have Hmain := private_policy_statement_state_main CT P Z cutoff
        (mk_watched_frame authority sGamma rΓ) stack incoming snapshots
        policies h Hprivate.
      have Hwf := proj1 (proj1 (proj2 (proj2 (proj2 (proj2 Hmain))))).
      have Hsound := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 (proj2 Hmain)))))).
      have Hincoming_runtime := proj1 (proj2 (proj2 Hmain)).
      destruct (private_advancing_policy_statement_result_is_state CT P Z
        cutoff authority sGamma' rΓ' stack incoming snapshots
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma' rΓ') snapshots)
        policies h' Hnew_advancing) as
        [final_policies [Hpolicy_metadata Hpost_state]].
      have Hpost_main := private_policy_statement_state_main CT P Z cutoff
        (mk_watched_frame authority sGamma' rΓ') stack incoming
        (advance_frozen_caller_snapshots CT h'
          (mk_watched_frame authority sGamma' rΓ') snapshots)
        final_policies h' (proj1 Hpost_state).
      have Hpost_wf := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 Hpost_main))))).
      have Hpost_sound := proj1 (proj1 (proj2 (proj2 (proj2
        (proj2 (proj2 Hpost_main)))))).
      apply executing_authority_old_colors_reflected_implies_or_outside.
      eapply new_old_colors_reflected; eauto.
  - eapply Hcall; eauto.
  - inversion Htyping; subst.
    destruct (IHHeval1 eq_refl P sGamma mt sΓ' authority stack Z
      cutoff incoming snapshots policies Hpotential Hprivate_full Htype1
      Hscope) as [middle_snapshots [Hfirst_advancing Hfirst_reflect]].
    destruct Hfirst_advancing as [middle_policies
      [Hmiddle_policy_metadata
        [Hmiddle_witness_growth
          [Hfirst Hmiddle_certificates]]]].
    destruct Hmiddle_certificates as
      (Hmiddle_cover & Hmiddle_phase & Hmiddle_roots & Hmiddle_nested &
        Hmiddle_completed & Hmiddle_stack_safe & Hmiddle_before &
        Hmiddle_temporal).
    have Hmiddle_private : private_advancing_policy_statement_state CT P Z
        cutoff (mk_watched_frame authority sΓ' rΓ') stack incoming
        middle_snapshots middle_policies h'.
    { split.
      - eapply private_policy_statement_result_is_state. exact Hfirst.
      - split; [exact Hmiddle_cover|].
        split; [exact Hmiddle_phase|].
        split; [exact Hmiddle_roots|].
        split; [exact Hmiddle_nested|].
        split; [exact Hmiddle_completed|].
        split; [exact Hmiddle_stack_safe|].
        split; assumption. }
    have Hmiddle_potential := proj1 (proj1 (proj1 Hfirst)).
    destruct (IHHeval2 eq_refl P sΓ' mt sGamma' authority stack Z
      cutoff incoming middle_snapshots middle_policies Hmiddle_potential
      Hmiddle_private Htype2 Hscope) as
      [final_snapshots [Hsecond Hsecond_reflect]].
    exists final_snapshots. split.
    + eapply private_advancing_policy_statement_result_trans_from_middle;
        eauto.
    + have Hgrowth : dom h <= dom h'.
      { eapply eval_stmt_preserves_heap_domain_simple. exact Heval1. }
      eapply executing_authority_old_colors_reflected_or_outside_trans; eauto.
Qed.

Lemma private_policy_eval_preserves_public_authority_history :
  private_policy_eval_preserves ->
  forall P CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff,
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma' rGamma') stack
        (Empty_set authority_flow_state) h'.
Proof.
  intros Hprivate P CT rGamma h statement rGamma' h' Heval sGamma mt
    sGamma' authority stack Z cutoff Hpotential Htyping Hscope.
  have Hstate := potential_live_history_starts_private_policy_statement CT P Z
    cutoff authority sGamma rGamma stack h Hpotential.
  have Hmain := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame authority sGamma rGamma) stack
    (Empty_set authority_flow_state) (repeat None (length stack))
    (initial_private_frame_join_policies
      (mk_watched_frame authority sGamma rGamma) stack) h Hstate.
  destruct (Hprivate P CT rGamma h statement rGamma' h' Heval sGamma mt
    sGamma' authority stack Z cutoff (Empty_set authority_flow_state)
    (repeat None (length stack))
    (initial_private_frame_join_policies
      (mk_watched_frame authority sGamma rGamma) stack)
    Hmain Hstate Htyping Hscope) as
    [final_snapshots [Hresult Hreflection]].
  exact (proj1 (proj1 (proj1 Hresult))).
Qed.

Lemma private_advancing_policy_eval_preserves_public_authority_history :
  private_advancing_policy_eval_preserves ->
  forall P CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff,
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      principled_phased_authority_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma' rGamma') stack
        (Empty_set authority_flow_state) h'.
Proof.
  intros Hprivate P CT rGamma h statement rGamma' h' Heval sGamma mt
    sGamma' authority stack Z cutoff Hpotential Htyping Hscope.
  have Hstate :=
    potential_live_history_starts_private_advancing_policy_statement CT P Z
      cutoff authority sGamma rGamma stack h Hpotential.
  have Hmain := private_policy_statement_state_main CT P Z cutoff
    (mk_watched_frame authority sGamma rGamma) stack
    (Empty_set authority_flow_state) (repeat None (length stack))
    (initial_private_frame_join_policies
      (mk_watched_frame authority sGamma rGamma) stack) h (proj1 Hstate).
  destruct (Hprivate P CT rGamma h statement rGamma' h' Heval sGamma mt
    sGamma' authority stack Z cutoff (Empty_set authority_flow_state)
    (repeat None (length stack))
    (initial_private_frame_join_policies
      (mk_watched_frame authority sGamma rGamma) stack)
    Hmain Hstate Htyping Hscope) as
    [final_snapshots [[final_policies
      [Hpolicy_metadata [Hwitness_growth
        [Hresult [Hwitness_cover Hwitness_phase]]]]]
      Hreflection]].
  exact (proj1 (proj1 (proj1 Hresult))).
Qed.

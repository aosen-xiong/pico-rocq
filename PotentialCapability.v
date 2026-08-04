Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability ComponentColoring.
Require Import ExecutionConfinement ProtectionHistory ForwardCapabilityHistory.
Require Import AuthorityCapability AuthorityHistory WatchedFrames
  LiveCapabilityStack.
Require Export PotentialCapabilityResume.
Require Import PotentialCapabilityRDMPop.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

Theorem successful_stmt_preserves_potential_history :
  forall P CT rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack Z cutoff,
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      potential_live_history_state CT P Z cutoff
        (mk_watched_frame authority sGamma' rGamma') stack h'.
Proof.
{
  intros P CT rGamma h statement rGamma' h' Heval.
  have Heval_copy := Heval.
  revert P.
  dependent induction Heval;
    intros P sGamma mt sGamma' authority stack Z cutoff Hstate Htyping Hsafe.
  - inversion Htyping; subst. exact Hstate.
  - eapply potential_history_after_local; eauto.
  - inversion Htyping; subst.
    assert (Hupdate :
      set_vars rΓ (update x v2 (vars rΓ)) = update_r_env_value rΓ x v2).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate.
    eapply potential_history_after_assignment with
      (CT := CT) (P := P) (Z := Z) (cutoff := cutoff)
      (authority := authority) (mt := mt)
      (rGamma := rΓ) (h := h) (stack := stack)
      (x := x) (e := e) (old := v1) (value := v2).
    + exact Hstate.
    + exact Htyping.
    + exact Hsafe.
    + exact Hval.
    + exact Heval.
  - eapply potential_history_after_field_write.
    + exact Hstate.
    + exact Htyping.
    + exact Hsafe.
    + exact Heval_copy.
  - eapply potential_history_after_new; eauto.
  - destruct Hfind as [Hfind_method Hbody_definition].
    subst mbody. subst mstmt. subst mret. subst rΓ'. subst rΓ'''.
    have Hcaller_wf : wf_r_config CT sGamma rΓ h :=
      proj1 (proj1 (proj2 (proj1 Hstate))).
    destruct (safe_typed_call_static_result CT sGamma mt rΓ h x m y zs
      sGamma' ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase Hfind_method)
      as [destination_type [receiver_type [static_mdef Hstatic_result]]].
    destruct Hstatic_result as
      [HsGamma [Hdestination_not_receiver [Hdestination_type
        [Hreceiver_type [Hfind_static
          [Hsignature_refinement
            [Hresult_sub Hstatic_receiver_sub]]]]]]].
    subst sGamma'.
    have Hcallee_safe := safe_typed_call_target_method_safe CT sGamma mt rΓ
      h x m y zs sGamma ly cy mdef Hcaller_wf Htyping Hsafe Hval_y Hbase
      Hfind_method.
    destruct (typed_call_target CT sGamma mt rΓ h x m y zs sGamma vals ly
      cy mdef Hcaller_wf Htyping Hval_y Hbase Hfind_method Hargs) as
      [declaring_class [declaring_def [body_end
        [Hruntime_sub [Hdeclaring_class [Hmethod_member
          [Hmethod_wf [Hbody_typing Hcallee_initial_wf]]]]]]]].
    unfold wf_method in Hmethod_wf. simpl in Hmethod_wf.
    destruct Hmethod_wf as
      [_ [method_end [body_return_type
        [Hmethod_body_typing [Hreturn_dom
          [Hreturn_type [Hbody_sub Hoverriding]]]]]]].
    destruct (potential_history_enter_call CT P Z cutoff authority sGamma mt
      rΓ h stack x m y zs sGamma vals ly cy mdef receiver_type Hstate
      Htyping Hsafe Hreceiver_type Hval_y Hbase Hfind_method Hargs) as
      [origins [entry_destination_type [Hentry_destination Hentry]]].
    assert (entry_destination_type = destination_type) by congruence.
    subst entry_destination_type.
    have Hbody_post := IHHeval eq_refl Heval P
      (mreceiver (msignature mdef) :: mparams (msignature mdef))
      (mscope (msignature mdef)) method_end
      (call_authority authority (sqtype receiver_type))
      (mk_watched_call_boundary
        (mk_watched_frame authority sGamma rΓ)
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins :: stack)
      Z cutoff Hentry Hmethod_body_typing Hcallee_safe.
    have Hsignature_safe :
        signature_has_no_mutable_roots (msignature mdef).
    { exact ((proj2 (proj2 Hoverriding)) Hcallee_safe). }
    have Hlive_start := proj1 Hstate.
    have Hauthority_start := proj1 Hlive_start.
    have Hcomponent_start := proj1 Hauthority_start.
    have Hcaller_zone : zone_env_safe Z sGamma rΓ :=
      proj1 (proj2 Hcomponent_start).
    have Hcaller_env : env_is_confined P cutoff rΓ :=
      proj1 (proj1 (proj2 (proj2 Hcomponent_start))).
    have Hcaller_final_wf := preservation_pico CT sGamma mt rΓ h
      (SCall x m y zs) (set_vars rΓ (update x retval (vars rΓ))) h' sGamma
      Hcaller_wf Htyping Heval_copy.
    assert (Hupdate : set_vars rΓ (update x retval (vars rΓ)) =
        update_r_env_value rΓ x retval).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate in Hcaller_final_wf |- *.
    destruct retval as [|return_location].
    + eapply potential_history_leave_call_null with
        (caller_h := h) (destination_type := destination_type)
        (receiver_type := receiver_type)
        (entry_senv := mreceiver (msignature mdef) ::
          mparams (msignature mdef))
        (entry_renv := mkr_env (Iot ly :: vals))
        (origins := origins) (callee_senv := method_end)
        (callee_renv := rΓ'') (callee_h := h'); eauto.
    + refine (potential_history_leave_call CT P Z cutoff authority sGamma rΓ
        h stack x destination_type y ly receiver_type
        (mreceiver (msignature mdef) :: mparams (msignature mdef))
        (mkr_env (Iot ly :: vals)) origins method_end rΓ'' h'
        (mreturn (mbody mdef)) body_return_type (msignature mdef)
        (msignature static_mdef) return_location Hcaller_zone Hcaller_env
        Hcaller_wf Hdestination_not_receiver Hdestination_type Hreceiver_type
        Hval_y Hreturn_type Hretval Hbody_sub Hsignature_refinement Hresult_sub
        Hbody_post Hcaller_final_wf _).
      intros Hdestination_rdm.
      have Hbody_live := proj1 Hbody_post.
      have Hbody_frames : live_frames_wf CT h'
          (mk_watched_frame
            (call_authority authority (sqtype receiver_type))
            method_end rΓ'')
          (mk_watched_call_boundary
            (mk_watched_frame authority sGamma rΓ)
            (mreceiver (msignature mdef) :: mparams (msignature mdef))
            (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
            stack) := proj1 (proj2 Hbody_live).
      have Hcallee_final_wf :
          wf_r_config CT method_end rΓ'' h' := proj1 Hbody_frames.
      have Hbody_sounds : live_frames_authority_sound h'
          (mk_watched_frame
            (call_authority authority (sqtype receiver_type))
            method_end rΓ'')
          (mk_watched_call_boundary
            (mk_watched_frame authority sGamma rΓ)
            (mreceiver (msignature mdef) :: mparams (msignature mdef))
            (mkr_env (Iot ly :: vals)) (sqtype receiver_type) (mreturn (mbody mdef)) (sqtype destination_type) (sqtype (mret (msignature mdef))) (dom h) origins ::
            stack) := proj1 (proj2 (proj2 Hbody_live)).
      have Hcaller_current_wf : wf_r_config CT sGamma rΓ h'.
      { exact (Forall_inv (proj2 Hbody_frames)). }
      have Hcaller_sound :
          authority_context_sound h' rΓ authority.
      { exact (Forall_inv (proj2 Hbody_sounds)). }
      have Hreceiver_nonbottom : sqtype receiver_type <> Bot.
      { eapply (wf_config_nonnull_variable_not_bot CT sGamma rΓ h y
          receiver_type ly); eauto. }
      have Hreturn_nonbottom : sqtype body_return_type <> Bot.
      { eapply (wf_config_nonnull_variable_not_bot CT method_end rΓ'' h'
          (mreturn (mbody mdef)) body_return_type return_location); eauto. }
      destruct (refined_call_rdm_result_classifies_body_return CT
        receiver_type body_return_type (msignature mdef)
        (msignature static_mdef) destination_type Hbody_sub
        Hsignature_refinement Hresult_sub Hreceiver_nonbottom
        Hreturn_nonbottom Hdestination_rdm) as
        [Hreceiver_rdm Hbody_cases].
      have Hcaller_receiver_root :
          typed_root RDM sGamma rΓ ly.
      { exists y, receiver_type. repeat split; assumption. }
      have Hcaller_result_root :
          typed_root RDM sGamma
            (update_r_env_value rΓ x (Iot return_location))
            return_location.
      { exists x, destination_type. repeat split; try assumption.
        have Hxdomain := Hdestination_type.
        apply static_getType_dom in Hxdomain.
        unfold wf_r_config in Hcaller_wf.
        destruct Hcaller_wf as [_ [_ [_ [_ [Hlength _]]]]].
        eapply runtime_getVal_update_same. lia. }
      destruct (extract_receiver_from_wf_config CT sGamma rΓ h Hcaller_wf)
        as [caller_this [caller_runtime
          [Hcaller_this [Hcaller_this_dom Hcaller_this_runtime]]]].
      have Hcaller_this_value :=
        get_this_var_mapping_runtime_getVal rΓ caller_this Hcaller_this.
      have Hcaller_post_this_value := runtime_getVal_update_diff rΓ x 0
        (Iot return_location) Hdestination_not_receiver.
      rewrite Hcaller_this_value in Hcaller_post_this_value.
      have Hreceiver_runtime := typed_rdm_root_matches_receiver_runtime CT
        sGamma rΓ h' caller_this caller_runtime ly Hcaller_current_wf
        Hcaller_this_value
        (ltac:(eapply eval_stmt_preserves_r_muttype; eauto))
        Hcaller_receiver_root.
      have Hreturn_runtime := typed_rdm_root_matches_receiver_runtime CT
        sGamma (update_r_env_value rΓ x (Iot return_location)) h'
        caller_this caller_runtime return_location Hcaller_final_wf
        Hcaller_post_this_value
        (ltac:(eapply eval_stmt_preserves_r_muttype; eauto))
        Hcaller_result_root.
      have Hincluded : Included Loc
          (live_capability_set CT h'
            (mk_watched_frame authority sGamma
              (update_r_env_value rΓ x (Iot return_location))) stack)
          (live_capability_set CT h'
            (mk_watched_frame
              (call_authority authority (sqtype receiver_type))
              method_end rΓ'')
            (mk_watched_call_boundary
              (mk_watched_frame authority sGamma rΓ)
              (mreceiver (msignature mdef) :: mparams (msignature mdef))
              (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
              (mreturn (mbody mdef)) (sqtype destination_type)
              (sqtype (mret (msignature mdef))) (dom h) origins ::
              stack)).
      { intros location Hlocation.
        eapply call_return_live_reachability_reflects_before_pop with
          (caller_h := h) (destination_type := destination_type)
          (receiver := y) (receiver_location := ly)
          (receiver_type := receiver_type)
          (entry_senv := mreceiver (msignature mdef) ::
            mparams (msignature mdef))
          (entry_renv := mkr_env (Iot ly :: vals)) (origins := origins)
          (callee_senv := method_end) (callee_renv := rΓ'')
          (return_var := mreturn (mbody mdef))
          (body_return_type := body_return_type)
          (runtime_sig := msignature mdef)
          (static_sig := msignature static_mdef)
          (return_location := return_location); eauto. }
      eapply classified_rdm_call_pop_merge_safe with
        (P := P) (Z := Z) (cutoff := cutoff) (stack := stack)
        (caller_authority := authority) (caller_senv := sGamma)
        (caller_renv := rΓ) (destination := x)
        (destination_type := destination_type) (receiver := y)
        (receiver_type := receiver_type) (receiver_location := ly)
        (callee_senv := method_end) (callee_renv := rΓ'')
        (return_var := mreturn (mbody mdef))
        (body_return_type := body_return_type)
        (return_location := return_location)
        (boundary :=
          mk_watched_call_boundary
            (mk_watched_frame authority sGamma rΓ)
            (mreceiver (msignature mdef) :: mparams (msignature mdef))
            (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
            (mreturn (mbody mdef)) (sqtype destination_type)
            (sqtype (mret (msignature mdef))) (dom h) origins);
        try reflexivity; try assumption.
      * rewrite Hreturn_runtime. rewrite Hreceiver_runtime. reflexivity.
      * destruct Hbody_cases as [Hbody_rdm | [Hbody_mut | Hbody_imm]].
        -- left. split; [exact Hbody_rdm|].
          simpl.
          eapply refined_call_rdm_rdm_body_signature_return with
            (receiver_type := receiver_type)
            (body_return_type := body_return_type)
            (static_sig := msignature static_mdef)
            (destination_type := destination_type); eauto.
        -- right. left. exact Hbody_mut.
        -- right. right. split; [exact Hbody_imm|].
          eapply typed_imm_root_runtime_immutable_live;
            [exact Hcallee_final_wf|].
          exists (mreturn (mbody mdef)), body_return_type.
          repeat split; [exact Hreturn_type|exact Hretval|exact Hbody_imm].
      * (* Residual under immutable caller authority with a covariant [Mut]
           body return.  The return value is a [Mut] root of the completed
           callee, hence one of its live capabilities, which settles the
           orientation whose protected endpoint hangs off the return.  The
           opposite orientation is the one genuine remaining obligation. *)
        intros Hauthority_imm Hbody_mut.
        intros capability protected Hcapability Hprotected Hbridge.
        have Hseparated := proj1 (proj2 Hbody_post).
        have Hreturn_capability :
            In Loc
              (live_capability_set CT h'
                (mk_watched_frame
                  (call_authority authority (sqtype receiver_type))
                  method_end rΓ'')
                (mk_watched_call_boundary
                  (mk_watched_frame authority sGamma rΓ)
                  (mreceiver (msignature mdef) :: mparams (msignature mdef))
                  (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
                  (mreturn (mbody mdef)) (sqtype destination_type)
                  (sqtype (mret (msignature mdef))) (dom h) origins ::
                  stack))
              return_location.
        { eapply typed_mut_root_is_active_live_capability.
          exists (mreturn (mbody mdef)), body_return_type.
          repeat split;
            [exact Hreturn_type|exact Hretval|exact Hbody_mut]. }
        destruct Hbridge as
          [[Hcap_receiver Hreturn_protected] |
           [Hcap_return Hreceiver_protected]].
        -- exact (Hseparated return_location protected Hreturn_capability
             Hprotected Hreturn_protected).
        -- (* Orientation B: an old caller capability would have to reach
              the fresh [Mut] return.  The RS freshness triple makes every
              potential step from an old runtime-mutable node land on an old
              node, so the return would be old -- contradicting its
              freshness. *)
           exfalso.
           (* the callee entry is channel-free *)
           destruct (refined_mut_return_call_has_channel_free_entry_shape CT
             sGamma mt rΓ h x m y zs vals ly receiver_type destination_type
             body_return_type mdef static_mdef Hcaller_wf Htyping Hsafe
             Hreceiver_type Hval_y Hargs Hfind_static Hbody_sub
             Hsignature_refinement Hresult_sub Hreceiver_nonbottom
             Hdestination_rdm Hbody_mut Hstatic_receiver_sub Hsignature_safe)
             as [Hreceiver_ro Hno_rdm_roots].
           (* seed the partition at the call entry: S = [], side = right *)
           have Hentry_J : rs_mut_vars_fresh h
               (mreceiver (msignature mdef) :: mparams (msignature mdef))
               (mkr_env (Iot ly :: vals)) h.
           { eapply rs_mut_vars_fresh_channel_free_entry; eauto. }
           have Hentry_pool : rs_pool_sided h [] true
               (mreceiver (msignature mdef) :: mparams (msignature mdef))
               (mkr_env (Iot ly :: vals)) h.
           { eapply rs_pool_right_from_mut_vars_fresh. exact Hentry_J. }
           have Hentry_stitch : rs_stitch_set_wf h h [].
           { intros l Hin. inversion Hin. }
           have Hentry_sides : rs_mut_edges_respect_sides CT h [] h.
           { eapply rs_mut_edges_respect_sides_entry.
             exact (proj1 (proj2 Hcaller_wf)). }
           destruct (rs_mutable_freshness_preserved CT
             (mkr_env (Iot ly :: vals)) h (mbody_stmt (Syntax.mbody mdef))
             rΓ'' h' Heval
             (mreceiver (msignature mdef) :: mparams (msignature mdef))
             (mscope (msignature mdef)) method_end h (@nil Loc) true
             Hmethod_body_typing Hcallee_safe Hcallee_initial_wf
             (le_n (dom h)) Hentry_stitch Hentry_sides Hentry_pool) as
             [Sf [_ [_ [_ [Hsides_f Hpool_f]]]]].
           (* the head boundary's callee return qualifier is Mut, not RDM *)
           have Hshape := refined_call_rdm_mut_body_signature_shape CT
             receiver_type body_return_type (msignature mdef)
             (msignature static_mdef) destination_type Hbody_sub
             Hsignature_refinement Hresult_sub Hreceiver_nonbottom
             Hdestination_rdm Hbody_mut.
           destruct Hshape as [_ Hmret_mut].
           (* stored caller frames hold only old values *)
           have Hframes_h : live_frames_wf CT h
               (mk_watched_frame authority sGamma rΓ) stack.
           { exact (proj1 (proj2 (proj1 Hstate))). }
           have Hstack_old : forall b,
               List.In b
                 (mk_watched_call_boundary
                   (mk_watched_frame authority sGamma rΓ)
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
                   (mreturn (mbody mdef)) (sqtype destination_type)
                   (sqtype (mret (msignature mdef))) (dom h) origins
                  :: stack) ->
               forall xv l,
                 runtime_getVal b.(boundary_caller).(frame_renv) xv
                   = Some (Iot l) ->
                 l < dom h.
           { intros b Hin xv l Hv.
             destruct Hin as [<- | Hin].
             - simpl in Hv.
               eapply wf_config_value_dom; [exact Hcaller_wf | exact Hv].
             - have Hb_wf : wf_r_config CT
                   b.(boundary_caller).(frame_senv)
                   b.(boundary_caller).(frame_renv) h.
               { have Hall := proj2 Hframes_h.
                 rewrite Forall_forall in Hall. exact (Hall b Hin). }
               eapply wf_config_value_dom; [exact Hb_wf | exact Hv]. }
           (* the capability's live root is old and runtime-mutable *)
           destruct Hcapability as [root [Hroot Hreach]].
           have Hcaller_post_frames : live_frames_wf CT h'
               (mk_watched_frame authority sGamma
                 (update_r_env_value rΓ x (Iot return_location))) stack.
           { split; [exact Hcaller_final_wf|].
             exact (Forall_inv_tail (proj2 Hbody_frames)). }
           have Hcaller_post_sound : live_frames_authority_sound h'
               (mk_watched_frame authority sGamma
                 (update_r_env_value rΓ x (Iot return_location))) stack.
           { split.
             - simpl. rewrite Hauthority_imm. intros Hbad. discriminate.
             - exact (Forall_inv_tail (proj2 Hbody_sounds)). }
           have Hroot_in_set : In Loc
               (live_capability_set CT h'
                 (mk_watched_frame authority sGamma
                   (update_r_env_value rΓ x (Iot return_location))) stack)
               root.
           { exists root. split; [exact Hroot | constructor]. }
           have Hroot_mut : r_muttype h' root = Some Mut_r.
           { eapply live_capability_members_runtime_mutable;
               [exact Hcaller_post_frames | exact Hcaller_post_sound
               | exact Hroot_in_set]. }
           have Hroot_old : root < dom h.
           { destruct Hroot as [Hactive | [b [Hin_b Hb_root]]].
             - destruct Hactive as [xv [T [Htype [Hvalue Hcap]]]].
               simpl in Htype, Hvalue.
               unfold capability_in_context in Hcap.
               rewrite Hauthority_imm in Hcap.
               destruct Hcap as [Hmutq | [_ Hbad]]; [|discriminate].
               destruct (Nat.eq_dec xv x) as [-> | Hneq].
               { rewrite Hdestination_type in Htype.
                 injection Htype as <-.
                 rewrite Hdestination_rdm in Hmutq. discriminate. }
               have Hxv : x <> xv by congruence.
               have Hd := runtime_getVal_update_diff rΓ x xv
                 (Iot return_location) Hxv.
               rewrite Hd in Hvalue.
               eapply wf_config_value_dom; [exact Hcaller_wf | exact Hvalue].
             - destruct Hb_root as [xv [T [Htype [Hvalue Hcap]]]].
               eapply Hstack_old with (b := b);
                 [right; exact Hin_b | exact Hvalue]. }
           (* compose: root reaches the return through the potential graph *)
           have Hroot_to_cap := retained_reachable_is_potential_connected CT
             h' (mk_watched_frame
                  (call_authority authority (sqtype receiver_type))
                  method_end rΓ'')
             (mk_watched_call_boundary
               (mk_watched_frame authority sGamma rΓ)
               (mreceiver (msignature mdef) :: mparams (msignature mdef))
               (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
               (mreturn (mbody mdef)) (sqtype destination_type)
               (sqtype (mret (msignature mdef))) (dom h) origins :: stack)
             root capability Hreach.
           have Hheap' : wf_heap CT h'.
           { exact (proj1 (proj2 Hcallee_final_wf)). }
           have Hhead_not_rdm :
               sqtype (mret (msignature mdef)) <> RDM.
           { rewrite Hmret_mut. discriminate. }
           have Hroot_left : rs_left h Sf root.
           { unfold rs_left. left. exact Hroot_old. }
           (* walk 1: the capability stays on the left side *)
           destruct (rs_potential_path_from_old_mut_stays_left CT h Sf h'
             (mk_watched_frame
               (call_authority authority (sqtype receiver_type))
               method_end rΓ'')
             (mk_watched_call_boundary
               (mk_watched_frame authority sGamma rΓ)
               (mreceiver (msignature mdef) :: mparams (msignature mdef))
               (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
               (mreturn (mbody mdef)) (sqtype destination_type)
               (sqtype (mret (msignature mdef))) (dom h) origins)
             stack root capability Hpool_f Hsides_f Hheap' Hbody_frames
             Hhead_not_rdm Hstack_old Hroot_to_cap Hroot_left Hroot_mut)
             as [Hcap_left Hcap_mut].
           (* walk 2: so would the return location be *)
           destruct (rs_potential_path_from_old_mut_stays_left CT h Sf h'
             (mk_watched_frame
               (call_authority authority (sqtype receiver_type))
               method_end rΓ'')
             (mk_watched_call_boundary
               (mk_watched_frame authority sGamma rΓ)
               (mreceiver (msignature mdef) :: mparams (msignature mdef))
               (mkr_env (Iot ly :: vals)) (sqtype receiver_type)
               (mreturn (mbody mdef)) (sqtype destination_type)
               (sqtype (mret (msignature mdef))) (dom h) origins)
             stack capability return_location Hpool_f Hsides_f Hheap'
             Hbody_frames Hhead_not_rdm Hstack_old Hcap_return Hcap_left
             Hcap_mut) as [Hret_left Hret_mut].
           (* but the callee's final pool places the Mut return strictly on
              the right side *)
           destruct (Hpool_f (mreturn (mbody mdef)) body_return_type
             return_location Hreturn_type Hretval (or_introl Hbody_mut)
             Hret_mut) as [Hret_ge Hret_nin].
           destruct Hret_left as [Hret_lt | Hret_in];
             [lia | exact (Hret_nin Hret_in)].
  - inversion Htyping; subst.
    eapply (IHHeval2 eq_refl Heval2 P).
    + eapply (IHHeval1 eq_refl Heval1 P); eauto.
    + exact Htype2.
    + exact Hsafe.
}
Qed.

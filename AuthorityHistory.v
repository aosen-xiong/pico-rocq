Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability AuthorityCapability.
Require Import ExecutionConfinement ProtectionHistory ComponentColoring.
Require Import ForwardCapabilityHistory.
From Stdlib Require Import List Lia Sets.Ensembles.
Import ListNotations.

(** The forward set [M] includes RDM roots exactly when the proof-only
    authority of the current frame is mutable. *)
Definition authority_env_roots_in
  (authority : q_r) (M : Ensemble Loc)
  (sGamma : s_env) (rGamma : r_env) : Prop :=
  forall root,
    (exists x T,
      static_getType sGamma x = Some T /\
      runtime_getVal rGamma x = Some (Iot root) /\
      capability_in_context authority (sqtype T)) ->
    In Loc M root.

Definition authority_component_history_state
  (CT : class_table) (P Z M : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  component_forward_history_state CT P Z M cutoff sGamma rGamma h /\
  authority_env_roots_in authority M sGamma rGamma /\
  authority_context_sound h rGamma authority.

Definition extend_capability_after_new_authority
  (M : Ensemble Loc) (authority : q_r) (qc : q_c) (fresh : Loc) :
  Ensemble Loc :=
  extend_authority_capability M authority qc fresh.

Lemma authority_new_extension_contains_old :
  forall M authority qc fresh,
    Included Loc M
      (extend_capability_after_new_authority M authority qc fresh).
Proof. intros M authority qc fresh l Hin. left. exact Hin. Qed.

Lemma authority_extension_matches_static_mut_extension :
  forall M authority qc fresh,
    (authority <> Mut_r \/ qc <> RDM_c) ->
    Same_set Loc
      (extend_capability_after_new_authority M authority qc fresh)
      (extend_capability_after_new M qc fresh).
Proof.
  intros M authority qc fresh Hnotcase.
  split; intros l Hin.
  - destruct Hin as [Hold | [Hcap Heq]]; [left; exact Hold|].
    unfold capability_in_context in Hcap.
    destruct authority, qc; simpl in Hcap.
    + right. split; [reflexivity|exact Heq].
    + destruct Hcap as [Hbad | [Hbad _]]; discriminate.
    + exfalso. destruct Hnotcase as [Hbad | Hbad]; apply Hbad; reflexivity.
    + right. split; [reflexivity|exact Heq].
    + destruct Hcap as [Hbad | [Hbad _]]; discriminate.
    + destruct Hcap as [Hbad | [_ Hbad]]; discriminate.
  - destruct Hin as [Hold | [Hmut Heq]]; [left; exact Hold|].
    subst qc. right. split; [|exact Heq].
    unfold capability_in_context. left. reflexivity.
Qed.

Lemma initial_authority_component_history :
  forall CT sGamma rGamma h,
    wf_r_config CT sGamma rGamma h ->
    env_respects_protected_set
      (reachable_locations_from_initial_env CT h rGamma) sGamma rGamma ->
    authority_component_history_state CT
      (reachable_locations_from_initial_env CT h rGamma)
      (reachable_locations_from_initial_env CT h rGamma)
      (Empty_set Loc) (dom h) Imm_r sGamma rGamma h.
Proof.
  intros CT sGamma rGamma h Hwf Henv.
  have Hcomponent := initial_component_forward_history CT sGamma rGamma h
    Hwf Henv.
  have Hcomponent_copy := Hcomponent.
  destruct Hcomponent as
    [[Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Hforwardcolors]]]]]]]
      [Hcomponents Hactive]].
  split; [exact Hcomponent_copy|]. split.
  - intros root [x [T [Htype [Hval Hcap]]]].
    destruct Hcap as [Hmut | [Hrdm Hbad]].
    + apply Hmutroots.
      exists x, T. repeat split; assumption.
    + discriminate.
  - intros Hbad. discriminate.
Qed.

Lemma authority_expression_capability_in_history :
  forall P Z M cutoff CT authority sGamma mt rGamma h e l T,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    eval_expr OK CT rGamma h e (Iot l) OK rGamma h ->
    expr_has_type CT sGamma mt e T ->
    safe_readonly_method_type mt ->
    capability_in_context authority (sqtype T) ->
    In Loc M l.
Proof.
  intros P Z M cutoff CT authority sGamma mt rGamma h e l T Hwf
    [Hcomponent [Hroots Hsound]] Heval Htyping Hscope Hcap.
  destruct Hcomponent as
    [[Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Hseparated]]]]]]]
      [Hcomponents Hactive]].
  inversion Heval; subst.
  - inversion Htyping; subst.
    apply Hroots. exists x, T. repeat split; assumption.
  - inversion Htyping; subst.
    + exfalso. destruct Hscope as [Hnot_abs _]. congruence.
    + assert (Hshape :
        mutability (ftype fDef) = RDM_f /\
        capability_in_context authority (sqtype T0)).
      { destruct Hcap as [Hout | [Hout Hauth]];
        destruct authority;
        destruct (sqtype T0) eqn:Hreceiver;
        destruct (mutability (ftype fDef)) eqn:Hfieldqual;
        simpl in Hout; try discriminate;
        split; auto;
        unfold capability_in_context; auto. }
      destruct Hshape as [Hrdm Hreceiver_cap].
      have HreceiverM : In Loc M v.
      { apply Hroots. exists x, T0. repeat split; assumption. }
      eapply Hclosed; [exact HreceiverM|].
      eapply runtime_static_rdm_edge; eauto.
Qed.

Lemma authority_history_after_assignment :
  forall CT P Z M cutoff authority sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    safe_readonly_method_type mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr OK CT rGamma h e value OK rGamma h ->
    authority_component_history_state CT P Z M cutoff authority sGamma
      (update_r_env_value rGamma x value) h.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x e old value Hwf
    [Hcomponent [Hroots Hsound]] Htyping Hscope Hx Heval.
  split.
  - eapply component_forward_history_after_assignment; eauto.
  - split.
    + intros root [y [Ty [Htype [Hval Hcap]]]].
      destruct (Nat.eq_dec y x) as [->|Hneq].
      * inversion Htyping; subst.
        assert (Hxdom : x < dom (vars rGamma)).
        { apply static_getType_dom in Hget_x.
          have Hwf_length := Hwf.
          unfold wf_r_config in Hwf_length.
          destruct Hwf_length as [_ [_ [_ [_ [Hlen _]]]]]. lia. }
        rewrite runtime_getVal_update_same in Hval; auto.
        destruct value as [|result|n]; try discriminate.
        injection Hval as <-. rewrite Hget_x in Htype. injection Htype as <-.
        destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
          as [this [qcontext [Hrthis [_ Hqcontext]]]].
        pose proof (expr_eval_preservation CT sGamma mt rGamma h e
          (Iot result) rGamma h Te this qcontext Hrthis Hqcontext Hwf Htype_e
          Heval) as Htypable.
        have Hexprcap := nonnull_subtype_preserves_authority_capability
          CT rGamma h result Te Tx qcontext authority Htypable Hsub Hcap.
        eapply authority_expression_capability_in_history
          with (P := P) (Z := Z) (cutoff := cutoff) (CT := CT)
            (authority := authority) (sGamma := sGamma) (mt := mt)
            (rGamma := rGamma) (h := h) (e := e) (T := Te); eauto.
        exact (conj Hcomponent (conj Hroots Hsound)).
      * rewrite runtime_getVal_update_diff in Hval; auto.
        apply Hroots. exists y, Ty. repeat split; assumption.
    + intros Hauth.
      specialize (Hsound Hauth).
      destruct Hsound as [this [Hthis Hmut]]. exists this. split; [|exact Hmut].
      inversion Htyping; subst.
      unfold update_r_env_value. destruct rGamma; simpl in *.
      rewrite get_this_var_mapping_update_nonzero; assumption.
Qed.

Lemma authority_history_after_local :
  forall CT P Z M cutoff authority sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    authority_component_history_state CT P Z M cutoff authority sGamma'
      (set_vars rGamma (vars rGamma ++ [default_value T])) h.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h T x sGamma' Hwf
    [Hcomponent [Hroots Hsound]] Htyping Hnone.
  split.
  - eapply component_forward_history_after_local; eauto.
  - split.
    + intros root [y [Ty [Htype [Hval Hcap]]]].
      inversion Htyping; subst.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
      destruct (appended_nonlocation_lookup_is_old sGamma rGamma T
        (default_value T) y Ty root (default_value_not_location T)
        Hlength Htype Hval) as [Holdtype Holdval].
      apply Hroots. exists y, Ty. repeat split; assumption.
    + intros Hauth. specialize (Hsound Hauth).
      destruct Hsound as [this [Hthis Hmut]]. exists this. split; [|exact Hmut].
      rewrite get_this_var_mapping_update_vars_app_default. exact Hthis.
Qed.

Lemma authority_history_after_field_write :
  forall CT P Z M cutoff authority sGamma mt rGamma h x f y rGamma' h'
    sGamma',
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    safe_readonly_method_type mt ->
    eval_stmt OK CT rGamma h (SFldWrite x f y) OK rGamma' h' ->
    exists M',
      Included Loc M M' /\
      authority_component_history_state CT P Z M' cutoff authority
        sGamma' rGamma' h'.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x f y rGamma' h'
    sGamma' Hwf [Hcomponent [Hroots Hsound]] Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  destruct (component_forward_history_after_field_write CT P Z M cutoff
    sGamma mt rGamma h x f y rGamma h' sGamma Hwf Hcomponent Htyping
    Hscope Heval) as [M' [Hincl Hcomponent']].
  exists M'. split; [exact Hincl|]. split; [exact Hcomponent'|]. split.
  - intros root [z [T [Htype [Hval Hcap]]]].
    inversion Heval; subst. apply Hincl. apply Hroots.
    exists z, T. repeat split; assumption.
  - intros Hauth. specialize (Hsound Hauth).
    destruct Hsound as [this [Hthis Hmut]]. exists this. split; [exact Hthis|].
    inversion Heval; subst. rewrite r_muttype_update_field_preserve. exact Hmut.
Qed.

Lemma mutable_authority_matches_runtime_receiver :
  forall h rGamma this qthis,
    authority_context_sound h rGamma Mut_r ->
    runtime_getVal rGamma 0 = Some (Iot this) ->
    r_muttype h this = Some qthis ->
    qthis = Mut_r.
Proof.
  intros h rGamma this qthis Hsound Hvalue Hqthis.
  destruct (Hsound eq_refl) as [receiver [Hreceiver Hmut]].
  unfold runtime_getVal in Hvalue.
  unfold get_this_var_mapping in Hreceiver.
  destruct (vars rGamma) as [|v values]; simpl in *; try discriminate.
  injection Hvalue as Hv. subst v.
  injection Hreceiver as Hr. subst receiver. congruence.
Qed.

Lemma authority_env_roots_after_new :
  forall CT M authority sGamma mt rGamma h x qc C args sGamma',
    wf_r_config CT sGamma rGamma h ->
    authority_env_roots_in authority M sGamma rGamma ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    authority_env_roots_in authority
      (extend_capability_after_new_authority M authority qc (dom h))
      sGamma' (update_r_env_value rGamma x (Iot (dom h))).
Proof.
  intros CT M authority sGamma mt rGamma h x qc C args sGamma' Hwf
    Hroots Htyping root [z [T [Htype [Hval Hcap]]]].
  destruct (new_typed_root_origin CT sGamma mt rGamma h x qc C args
    sGamma' (sqtype T) root Hwf Htyping
    (ltac:(exists z, T; repeat split; assumption))) as
    [Hold | [Hfresh [Tx [Hgetx Hqual]]]].
  - left. apply Hroots. destruct Hold as [oldz [OldT
      [Holdtype [Holdval Holdqual]]]].
    exists oldz, OldT. repeat split; try assumption.
    rewrite Holdqual. exact Hcap.
  - right. split; [|exact Hfresh].
    assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
    destruct Hcap as [Hmut | [Hrdm Hauthority]].
    + assert (Hcreation : qc2q qc = Mut).
      { eapply new_mut_result_requires_mut_creation with (Tx := Tx).
        - exact Htyping.
        - rewrite HsGamma. exact Hgetx.
        - rewrite Hqual. exact Hmut. }
      unfold capability_in_context. left. exact Hcreation.
    + assert (Hcreation : qc2q qc = RDM).
      { eapply new_rdm_result_requires_rdm_creation with (Tx := Tx).
        - exact Htyping.
        - rewrite HsGamma. exact Hgetx.
        - rewrite Hqual. exact Hrdm. }
      unfold capability_in_context. right. split; assumption.
Qed.

Lemma authority_new_extension_runtime_mutable :
  forall h M authority rGamma qc C vals qthis qruntime this,
    mutable_members_runtime_mut h M ->
    authority_context_sound h rGamma authority ->
    runtime_getVal rGamma 0 = Some (Iot this) ->
    r_muttype h this = Some qthis ->
    vpa_mutability_object_creation qthis qc = qruntime ->
    mutable_members_runtime_mut
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new_authority M authority qc (dom h)).
Proof.
  intros h M authority rGamma qc C vals qthis qruntime this Hruntime Hsound
    Hthis Hqthis Hadapt location [Hold | [Hcap Hfresh]].
  - specialize (Hruntime location Hold).
    unfold r_muttype, r_type in *.
    destruct (runtime_getObj h location) as [old|] eqn:Hobj;
      try discriminate.
    have Hlocation := Hobj. apply runtime_getObj_dom in Hlocation.
    erewrite runtime_getObj_last2; [|exact Hlocation]. rewrite Hobj.
    exact Hruntime.
  - subst location. unfold r_muttype, r_type. rewrite runtime_getObj_last. simpl.
    destruct qc.
    + destruct qthis; simpl in Hadapt; subst qruntime; reflexivity.
    + unfold capability_in_context in Hcap.
      destruct Hcap as [Hbad | [Hbad _]]; discriminate.
    + unfold capability_in_context in Hcap.
      destruct Hcap as [Hbad | [Hrdm Hauthority]]; [discriminate|].
      subst authority.
      have Hqthis_mut := mutable_authority_matches_runtime_receiver h rGamma
        this qthis Hsound Hthis Hqthis.
      subst qthis. simpl in Hadapt. subst qruntime. reflexivity.
Qed.

Lemma authority_new_extension_closed :
  forall CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    mutable_heap_closed CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new_authority M authority qc (dom h)).
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime Hwf
    [[[Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Hforwardcolors]]]]]]]
      [Hcomponents Hactive]] [Hroots Hsound]]
    Htyping Hvals source target [Hsource | [Hcap Hsourcefresh]] Hedge.
  - destruct (mutable_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) source target Hedge) as
      [Holdedge | [Hfresh _]].
    + left. eapply Hclosed; eauto.
    + subst source. exfalso. eapply old_mutable_member_not_fresh; eauto.
  - subst source.
    destruct (mutable_edge_after_append CT h
      (mkObj (mkruntime_type qruntime C) vals) (dom h) target Hedge) as
      [Holdedge | [Hfresh [field [D [fdef [Hfield [Hsub
        [Hfd Hrdm]]]]]]]].
    + inversion Holdedge as [? ? old oldfield oldD oldfdef Hobj Hvalue
        Holdsub Holdfd Holdrdm]; subst.
      apply runtime_getObj_dom in Hobj. lia.
    + left. apply Hroots.
      assert (HfdC : sf_def_rel CT C field fdef).
      { eapply field_inheritance_subtyping; eauto. }
      have Htarget := new_creation_rdm_field_target_has_creation_root CT
        sGamma mt rGamma h x qc C args sGamma' vals field fdef target Hwf
        Htyping Hvals Hfield HfdC Hrdm.
      destruct Htarget as [z [T [Htype [Hval Hqual]]]].
      exists z, T. repeat split; try assumption.
      rewrite Hqual. exact Hcap.
Qed.

Lemma authority_component_colors_after_new :
  forall CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    component_colors_separated CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new_authority M authority qc (dom h)) Z.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime Hwf
    [Hcomponent [Hroots Hsound]] Htyping Hvals HfreshZ
    capability protected [Hcapability | [Hcap Hcapfresh]] Hprotected
    Hconnected.
  - have Hexisting := component_colors_after_new_existing_sets CT P Z M
      cutoff sGamma mt rGamma h x qc C args sGamma' vals qruntime Hwf
      Hcomponent Htyping Hvals HfreshZ.
    exact (Hexisting capability protected Hcapability Hprotected Hconnected).
  - subst capability.
    assert (Hfresh_touches : component_touches CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals]) Z (dom h)).
    { exists protected. split; assumption. }
    destruct (fresh_component_touches_old_set_has_creation_root CT sGamma mt
      rGamma h x qc C args sGamma' vals qruntime Z Hwf Htyping Hvals
      HfreshZ Hfresh_touches) as [target [Htarget HtargetZ]].
    have HtargetM : In Loc M target.
    { apply Hroots. destruct Htarget as [z [T [Htype [Hval Hqual]]]].
      exists z, T. repeat split; try assumption. rewrite Hqual. exact Hcap. }
    destruct Hcomponent as [Hforward [Hcomponents Hactive]].
    eapply separated_components_cannot_touch_both with (root := target).
    + exact Hcomponents.
    + exists target. split; [exact HtargetM|apply mutable_connected_refl].
    + exact HtargetZ.
Qed.

Lemma authority_active_colors_after_new :
  forall CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    active_rdm_component_colors_separated CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new_authority M authority qc (dom h)) Z
      sGamma' (update_r_env_value rGamma x (Iot (dom h))).
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime Hwf Hstate Htyping Hvals HfreshZ.
  destruct authority.
  - have Hpostroots := authority_env_roots_after_new CT M Mut_r sGamma mt
      rGamma h x qc C args sGamma' Hwf (proj1 (proj2 Hstate)) Htyping.
    have Hcomponents := authority_component_colors_after_new CT P Z M cutoff
      Mut_r sGamma mt rGamma h x qc C args sGamma' vals qruntime Hwf Hstate
      Htyping Hvals HfreshZ.
    intros capability_root zone_root Hcaproot Hcapability Hzoneroot
      [protected [Hprotected Hzoneconnected]].
    have HzoneM : In Loc
      (extend_capability_after_new_authority M Mut_r qc (dom h)) zone_root.
    { apply Hpostroots. destruct Hzoneroot as [z [T [Htype [Hval Hrdm]]]].
      exists z, T. repeat split; try assumption.
      rewrite Hrdm. unfold capability_in_context. right. split; reflexivity. }
    exact (Hcomponents zone_root protected HzoneM Hprotected Hzoneconnected).
  - have Heq := authority_extension_matches_static_mut_extension M Imm_r qc
      (dom h) (ltac:(left; discriminate)).
    have Hstatic := active_rdm_colors_after_new CT P Z M cutoff sGamma mt
      rGamma h x qc C args sGamma' vals qruntime Hwf (proj1 Hstate) Htyping
      Hvals HfreshZ.
    intros capability_root zone_root Hcaproot
      [capability [Hcapability Hcapconnected]] Hzoneroot Hzonetouch.
    eapply Hstatic with (capability_root := capability_root)
      (zone_root := zone_root); eauto.
    exists capability. split; [exact ((proj1 Heq) capability Hcapability)|].
    exact Hcapconnected.
Qed.

Lemma authority_context_sound_after_new :
  forall CT authority sGamma mt rGamma h x qc C args sGamma'
    vals qthis qruntime this,
    wf_r_config CT sGamma rGamma h ->
    authority_context_sound h rGamma authority ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_getVal rGamma 0 = Some (Iot this) ->
    r_muttype h this = Some qthis ->
    authority_context_sound
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (update_r_env_value rGamma x (Iot (dom h))) authority.
Proof.
  intros CT authority sGamma mt rGamma h x qc C args sGamma' vals qthis
    qruntime this Hwf Hsound Htyping Hthis Hqthis Hauthority.
  destruct (Hsound Hauthority) as [receiver [Hreceiver Hreceiver_mut]].
  exists receiver. split.
  - inversion Htyping; subst.
    unfold update_r_env_value. destruct rGamma; simpl in *.
    rewrite get_this_var_mapping_update_nonzero; assumption.
  - rewrite r_muttype_app_preserve_old.
    + unfold r_muttype, r_type in Hreceiver_mut.
      destruct (runtime_getObj h receiver) eqn:Hobj; try discriminate.
      apply runtime_getObj_dom in Hobj. exact Hobj.
    + exact Hreceiver_mut.
Qed.

Lemma authority_history_after_new :
  forall CT P Z M cutoff authority sGamma mt rGamma h x qc C args rGamma'
    h' sGamma',
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    cutoff <= dom h ->
    ~ In Loc Z (dom h) ->
    eval_stmt OK CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    exists M',
      Included Loc M M' /\
      authority_component_history_state CT P Z M' cutoff authority
        sGamma' rGamma' h'.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x qc C args rGamma'
    h' sGamma' Hwf Hstate Htyping Hcutoff HfreshZ Heval.
  have Hcomponent := proj1 Hstate.
  have Hcomponent_base := component_forward_history_after_new CT P Z M cutoff
    sGamma mt rGamma h x qc C args rGamma' h' sGamma' Hwf Hcomponent Htyping
    Hcutoff HfreshZ Heval.
  inversion Heval; subst.
  assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
  subst sGamma'.
  set (qruntime := vpa_mutability_object_creation qthisr qc).
  set (newobj := mkObj (mkruntime_type qruntime C) vals).
  assert (Hnewobj :
    mkObj (mkruntime_type (vpa_mutability_object_creation qthisr qc) C) vals
      = newobj) by reflexivity.
  assert (Hnewenv :
    set_vars rGamma (update x (Iot (dom h)) (vars rGamma)) =
      update_r_env_value rGamma x (Iot (dom h))) by
    (destruct rGamma; reflexivity).
  rewrite Hnewobj in Hcomponent_base. rewrite Hnewenv in Hcomponent_base.
  destruct Hcomponent_base as [Mbase [Hbase_include Hbase_state]].
  exists (extend_capability_after_new_authority M authority qc (dom h)).
  split; [apply authority_new_extension_contains_old|].
  have Hclosed' := authority_new_extension_closed CT P Z M cutoff authority
    sGamma mt rGamma h x qc C args sGamma vals qruntime Hwf Hstate Htyping
    Hargs.
  have Hruntime' := authority_new_extension_runtime_mutable h M authority
    rGamma qc C vals qthisr qruntime l1
    (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 (proj1 Hstate)))))))
    (proj2 (proj2 Hstate)) Hthis Hmut (ltac:(unfold qruntime; reflexivity)).
  have Hroots' := authority_env_roots_after_new CT M authority sGamma mt
    rGamma h x qc C args sGamma Hwf (proj1 (proj2 Hstate)) Htyping.
  have Hcomponents' := authority_component_colors_after_new CT P Z M cutoff
    authority sGamma mt rGamma h x qc C args sGamma vals qruntime Hwf Hstate
    Htyping Hargs HfreshZ.
  have Hactive' := authority_active_colors_after_new CT P Z M cutoff
    authority sGamma mt rGamma h x qc C args sGamma vals qruntime Hwf Hstate
    Htyping Hargs HfreshZ.
  have Hcontext' := authority_context_sound_after_new CT authority sGamma mt
    rGamma h x qc C args sGamma vals qthisr qruntime l1 Hwf
    (proj2 (proj2 Hstate)) Htyping Hthis Hmut.
  destruct Hbase_state as
    [[Hcontains' [Hzone' [Hconfined' [Hbaseclosed [Hbaseruntime
      [Hbasemutroots [Hbaseavoid Hbaseforwardcolors]]]]]]]
      [Hbasecomponents Hbaseactive]].
  destruct Hstate as
    [[[Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Hforwardcolors]]]]]]]
      [Hcomponents Hactive]] [Hroots Hcontext]].
  rewrite Hnewenv.
  split.
  - split.
    + refine (conj Hcontains' (conj Hzone' (conj Hconfined'
        (conj Hclosed' (conj Hruntime' (conj _ (conj _ _))))))).
      * intros root Hroot. apply Hroots'.
        destruct Hroot as [z [T [Htype [Hval Hmutq]]]].
        exists z, T. repeat split; try assumption.
        unfold capability_in_context. left. exact Hmutq.
      * intros location [Hold | [Hcap ->]].
        -- eapply Havoid; eauto.
        -- exact HfreshZ.
      * eapply active_component_colors_imply_rdm_separation; eauto.
    + split; assumption.
  - split; assumption.
Qed.

Lemma safe_call_callee_authority_roots :
  forall CT P Z M cutoff caller_authority sGamma mt rGamma h x y m args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff caller_authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
    safe_readonly_method_type mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_env_roots_in (call_authority caller_authority (sqtype Ty)) M
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)).
Proof.
  intros CT P Z M cutoff caller_authority sGamma mt rGamma h x y m args
    sGamma' vals ly cy runtime_mdef Ty Hwf
    [Hcomponent [Hroots Hsound]] Htyping Hscope Hgety Hval Hbase Hfind
    Hargs root [z [T [Htype [Hrootval Hcap]]]].
  destruct Hcap as [Hmut | [Hrdm Hcallee_mut]].
  - exfalso. eapply safe_call_callee_has_no_mut_root with
      (CT := CT) (sGamma := sGamma) (mt := mt) (rGamma := rGamma)
      (h := h) (x := x) (m := m) (y := y) (args := args)
      (sGamma' := sGamma') (vals := vals) (ly := ly) (cy := cy)
      (runtime_mdef := runtime_mdef) (root := root); eauto.
    exists z, T. repeat split; assumption.
  - assert (Hrootrdm : typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) root).
    { exists z, T. repeat split; assumption. }
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x y m
      args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope Hval Hbase
      Hfind Hargs Hrootrdm) as
      [[Ty0 [Hgety0 [Hshape Hcallerroot]]] |
       [Ty0 [Hgety0 [Hro Hroot]]]].
    + assert (Ty0 = Ty) by congruence. subst Ty0.
      apply Hroots. destruct Hcallerroot as
        [caller_var [CallerT [Hcaller_type [Hcaller_val Hcaller_qual]]]].
      exists caller_var, CallerT. repeat split; try assumption.
      rewrite Hcaller_qual.
      eapply safe_call_receiver_authority_reflects.
      * eapply wf_config_nonnull_variable_not_bot; eauto.
      * unfold capability_in_context. right. split; [reflexivity|].
        exact Hcallee_mut.
    + assert (Ty0 = Ty) by congruence. subst Ty0.
      rewrite Hro in Hcallee_mut. simpl in Hcallee_mut. discriminate.
Qed.

Lemma safe_call_callee_authority_context :
  forall CT P Z M cutoff caller_authority sGamma mt rGamma h x y m args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff caller_authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
    safe_readonly_method_type mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_context_sound h (mkr_env (Iot ly :: vals))
      (call_authority caller_authority (sqtype Ty)).
Proof.
  intros CT P Z M cutoff caller_authority sGamma mt rGamma h x y m args
    sGamma' vals ly cy runtime_mdef Ty Hwf
    [Hcomponent [Hroots Hsound]] Htyping Hscope Hgety Hval Hbase Hfind
    Hargs Hcallee_mut.
  exists ly. split; [reflexivity|].
  destruct Hcomponent as
    [[Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots [Havoid Hforwardcolors]]]]]]]
      [Hcomponents Hactive]].
  apply Hruntime. apply Hroots.
  exists y, Ty. repeat split; try assumption.
  eapply safe_call_receiver_authority_reflects.
  - eapply wf_config_nonnull_variable_not_bot; eauto.
  - unfold capability_in_context. right. split; [reflexivity|].
    exact Hcallee_mut.
Qed.

Lemma authority_history_enter_call :
  forall CT P Z M cutoff caller_authority sGamma mt rGamma h x y m args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff caller_authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x y m args) sGamma' ->
    safe_readonly_method_type mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_component_history_state CT P Z M cutoff
      (call_authority caller_authority (sqtype Ty))
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) h.
Proof.
  intros CT P Z M cutoff caller_authority sGamma mt rGamma h x y m args
    sGamma' vals ly cy runtime_mdef Ty Hwf Hstate Htyping Hscope Hgety Hval
    Hbase Hfind Hargs.
  split.
  - eapply safe_call_callee_component_forward_history; eauto.
    exact (proj1 Hstate).
  - split.
    + eapply safe_call_callee_authority_roots; eauto.
    + eapply safe_call_callee_authority_context; eauto.
Qed.

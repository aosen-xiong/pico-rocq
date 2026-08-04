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

(** Authority controls which RDM roots are capabilities, but not which RDM
    roots may be joined by a future write.  ReadonlyState may update an
    Assignable RDM field; such a write must not leak a protected reference
    into a component retained by a suspended mutable caller.  Component and
    active-frame colors are therefore unconditional. *)
Definition authority_component_colors
  (CT : class_table) (h : heap) (authority : q_r)
  (M Z : Ensemble Loc) (sGamma : s_env) (rGamma : r_env) : Prop :=
  component_colors_separated CT h M Z /\
  active_rdm_component_colors_separated CT h M Z sGamma rGamma.

(** The unconditional part of the history contains only facts about actual
    capabilities and actual protected state.  It deliberately excludes every
    condition whose purpose is to anticipate a future RDM write. *)
Definition directed_authority_history_state
  (CT : class_table) (P Z M : Ensemble Loc) (cutoff : Loc)
  (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  protected_zone_contains P Z /\
  zone_env_safe Z sGamma rGamma /\
  state_is_confined P cutoff rGamma h /\
  mutable_heap_closed CT h M /\
  mutable_members_runtime_mut h M /\
  env_mut_roots_in M sGamma rGamma /\
  (forall l, In Loc M l -> ~ In Loc Z l).

Lemma forward_history_implies_directed_authority_history :
  forall CT P Z M cutoff sGamma rGamma h,
    forward_history_state CT P Z M cutoff sGamma rGamma h ->
    directed_authority_history_state CT P Z M cutoff sGamma rGamma h.
Proof.
  intros CT P Z M cutoff sGamma rGamma h
    [Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hroots [Havoid Hrdm]]]]]]].
  exact (conj Hcontains (conj Hzone (conj Hconfined
    (conj Hclosed (conj Hruntime (conj Hroots Havoid)))))).
Qed.

Lemma directed_authority_history_with_rdm :
  forall CT P Z M cutoff sGamma rGamma h,
    directed_authority_history_state CT P Z M cutoff sGamma rGamma h ->
    rdm_capability_zone_separated CT h M Z sGamma rGamma ->
    forward_history_state CT P Z M cutoff sGamma rGamma h.
Proof.
  intros CT P Z M cutoff sGamma rGamma h
    [Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hroots Havoid]]]]]] Hrdm.
  exact (conj Hcontains (conj Hzone (conj Hconfined
    (conj Hclosed (conj Hruntime (conj Hroots (conj Havoid Hrdm))))))).
Qed.

Definition authority_component_history_state
  (CT : class_table) (P Z M : Ensemble Loc) (cutoff : Loc)
  (authority : q_r) (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  directed_authority_history_state CT P Z M cutoff sGamma rGamma h /\
  authority_env_roots_in authority M sGamma rGamma /\
  authority_context_sound h rGamma authority /\
  authority_component_colors CT h authority M Z sGamma rGamma.

Lemma mutable_authority_component_history :
  forall CT P Z M cutoff authority sGamma rGamma h,
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h.
Proof.
  intros CT P Z M cutoff authority sGamma rGamma h
    [Hdirected [Hroots [Hsound Hcolors]]].
  destruct Hcolors as [Hcomponents Hactive].
  split.
  - eapply directed_authority_history_with_rdm; [exact Hdirected|].
    eapply active_component_colors_imply_rdm_separation; eauto.
  - split; assumption.
Qed.

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
      (reachable_locations_from_initial_env h rGamma) sGamma rGamma ->
    authority_component_history_state CT
      (reachable_locations_from_initial_env h rGamma)
      (reachable_locations_from_initial_env h rGamma)
      (Empty_set Loc) (dom h) Imm_r sGamma rGamma h.
Proof.
  intros CT sGamma rGamma h Hwf Henv.
  have Hcomponent := initial_component_forward_history CT sGamma rGamma h
    Hwf Henv.
  destruct Hcomponent as
    [Hforward [Hcomponents Hactive]].
  have Hforward_copy := Hforward.
  destruct Hforward as
    [Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]].
  split.
  - eapply forward_history_implies_directed_authority_history.
    exact Hforward_copy.
  - split.
    + intros root [x [T [Htype [Hval Hcap]]]].
      destruct Hcap as [Hmut | [Hrdm Hbad]].
      * apply Hmutroots.
        exists x, T. repeat split; assumption.
      * discriminate.
    + split.
      * intros Hbad. discriminate.
      * split; assumption.
Qed.

Lemma authority_expression_capability_in_history :
  forall P Z M cutoff CT authority sGamma mt rGamma h e l T,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    retained_heap_closed CT h M ->
    eval_expr CT rGamma h e (Iot l) OK rGamma h ->
    expr_has_type CT sGamma mt e T ->
    readonly_state_method_scope mt ->
    capability_in_context authority (sqtype T) ->
    In Loc M l.
Proof.
  intros P Z M cutoff CT authority sGamma mt rGamma h e l T Hwf
    [Hforward [Hroots [Hsound Hcolors]]]
    Hretained Heval Htyping Hscope Hcap.
  destruct Hforward as
    [Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]].
  inversion Heval; subst.
  - inversion Htyping; subst.
    apply Hroots. exists x, T. repeat split; assumption.
  - inversion Htyping; subst.
    + exfalso. destruct Hmt; subst; destruct Hscope; congruence.
    + assert (Hshape :
        (mutability (ftype fDef) = RDM_f /\
         capability_in_context authority (sqtype T0)) \/
        (mutability (ftype fDef) = Mut_f /\ sqtype T0 = Mut)).
      { destruct Hcap as [Hout | [Hout Hauth]];
        destruct authority;
        destruct (sqtype T0) eqn:Hreceiver;
        destruct (mutability (ftype fDef)) eqn:Hfieldqual;
        simpl in Hout; try discriminate; auto;
        unfold capability_in_context; auto. }
      destruct Hshape as [[Hrdm Hreceiver_cap] | [Hmut Hreceiver]].
      * have HreceiverM : In Loc M v.
        { apply Hroots. exists x, T0. repeat split; assumption. }
        eapply Hclosed; [exact HreceiverM|].
        eapply runtime_static_rdm_edge; eauto.
      * have HreceiverM : In Loc M v.
        { apply Hroots. exists x, T0. repeat split; try assumption.
          unfold capability_in_context. left. exact Hreceiver. }
        eapply Hretained; [exact HreceiverM|].
        eapply runtime_static_mut_field_edge; eauto.
Qed.

Lemma directed_expression_into_zone_has_safe_type :
  forall P Z M cutoff CT sGamma mt rGamma h e l T,
    wf_r_config CT sGamma rGamma h ->
    directed_authority_history_state CT P Z M cutoff sGamma rGamma h ->
    retained_heap_closed CT h M ->
    eval_expr CT rGamma h e (Iot l) OK rGamma h ->
    expr_has_type CT sGamma mt e T ->
    readonly_state_method_scope mt ->
    In Loc Z l ->
    is_nonmutable_qualifier (sqtype T).
Proof.
  intros P Z M cutoff CT sGamma mt rGamma h e l T Hwf
    [Hcontains [Henv [Hconfined [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]] Hretained Heval Htyping Hscope HinZ.
  inversion Heval; subst.
  - inversion Htyping; subst.
    destruct (sqtype T) eqn:Hq; unfold is_nonmutable_qualifier; auto.
    + exfalso. apply (Havoid l).
      * apply Hmutroots. exists x, T. repeat split; assumption.
      * exact HinZ.
    + exfalso.
      destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
        as [this [qcontext [Hthis [_ Hqcontext]]]].
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
      have Hxdom := Hget. apply static_getType_dom in Hxdom.
      specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T Hget).
      rewrite Hval in Hcorr.
      eapply typable_nonnull_not_bot; eauto.
  - inversion Htyping; subst.
    + exfalso. destruct Hmt; subst; destruct Hscope; congruence.
    + destruct (sqtype T0) eqn:Hreceiver;
        destruct (mutability (ftype fDef)) eqn:Hfieldq;
        simpl; unfold is_nonmutable_qualifier; auto.
      * exfalso. apply (Havoid l).
        -- eapply Hretained.
          ++ apply Hmutroots. exists x, T0.
             split; [exact Hget_x|]. split; [exact Hval|exact Hreceiver].
          ++ eapply runtime_static_mut_field_edge; eauto.
        -- exact HinZ.
      * exfalso. apply (Havoid l).
        -- eapply Hclosed.
          ++ apply Hmutroots. exists x, T0.
             split; [exact Hget_x|]. split; [exact Hval|exact Hreceiver].
          ++ eapply runtime_static_rdm_edge; eauto.
        -- exact HinZ.
      * exfalso.
        destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
          as [this [qcontext [Hthis [_ Hqcontext]]]].
        unfold wf_r_config in Hwf.
        destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
        have Hxdom := Hget_x. apply static_getType_dom in Hxdom.
        specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T0 Hget_x).
        rewrite Hval in Hcorr.
        eapply typable_nonnull_not_bot; eauto.
Qed.

Lemma directed_history_after_assignment :
  forall CT P Z M cutoff sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    directed_authority_history_state CT P Z M cutoff sGamma rGamma h ->
    retained_heap_closed CT h M ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    directed_authority_history_state CT P Z M cutoff sGamma
      (update_r_env_value rGamma x value) h.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h x e old value Hwf Hstate
    Hretained Htyping Hscope Hx Heval.
  destruct Hstate as
    [Hcontains [Henv [[Hconfenv Hconfheap] [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]].
  inversion Htyping; subst.
  assert (Hxdom : x < dom (vars rGamma)).
  { apply static_getType_dom in Hget_x.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]]. lia. }
  refine (conj Hcontains (conj _ (conj _ (conj Hclosed
    (conj Hruntime (conj _ Havoid)))))).
  - intros z l Tz Htype_z Hval_z HinZ.
    destruct (Nat.eq_dec z x) as [->|Hneq].
    + rewrite Hget_x in Htype_z. injection Htype_z as <-.
      destruct value as [|result].
      * rewrite runtime_getVal_update_same in Hval_z; auto. discriminate.
      * rewrite runtime_getVal_update_same in Hval_z; auto.
        injection Hval_z as <-.
        have Hsafe_result := directed_expression_into_zone_has_safe_type
          P Z M cutoff CT sGamma mt rGamma h e result Te Hwf
          (conj Hcontains (conj Henv (conj (conj Hconfenv Hconfheap)
            (conj Hclosed (conj Hruntime (conj Hmutroots Havoid))))))
          Hretained Heval Htype_e Hscope HinZ.
        eapply subtype_safe_implies_safe; eauto.
    + rewrite runtime_getVal_update_diff in Hval_z; auto.
      eapply Henv; eauto.
  - split; [|exact Hconfheap].
    apply env_confined_update; [exact Hconfenv|].
    destruct value as [|result]; [trivial|].
    eapply eval_expr_preserves_confinement; eauto. split; assumption.
  - intros root Hroot.
    destruct (assignment_mut_root_has_old_ancestor CT sGamma mt rGamma h
      x e old value Hwf Htyping Hscope Hx Heval root Hroot)
      as [old_root [Holdroot Holdreach]].
    eapply retained_heap_closed_reachable with (source := old_root).
    + exact Hretained.
    + exact Holdreach.
    + apply Hmutroots. exact Holdroot.
Qed.

Lemma directed_history_after_local :
  forall CT P Z M cutoff sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    directed_authority_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    directed_authority_history_state CT P Z M cutoff sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])) h.
Proof.
  intros CT P Z M cutoff sGamma mt rGamma h T x sGamma' Hwf Hstate
    Htyping Hrnone.
  inversion Htyping; subst.
  destruct Hstate as
    [Hcontains [Henv [[Hconfenv Hconfheap] [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
  refine (conj Hcontains (conj _ (conj _ (conj Hclosed
    (conj Hruntime (conj _ Havoid)))))).
  - intros y l Ty Htype Hval HinZ.
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T y Ty l
      Hlength Htype Hval) as [Holdtype Holdval].
    eapply Henv; eauto.
  - split; [|exact Hconfheap].
    intros y l Hval.
    destruct (Nat.eq_dec y (dom (vars rGamma))) as [->|Hneq].
    + rewrite runtime_getVal_last in Hval. discriminate.
    + assert (Hy : y < dom (vars rGamma)).
      { apply runtime_getVal_dom in Hval. simpl in Hval.
        rewrite length_app in Hval. simpl in Hval. lia. }
      rewrite runtime_getVal_last2 in Hval; auto. eapply Hconfenv; eauto.
  - intros root [y [Ty [Htype [Hval Hmut]]]].
    destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T y Ty root
      Hlength Htype Hval) as [Holdtype Holdval].
    apply Hmutroots. exists y, Ty. repeat split; assumption.
Qed.

Lemma authority_history_after_assignment :
  forall CT P Z M cutoff authority sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    retained_heap_closed CT h M ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    authority_component_history_state CT P Z M cutoff authority sGamma
      (update_r_env_value rGamma x value) h.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x e old value Hwf
    [Hforward [Hroots [Hsound Hcolors]]]
    Hretained Htyping Hscope Hx Heval.
  split.
  - eapply directed_history_after_assignment; eauto.
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
        destruct value as [|result]; try discriminate.
        injection Hval as <-. rewrite Hget_x in Htype. injection Htype as <-.
        destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
          as [this [qcontext [Hrthis [_ Hqcontext]]]].
        pose proof (expr_eval_preservation CT sGamma mt rGamma h e
          (Iot result) rGamma h Te this qcontext Hrthis Hqcontext Hwf Htype_e
          Heval) as Htypable.
        have Hexprcap := nonnull_subtype_preserves_authority_capability
          CT h result Te Tx qcontext authority Htypable Hsub Hcap.
        eapply authority_expression_capability_in_history
          with (P := P) (Z := Z) (cutoff := cutoff) (CT := CT)
            (authority := authority) (sGamma := sGamma) (mt := mt)
            (rGamma := rGamma) (h := h) (e := e) (T := Te); eauto.
        exact (conj Hforward (conj Hroots (conj Hsound Hcolors))).
      * rewrite runtime_getVal_update_diff in Hval; auto.
        apply Hroots. exists y, Ty. repeat split; assumption.
    + split.
      * intros Hauth.
        specialize (Hsound Hauth).
        destruct Hsound as [this [Hthis Hmut]].
        exists this. split; [|exact Hmut].
        inversion Htyping; subst.
        unfold update_r_env_value. destruct rGamma; simpl in *.
        rewrite get_this_var_mapping_update_nonzero; assumption.
      * have Hcomponent : component_forward_history_state CT P Z M cutoff
            sGamma rGamma h.
        { apply mutable_authority_component_history with
            (authority := authority).
          exact (conj Hforward (conj Hroots (conj Hsound Hcolors))). }
        exact (proj2 (component_forward_history_after_assignment CT P Z M
          cutoff sGamma mt rGamma h x e old value Hwf Hcomponent Hretained
          Htyping Hscope Hx Heval)).
Qed.

Lemma authority_history_after_local :
  forall CT P Z M cutoff authority sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    authority_component_history_state CT P Z M cutoff authority sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])) h.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h T x sGamma' Hwf
    [Hforward [Hroots [Hsound Hcolors]]] Htyping Hnone.
  split.
  - eapply directed_history_after_local; eauto.
  - split.
    + intros root [y [Ty [Htype [Hval Hcap]]]].
      inversion Htyping; subst.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
      destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T y Ty root
        Hlength Htype Hval) as [Holdtype Holdval].
      apply Hroots. exists y, Ty. repeat split; assumption.
    + split.
      * intros Hauth. specialize (Hsound Hauth).
        destruct Hsound as [this [Hthis Hmut]].
        exists this. split; [|exact Hmut].
        simpl. rewrite get_this_var_mapping_app_null_last. exact Hthis.
      * have Hcomponent : component_forward_history_state CT P Z M cutoff
            sGamma rGamma h.
        { apply mutable_authority_component_history with
            (authority := authority).
          exact (conj Hforward (conj Hroots (conj Hsound Hcolors))). }
        exact (proj2 (component_forward_history_after_local CT P Z M cutoff
          sGamma mt rGamma h T x sGamma' Hwf Hcomponent Htyping Hnone)).
Qed.

Lemma authority_history_after_field_write :
  forall CT P Z M cutoff authority sGamma mt rGamma h x f y rGamma' h'
    sGamma',
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff authority
      sGamma rGamma h ->
    component_colors_separated CT h M Z ->
    active_rdm_component_colors_separated CT h M Z sGamma rGamma ->
    stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
    readonly_state_method_scope mt ->
    eval_stmt CT rGamma h (SFldWrite x f y) OK rGamma' h' ->
    exists M',
      Included Loc M M' /\
      authority_component_history_state CT P Z M' cutoff authority
        sGamma' rGamma' h'.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x f y rGamma' h'
    sGamma' Hwf [Hforward [Hroots [Hsound Hcolors]]]
    Hcomponents Hactive Htyping Hscope Heval.
  assert (HsGamma : sGamma' = sGamma) by (inversion Htyping; reflexivity).
  assert (HrGamma : rGamma' = rGamma) by (inversion Heval; reflexivity).
  subst sGamma' rGamma'.
  have Hcomponent : component_forward_history_state CT P Z M cutoff
      sGamma rGamma h.
  { split.
    - eapply directed_authority_history_with_rdm; [exact Hforward|].
      eapply active_component_colors_imply_rdm_separation; eauto.
    - split; assumption. }
  destruct (component_forward_history_after_field_write CT P Z M cutoff
    sGamma mt rGamma h x f y rGamma h' sGamma Hwf Hcomponent
    (proj2 (proj2 Hcomponent)) Htyping Hscope Heval)
    as [M' [Hincl Hcomponent']].
  exists M'. split; [exact Hincl|].
  destruct Hcomponent' as [Hforward' [Hcomponents' Hactive']].
  split.
  - eapply forward_history_implies_directed_authority_history.
    exact Hforward'.
  - split.
    + intros root [z [T [Htype [Hval Hcap]]]].
      inversion Heval; subst. apply Hincl. apply Hroots.
      exists z, T. repeat split; assumption.
    + split.
      * intros Hauth. specialize (Hsound Hauth).
        destruct Hsound as [this [Hthis Hmut]].
        exists this. split; [exact Hthis|].
        inversion Heval; subst. rewrite r_muttype_update_field_preserve.
        exact Hmut.
      * split; assumption.
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
    [[Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]]
      [Hroots [Hsound Hcolors]]]
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
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    component_colors_separated CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new_authority M authority qc (dom h)) Z.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime Hwf
    [Hforward [Hroots [Hsound Hcolors]]] Hcomponent
    Htyping Hvals HfreshZ
    capability protected [Hcapability | [Hcap Hcapfresh]] Hprotected
    Hconnected.
  - have Hexisting := component_colors_after_new_existing_sets CT P Z M
      cutoff sGamma mt rGamma h x qc C args sGamma' vals qruntime Hwf
      Hcomponent (proj2 (proj2 Hcomponent)) Htyping Hvals HfreshZ.
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
    destruct Hcomponent as [Hcomponent_forward [Hcomponents Hactive]].
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
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    runtime_lookup_list rGamma args = Some vals ->
    ~ In Loc Z (dom h) ->
    active_rdm_component_colors_separated CT
      (h ++ [mkObj (mkruntime_type qruntime C) vals])
      (extend_capability_after_new_authority M authority qc (dom h)) Z
      sGamma' (update_r_env_value rGamma x (Iot (dom h))).
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x qc C args sGamma'
    vals qruntime Hwf Hstate Hcomponent Htyping Hvals HfreshZ.
  destruct authority.
  - have Hpostroots := authority_env_roots_after_new CT M Mut_r sGamma mt
      rGamma h x qc C args sGamma' Hwf (proj1 (proj2 Hstate)) Htyping.
    have Hcomponents := authority_component_colors_after_new CT P Z M cutoff
      Mut_r sGamma mt rGamma h x qc C args sGamma' vals qruntime Hwf Hstate
      Hcomponent Htyping Hvals HfreshZ.
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
      rGamma h x qc C args sGamma' vals qruntime Hwf Hcomponent
      (proj2 (proj2 Hcomponent)) Htyping Hvals HfreshZ.
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
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
    cutoff <= dom h ->
    ~ In Loc Z (dom h) ->
    eval_stmt CT rGamma h (SNew x qc C args) OK rGamma' h' ->
    exists M',
      Included Loc M M' /\
      authority_component_history_state CT P Z M' cutoff authority
        sGamma' rGamma' h'.
Proof.
  intros CT P Z M cutoff authority sGamma mt rGamma h x qc C args rGamma'
    h' sGamma' Hwf Hstate Hcomponent Htyping Hcutoff HfreshZ Heval.
  have Hcomponent_base := component_forward_history_after_new CT P Z M cutoff
    sGamma mt rGamma h x qc C args rGamma' h' sGamma' Hwf Hcomponent
    (proj2 (proj2 Hcomponent)) Htyping Hcutoff HfreshZ Heval.
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
    (proj1 (proj2 (proj2 (proj2 (proj2 (proj1 Hstate))))))
    (proj1 (proj2 (proj2 Hstate))) Hthis Hmut
    (ltac:(unfold qruntime; reflexivity)).
  have Hroots' := authority_env_roots_after_new CT M authority sGamma mt
    rGamma h x qc C args sGamma Hwf (proj1 (proj2 Hstate)) Htyping.
  have Hcomponents' := authority_component_colors_after_new CT P Z M cutoff
    authority sGamma mt rGamma h x qc C args sGamma vals qruntime Hwf Hstate
    Hcomponent Htyping Hargs HfreshZ.
  have Hactive' := authority_active_colors_after_new CT P Z M cutoff
    authority sGamma mt rGamma h x qc C args sGamma vals qruntime Hwf Hstate
    Hcomponent Htyping Hargs HfreshZ.
  have Hcontext' := authority_context_sound_after_new CT authority sGamma mt
    rGamma h x qc C args sGamma vals qthisr qruntime l1 Hwf
    (proj1 (proj2 (proj2 Hstate))) Htyping Hthis Hmut.
  destruct Hbase_state as
    [[Hcontains' [Hzone' [Hconfined' [Hbaseclosed [Hbaseruntime
      [Hbasemutroots [Hbaseavoid Hbaseforwardcolors]]]]]]]
      [Hbasecomponents Hbaseactive]].
  destruct Hstate as
    [[Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]]
      [Hroots [Hcontext Hcolors]]].
  rewrite Hnewenv.
  split.
  - refine (conj Hcontains' (conj Hzone' (conj Hconfined'
      (conj Hclosed' (conj Hruntime' (conj _ _)))))).
    + intros root Hroot. apply Hroots'.
      destruct Hroot as [z [T [Htype [Hval Hmutq]]]].
      exists z, T. repeat split; try assumption.
      unfold capability_in_context. left. exact Hmutq.
    + intros location [Hold | [Hcap ->]].
      * eapply Havoid; eauto.
      * exact HfreshZ.
  - split; [exact Hroots'|].
    split; [exact Hcontext'|].
    split; assumption.
Qed.

Lemma safe_call_callee_authority_roots :
  forall CT P Z M cutoff caller_authority sGamma mt rGamma h x m y args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff caller_authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    readonly_state_method_scope mt ->
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
  intros CT P Z M cutoff caller_authority sGamma mt rGamma h x m y args
    sGamma' vals ly cy runtime_mdef Ty Hwf
    [Hforward [Hroots [Hsound Hcolors]]]
    Htyping Hscope Hgety Hval Hbase Hfind
    Hargs root [z [T [Htype [Hrootval Hcap]]]].
  destruct Hcap as [Hmut | [Hrdm Hcallee_mut]].
  - apply Hroots.
    destruct (safe_call_callee_mut_root_origin CT sGamma mt rGamma h x m y
      args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope Hval Hbase
      Hfind Hargs) as [caller_z [caller_T
        [Hcaller_type [Hcaller_val Hcaller_mut]]]].
    + exists z, T. repeat split; assumption.
    + exists caller_z, caller_T. repeat split; try assumption.
      unfold capability_in_context. left. exact Hcaller_mut.
  - assert (Hrootrdm : typed_root RDM
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) root).
    { exists z, T. repeat split; assumption. }
    destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x m y
      args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope Hval Hbase
      Hfind Hargs Hrootrdm) as
      [Ty0 [Hgety0 [[Hshape Hcallerroot] | [Hro [Hrooteq Hro_origin]]]]].
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
  forall CT P Z M cutoff caller_authority sGamma mt rGamma h x m y args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff caller_authority
      sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    authority_context_sound h (mkr_env (Iot ly :: vals))
      (call_authority caller_authority (sqtype Ty)).
Proof.
  intros CT P Z M cutoff caller_authority sGamma mt rGamma h x m y args
    sGamma' vals ly cy runtime_mdef Ty Hwf
    [Hforward [Hroots [Hsound Hcolors]]]
    Htyping Hscope Hgety Hval Hbase Hfind
    Hargs Hcallee_mut.
  exists ly. split; [reflexivity|].
  destruct Hforward as
    [Hcontains [Hzone [Hconfined [Hclosed [Hruntime
      [Hmutroots Havoid]]]]]].
  apply Hruntime. apply Hroots.
  exists y, Ty. repeat split; try assumption.
  eapply safe_call_receiver_authority_reflects.
  - eapply wf_config_nonnull_variable_not_bot; eauto.
  - unfold capability_in_context. right. split; [reflexivity|].
    exact Hcallee_mut.
Qed.

Lemma authority_history_enter_call :
  forall CT P Z M cutoff caller_authority sGamma mt rGamma h x m y args
    sGamma' vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    authority_component_history_state CT P Z M cutoff caller_authority
      sGamma rGamma h ->
    component_forward_history_state CT P Z M cutoff sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    readonly_state_method_scope mt ->
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
  intros CT P Z M cutoff caller_authority sGamma mt rGamma h x m y args
    sGamma' vals ly cy runtime_mdef Ty Hwf Hstate Hcomponent Htyping Hscope
    Hgety Hval Hbase Hfind Hargs.
  have Hcomponent_post := safe_call_callee_component_forward_history CT P Z M
    cutoff sGamma mt rGamma h x m y args sGamma' vals ly cy runtime_mdef
    Hwf Htyping Hscope Hcomponent (proj2 (proj2 Hcomponent)) Hval Hbase Hfind
    Hargs.
  destruct Hcomponent_post as [Hforward_post [Hcomponents_post Hactive_post]].
  split.
  - eapply forward_history_implies_directed_authority_history.
    exact Hforward_post.
  - split.
    + eapply safe_call_callee_authority_roots; eauto.
    + split.
      * eapply safe_call_callee_authority_context; eauto.
      * split; assumption.
Qed.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties AbstractStatePreservation Reachability Preservation ExecutionConfinement.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

(** Qualifiers that do not grant direct mutable authority. *)
Definition is_nonmutable_qualifier (qualifier : q) : Prop :=
  qualifier = RO \/ qualifier = Lost \/ qualifier = RDM \/ qualifier = Imm.

Ltac solve_nonmutable_qualifier :=
  match goal with
  (* Recursively select a disjunct. *)
  | |- ?A \/ ?B => (left; solve_nonmutable_qualifier) || (right; solve_nonmutable_qualifier)
  | |- ?X = ?X => reflexivity
  | |- _ => assumption
  end.

(** Every reference into [P] has a qualifier that does not grant direct
    mutable authority. *)
Definition env_respects_protected_set
  (P : Ensembles.Ensemble Loc) (sΓ : s_env) (rΓ : r_env) : Prop :=
  forall x l T,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot l) ->

    Ensembles.In Loc P l ->
    is_nonmutable_qualifier (sqtype T).

Lemma extract_receiver_from_wf_config :
  forall CT sΓ rΓ h
    (Hwf : wf_r_config CT sΓ rΓ h),
    exists iot qcontext,
      get_this_var_mapping (vars rΓ) = Some iot /\
      iot < dom h /\
      r_muttype h iot = Some qcontext.
Proof.
  intros CT sΓ rΓ h Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [Hrenv _]]].
  destruct Hrenv as [_ [Hreceiver _]].
  destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
  exists iot.
  destruct (receiver_mutability_exists_from_bound h iot Hiot_dom)
    as [qcontext Hqcontext].
  exists qcontext. repeat split; assumption.
Qed.

Lemma subtype_safe_implies_safe :
  forall CT T_sub T_super
         (Hsub : qualified_type_subtype CT T_sub T_super)
         (Hsafe_sub : is_nonmutable_qualifier (sqtype T_sub)),
    is_nonmutable_qualifier (sqtype T_super).
Proof.
  intros. unfold is_nonmutable_qualifier in *.
  apply qualified_type_subtype_q_subtype in Hsub.
  inversion Hsub; subst; auto.
  rewrite <- H0 in Hsafe_sub.
  destruct Hsafe_sub as [Hrd | [Hlost| HRDM]].
  inversion Hrd. 
  inversion Hlost.
  inversion HRDM.
  discriminate.
  discriminate.
Qed.

Lemma adapted_subtype_safe_implies_safe :
  forall CT T_sub T_Receiver T_super
         (Hsub : qualified_type_subtype CT T_sub (vpa_mutability_tt_readonly_state T_Receiver T_super))
         (Hsafe_sub : is_nonmutable_qualifier (sqtype T_sub)),
    is_nonmutable_qualifier (sqtype T_super).
Proof.
  intros.
  unfold is_nonmutable_qualifier in *.
  apply qualified_type_subtype_q_subtype in Hsub.
  unfold vpa_mutability_tt_readonly_state in Hsub.
  destruct (sqtype T_Receiver) eqn: Hreceiver;
  destruct (sqtype T_super) eqn: HSuper;
  destruct Hsafe_sub as [Hrd | [Hlost| [HRDM | HImm]]];
  try rewrite Hrd in Hsub;
  try rewrite Hlost in Hsub;
  try rewrite HRDM in Hsub;
  try rewrite HImm in Hsub;
  try rewrite <- H in Hsub;
  inversion Hsub; subst; auto.
  all: try rewrite HSuper in H; try rewrite HSuper in H1; try discriminate.
  all: try simpl in Hsub.
  all: try easy.
Qed.

Lemma reachable_dom :
  forall h l_src l_dst
    (Hreach : reachable h l_src l_dst),
    l_dst < dom h.
Proof.
  intros.
  induction Hreach.
  - (* Base case: reachable_abs_heap *)
    exact Hdom.
  - (* Step case: reachable_abs_step *)
    exact Hdom.
  - (* Trans case *)
    exact IHHreach2.
Qed.

Lemma confinement_from_all_readonly_env :
  forall CT sΓ rΓ h
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Hall_readonly : forall y T,
      static_getType sΓ y = Some T ->
      is_nonmutable_qualifier (sqtype T)),
    env_respects_protected_set (reachable_locations_from_initial_env h rΓ) sΓ rΓ.
Proof.
  intros.
  unfold env_respects_protected_set.
  intros z l T Hlookup_s Hlookup_r Hin_P.
  exact (Hall_readonly z T Hlookup_s).
Qed.

Lemma runtime_getObj_app_left_equal : forall h h_ext loc,
  loc < dom h ->
  runtime_getObj h loc = runtime_getObj (h ++ [h_ext]) loc.
Proof.
  intros h h_ext loc Hloc_dom.
  unfold runtime_getObj.
  rewrite nth_error_app1; auto.
Qed.

Lemma reachable_locations_from_initial_env_dom :
  forall h rΓ l_y
    (Hin : Ensembles.In Loc (reachable_locations_from_initial_env h rΓ) l_y),
    l_y < dom h.
Proof.
  intros.
  unfold reachable_locations_from_initial_env in Hin.
  (* Hin is now: exists x l_root T, ... *)
  destruct Hin as [x [l_root [Hruntime_val]]].
  eapply reachable_dom; exact H.
Qed.

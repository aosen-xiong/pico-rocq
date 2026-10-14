From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels GhostTyping
  GhostForget GhostFit GhostInvariant GhostOverride GhostCall GhostEntry.

(** The bound condition on protected methods, reduced to what the typing
    rules do not already give.  A readonly-state or transitive-state method
    has a receiver and parameters with no mutable position, reading type
    variables through their bounds; the receiver mentions every type
    parameter of its class, so the class's bounds are covered.  What remains
    is the method's own type parameters. *)

Definition clean_method_bounds_ct (CT : class_table) : Prop :=
  forall C def md,
    find_class CT C = Some def -> List.In md (methods (body def)) ->
    readonly_state_method_scope (mscope (msignature md)) ->
    Forall (no_mut (method_tv_env CT C (msignature md)))
      (mtparams (msignature md)).

Lemma class_method_wf : forall CT C def md,
  wf_class_table CT -> find_class CT C = Some def ->
  List.In md (methods (body def)) -> wf_method CT C md.
Proof.
  intros CT C def md Hct Hfind Hin.
  pose proof (wf_class_table_class _ _ _ Hct Hfind) as Hc.
  destruct Hct as (_ & _ & _ & Hname).
  pose proof (Hname _ _ Hfind) as HC.
  inversion Hc; subst.
  - rewrite Hno_methods in Hin. contradiction.
  - match goal with
    | HH : Forall (wf_method CT _) _ |- _ =>
        rewrite Forall_forall in HH; exact (HH _ Hin)
    end.
Qed.

Lemma class_var_types_In : forall n i,
  i < n -> List.In (TVar TVSub ClassVar i) (class_var_types n).
Proof.
  intros n i Hi. unfold class_var_types.
  apply in_map_iff. exists i. split; auto. apply in_seq. lia.
Qed.

(** The method rule checks the bounds of the type parameters of every
    readonly-state and transitive-state method, so a well-formed class table
    satisfies the condition. *)
Lemma clean_method_bounds_of_wf : forall CT,
  wf_class_table CT -> clean_method_bounds_ct CT.
Proof.
  intros CT Hct C def md Hfind Hin Hrs.
  pose proof (class_method_wf _ _ _ _ Hct Hfind Hin) as Hwm.
  destruct Hwm as (_ & Hmb & _).
  eapply Forall_impl; [|exact Hmb].
  intros B (_ & _ & H). exact (H Hrs).
Qed.

Lemma clean_bounds_of_signature : forall CT,
  wf_class_table CT -> clean_method_bounds_ct CT -> clean_bounds_ct CT.
Proof.
  intros CT Hct Hcm C def md Hfind Hin Hrs o n B Hb.
  pose proof (class_method_wf _ _ _ _ Hct Hfind Hin) as Hwm.
  unfold wf_method in Hwm.
  destruct Hwm as (Hshape & Hmb & _ & _ & _ & Hroots).
  specialize (Hroots Hrs). destruct Hroots as [Hrecv _].
  destruct o.
  - (* a class type parameter: through the receiver *)
    assert (HbC : nth_error (ctparams (signature def)) n = Some B).
    { unfold tv_bound, method_tv_env, class_tparams in Hb. simpl in Hb.
      rewrite Hfind in Hb. exact Hb. }
    split.
    + pose proof (class_bounds_class _ _ _ Hct Hfind) as Hall.
      rewrite Forall_forall in Hall. apply Hall. eapply nth_error_In; eauto.
    + destruct (proj2 Hshape Hrs) as [Hplain | [Hcb _]].
      2:{ rewrite Forall_forall in Hcb. apply Hcb.
          unfold tv_bound in Hb. simpl in Hb. eapply nth_error_In; eauto. }
      assert (Hargs : Forall (no_mut (method_tv_env CT C (msignature md)))
                        (class_var_types (length (class_tparams CT C)))).
      { destruct Hplain as [[qr Hr] | [n0 Hr]]; rewrite Hr in Hrecv;
          inversion Hrecv; subst; assumption. }
      rewrite Forall_forall in Hargs.
      assert (Hlt : n < length (class_tparams CT C)).
      { unfold class_tparams. rewrite Hfind.
        apply nth_error_Some. rewrite HbC. discriminate. }
      pose proof (Hargs _ (class_var_types_In _ _ Hlt)) as Hv.
      inversion Hv; subst. rewrite Hb in Hbound. inversion Hbound; subst.
      exact Hrec.
  - (* a method type parameter *)
    assert (HbM : nth_error (mtparams (msignature md)) n = Some B).
    { unfold tv_bound, method_tv_env in Hb. simpl in Hb. exact Hb. }
    split.
    + rewrite Forall_forall in Hmb.
      exact (proj1 (Hmb _ (nth_error_In _ _ HbM))).
    + pose proof (Hcm _ _ _ Hfind Hin Hrs) as Hall.
      rewrite Forall_forall in Hall. apply Hall. eapply nth_error_In; eauto.
Qed.

Print Assumptions clean_bounds_of_signature.

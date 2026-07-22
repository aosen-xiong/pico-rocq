Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import ExecutionConfinement.
From Stdlib Require Import List.
From Stdlib Require Import Sets.Ensembles.
Import ListNotations.

(** An RDM heap edge that preserves a mutable capability.  SafeRO viewpoint
    adaptation can also preserve [Mut] through an explicitly [Mut_f] field;
    [retained_mut_edge] below includes both cases.  The declaring class may be
    a supertype of the runtime class. *)
Inductive mutable_edge (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=
| mutable_edge_rdm : forall l l' o f D fdef,
    runtime_getObj h l = Some o ->
    getVal o.(fields_map) f = Some (Iot l') ->
    base_subtype CT (rctype (rt_type o)) D ->
    sf_def_rel CT D f fdef ->
    mutability (ftype fdef) = RDM_f ->
    mutable_edge CT h l l'.

Inductive mutable_reachable (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=
| mr_refl : forall l, mutable_reachable CT h l l
| mr_step : forall l1 l2 l3,
    mutable_reachable CT h l1 l2 ->
    mutable_edge CT h l2 l3 ->
    mutable_reachable CT h l1 l3.

(** Retained mutable authority follows the RDM component graph and also an
    explicitly mutable field.  The latter edge is usable only from a [Mut]
    static viewpoint; membership in the capability set records that fact. *)
Inductive retained_mut_edge (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=
| retained_edge_rdm : forall l l',
    mutable_edge CT h l l' ->
    retained_mut_edge CT h l l'
| retained_edge_mut : forall l l' o f D fdef,
    runtime_getObj h l = Some o ->
    r_muttype h l = Some Mut_r ->
    getVal o.(fields_map) f = Some (Iot l') ->
    base_subtype CT (rctype (rt_type o)) D ->
    sf_def_rel CT D f fdef ->
    mutability (ftype fdef) = Mut_f ->
    retained_mut_edge CT h l l'.

Inductive retained_mut_reachable
  (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=
| rmr_refl : forall l, retained_mut_reachable CT h l l
| rmr_step : forall l1 l2 l3,
    retained_mut_reachable CT h l1 l2 ->
    retained_mut_edge CT h l2 l3 ->
    retained_mut_reachable CT h l1 l3.

Lemma mutable_reachable_is_retained : forall CT h l l',
  mutable_reachable CT h l l' -> retained_mut_reachable CT h l l'.
Proof.
  intros CT h l l' Hreach. induction Hreach.
  - constructor.
  - eapply rmr_step; [exact IHHreach|]. constructor. exact H.
Qed.

Lemma retained_mut_reachable_transitive : forall CT h l1 l2 l3,
  retained_mut_reachable CT h l1 l2 ->
  retained_mut_reachable CT h l2 l3 ->
  retained_mut_reachable CT h l1 l3.
Proof.
  intros CT h l1 l2 l3 H12 H23.
  induction H23 as [l | start middle finish Hprefix IH Hedge].
  - exact H12.
  - eapply rmr_step; [exact (IH H12)|exact Hedge].
Qed.

Lemma mutable_edge_target_dom :
  forall CT h l l',
    wf_heap CT h ->
    mutable_edge CT h l l' ->
    l' < dom h.
Proof.
  intros CT h l l' Hwf Hedge.
  inversion Hedge as [? ? o f D fdef Hobj Hfield Hsub Hfd Hrdm]; subst.
  specialize (Hwf l).
  apply runtime_getObj_dom in Hobj as Hldom.
  specialize (Hwf Hldom).
  unfold wf_obj in Hwf. rewrite Hobj in Hwf.
  destruct Hwf as [_ [field_defs [Hcollect [Hlen Hvalues]]]].
  assert (Hfdom : f < dom (fields_map o)) by (apply getVal_dom in Hfield; exact Hfield).
  assert (Hfd_at : exists fd, nth_error field_defs f = Some fd).
  { apply nth_error_Some_exists. rewrite <- Hlen. exact Hfdom. }
  destruct Hfd_at as [fd Hfd_at].
  unfold getVal in Hfield.
  eapply Forall2_nth_error_prop in Hvalues; eauto.
  simpl in Hvalues.
  destruct (runtime_getObj h l') eqn:Htarget; try contradiction.
  apply runtime_getObj_dom in Htarget. exact Htarget.
Qed.

Lemma retained_edge_target_dom :
  forall CT h l l',
    wf_heap CT h ->
    retained_mut_edge CT h l l' ->
    l' < dom h.
Proof.
  intros CT h l l' Hwf Hedge.
  inversion Hedge as [source target Hrdm | source target o f D fdef
    Hobj Hsource_mut Hfield Hsub Hfd Hmut]; subst.
  - eapply mutable_edge_target_dom; eauto.
  - eapply wf_raw_edge_target_dom.
    + exact Hwf.
    + exists o, f. split; [exact Hobj|exact Hfield].
Qed.

Definition capability_in_context (qcontext : q_r) (q0 : q) : Prop :=
  q0 = Mut \/ (q0 = RDM /\ qcontext = Mut_r).

(** The authority inherited by a callee is determined by the caller's
    viewpoint of the receiver, not by the receiver object's runtime
    mutability.  In particular, the readonly-to-RDM special call retains a
    safe authority context even when the receiver object is runtime mutable. *)
Definition call_authority (caller_authority : q_r) (receiver_q : q) : q_r :=
  match receiver_q with
  | Mut => Mut_r
  | RDM => caller_authority
  | _ => Imm_r
  end.

Lemma safe_call_receiver_authority_reflects :
  forall caller_authority qreceiver,
    qreceiver <> Bot ->
    capability_in_context (call_authority caller_authority qreceiver) RDM ->
    capability_in_context caller_authority qreceiver.
Proof.
  intros caller_authority qreceiver Hnotbot Hcap.
  destruct caller_authority, qreceiver; simpl in *;
    unfold capability_in_context in *; intuition discriminate.
Qed.

(** [M] is a semantic set of locations for which the execution has retained a
    mutable capability.  It is deliberately not reconstructed from runtime
    mutability: an RDM object can be mutable at runtime without admitting a
    statically mutable alias. *)
Definition mutable_heap_closed
  (CT : class_table) (h : heap) (M : Ensemble Loc) : Prop :=
  forall l l', In Loc M l -> mutable_edge CT h l l' -> In Loc M l'.

Definition retained_heap_closed
  (CT : class_table) (h : heap) (M : Ensemble Loc) : Prop :=
  forall l l', In Loc M l -> retained_mut_edge CT h l l' -> In Loc M l'.

Lemma retained_heap_closed_implies_mutable_heap_closed :
  forall CT h M,
    retained_heap_closed CT h M ->
    mutable_heap_closed CT h M.
Proof.
  intros CT h M Hclosed source target Hsource Hedge.
  eapply Hclosed; [exact Hsource|]. constructor. exact Hedge.
Qed.

Definition mutable_members_runtime_mut
  (h : heap) (M : Ensemble Loc) : Prop :=
  forall l, In Loc M l -> r_muttype h l = Some Mut_r.

Lemma runtime_static_rdm_edge :
  forall CT sGamma rGamma h x T l o f fdef l'
    (Hwf : wf_r_config CT sGamma rGamma h)
    (Htype : static_getType sGamma x = Some T)
    (Hval : runtime_getVal rGamma x = Some (Iot l))
    (Hobj : runtime_getObj h l = Some o)
    (Hfield : getVal o.(fields_map) f = Some (Iot l'))
    (Hfld : sf_def_rel CT (sctype T) f fdef)
    (Hrdm : mutability (ftype fdef) = RDM_f),
    mutable_edge CT h l l'.
Proof.
  intros.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  assert (Hxdom : x < dom sGamma).
  { apply static_getType_dom in Htype. exact Htype. }
  specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T Htype).
  rewrite Hval in Hcorr.
  unfold wf_r_typable, r_type in Hcorr. rewrite Hobj in Hcorr.
  eapply mutable_edge_rdm; eauto. exact (proj1 Hcorr).
Qed.

Lemma runtime_static_mut_field_edge :
  forall CT sGamma rGamma h x T l o f fdef l'
    (Hwf : wf_r_config CT sGamma rGamma h)
    (Htype : static_getType sGamma x = Some T)
    (Hval : runtime_getVal rGamma x = Some (Iot l))
    (Hobj : runtime_getObj h l = Some o)
    (Hfield : getVal o.(fields_map) f = Some (Iot l'))
    (Hfld : sf_def_rel CT (sctype T) f fdef)
    (Hreceiver : sqtype T = Mut)
    (Hmut : mutability (ftype fdef) = Mut_f),
    retained_mut_edge CT h l l'.
Proof.
  intros.
  destruct (extract_receiver_from_wf_config CT sGamma rGamma h Hwf)
    as [this [qcontext [Hthis [_ Hqcontext]]]].
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
  have Hxdom := Htype. apply static_getType_dom in Hxdom.
  specialize (Hcorr this qcontext Hthis Hqcontext x Hxdom T Htype).
  rewrite Hval in Hcorr.
  unfold wf_r_typable, r_type in Hcorr. rewrite Hobj in Hcorr.
  destruct Hcorr as [Hbase Hqual].
  assert (Hsource_mut : r_muttype h l = Some Mut_r).
  { unfold r_muttype, r_type. rewrite Hobj. simpl.
    destruct (rqtype (rt_type o)); [reflexivity|].
    unfold qualifier_typable_context, vpa_mutability_rs in Hqual.
    rewrite Hreceiver in Hqual. destruct qcontext; contradiction. }
  eapply retained_edge_mut; eauto.
Qed.

Lemma field_defs_agree_at_runtime_subtype :
  forall CT C D1 D2 f fd1 fd2,
    base_subtype CT C D1 ->
    base_subtype CT C D2 ->
    sf_def_rel CT D1 f fd1 ->
    sf_def_rel CT D2 f fd2 ->
    fd1 = fd2.
Proof.
  intros CT C D1 D2 f fd1 fd2 Hsub1 Hsub2 Hfd1 Hfd2.
  eapply field_lookup_deterministic_rel.
  - eapply field_inheritance_subtyping; [exact Hsub1|exact Hfd1].
  - eapply field_inheritance_subtyping; [exact Hsub2|exact Hfd2].
Qed.

Lemma mutable_edge_after_field_update :
  forall CT h lx old fnew value l l',
    runtime_getObj h lx = Some old ->
    mutable_edge CT (update_field h lx fnew value) l l' ->
    mutable_edge CT h l l' \/
    (l = lx /\ value = Iot l' /\
      exists D fdef,
        base_subtype CT (rctype (rt_type old)) D /\
        sf_def_rel CT D fnew fdef /\
        mutability (ftype fdef) = RDM_f).
Proof.
  intros CT h lx old fnew value l l' Hold Hedge.
  inversion Hedge as [l0 l0' newobj f D fdef Hnewobj Hnewfield Hsub Hfd Hrdm]; subst.
  destruct (Nat.eq_dec l lx) as [Heq|Hneq].
  - subst l.
    unfold update_field in Hnewobj. rewrite Hold in Hnewobj.
    have Hlxdom := Hold. apply runtime_getObj_dom in Hlxdom.
    rewrite runtime_getObj_update_same in Hnewobj; auto.
    injection Hnewobj as Hobj_eq. subst newobj. simpl in Hnewfield, Hsub.
    destruct (Nat.eq_dec f fnew) as [->|Hfdiff].
    + unfold getVal in Hnewfield.
      assert (Hfdom : fnew < dom (update fnew value (fields_map old))).
      { apply nth_error_Some. rewrite Hnewfield. discriminate. }
      rewrite update_length in Hfdom.
      pose proof (@update_same Syntax.value fnew value (fields_map old) Hfdom) as Hsame.
      rewrite Hsame in Hnewfield.
      injection Hnewfield as <-.
      right. repeat split; auto. exists D, fdef. repeat split; auto.
    + unfold getVal in Hnewfield. rewrite update_diff in Hnewfield; auto.
      left. eapply mutable_edge_rdm; eauto.
  - left.
    unfold update_field in Hnewobj. rewrite Hold in Hnewobj.
    rewrite runtime_getObj_update_diff in Hnewobj; auto.
    eapply mutable_edge_rdm; eauto.
Qed.

Lemma retained_edge_after_field_update :
  forall CT h lx old fnew value l l',
    runtime_getObj h lx = Some old ->
    retained_mut_edge CT (update_field h lx fnew value) l l' ->
    retained_mut_edge CT h l l' \/
    (l = lx /\ value = Iot l' /\
      exists D fdef,
        base_subtype CT (rctype (rt_type old)) D /\
        sf_def_rel CT D fnew fdef /\
        (mutability (ftype fdef) = RDM_f \/
         mutability (ftype fdef) = Mut_f)).
Proof.
  intros CT h lx old fnew value l l' Hold Hedge.
  inversion Hedge as [l0 l0' Hrdmedge | l0 l0' newobj f D fdef
    Hnewobj Hsource_mut Hnewfield Hsub Hfd Hmut]; subst.
  - destruct (mutable_edge_after_field_update CT h lx old fnew value l l'
      Hold Hrdmedge) as [Holdedge | [Hsource [Hvalue
        [D [fdef [Hsub [Hfd Hrdm]]]]]]].
    + left. constructor. exact Holdedge.
    + right. repeat split; try assumption. exists D, fdef.
      repeat split; try assumption. left. exact Hrdm.
  - destruct (Nat.eq_dec l lx) as [Heq|Hneq].
    + subst l. unfold update_field in Hnewobj. rewrite Hold in Hnewobj.
      have Hlxdom := Hold. apply runtime_getObj_dom in Hlxdom.
      rewrite runtime_getObj_update_same in Hnewobj; auto.
      injection Hnewobj as Hobj_eq. subst newobj.
      simpl in Hnewfield, Hsub.
      destruct (Nat.eq_dec f fnew) as [->|Hfdiff].
      * unfold getVal in Hnewfield.
        assert (Hfdom : fnew < dom (update fnew value (fields_map old))).
        { apply nth_error_Some. rewrite Hnewfield. discriminate. }
        rewrite update_length in Hfdom.
        pose proof (@update_same Syntax.value fnew value (fields_map old) Hfdom)
          as Hsame.
        rewrite Hsame in Hnewfield. injection Hnewfield as <-.
        right. repeat split; auto. exists D, fdef. repeat split; auto.
      * unfold getVal in Hnewfield. rewrite update_diff in Hnewfield; auto.
        left. eapply retained_edge_mut; eauto.
        rewrite r_muttype_update_field_preserve in Hsource_mut.
        exact Hsource_mut.
    + left. unfold update_field in Hnewobj. rewrite Hold in Hnewobj.
      rewrite runtime_getObj_update_diff in Hnewobj; auto.
      eapply retained_edge_mut; eauto.
      rewrite r_muttype_update_field_preserve in Hsource_mut.
      exact Hsource_mut.
Qed.

Lemma written_rdm_field_is_mutable_edge :
  forall CT h lx old f oldvalue target D fdef,
    runtime_getObj h lx = Some old ->
    getVal old.(fields_map) f = Some oldvalue ->
    base_subtype CT (rctype (rt_type old)) D ->
    sf_def_rel CT D f fdef ->
    mutability (ftype fdef) = RDM_f ->
    mutable_edge CT (update_field h lx f (Iot target)) lx target.
Proof.
  intros CT h lx old f oldvalue target D fdef Hobj Holdfield Hsub Hfd Hrdm.
  eapply mutable_edge_rdm with
    (o := set_fields_map old (update f (Iot target) (fields_map old)))
    (f := f) (D := D) (fdef := fdef).
  - unfold update_field. rewrite Hobj.
    have Hlxdom := Hobj. apply runtime_getObj_dom in Hlxdom.
    rewrite runtime_getObj_update_same; auto.
  - have Hfdom := Holdfield. apply getVal_dom in Hfdom.
    simpl. unfold getVal.
    rewrite update_same; auto.
  - simpl. exact Hsub.
  - exact Hfd.
  - exact Hrdm.
Qed.

Lemma written_capability_field_is_retained_edge :
  forall CT h lx old f oldvalue target D fdef,
    runtime_getObj h lx = Some old ->
    r_muttype h lx = Some Mut_r ->
    getVal old.(fields_map) f = Some oldvalue ->
    base_subtype CT (rctype (rt_type old)) D ->
    sf_def_rel CT D f fdef ->
    (mutability (ftype fdef) = RDM_f \/
     mutability (ftype fdef) = Mut_f) ->
    retained_mut_edge CT (update_field h lx f (Iot target)) lx target.
Proof.
  intros CT h lx old f oldvalue target D fdef Hobj Hsource_mut Holdfield Hsub Hfd
    [Hrdm | Hmut].
  - constructor. eapply written_rdm_field_is_mutable_edge; eauto.
  - eapply retained_edge_mut with
      (o := set_fields_map old (update f (Iot target) (fields_map old)))
      (f := f) (D := D) (fdef := fdef).
    + unfold update_field. rewrite Hobj.
      have Hlxdom := Hobj. apply runtime_getObj_dom in Hlxdom.
      rewrite runtime_getObj_update_same; auto.
    + rewrite r_muttype_update_field_preserve. exact Hsource_mut.
    + have Hfdom := Holdfield. apply getVal_dom in Hfdom.
      simpl. unfold getVal. rewrite update_same; auto.
    + simpl. exact Hsub.
    + exact Hfd.
    + exact Hmut.
Qed.

Lemma mutable_reachable_after_field_update :
  forall CT h lx old f value root target,
    runtime_getObj h lx = Some old ->
    mutable_reachable CT (update_field h lx f value) root target ->
    mutable_reachable CT h root target \/
    exists written,
      value = Iot written /\
      mutable_reachable CT h root lx /\
      mutable_reachable CT h written target.
Proof.
  intros CT h lx old f value root target Hobj Hreach.
  induction Hreach as [root|root middle target Hprefix IH Hedge].
  - left. constructor.
  - destruct (mutable_edge_after_field_update CT h lx old f value
      middle target Hobj Hedge) as
      [Holdedge | [Hmiddle [Hvalue Hnewedge]]].
    + destruct IH as [Holdprefix | [written [Hwritten [Hto_source Hsuffix]]]].
      * left. eapply mr_step; eauto.
      * right. exists written. repeat split; try assumption.
        eapply mr_step; eauto.
    + subst middle.
      destruct IH as [Holdprefix | [written [Hwritten [Hto_source Hsuffix]]]].
      * right. exists target. repeat split; try assumption. constructor.
      * rewrite Hvalue in Hwritten. injection Hwritten as <-.
        right. exists target. repeat split; try assumption. constructor.
Qed.

Lemma retained_reachable_after_field_update :
  forall CT h lx old f value root target,
    runtime_getObj h lx = Some old ->
    retained_mut_reachable CT (update_field h lx f value) root target ->
    retained_mut_reachable CT h root target \/
    exists written,
      value = Iot written /\
      retained_mut_reachable CT h root lx /\
      retained_mut_reachable CT h written target.
Proof.
  intros CT h lx old f value root target Hobj Hreach.
  induction Hreach as [root|root middle target Hprefix IH Hedge].
  - left. constructor.
  - destruct (retained_edge_after_field_update CT h lx old f value
      middle target Hobj Hedge) as
      [Holdedge | [Hmiddle [Hvalue Hnewedge]]].
    + destruct IH as [Holdprefix | [written [Hwritten [Hto_source Hsuffix]]]].
      * left. eapply rmr_step; eauto.
      * right. exists written. repeat split; try assumption.
        eapply rmr_step; eauto.
    + subst middle.
      destruct IH as [Holdprefix | [written [Hwritten [Hto_source Hsuffix]]]].
      * right. exists target. repeat split; try assumption. constructor.
      * rewrite Hvalue in Hwritten. injection Hwritten as <-.
        right. exists target. repeat split; try assumption. constructor.
Qed.

Lemma mutable_edge_after_append :
  forall CT h newobj l l',
    mutable_edge CT (h ++ [ newobj ]) l l' ->
    mutable_edge CT h l l' \/
    (l = dom h /\ exists f D fdef,
      getVal newobj.(fields_map) f = Some (Iot l') /\
      base_subtype CT (rctype (rt_type newobj)) D /\
      sf_def_rel CT D f fdef /\
      mutability (ftype fdef) = RDM_f).
Proof.
  intros CT h newobj l l' Hedge.
  destruct newobj as [newrt newfields].
  inversion Hedge as [? ? o f D fdef Hobj Hfield Hsub Hfd Hrdm]; subst.
  have Hldom := Hobj. apply runtime_getObj_dom in Hldom.
  rewrite length_app in Hldom. simpl in Hldom.
  destruct (Nat.eq_dec l (dom h)) as [Heq|Hneq].
  - subst l. right. split; [reflexivity|].
    rewrite runtime_getObj_last in Hobj. injection Hobj as <-.
    exists f, D, fdef. repeat split; assumption.
  - assert (Hlold : l < dom h) by lia.
    left. rewrite runtime_getObj_last2 in Hobj; auto.
    eapply mutable_edge_rdm; eauto.
Qed.

Lemma retained_edge_after_append :
  forall CT h newobj l l',
    retained_mut_edge CT (h ++ [newobj]) l l' ->
    retained_mut_edge CT h l l' \/
    (l = dom h /\ exists f D fdef,
      getVal newobj.(fields_map) f = Some (Iot l') /\
      base_subtype CT (rctype (rt_type newobj)) D /\
      sf_def_rel CT D f fdef /\
      (mutability (ftype fdef) = RDM_f \/
       mutability (ftype fdef) = Mut_f)).
Proof.
  intros CT h newobj l l' Hedge.
  destruct newobj as [newrt newfields].
  inversion Hedge as [source target Hrdm | source target o f D fdef
    Hobj Hsource_mut Hfield Hsub Hfd Hmut]; subst.
  - destruct (mutable_edge_after_append CT h
      (mkObj newrt newfields) l l' Hrdm)
      as [Hold | [Hfresh [f [D [fdef [Hfield [Hsub [Hfd Hrdm']]]]]]]].
    + left. constructor. exact Hold.
    + right. split; [exact Hfresh|]. exists f, D, fdef.
      repeat split; try assumption. left. exact Hrdm'.
  - have Hldom := Hobj. apply runtime_getObj_dom in Hldom.
    rewrite length_app in Hldom. simpl in Hldom.
    destruct (Nat.eq_dec l (dom h)) as [Heq|Hneq].
    + subst l. right. split; [reflexivity|].
      rewrite runtime_getObj_last in Hobj. injection Hobj as <-.
      exists f, D, fdef. repeat split; try assumption. right. exact Hmut.
    + assert (Hlold : l < dom h) by lia.
      left. rewrite runtime_getObj_last2 in Hobj; auto.
      eapply retained_edge_mut; eauto.
      unfold r_muttype, r_type in *. rewrite runtime_getObj_last2 in Hsource_mut; auto.
Qed.

Lemma retained_reachable_from_old_after_append :
  forall CT h newobj root target,
    wf_heap CT h ->
    root < dom h ->
    retained_mut_reachable CT (h ++ [newobj]) root target ->
    target < dom h /\ retained_mut_reachable CT h root target.
Proof.
  intros CT h newobj root target Hwf Hroot Hreach.
  induction Hreach as [root|root middle target Hprefix IH Hedge].
  - split; [exact Hroot|constructor].
  - destruct (IH Hroot) as [Hmiddle Holdprefix].
    destruct (retained_edge_after_append CT h newobj middle target Hedge)
      as [Holdedge | [Hfresh Hnew]].
    + split.
      * eapply retained_edge_target_dom; eauto.
      * eapply rmr_step; eauto.
    + lia.
Qed.

Lemma runtime_mut_typable_not_imm :
  forall CT rGamma h l T qcontext,
    r_muttype h l = Some Mut_r ->
    wf_r_typable CT rGamma h l T qcontext ->
    sqtype T <> Imm.
Proof.
  intros CT rGamma h l T qcontext Hrmut Htyp Himm.
  unfold wf_r_typable in Htyp.
  unfold r_muttype, r_type in *.
  destruct (runtime_getObj h l) as [o|] eqn:Hobj; try discriminate.
  inversion Hrmut; subst.
  destruct Htyp as [_ Hqual].
  unfold qualifier_typable_context, vpa_mutability_rs in Hqual.
  rewrite Himm in Hqual. rewrite H0 in Hqual. destruct qcontext; exact Hqual.
Qed.

Lemma rdm_typable_runtime_matches_context :
  forall CT rGamma h l T qcontext,
    wf_r_typable CT rGamma h l T qcontext ->
    sqtype T = RDM ->
    r_muttype h l = Some qcontext.
Proof.
  intros CT rGamma h l T qcontext Htyp Hrdm.
  unfold wf_r_typable in Htyp.
  destruct (r_type h l) as [rt|] eqn:Hrt; try contradiction.
  destruct Htyp as [_ Hqual].
  unfold r_type in Hrt.
  destruct (runtime_getObj h l) as [o|] eqn:Hobj; try discriminate.
  injection Hrt as <-.
  unfold r_muttype. rewrite Hobj. simpl.
  unfold qualifier_typable_context, vpa_mutability_rs in Hqual.
  rewrite Hrdm in Hqual.
  destruct (rqtype (rt_type o)), qcontext; try reflexivity; contradiction.
Qed.

Lemma typable_nonnull_not_bot :
  forall CT rGamma h l T qcontext,
    wf_r_typable CT rGamma h l T qcontext ->
    sqtype T <> Bot.
Proof.
  intros CT rGamma h l T qcontext Htyp Hbot.
  unfold wf_r_typable in Htyp.
  destruct (r_type h l) as [rt|] eqn:Hrt; try contradiction.
  destruct Htyp as [_ Hqual].
  unfold qualifier_typable_context, vpa_mutability_rs in Hqual.
  rewrite Hbot in Hqual.
  destruct (rqtype rt); destruct qcontext; exact Hqual.
Qed.

Lemma nonnull_subtype_to_mut_is_mut :
  forall CT rGamma h l T1 T2 qcontext,
    wf_r_typable CT rGamma h l T1 qcontext ->
    qualified_type_subtype CT T1 T2 ->
    sqtype T2 = Mut ->
    sqtype T1 = Mut.
Proof.
  intros CT rGamma h l T1 T2 qcontext Htyp Hsub Hmut.
  apply qualified_type_subtype_q_subtype in Hsub.
  rewrite Hmut in Hsub.
  inversion Hsub; subst; auto.
  exfalso. eapply typable_nonnull_not_bot; eauto.
Qed.

Lemma old_mutable_member_not_fresh :
  forall h M,
    mutable_members_runtime_mut h M ->
    ~ In Loc M (dom h).
Proof.
  intros h M Hrmut Hin.
  specialize (Hrmut (dom h) Hin).
  unfold r_muttype, r_type in Hrmut.
  assert (Hnone : runtime_getObj h (dom h) = None).
  { unfold runtime_getObj. apply nth_error_None. lia. }
  rewrite Hnone in Hrmut. discriminate.
Qed.

Require Import Syntax Notations Helpers Subtyping Typing Bigstep.
Require Import MutableCapability ProtectionHistory.
From Stdlib Require Import List Lia Sets.Ensembles Relations.Relation_Operators.
Import ListNotations.

(** Component colors record alias contamination, not mutable authority.
    Consequently, traversing an RDM edge in either direction propagates a
    color, while only the separate forward capability set grants authority. *)
Definition mutable_adjacent
  (CT : class_table) (h : heap) (l1 l2 : Loc) : Prop :=
  mutable_edge CT h l1 l2 \/ mutable_edge CT h l2 l1.

Definition mutable_connected
  (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=
  clos_refl_trans Loc (mutable_adjacent CT h).

Lemma mutable_adjacent_symmetric :
  forall CT h l1 l2,
    mutable_adjacent CT h l1 l2 -> mutable_adjacent CT h l2 l1.
Proof.
  intros CT h l1 l2 [Hedge | Hedge]; [right | left]; exact Hedge.
Qed.

Lemma mutable_connected_refl :
  forall CT h l, mutable_connected CT h l l.
Proof. intros. apply rt_refl. Qed.

Lemma mutable_connected_step :
  forall CT h l1 l2,
    mutable_edge CT h l1 l2 -> mutable_connected CT h l1 l2.
Proof. intros. apply rt_step. left. assumption. Qed.

Lemma mutable_connected_sym :
  forall CT h l1 l2,
    mutable_connected CT h l1 l2 -> mutable_connected CT h l2 l1.
Proof.
  intros CT h l1 l2 Hconnected.
  induction Hconnected.
  - apply rt_step. eapply mutable_adjacent_symmetric; eauto.
  - apply rt_refl.
  - eapply rt_trans; [exact IHHconnected2 | exact IHHconnected1].
Qed.

Lemma mutable_connected_trans :
  forall CT h l1 l2 l3,
    mutable_connected CT h l1 l2 ->
    mutable_connected CT h l2 l3 ->
    mutable_connected CT h l1 l3.
Proof. intros. eapply rt_trans; eauto. Qed.

Lemma mutable_reachable_connected :
  forall CT h l1 l2,
    mutable_reachable CT h l1 l2 -> mutable_connected CT h l1 l2.
Proof.
  intros CT h l1 l2 Hreach.
  induction Hreach.
  - apply mutable_connected_refl.
  - eapply mutable_connected_trans; [exact IHHreach|].
    eapply mutable_connected_step; eauto.
Qed.

Definition fresh_component_attachment
  (CT : class_table) (h : heap) (newobj : Obj) (root : Loc) : Prop :=
  root = dom h \/
  exists field D fdef target,
    getVal newobj.(fields_map) field = Some (Iot target) /\
    class_subtype CT (rctype (rt_type newobj)) D /\
    sf_def_rel CT D field fdef /\
    mutability (ftype fdef) = RDM_f /\
    mutable_connected CT h target root.

Lemma old_component_reaching_fresh_is_fresh :
  forall CT h root,
    wf_heap CT h ->
    mutable_connected CT h root (dom h) ->
    root = dom h.
Proof.
  intros CT h root Hwf Hconnected.
  assert (Hgeneral : forall l1 l2,
    mutable_connected CT h l1 l2 -> l2 = dom h -> l1 = dom h).
  { intros l1 l2 Hpath. induction Hpath; intros Hend.
    - subst y. destruct H as [Hforward | Hbackward].
      + have Htarget := mutable_edge_target_dom CT h x (dom h) Hwf Hforward.
        lia.
      + inversion Hbackward as [? ? old field D fdef Hobj Hfield Hsub Hfd
          Hrdm]; subst.
        apply runtime_getObj_dom in Hobj. lia.
    - exact Hend.
    - apply IHHpath1. apply IHHpath2. exact Hend. }
  eapply Hgeneral; [exact Hconnected|reflexivity].
Qed.

Lemma fresh_attachment_transport_old_component :
  forall CT h newobj root1 root2,
    wf_heap CT h ->
    mutable_connected CT h root1 root2 ->
    fresh_component_attachment CT h newobj root2 ->
    fresh_component_attachment CT h newobj root1.
Proof.
  intros CT h newobj root1 root2 Hwf Hconnected
    [Hfresh | [field [D [fdef [target [Hfield [Hsub [Hfd
      [Hrdm Htarget]]]]]]]]].
  - subst root2. left.
    eapply old_component_reaching_fresh_is_fresh; eauto.
  - right. exists field, D, fdef, target. repeat split; try assumption.
    eapply mutable_connected_trans.
    + exact Htarget.
    + eapply mutable_connected_sym; exact Hconnected.
Qed.

Lemma mutable_connected_after_append_components :
  forall CT h newobj l1 l2,
    wf_heap CT h ->
    mutable_connected CT (h ++ [newobj]) l1 l2 ->
    mutable_connected CT h l1 l2 \/
    (fresh_component_attachment CT h newobj l1 /\
     fresh_component_attachment CT h newobj l2).
Proof.
  intros CT h newobj l1 l2 Hwf Hconnected.
  induction Hconnected.
  - destruct H as [Hforward | Hbackward].
    + destruct (mutable_edge_after_append CT h newobj x y Hforward)
        as [Hold | [Hfresh [field [D [fdef [Hfield [Hsub
          [Hfd Hrdm]]]]]]]].
      * left. apply rt_step. left. exact Hold.
      * subst x. right. split.
        -- left. reflexivity.
        -- right. exists field, D, fdef, y. repeat split; try assumption.
           apply mutable_connected_refl.
    + destruct (mutable_edge_after_append CT h newobj y x Hbackward)
        as [Hold | [Hfresh [field [D [fdef [Hfield [Hsub
          [Hfd Hrdm]]]]]]]].
      * left. apply rt_step. right. exact Hold.
      * subst y. right. split.
        -- right. exists field, D, fdef, x. repeat split; try assumption.
           apply mutable_connected_refl.
        -- left. reflexivity.
  - left. apply mutable_connected_refl.
  - destruct IHHconnected1 as [Hxy | [Hattachx Hattachy]];
      destruct IHHconnected2 as [Hyz | [Hattachy' Hattachz]].
    + left. eapply mutable_connected_trans; eauto.
    + right. split.
      * eapply fresh_attachment_transport_old_component; eauto.
      * exact Hattachz.
    + right. split.
      * exact Hattachx.
      * eapply fresh_attachment_transport_old_component.
        -- exact Hwf.
        -- eapply mutable_connected_sym; exact Hyz.
        -- exact Hattachy.
    + right. split; assumption.
Qed.

Lemma mutable_connected_preserves_runtime_mutability :
  forall CT h l1 l2 qruntime,
    wf_heap CT h ->
    mutable_connected CT h l1 l2 ->
    r_muttype h l1 = Some qruntime ->
    r_muttype h l2 = Some qruntime.
Proof.
  intros CT h l1 l2 qruntime Hwf Hconnected.
  induction Hconnected; intros Hruntime.
  - destruct H as [Hforward | Hbackward].
    + eapply mutable_edge_preserves_runtime_mutability; eauto.
    + eapply mutable_edge_reflects_runtime_mutability; eauto.
  - exact Hruntime.
  - apply IHHconnected2. apply IHHconnected1. exact Hruntime.
Qed.

Definition component_touches
  (CT : class_table) (h : heap) (S : Ensemble Loc) (root : Loc) : Prop :=
  exists member, In Loc S member /\ mutable_connected CT h root member.

(** No undirected RDM component carries both the capability-contamination
    color and the protected-zone color. *)
Definition component_colors_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc) : Prop :=
  forall capability protected,
    In Loc M capability ->
    In Loc Z protected ->
    ~ mutable_connected CT h capability protected.

Definition active_rdm_component_colors_separated
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (sGamma : s_env) (rGamma : r_env) : Prop :=
  forall capability_root zone_root,
    typed_root RDM sGamma rGamma capability_root ->
    component_touches CT h M capability_root ->
    typed_root RDM sGamma rGamma zone_root ->
    component_touches CT h Z zone_root ->
    False.

Lemma separated_components_cannot_touch_both :
  forall CT h M Z root,
    component_colors_separated CT h M Z ->
    component_touches CT h M root ->
    component_touches CT h Z root ->
    False.
Proof.
  intros CT h M Z root Hseparated
    [capability [Hcapability Hroot_capability]]
    [protected [Hprotected Hroot_protected]].
  apply (Hseparated capability protected Hcapability Hprotected).
  eapply mutable_connected_trans.
  - eapply mutable_connected_sym; eauto.
  - exact Hroot_protected.
Qed.

Lemma mutable_adjacent_after_field_update :
  forall CT h lx old f value l1 l2,
    runtime_getObj h lx = Some old ->
    mutable_adjacent CT (update_field h lx f value) l1 l2 ->
    mutable_adjacent CT h l1 l2 \/
    exists written,
      value = Iot written /\
      ((l1 = lx /\ l2 = written) \/ (l1 = written /\ l2 = lx)).
Proof.
  intros CT h lx old f value l1 l2 Hobj [Hforward | Hbackward].
  - destruct (mutable_edge_after_field_update CT h lx old f value l1 l2
      Hobj Hforward) as [Hold | [Hsource [Hvalue Hnew]]].
    + left. left. exact Hold.
    + right. exists l2. split; [exact Hvalue|]. left. split; auto.
  - destruct (mutable_edge_after_field_update CT h lx old f value l2 l1
      Hobj Hbackward) as [Hold | [Hsource [Hvalue Hnew]]].
    + left. right. exact Hold.
    + right. exists l1. split; [exact Hvalue|]. right. split; auto.
Qed.

Lemma mutable_connected_after_field_update :
  forall CT h lx old f value l1 l2,
    runtime_getObj h lx = Some old ->
    mutable_connected CT (update_field h lx f value) l1 l2 ->
    mutable_connected CT h l1 l2 \/
    exists written,
      value = Iot written /\
      ((mutable_connected CT h l1 lx /\
          mutable_connected CT h written l2) \/
       (mutable_connected CT h l1 written /\
          mutable_connected CT h lx l2)).
Proof.
  intros CT h lx old f value l1 l2 Hobj Hconnected.
  induction Hconnected.
  - destruct (mutable_adjacent_after_field_update CT h lx old f value x y
      Hobj H) as [Hold | [written [Hvalue [[-> ->] | [-> ->]]]]].
    + left. apply rt_step. exact Hold.
    + right. exists written. split; [exact Hvalue|]. left. split;
        apply mutable_connected_refl.
    + right. exists written. split; [exact Hvalue|]. right. split;
        apply mutable_connected_refl.
  - left. apply mutable_connected_refl.
  - destruct IHHconnected1 as
      [Hxy | [written1 [Hvalue1 [[Hxlx Hwritten1y] | [Hxwritten1 Hlxy]]]]];
    destruct IHHconnected2 as
      [Hyz | [written2 [Hvalue2 [[Hylx Hwritten2z] | [Hywritten2 Hlxyz]]]]].
    + left. eapply mutable_connected_trans; eauto.
    + right. exists written2. split; [exact Hvalue2|]. left. split.
      * eapply mutable_connected_trans; eauto.
      * exact Hwritten2z.
    + right. exists written2. split; [exact Hvalue2|]. right. split.
      * eapply mutable_connected_trans; eauto.
      * exact Hlxyz.
    + right. exists written1. split; [exact Hvalue1|]. left. split.
      * exact Hxlx.
      * eapply mutable_connected_trans; eauto.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply mutable_connected_trans; [exact Hxlx|].
      eapply mutable_connected_trans.
      * eapply mutable_connected_sym.
        eapply mutable_connected_trans; [exact Hwritten1y | exact Hylx].
      * exact Hwritten2z.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply mutable_connected_trans; eauto.
    + right. exists written1. split; [exact Hvalue1|]. right. split.
      * exact Hxwritten1.
      * eapply mutable_connected_trans; eauto.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply mutable_connected_trans; eauto.
    + rewrite Hvalue1 in Hvalue2. injection Hvalue2 as <-.
      left. eapply mutable_connected_trans; [exact Hxwritten1|].
      eapply mutable_connected_trans.
      * eapply mutable_connected_sym.
        eapply mutable_connected_trans; [exact Hlxy | exact Hywritten2].
      * exact Hlxyz.
Qed.

Lemma component_colors_after_field_update_existing_sets :
  forall CT h lx old f value M Z,
    runtime_getObj h lx = Some old ->
    component_colors_separated CT h M Z ->
    (forall written,
      value = Iot written ->
      component_touches CT h M lx ->
      component_touches CT h Z written -> False) ->
    (forall written,
      value = Iot written ->
      component_touches CT h Z lx ->
      component_touches CT h M written -> False) ->
    component_colors_separated CT (update_field h lx f value) M Z.
Proof.
  intros CT h lx old f value M Z Hobj Hseparated
    Hcapability_to_zone Hzone_to_capability capability protected
    Hcapability Hprotected Hconnected.
  destruct (mutable_connected_after_field_update CT h lx old f value
    capability protected Hobj Hconnected) as
    [Hold | [written [Hvalue [[Hcap_lx Hwritten_protected] |
      [Hcap_written Hlx_protected]]]]].
  - exact (Hseparated capability protected Hcapability Hprotected Hold).
  - eapply Hcapability_to_zone with (written := written); [exact Hvalue| |].
    + exists capability. split; [exact Hcapability|].
      eapply mutable_connected_sym; exact Hcap_lx.
    + exists protected. split; assumption.
  - eapply Hzone_to_capability with (written := written); [exact Hvalue| |].
    + exists protected. split; [exact Hprotected|].
      exact Hlx_protected.
    + exists capability. split; [exact Hcapability|].
      eapply mutable_connected_sym; exact Hcap_written.
Qed.

Lemma component_touch_after_field_update_origin :
  forall CT h lx old f value S root,
    runtime_getObj h lx = Some old ->
    component_touches CT (update_field h lx f value) S root ->
    component_touches CT h S root \/
    exists written,
      value = Iot written /\
      ((mutable_connected CT h root lx /\
          component_touches CT h S written) \/
       (mutable_connected CT h root written /\
          component_touches CT h S lx)).
Proof.
  intros CT h lx old f value S root Hobj
    [member [HinS Hconnected]].
  destruct (mutable_connected_after_field_update CT h lx old f value
    root member Hobj Hconnected) as
    [Hold | [written [Hvalue [[Hroot_lx Hwritten_member] |
      [Hroot_written Hlx_member]]]]].
  - left. exists member. split; assumption.
  - right. exists written. split; [exact Hvalue|]. left. split.
    + exact Hroot_lx.
    + exists member. split; assumption.
  - right. exists written. split; [exact Hvalue|]. right. split.
    + exact Hroot_written.
    + exists member. split; assumption.
Qed.

Lemma mutable_edge_after_non_rdm_field_update_is_old :
  forall CT h lx old f value C fieldT l1 l2,
    runtime_getObj h lx = Some old ->
    class_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C f fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    mutable_edge CT (update_field h lx f value) l1 l2 ->
    mutable_edge CT h l1 l2.
Proof.
  intros CT h lx old f value C fieldT l1 l2 Hobj Hbase Hfield Hnotrdm Hedge.
  destruct (mutable_edge_after_field_update CT h lx old f value l1 l2
    Hobj Hedge) as [Hold | [Hsource [Hvalue [D [runtime_fd
      [Hruntime_base [Hruntime_field Hruntime_rdm]]]]]]].
  - exact Hold.
  - assert (runtime_fd = fieldT).
    { eapply field_defs_agree_at_runtime_subtype with
        (C := rctype (rt_type old)) (D1 := D) (D2 := C); eauto. }
    subst runtime_fd. contradiction.
Qed.

Lemma mutable_connected_after_non_rdm_field_update_is_old :
  forall CT h lx old f value C fieldT l1 l2,
    runtime_getObj h lx = Some old ->
    class_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C f fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    mutable_connected CT (update_field h lx f value) l1 l2 ->
    mutable_connected CT h l1 l2.
Proof.
  intros CT h lx old f value C fieldT l1 l2 Hobj Hbase Hfield Hnotrdm
    Hconnected.
  induction Hconnected.
  - apply rt_step. destruct H as [Hforward | Hbackward].
    + left. eapply mutable_edge_after_non_rdm_field_update_is_old; eauto.
    + right. eapply mutable_edge_after_non_rdm_field_update_is_old; eauto.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma component_colors_after_non_rdm_field_update :
  forall CT h lx old f value C fieldT M Z,
    runtime_getObj h lx = Some old ->
    class_subtype CT (rctype (rt_type old)) C ->
    sf_def_rel CT C f fieldT ->
    mutability (ftype fieldT) <> RDM_f ->
    component_colors_separated CT h M Z ->
    component_colors_separated CT (update_field h lx f value) M Z.
Proof.
  intros CT h lx old f value C fieldT M Z Hobj Hbase Hfield Hnotrdm
    Hseparated capability protected Hcapability Hprotected Hconnected.
  apply (Hseparated capability protected Hcapability Hprotected).
  eapply mutable_connected_after_non_rdm_field_update_is_old; eauto.
Qed.

Lemma mutable_connected_after_nonlocation_field_update_is_old :
  forall CT h lx old f value l1 l2,
    runtime_getObj h lx = Some old ->
    (forall l, value <> Iot l) ->
    mutable_connected CT (update_field h lx f value) l1 l2 ->
    mutable_connected CT h l1 l2.
Proof.
  intros CT h lx old f value l1 l2 Hobj Hnonlocation Hconnected.
  destruct (mutable_connected_after_field_update CT h lx old f value
    l1 l2 Hobj Hconnected) as
    [Hold | [written [Hvalue Hbridge]]].
  - exact Hold.
  - exfalso. exact (Hnonlocation written Hvalue).
Qed.

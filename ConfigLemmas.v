From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping.

(** Transport of well-formed configurations along heap growth and variable
    updates. *)

(** [h'] keeps every object of [h] at its location with its runtime type. *)
Definition heap_ext (h h' : heap) : Prop :=
  dom h <= dom h' /\ forall ι, ι < dom h -> r_type h' ι = r_type h ι.

Lemma heap_ext_refl : forall h, heap_ext h h.
Proof. split; auto. Qed.

Lemma heap_ext_trans : forall h1 h2 h3,
  heap_ext h1 h2 -> heap_ext h2 h3 -> heap_ext h1 h3.
Proof.
  intros h1 h2 h3 [H1 H1'] [H2 H2']. split; [lia|].
  intros ι Hι. rewrite H2'; [lia|]. apply H1'; auto.
Qed.

Lemma heap_ext_getObj : forall h h' l o,
  heap_ext h h' -> runtime_getObj h l = Some o ->
  exists o', runtime_getObj h' l = Some o' /\ rt_type o' = rt_type o.
Proof.
  intros h h' l o [Hdom Hty] Hobj.
  pose proof (runtime_getObj_dom _ _ _ Hobj) as Hl.
  specialize (Hty l Hl). unfold r_type in Hty. rewrite Hobj in Hty.
  destruct (runtime_getObj h' l) as [o'|]; [|discriminate].
  exists o'. split; auto. congruence.
Qed.

Lemma loc_has_rtype_getObj : forall CT h ι R,
  loc_has_rtype CT h ι R -> exists o, runtime_getObj h ι = Some o.
Proof.
  intros CT h ι R H. unfold loc_has_rtype in H.
  destruct (runtime_getObj h ι); [eauto|contradiction].
Qed.

Lemma loc_has_rtype_ext : forall CT h h' ι R,
  heap_ext h h' -> loc_has_rtype CT h ι R -> loc_has_rtype CT h' ι R.
Proof.
  intros CT h h' ι R Hext H.
  destruct (loc_has_rtype_getObj _ _ _ _ H) as [o Hobj].
  eapply loc_has_rtype_heap_irrel; [|exact H].
  destruct Hext as [_ Hty]. symmetry. apply Hty.
  eapply runtime_getObj_dom; eauto.
Qed.

Lemma heap_ext_r_muttype : forall h h' ι qr,
  heap_ext h h' -> ι < dom h -> r_muttype h' ι = Some qr -> r_muttype h ι = Some qr.
Proof.
  intros h h' ι qr [_ Hty] Hι H. specialize (Hty ι Hι).
  unfold r_muttype, r_type in *.
  destruct (runtime_getObj h' ι); [|discriminate].
  destruct (runtime_getObj h ι); [|discriminate]. congruence.
Qed.

Lemma get_this_var_mapping_dom : forall rΓ h CT ι,
  wf_renv CT rΓ h -> get_this_var_mapping (vars rΓ) = Some ι -> ι < dom h.
Proof.
  intros rΓ h CT ι [_ [[i [Hi Hd]] _]] H. congruence.
Qed.

Lemma wf_r_config_heap_ext : forall CT Δ sΓ rΓ h h',
  wf_r_config CT Δ sΓ rΓ h ->
  heap_ext h h' ->
  wf_heap CT h' ->
  wf_r_config CT Δ sΓ rΓ h'.
Proof.
  intros CT Δ sΓ rΓ h h' Hwf Hext Hheap'.
  destruct Hwf as (Hct & Hheap & Hrenv & Hsenv & Hframe & Hlen & Hcorr).
  refine (conj Hct (conj Hheap' (conj _ (conj Hsenv (conj _ (conj Hlen _)))))).
  - refine (conj _ (conj _ _)).
    + destruct Hrenv as [H _]; exact H.
    + destruct Hrenv as [_ [[i [Hi Hd]] _]]. exists i. split; auto.
      destruct Hext; lia.
    + destruct Hrenv as [_ [_ H]].
      eapply Forall_impl; [|exact H]. intros [|loc]; auto.
      destruct (runtime_getObj h loc) eqn:Hobj; [|contradiction]. intros _.
      destruct (heap_ext_getObj _ _ _ _ Hext Hobj) as [o' [Ho' _]].
      rewrite Ho'. exact I.
  - destruct Hframe as (ι & o & Cthis & Hthis & Hobj & Hrest).
    destruct (heap_ext_getObj _ _ _ _ Hext Hobj) as [o' [Ho' Hrt]].
    exists ι, o', Cthis. rewrite Hrt. auto.
  - intros ι qcontext Hthis Hmut i Hi sqt Hnth.
    assert (Hι : ι < dom h) by eauto using get_this_var_mapping_dom.
    pose proof (heap_ext_r_muttype _ _ _ _ Hext Hι Hmut) as Hmut0.
    specialize (Hcorr ι qcontext Hthis Hmut0 i Hi sqt Hnth).
    destruct (runtime_getVal rΓ i) as [[|loc]|]; auto.
    unfold wf_r_typable in *. eauto using loc_has_rtype_ext.
Qed.

Lemma get_this_var_mapping_update : forall x v l,
  x <> 0 -> get_this_var_mapping (update x v l) = get_this_var_mapping l.
Proof.
  intros x v l Hx. destruct l; destruct x; simpl; auto. congruence.
Qed.

(** The receiver of a well-formed configuration. *)
Lemma wf_r_config_this : forall CT Δ sΓ rΓ h,
  wf_r_config CT Δ sΓ rΓ h ->
  exists ι o,
    get_this_var_mapping (vars rΓ) = Some ι /\
    runtime_getObj h ι = Some o /\
    r_muttype h ι = Some (rqtype (rt_type o)) /\
    Forall rlost_free (cargs rΓ) /\
    Forall rlost_free (margs rΓ) /\
    frame_bounds_ok CT Δ (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ).
Proof.
  intros CT Δ sΓ rΓ h Hwf.
  destruct Hwf as (_ & _ & _ & _ & Hframe & _).
  destruct Hframe as (ι & o & Cthis & Hthis & Hobj & _ & _ & Hlc & [Hlm _] & Hbc & Hbm).
  exists ι, o.
  refine (conj Hthis (conj Hobj (conj _ (conj Hlc (conj Hlm _))))).
  - unfold r_muttype. rewrite Hobj. reflexivity.
  - apply frame_bounds_ok_of_rbounds; auto.
Qed.

(** No qualifier argument of the activation is unknown. *)
Lemma wf_r_config_qargs : forall CT Δ sΓ rΓ h,
  wf_r_config CT Δ sΓ rΓ h ->
  Forall (fun q0 => q0 <> Lost) (qargs rΓ).
Proof.
  intros CT Δ sΓ rΓ h Hwf.
  destruct Hwf as (_ & _ & _ & _ & Hframe & _).
  destruct Hframe as (ι & o & Cthis & _ & _ & _ & _ & _ & [_ Hq] & _).
  exact Hq.
Qed.

(** Typability of a variable's value in a well-formed configuration. *)
Lemma wf_r_config_var : forall CT Δ sΓ rΓ h ι o x T,
  wf_r_config CT Δ sΓ rΓ h ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  static_getType sΓ x = Some T ->
  match runtime_getVal rΓ x with
  | Some (Iot loc) =>
      wf_r_typable CT h loc T (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ)
  | Some Null_a => True
  | None => False
  end.
Proof.
  intros CT Δ sΓ rΓ h ι o x T Hwf Hthis Hobj Hx.
  destruct Hwf as (_ & _ & _ & _ & _ & _ & Hcorr).
  apply (Hcorr ι (rqtype (rt_type o))); auto.
  - unfold r_muttype. rewrite Hobj. reflexivity.
  - eapply static_getType_dom; eauto.
Qed.

Definition val_typable (CT : class_table) (h : heap) (v : value)
    (T : qualified_type) (qctx : q_r) (ca ma : list rtype) (ka : list q) : Prop :=
  match v with
  | Null_a => True
  | Iot loc => wf_r_typable CT h loc T qctx ca ma ka
  end.

Lemma wf_r_config_update_var : forall CT Δ sΓ rΓ h x v ι o Tx,
  wf_r_config CT Δ sΓ rΓ h ->
  x <> 0 ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  static_getType sΓ x = Some Tx ->
  val_typable CT h v Tx (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ) ->
  wf_r_config CT Δ sΓ (set_vars rΓ (update x v (vars rΓ))) h.
Proof.
  intros CT Δ sΓ rΓ h x v ι o Tx Hwf Hx Hthis Hobj HTx Hv.
  destruct Hwf as (Hct & Hheap & Hrenv & Hsenv & Hframe & Hlen & Hcorr).
  assert (Hxdom : x < dom (vars rΓ)).
  { rewrite <- Hlen. eapply static_getType_dom; eauto. }
  refine (conj Hct (conj Hheap (conj _ (conj Hsenv (conj _ (conj _ _)))))).
  - refine (conj _ (conj _ _)); simpl.
    + rewrite update_length. destruct Hrenv as [H _]; exact H.
    + rewrite get_this_var_mapping_update; auto.
      destruct Hrenv as [_ [H _]]; exact H.
    + destruct Hrenv as [_ [_ H]]. apply Forall_update; auto.
      destruct v as [|loc]; auto.
      simpl in Hv. unfold wf_r_typable in Hv.
      destruct (loc_has_rtype_getObj _ _ _ _ Hv) as [o' Ho']. rewrite Ho'. exact I.
  - destruct Hframe as (ι' & o' & Cthis & Hthis' & Hrest).
    exists ι', o', Cthis. simpl. rewrite get_this_var_mapping_update; auto.
  - simpl. rewrite update_length. exact Hlen.
  - intros ι' qcontext Hthis' Hmut i Hi sqt Hnth.
    rewrite get_this_var_mapping_update in Hthis'; auto.
    unfold runtime_getVal. simpl.
    destruct (Nat.eq_dec x i) as [-> | Hne].
    + rewrite update_same; auto.
      destruct v as [|loc]; auto. simpl in Hv.
      assert (ι' = ι) by congruence. subst ι'.
      unfold r_muttype in Hmut. rewrite Hobj in Hmut. inversion Hmut; subst.
      unfold static_getType in HTx. congruence.
    + rewrite update_diff; auto.
      apply (Hcorr ι' qcontext Hthis' Hmut i Hi sqt Hnth).
Qed.

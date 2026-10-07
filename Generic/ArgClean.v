From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant ArgCases.

(** Classes whose bounds write no mutable position.

    A class that declares a readonly-state or transitive-state method is such
    a class: the method's receiver type mentions every type variable of the
    class, and may reach no mutable position through their bounds.  From such
    a class upwards an object reads every mutable position written in a class
    header as its own label. *)

Lemma no_mut_has_mut : forall Δ T, no_mut Δ T -> has_mut T = false.
Proof.
  intros Δ T. induction T using qualified_type_ind'; intros Hn.
  - inversion Hn; subst. rewrite has_mut_class.
    destruct (q_eq_dec qual Mut) as [Hx | Hx]; [congruence|]. simpl.
    clear Hn Hq Hx. revert Hargs.
    induction H as [|t r Ht _ IH]; intros Hargs; simpl; auto.
    inversion Hargs; subst. rewrite Ht; auto.
  - destruct u as [|q0]; [reflexivity|].
    inversion Hn; subst. destruct q0; try reflexivity. congruence.
  - inversion Hn; subst. rewrite has_mut_head.
    clear Hn Hbound. revert Hargs.
    induction H as [|t r Ht _ IH]; intros Hargs; simpl; auto.
    inversion Hargs; subst. rewrite Ht; auto.
Qed.

Lemma pwalks_none : forall CT Bs,
  Forall (fun B => forall A, pwalk CT B A = None) Bs ->
  forall Vs, pwalks CT Bs Vs = None.
Proof.
  intros CT Bs H. induction H as [|B Bs HB _ IH]; intros [|V Vs]; simpl; auto.
  rewrite HB. apply IH.
Qed.

Lemma pwalk_nomut : forall CT B A, has_mut B = false -> pwalk CT B A = None.
Proof.
  intros CT B. induction B using qualified_type_ind'; intros [q0 l C0 As] Hn.
  - rewrite has_mut_class in Hn. apply orb_false_iff in Hn.
    destruct Hn as [Hq Hargs].
    destruct (q_eq_dec qual Mut) as [|Hne]; [discriminate|].
    rewrite (pwalk_class CT qual C args q0 l C0 As Hne).
    destruct (tviewf CT (S C0) q0 l C0 As C) as [Vs|]; auto.
    apply pwalks_none.
    clear - H Hargs. induction H as [|t r Ht _ IH]; constructor.
    + intros A. apply Ht. simpl in Hargs. apply orb_false_iff in Hargs. tauto.
    + apply IH. simpl in Hargs. apply orb_false_iff in Hargs. tauto.
  - destruct u as [|q1]; [reflexivity|]. destruct q1; try reflexivity.
    simpl in Hn. discriminate.
  - rewrite has_mut_head in Hn.
    rewrite (pwalk_head CT o n C args q0 l C0 As).
    destruct (tviewf CT (S C0) q0 l C0 As C) as [Vs|]; auto.
    apply pwalks_none.
    clear - H Hn. induction H as [|t r Ht _ IH]; constructor.
    + intros A. apply Ht. simpl in Hn. apply orb_false_iff in Hn. tauto.
    + apply IH. simpl in Hn. apply orb_false_iff in Hn. tauto.
Qed.

Lemma pfindsf_nomut : forall CT Bs Vs,
  Forall (fun B => has_mut B = false) Bs -> pfindsf CT Bs Vs = None.
Proof.
  intros CT Bs Vs H. revert Vs.
  induction H as [|B Bs HB _ IH]; intros [|V Vs]; simpl; auto.
  assert (Hf : pfindf CT B V = None).
  { destruct V as [q0 l C0 As]. unfold pfindf.
    destruct q0; auto using pwalk_nomut. }
  rewrite Hf. apply IH.
Qed.

(** A class without a written mutable position in its bounds has no
    payload. *)
Lemma pclassf_clean : forall CT C As,
  (forall def, find_class CT C = Some def ->
     Forall (fun B => has_mut B = false) (ctparams (signature def))) ->
  pclassf CT C As = None.
Proof.
  intros CT C As H. unfold pclassf.
  destruct (find_class CT C) as [def|] eqn:Hf; auto.
  apply pfindsf_nomut. auto.
Qed.

(** The class of a protected method. *)
Lemma nomut_bounds_clean : forall CT C sig def,
  find_class CT C = Some def ->
  nomut_bounds (method_tv_env CT C sig) ->
  Forall (fun B => has_mut B = false) (ctparams (signature def)).
Proof.
  intros CT C sig def Hfind Hnb. apply Forall_forall. intros B HB.
  apply In_nth_error in HB. destruct HB as [n Hn].
  assert (Hb : tv_bound (method_tv_env CT C sig) ClassVar n = Some B).
  { unfold tv_bound, method_tv_env, class_tparams. simpl. rewrite Hfind.
    exact Hn. }
  destruct (Hnb _ _ _ Hb) as [_ Hnm].
  eapply no_mut_has_mut; eauto.
Qed.

(** From a clean class upwards, the payloads are of the object's own label,
    and so is the label of its header frames. *)
Lemma pown_above_clean : forall CT L qo l C As D Vs,
  wf_class_table CT ->
  hinv CT L qo l C As ->
  pclassf CT C As = None ->
  oview CT qo l C As D Vs ->
  hinv CT L qo l D Vs /\ pown CT L l D Vs /\
  norm L (lf_mut (hfr CT qo l D Vs)) = norm L l.
Proof.
  intros CT L qo l C As D Vs Hwf Hi Hp Hv.
  assert (Hk : pown CT L l C As).
  { intros q' l' Hx. rewrite Hp in Hx. discriminate. }
  destruct (hinv_oview CT L qo l C As D Vs Hwf Hv Hi) as [HiD HkD].
  refine (conj HiD (conj (HkD Hk) _)).
  apply pown_hdr. exact (HkD Hk).
Qed.

Print Assumptions pown_above_clean.

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability
  ViewpointAdaptation.
Require Import Examples.PicoIfZeroCache.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreFrame
  PICOBridge.PicoCoreInvariant
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoDerivationPrefix PICOBridge.PicoSemanticConcurrency.

(** * Reference-Valued Caches

    A reference cache holds [null] until some thread stores a reference to a
    freshly allocated object.  Different threads may allocate different
    objects, so the cached value is not determined; what is determined is
    what such an object represents.  A cached reference is valid when it
    points to an immutable object of the view class whose abstract fields
    hold the values the initializer computes in the reference heap, and whose
    histories for those fields contain nothing else.

    Validity depends on the heap, so it is part of the shared invariant: every
    value in the history of the cache field is [null] or a valid reference.
    The invariant is preserved by every step of every thread except a write
    of an invalid value to the cache field. *)

Section ref_cache.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context (receiver : Loc) (h0 : heap).
  Context (cf : var) (Cv : class_name) (vals0 : list value).

  Let footprint := reachable_abs CT h0 receiver.

  Hypothesis Himm : forall l, footprint l ->
    exists C vals,
      runtime_getObj h0 l = Some (mkObj (mkruntime_type Imm_r C) vals).

  (** ** Valid references *)
  Definition view_ok (S : pico_core_state) (l : Loc) : Prop :=
    exists fs,
      runtime_getObj (pcs_heap S) l =
        Some (mkObj (mkruntime_type Imm_r Cv) fs) /\
      forall f,
        abstract_field CT Cv f ->
        nth_error fs f = nth_error vals0 f /\
        forall v0 w,
          nth_error vals0 f = Some v0 ->
          List.In w (values_written_to (pcs_weak S) (l, f)) ->
          w = v0.

  Definition val_ok (S : pico_core_state) (v : value) : Prop :=
    v = Null_a \/ exists l, v = Iot l /\ view_ok S l.

  (** ** The shared invariant *)
  Definition ref_inv (S : pico_core_state) : Prop :=
    heap_wm_type_agree (pcs_heap S) (pcs_weak S) /\
    footprint_state CT footprint h0 S /\
    (exists o, runtime_getObj (pcs_heap S) receiver = Some o) /\
    forall v,
      List.In v (values_written_to (pcs_weak S) (receiver, cf)) ->
      val_ok S v.

  Lemma getObj_update_field_same :
    forall h l rt fs f v,
      runtime_getObj h l = Some (mkObj rt fs) ->
      runtime_getObj (update_field h l f v) l =
        Some (mkObj rt (update f v fs)).
  Proof.
    intros h l rt fs f v Hobj.
    unfold update_field. rewrite Hobj. simpl.
    apply runtime_getObj_update_same. eapply runtime_getObj_dom. exact Hobj.
  Qed.

  Lemma imm_abstract_not_assignable :
    forall C f a,
      abstract_field CT C f ->
      sf_assignability_rel CT C f a ->
      runtime_vpa_assignability Imm_r a = Assignable ->
      False.
  Proof.
    intros C f a [_ [Hrda | Hfinal]] Hassign Hrun.
    - have Heq := sf_assignability_deterministic_rel CT C f a RDA Hassign Hrda.
      subst a. discriminate.
    - have Heq := sf_assignability_deterministic_rel CT C f a Final Hassign Hfinal.
      subst a. discriminate.
  Qed.

  (** A valid reference stays valid across every step of every thread. *)
  Lemma view_ok_step :
    forall e S e' S' l,
      heap_wm_type_agree (pcs_heap S) (pcs_weak S) ->
      view_ok S l ->
      pico_core_step CT e S e' S' ->
      view_ok S' l.
  Proof.
    intros e S e' S' l Hagree (fs & Hobj & Hfields) Hstep.
    inversion Hstep; subst; try (exists fs; split; assumption).
    - (* field write *)
      simpl in *.
      destruct (Nat.eq_dec loc_x l) as [-> | Hneq].
      + match goal with
        | Ho : runtime_getObj h l = Some ?ob |- _ =>
            rewrite Hobj in Ho; injection Ho as <-
        end.
        exists (update f val_y fs).
        split; [apply getObj_update_field_same; exact Hobj |].
        intros g Habs.
        assert (Hgf : f <> g).
        { intros ->. eapply imm_abstract_not_assignable; eassumption. }
        destruct (Hfields g Habs) as [Hval Hhist].
        split; [rewrite update_diff; assumption |].
        intros v0 w Hv0 Hin. eapply Hhist; [exact Hv0 |].
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq. congruence.
      + exists fs.
        split; [rewrite runtime_getObj_update_field_other_general; assumption |].
        intros g Habs. destruct (Hfields g Habs) as [Hval Hhist].
        split; [exact Hval |].
        intros v0 w Hv0 Hin. eapply Hhist; [exact Hv0 |].
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq _. congruence.
    - (* allocation *)
      simpl in *.
      have Hl := runtime_getObj_dom _ _ _ Hobj.
      exists fs.
      split; [rewrite runtime_getObj_last2; assumption |].
      intros g Habs. destruct (Hfields g Habs) as [Hval Hhist].
      split; [exact Hval |].
      intros v0 w Hv0 Hin. eapply Hhist; [exact Hv0 |].
      unfold values_written_to, history_of, pico_core_alloc_weak in Hin.
      simpl in Hin.
      destruct Hagree as [Hlen _].
      assert (Hneq : Nat.eqb l (length (wm_objs sigma)) = false)
        by (apply Nat.eqb_neq; lia).
      rewrite Hneq in Hin. exact Hin.
  Qed.

  Lemma val_ok_step :
    forall e S e' S' v,
      heap_wm_type_agree (pcs_heap S) (pcs_weak S) ->
      val_ok S v ->
      pico_core_step CT e S e' S' ->
      val_ok S' v.
  Proof.
    intros e S e' S' v Hagree [-> | (l & -> & Hview)] Hstep.
    - left. reflexivity.
    - right. exists l. split; [reflexivity |].
      eapply view_ok_step; eassumption.
  Qed.

  (** A value new in the cache field's history was written there by this
      step. *)
  Lemma cache_history_step :
    forall e S e' S' v,
      ref_inv S ->
      pico_core_step CT e S e' S' ->
      List.In v (values_written_to (pcs_weak S') (receiver, cf)) ->
      List.In v (values_written_to (pcs_weak S) (receiver, cf)) \/
      exists rGamma x y V K,
        e = CoreRun rGamma (SFldWrite x cf y) V K /\
        runtime_getVal rGamma x = Some (Iot receiver) /\
        runtime_getVal rGamma y = Some v.
  Proof.
    intros e S e' S' v (Hagree & _ & [o Hrecv] & _) Hstep Hin.
    inversion Hstep; subst; try (left; exact Hin).
    - (* field write *)
      simpl in *.
      destruct (Nat.eq_dec loc_x receiver) as [-> | Hneq];
        [destruct (Nat.eq_dec f cf) as [-> | Hneqf] |].
      + match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ =>
            have Hhist := wm_write_history_same _ _ _ _ _ _ Hw
        end.
        unfold values_written_to in *. rewrite Hhist in Hin.
        rewrite map_app in Hin. apply in_app_or in Hin.
        destruct Hin as [Hold | [<- | []]]; [left; exact Hold |].
        right. do 5 eexists. split; [reflexivity |]. split; eassumption.
      + left.
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq. congruence.
      + left.
        match goal with
        | Hw : wm_write _ _ _ _ _ _ |- _ => destruct Hw as [-> _]
        end.
        unfold values_written_to in *.
        rewrite history_of_append_write_other in Hin; [exact Hin |].
        intros Heq. injection Heq as Heq _. congruence.
    - (* allocation *)
      left. simpl in *.
      have Hl := runtime_getObj_dom _ _ _ Hrecv.
      unfold values_written_to, history_of, pico_core_alloc_weak in Hin.
      simpl in Hin.
      destruct Hagree as [Hlen _].
      assert (Hneq : Nat.eqb receiver (length (wm_objs sigma)) = false)
        by (apply Nat.eqb_neq; lia).
      rewrite Hneq in Hin. exact Hin.
  Qed.

  (** Every step preserves the invariant, provided a write to the cache
      field stores a valid value. *)
  Theorem ref_inv_step :
    forall e S e' S',
      ref_inv S ->
      pico_core_step CT e S e' S' ->
      (forall rGamma x y V K v,
         e = CoreRun rGamma (SFldWrite x cf y) V K ->
         runtime_getVal rGamma x = Some (Iot receiver) ->
         runtime_getVal rGamma y = Some v ->
         val_ok S v) ->
      ref_inv S'.
  Proof.
    intros e S e' S' Hinv Hstep Hwrite.
    pose proof Hinv as (Hagree & [Habs Hst] & [o Hrecv] & Hhist).
    destruct S as [h sigma]. simpl in *.
    destruct (core_step_preserves_footprint CT footprint h0 Himm e h sigma e' S'
      Habs Hagree Hstep) as [Habs' Hst'].
    split; [eapply (pico_core_step_preserves_heap_wm_type_agree CT e
      (mkPicoCoreState h sigma)); eassumption |].
    split; [split; [exact Habs' | exact (Hst' Hst)] |].
    split.
    - destruct (pico_core_step_preserves_heap_types CT e _ e' S' Hstep)
        as [_ Hty].
      specialize (Hty receiver (rt_type o)). simpl in Hty.
      unfold r_type in Hty. rewrite Hrecv in Hty. specialize (Hty eq_refl).
      destruct (runtime_getObj (pcs_heap S') receiver) as [o' |];
        [eauto | discriminate].
    - intros v Hin.
      destruct (cache_history_step e (mkPicoCoreState h sigma) e' S' v Hinv
        Hstep Hin) as [Hold | (rG & x & y & V & K & -> & Hx & Hy)].
      + eapply (val_ok_step _ (mkPicoCoreState h sigma));
          [exact Hagree | exact (Hhist v Hold) | exact Hstep].
      + eapply (val_ok_step _ (mkPicoCoreState h sigma));
          [exact Hagree | | exact Hstep].
        eapply Hwrite; [reflexivity | exact Hx | exact Hy].
  Qed.
End ref_cache.

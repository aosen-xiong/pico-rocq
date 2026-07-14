From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl updates.
From iris.base_logic Require Import own.

Require Import Core.GenericCacheProtocol.

(** * Generic Cache-History Ghost State

    This file provides PICO-independent Iris ownership for a single
    cache-history snapshot.

    The layer is deliberately small: an exclusive resource records the current
    snapshot for one object/protocol pair, while the public interpretation pairs
    that ownership with [CacheHistSnapshotOK].  A history extension updates the
    resource in place and therefore preserves its ghost name.  PICO-specific
    state interpretations instantiate this layer with concrete field histories. *)

(** Iris resource class for exclusive authoritative ownership of one
    protocol-specific cache-history snapshot. The exclusive resource can be
    updated in place, so successive snapshots retain one ghost identity. *)
Class genericCacheG {AbsVal : Type}
    (P : CacheProtocol AbsVal) (Σ : gFunctors) := GenericCacheG {
  generic_cache_history_inG :
    inG Σ (exclR (leibnizO (CacheHistorySnapshot P)))
}.

Section generic_cache_ghost_state.
  Context {AbsVal : Type}.
  Context (P : CacheProtocol AbsVal).
  Context `{!genericCacheG P Σ}.

(** Authoritative snapshot ownership. *)
  Definition generic_cache_history_auth
      (γ : gname) (snap : CacheHistorySnapshot P) : iProp Σ :=
    @own
      Σ
      (exclR (leibnizO (CacheHistorySnapshot P)))
      generic_cache_history_inG
      γ
      (Excl snap).

(** Public interpretation: ownership of the snapshot plus the pure fact that all
    values in it satisfy the cache protocol for abstract value [a]. *)
  Definition generic_cache_history_interp
      (γ : gname) (a : AbsVal) (snap : CacheHistorySnapshot P) : iProp Σ :=
    generic_cache_history_auth γ snap ∗
    ⌜CacheHistSnapshotOK P snap a⌝.

(** Semantic immutability interpretation for one provider object and one cache
    snapshot. *)
  Definition generic_semantic_immutability_interp
      {Obj : Type} (Stable : StableAbs Obj AbsVal)
      (γ : gname) (o : Obj) (a : AbsVal)
      (snap : CacheHistorySnapshot P) : iProp Σ :=
    ⌜Stable o a⌝ ∗ generic_cache_history_interp γ a snap.

(** Allocate authoritative ownership for a snapshot. *)
  Lemma generic_cache_history_auth_alloc snap :
    ⊢ |==> ∃ γ, generic_cache_history_auth γ snap.
  Proof.
    iMod (@own_alloc
      Σ
      (exclR (leibnizO (CacheHistorySnapshot P)))
      generic_cache_history_inG
      (Excl snap)) as (γ) "Hauth"; [done |].
    iModIntro.
    iExists γ. unfold generic_cache_history_auth. iExact "Hauth".
  Qed.

(** Allocate the public interpretation from a valid snapshot. *)
  Lemma generic_cache_history_interp_alloc a snap :
    forall (Hsnap : CacheHistSnapshotOK P snap a),
    ⊢ |==> ∃ γ, generic_cache_history_interp γ a snap.
  Proof.
    intros Hsnap.
    iMod (generic_cache_history_auth_alloc snap) as (γ) "Hauth".
    iModIntro.
    iExists γ.
    unfold generic_cache_history_interp.
    iSplitL "Hauth"; [iExact "Hauth" |].
    iPureIntro. exact Hsnap.
  Qed.

  Lemma generic_cache_history_interp_alloc_from_hist
      {Obj : Type} (Hist : CacheHistory P) o a :
    forall (Hhist : CacheHistOK P Hist o a),
    ⊢ |==> ∃ γ,
      generic_cache_history_interp
        γ
        a
        (@cache_history_snapshot Obj AbsVal P Hist o).
  Proof.
    intros Hhist.
    apply generic_cache_history_interp_alloc.
    eapply cache_hist_ok_snapshot.
    exact Hhist.
  Qed.

  Lemma generic_cache_history_interp_read_valid γ a snap
      k (v : cache_val P k) :
    generic_cache_history_interp γ a snap -∗
    ⌜In v (snap k)⌝ -∗
    ⌜cache_valid P a k v⌝.
  Proof.
    iIntros "Hinterp %Hin".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & %Hsnap)".
    iPureIntro.
    eapply Hsnap.
    exact Hin.
  Qed.

(** Reading a value contained in the snapshot preserves the interpretation and
    yields protocol validity for the observed value. *)
  Lemma generic_cache_history_interp_read_valid_preserve γ a snap
      k (v : cache_val P k) :
    generic_cache_history_interp γ a snap -∗
    ⌜In v (snap k)⌝ -∗
    generic_cache_history_interp γ a snap ∗
    ⌜cache_valid P a k v⌝.
  Proof.
    iIntros "Hinterp %Hin".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(Hauth & %Hsnap)".
    iSplitL "Hauth".
    - iSplitL "Hauth"; [iExact "Hauth" |].
      iPureIntro. exact Hsnap.
    - iPureIntro.
      eapply Hsnap.
      exact Hin.
  Qed.

  Lemma generic_cache_history_interp_valid_extension γ a snap snap' :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ -∗
    ⌜CacheHistSnapshotOK P snap' a⌝.
  Proof.
    iIntros "Hinterp %Hext".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & %Hsnap)".
    iPureIntro.
    eapply cache_hist_snapshot_ok_valid_extension; eauto.
  Qed.

(** A valid history extension updates the snapshot at the same ghost name. *)
  Lemma generic_cache_history_interp_valid_extension_update γ a snap snap' :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    generic_cache_history_interp γ a snap'.
  Proof.
    iIntros "Hinterp %Hext".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(Hauth & %Hsnap)".
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (@own_update Σ (exclR (leibnizO (CacheHistorySnapshot P)))
      generic_cache_history_inG γ (Excl snap) (Excl snap') with "Hauth")
      as "Hauth".
    { apply cmra_update_exclusive; done. }
    iModIntro.
    iSplitL "Hauth"; [iExact "Hauth" |].
    iPureIntro. exact Hsnap'.
  Qed.

  Lemma generic_cache_history_interp_valid_trace γ a snap tr :
    generic_cache_history_interp γ a snap -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜ValidTrace P a tr⌝.
  Proof.
    iIntros "Hinterp %Hreads".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & %Hsnap)".
    iPureIntro.
    eapply valid_trace_from_snapshot; eauto.
  Qed.

  Lemma generic_cache_history_interp_valid_trace_preserve γ a snap tr :
    generic_cache_history_interp γ a snap -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    generic_cache_history_interp γ a snap ∗
    ⌜ValidTrace P a tr⌝.
  Proof.
    iIntros "Hinterp %Hreads".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(Hauth & %Hsnap)".
    iSplitL "Hauth".
    - iSplitL "Hauth"; [iExact "Hauth" |].
      iPureIntro. exact Hsnap.
    - iPureIntro.
      eapply valid_trace_from_snapshot; eauto.
  Qed.

  Lemma generic_cache_history_interp_valid_trace_post_extension
      γ a snap snap' tr :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ -∗
    ⌜TraceReadsFromSnapshot P snap' tr⌝ -∗
    ⌜ValidTrace P a tr⌝.
  Proof.
    iIntros "Hinterp %Hext %Hreads".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & %Hsnap)".
    iPureIntro.
    eapply valid_trace_from_post_snapshot_with_valid_extension; eauto.
  Qed.

  Lemma generic_cache_history_interp_valid_trace_post_extension_preserve
      γ a snap snap' tr :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ -∗
    ⌜TraceReadsFromSnapshot P snap' tr⌝ -∗
    generic_cache_history_interp γ a snap ∗
    ⌜ValidTrace P a tr⌝.
  Proof.
    iIntros "Hinterp %Hext %Hreads".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(Hauth & %Hsnap)".
    iSplitL "Hauth".
    - iSplitL "Hauth"; [iExact "Hauth" |].
      iPureIntro. exact Hsnap.
    - iPureIntro.
      eapply valid_trace_from_post_snapshot_with_valid_extension; eauto.
  Qed.

  Lemma generic_cache_history_interp_writes_valid_extension
      {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ a snap snap' args tr :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝.
  Proof.
    iIntros "Hinterp %Hsafe %Hreads %Hext_by_writes".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    iPureIntro.
    eapply cache_safe_method_writes_snapshot_valid_extension; eauto.
  Qed.

  Lemma generic_cache_history_interp_writes_valid_extension_preserve
      {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ a snap snap' args tr :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))⌝ -∗
    generic_cache_history_interp γ a snap ∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝.
  Proof.
    iIntros "Hinterp %Hsafe %Hreads %Hext_by_writes".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(Hauth & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_writes_snapshot_valid_extension
        P snap snap' F run_with_cache_trace a args tr Hsafe Htrace
        Hext_by_writes) as Hext.
    iSplitL "Hauth".
    - iSplitL "Hauth"; [iExact "Hauth" |].
      iPureIntro. exact Hsnap.
    - iPureIntro.
      exact Hext.
  Qed.

  Lemma generic_cache_history_interp_writes_valid_extension_update
      {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ a snap snap' args tr :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))⌝ ==∗
    generic_cache_history_interp γ a snap'.
  Proof.
    iIntros "Hinterp %Hsafe %Hreads %Hext_by_writes".
    iDestruct
      (generic_cache_history_interp_writes_valid_extension_preserve
        F run_with_cache_trace with "Hinterp [] [] []")
      as "[Hinterp %Hext]".
    {
      iPureIntro.
      exact Hsafe.
    }
    {
      iPureIntro.
      exact Hreads.
    }
    {
      iPureIntro.
      exact Hext_by_writes.
    }
    iMod (generic_cache_history_interp_valid_extension_update with
      "Hinterp []") as "Hinterp".
    { iPureIntro. exact Hext. }
    iModIntro. iExact "Hinterp".
  Qed.

  Theorem generic_cache_history_interp_refines_pure
      {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ a snap args tr r :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    ⌜PureRecomputeResult F a args r⌝.
  Proof.
    iIntros "Hinterp %Hsafe %Hreads %Hexec".
    iDestruct
      (generic_cache_history_interp_valid_trace with "Hinterp []")
      as %Htrace.
    {
      iPureIntro.
      exact Hreads.
    }
    iPureIntro.
    eapply cache_safe_method_refines_pure; eauto.
  Qed.

  Theorem generic_cache_history_interp_refines_pure_preserve
      {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ a snap args tr r :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    generic_cache_history_interp γ a snap ∗
    ⌜PureRecomputeResult F a args r⌝.
  Proof.
    iIntros "Hinterp %Hsafe %Hreads %Hexec".
    iDestruct
      (generic_cache_history_interp_valid_trace_preserve with "Hinterp []")
      as "[Hinterp %Htrace]".
    {
      iPureIntro.
      exact Hreads.
    }
    iSplitL "Hinterp".
    - iExact "Hinterp".
    - iPureIntro.
      eapply cache_safe_method_refines_pure; eauto.
  Qed.

  Theorem generic_cache_history_interp_refines_pure_post_extension
      {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ a snap snap' args tr r :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ -∗
    ⌜TraceReadsFromSnapshot P snap' tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    ⌜PureRecomputeResult F a args r⌝.
  Proof.
    iIntros "Hinterp %Hsafe %Hext %Hreads %Hexec".
    iDestruct
      (generic_cache_history_interp_valid_trace_post_extension
        with "Hinterp [] []")
      as %Htrace.
    {
      iPureIntro.
      exact Hext.
    }
    {
      iPureIntro.
      exact Hreads.
    }
    iPureIntro.
    eapply cache_safe_method_refines_pure; eauto.
  Qed.

  Theorem generic_cache_history_interp_refines_pure_post_extension_preserve
      {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ a snap snap' args tr r :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ -∗
    ⌜TraceReadsFromSnapshot P snap' tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    generic_cache_history_interp γ a snap ∗
    ⌜PureRecomputeResult F a args r⌝.
  Proof.
    iIntros "Hinterp %Hsafe %Hext %Hreads %Hexec".
    iDestruct
      (generic_cache_history_interp_valid_trace_post_extension_preserve
        with "Hinterp [] []")
      as "[Hinterp %Htrace]".
    {
      iPureIntro.
      exact Hext.
    }
    {
      iPureIntro.
      exact Hreads.
    }
    iSplitL "Hinterp".
    - iExact "Hinterp".
    - iPureIntro.
      eapply cache_safe_method_refines_pure; eauto.
  Qed.

  Theorem generic_semantic_immutability_interp_method_post
      {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o a snap args tr r :
    generic_semantic_immutability_interp Stable γ o a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    ⌜r = F a args⌝ ∗
    generic_semantic_immutability_interp Stable γ o a snap.
  Proof.
    iIntros "Hsem %Hsafe %Hreads %Hexec".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(%Hstable & Hauth & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_refines_pure
        P F run_with_cache_trace Hsafe a args tr r Htrace Hexec) as Hresult.
    unfold PureRecomputeResult in Hresult.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp, generic_cache_history_interp.
      iSplit.
      + iPureIntro.
        exact Hstable.
      + iSplitL "Hauth"; [iExact "Hauth" |].
        iPureIntro. exact Hsnap.
  Qed.

  Theorem generic_semantic_immutability_interp_method_post_valid_extension_update
      {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o a snap snap' args tr r :
    generic_semantic_immutability_interp Stable γ o a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    ⌜r = F a args⌝ ∗
    generic_semantic_immutability_interp Stable γ o a snap'.
  Proof.
    iIntros "Hsem %Hsafe %Hreads %Hexec %Hext".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(%Hstable & Hauth & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_refines_pure
        P F run_with_cache_trace Hsafe a args tr r Htrace Hexec) as Hresult.
    unfold PureRecomputeResult in Hresult.
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (@own_update Σ (exclR (leibnizO (CacheHistorySnapshot P)))
      generic_cache_history_inG γ (Excl snap) (Excl snap') with "Hauth")
      as "Hauth".
    { apply cmra_update_exclusive; done. }
    iModIntro.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable.
      + iSplitL "Hauth"; [iExact "Hauth" |].
        iPureIntro. exact Hsnap'.
  Qed.

  Theorem generic_semantic_immutability_interp_method_post_valid_extension_update_post
      {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o o' a snap snap' args tr r :
    generic_semantic_immutability_interp Stable γ o a snap -∗
    ⌜Stable o' a⌝ -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    ⌜r = F a args⌝ ∗
    generic_semantic_immutability_interp Stable γ o' a snap'.
  Proof.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(_ & Hauth & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_refines_pure
        P F run_with_cache_trace Hsafe a args tr r Htrace Hexec) as Hresult.
    unfold PureRecomputeResult in Hresult.
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (@own_update Σ (exclR (leibnizO (CacheHistorySnapshot P)))
      generic_cache_history_inG γ (Excl snap) (Excl snap') with "Hauth")
      as "Hauth".
    { apply cmra_update_exclusive; done. }
    iModIntro.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable'.
      + iSplitL "Hauth"; [iExact "Hauth" |].
        iPureIntro. exact Hsnap'.
  Qed.

  Theorem generic_semantic_immutability_interp_method_post_valid_extension_update_post_trace
      {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o o' a snap snap' args tr r :
    generic_semantic_immutability_interp Stable γ o a snap -∗
    ⌜Stable o' a⌝ -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap' tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    ⌜r = F a args⌝ ∗
    generic_semantic_immutability_interp Stable γ o' a snap'.
  Proof.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(_ & Hauth & %Hsnap)".
    pose proof
      (valid_trace_from_post_snapshot_with_valid_extension
        P snap snap' a tr Hsnap Hext Hreads) as Htrace.
    pose proof
      (cache_safe_method_refines_pure
        P F run_with_cache_trace Hsafe a args tr r Htrace Hexec) as Hresult.
    unfold PureRecomputeResult in Hresult.
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (@own_update Σ (exclR (leibnizO (CacheHistorySnapshot P)))
      generic_cache_history_inG γ (Excl snap) (Excl snap') with "Hauth")
      as "Hauth".
    { apply cmra_update_exclusive; done. }
    iModIntro.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable'.
      + iSplitL "Hauth"; [iExact "Hauth" |].
        iPureIntro. exact Hsnap'.
  Qed.

  Theorem generic_trace_robust_semantic_immutability_interp_update_post
      {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o o' a snap snap' args tr r :
    generic_semantic_immutability_interp Stable γ o a snap -∗
    ⌜Stable o' a⌝ -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜trace_result_matches P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))⌝ ==∗
    ⌜r = F a args⌝ ∗
    generic_semantic_immutability_interp Stable γ o' a snap'.
  Proof.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext_by_writes".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(_ & Hauth & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_refines_pure
        P F run_with_cache_trace Hsafe a args tr r Htrace Hexec) as Hresult.
    unfold PureRecomputeResult in Hresult.
    pose proof
      (cache_safe_method_writes_snapshot_valid_extension
        P snap snap' F run_with_cache_trace a args tr Hsafe Htrace
        Hext_by_writes) as Hext.
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (@own_update Σ (exclR (leibnizO (CacheHistorySnapshot P)))
      generic_cache_history_inG γ (Excl snap) (Excl snap') with "Hauth")
      as "Hauth".
    { apply cmra_update_exclusive; done. }
    iModIntro.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable'.
      + iSplitL "Hauth"; [iExact "Hauth" |].
        iPureIntro. exact Hsnap'.
  Qed.
End generic_cache_ghost_state.

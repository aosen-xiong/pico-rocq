From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth agree.
From iris.base_logic Require Import own.

Require Import Core.GenericCacheProtocol.

(** * Generic Cache-History Ghost State

    This file provides PICO-independent Iris ownership for a single
    cache-history snapshot.

    The first ghost-backed layer is deliberately small: an authoritative
    agreement resource records the snapshot for one object/protocol pair, while
    the public interpretation pairs that ownership with the generic
    [CacheHistSnapshotOK] validity predicate.  PICO-specific state
    interpretations can instantiate this layer with their concrete field
    histories. *)

(** Iris resource class for authoritative agreement over one protocol-specific
    cache-history snapshot. *)
Class genericCacheG {AbsVal : Type}
    (P : CacheProtocol AbsVal) (Σ : gFunctors) := GenericCacheG {
  generic_cache_history_inG :
    inG
      Σ
      (authR
        (optionUR
          (agreeR (leibnizO (CacheHistorySnapshot P)))))
}.

Section generic_cache_ghost_state.
  Context {AbsVal : Type}.
  Context (P : CacheProtocol AbsVal).
  Context `{!genericCacheG P Σ}.

  Definition generic_cache_history_elem
      (snap : CacheHistorySnapshot P) :
      optionUR (agreeR (leibnizO (CacheHistorySnapshot P))) :=
    Some (to_agree (A := leibnizO (CacheHistorySnapshot P)) snap).

(** Authoritative snapshot ownership. *)
  Definition generic_cache_history_auth
      (γ : gname) (snap : CacheHistorySnapshot P) : iProp Σ :=
    @own
      Σ
      (authR (optionUR (agreeR (leibnizO (CacheHistorySnapshot P)))))
      generic_cache_history_inG
      γ
      (● generic_cache_history_elem snap).

(** Persistent fragment witnessing the same snapshot. *)
  Definition generic_cache_history_own
      (γ : gname) (snap : CacheHistorySnapshot P) : iProp Σ :=
    @own
      Σ
      (authR (optionUR (agreeR (leibnizO (CacheHistorySnapshot P)))))
      generic_cache_history_inG
      γ
      (◯ generic_cache_history_elem snap).

(** Public interpretation: ownership of the snapshot plus the pure fact that all
    values in it satisfy the cache protocol for abstract value [a]. *)
  Definition generic_cache_history_interp
      (γ : gname) (a : AbsVal) (snap : CacheHistorySnapshot P) : iProp Σ :=
    generic_cache_history_auth γ snap ∗
    generic_cache_history_own γ snap ∗
    ⌜CacheHistSnapshotOK P snap a⌝.

(** Semantic immutability interpretation for one provider object and one cache
    snapshot. *)
  Definition generic_semantic_immutability_interp
      {Obj : Type} (Stable : StableAbs Obj AbsVal)
      (γ : gname) (o : Obj) (a : AbsVal)
      (snap : CacheHistorySnapshot P) : iProp Σ :=
    ⌜Stable o a⌝ ∗ generic_cache_history_interp γ a snap.

  Global Instance generic_cache_history_own_persistent γ snap :
    Persistent (generic_cache_history_own γ snap).
  Proof. apply _. Qed.

(** Allocate authoritative and persistent ownership for a snapshot. *)
  Lemma generic_cache_history_own_alloc snap :
    ⊢ |==> ∃ γ,
      generic_cache_history_auth γ snap ∗
      generic_cache_history_own γ snap.
  Proof.
    iMod (@own_alloc
      Σ
      (authR (optionUR (agreeR (leibnizO (CacheHistorySnapshot P)))))
      generic_cache_history_inG
      (● generic_cache_history_elem snap ⋅
       ◯ generic_cache_history_elem snap))
      as (γ) "[Hauth #Hown]".
    {
      apply auth_both_valid.
      split; done.
    }
    iModIntro.
    iExists γ.
    iSplitL "Hauth".
    - unfold generic_cache_history_auth.
      iExact "Hauth".
    - unfold generic_cache_history_own.
      iExact "Hown".
  Qed.

(** Allocate the public interpretation from a valid snapshot. *)
  Lemma generic_cache_history_interp_alloc a snap :
    forall (Hsnap : CacheHistSnapshotOK P snap a),
    ⊢ |==> ∃ γ, generic_cache_history_interp γ a snap.
  Proof.
    intros Hsnap.
    iMod (generic_cache_history_own_alloc snap) as (γ) "[Hauth #Hown]".
    iModIntro.
    iExists γ.
    unfold generic_cache_history_interp.
    iSplitL "Hauth".
    - iExact "Hauth".
    - iSplit.
      + iExact "Hown".
      + iPureIntro.
        exact Hsnap.
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

  Lemma generic_cache_history_interp_snapshot γ a snap :
    generic_cache_history_interp γ a snap -∗
    generic_cache_history_interp γ a snap ∗
    generic_cache_history_own γ snap.
  Proof.
    iIntros "Hinterp".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(Hauth & #Hown & %Hsnap)".
    iSplitL "Hauth".
    - iFrame.
      iSplit; first iExact "Hown".
      iPureIntro.
      exact Hsnap.
    - iExact "Hown".
  Qed.

  Lemma generic_cache_history_interp_read_valid γ a snap
      k (v : cache_val P k) :
    generic_cache_history_interp γ a snap -∗
    ⌜In v (snap k)⌝ -∗
    ⌜cache_valid P a k v⌝.
  Proof.
    iIntros "Hinterp %Hin".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & _ & %Hsnap)".
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
    iDestruct "Hinterp" as "(Hauth & #Hown & %Hsnap)".
    iSplitL "Hauth".
    - iSplitL "Hauth".
      + iExact "Hauth".
      + iSplit.
        * iExact "Hown".
        * iPureIntro.
          exact Hsnap.
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
    iDestruct "Hinterp" as "(_ & _ & %Hsnap)".
    iPureIntro.
    eapply cache_hist_snapshot_ok_valid_extension; eauto.
  Qed.

(** Valid history extensions can be reallocated as a fresh snapshot
    interpretation. *)
  Lemma generic_cache_history_interp_valid_extension_alloc γ a snap snap' :
    generic_cache_history_interp γ a snap -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    ∃ γ', generic_cache_history_interp γ' a snap'.
  Proof.
    iIntros "Hinterp %Hext".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & _ & %Hsnap)".
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (generic_cache_history_interp_alloc a snap' Hsnap')
      as (γ') "Hinterp'".
    iModIntro.
    iExists γ'.
    iExact "Hinterp'".
  Qed.

  Lemma generic_cache_history_interp_valid_trace γ a snap tr :
    generic_cache_history_interp γ a snap -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜ValidTrace P a tr⌝.
  Proof.
    iIntros "Hinterp %Hreads".
    unfold generic_cache_history_interp.
    iDestruct "Hinterp" as "(_ & _ & %Hsnap)".
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
    iDestruct "Hinterp" as "(Hauth & #Hown & %Hsnap)".
    iSplitL "Hauth".
    - iSplitL "Hauth".
      + iExact "Hauth".
      + iSplit.
        * iExact "Hown".
        * iPureIntro.
          exact Hsnap.
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
    iDestruct "Hinterp" as "(_ & _ & %Hsnap)".
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
    iDestruct "Hinterp" as "(Hauth & #Hown & %Hsnap)".
    iSplitL "Hauth".
    - iSplitL "Hauth".
      + iExact "Hauth".
      + iSplit.
        * iExact "Hown".
        * iPureIntro.
          exact Hsnap.
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
    iDestruct "Hinterp" as "(_ & _ & %Hsnap)".
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
    iDestruct "Hinterp" as "(Hauth & #Hown & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_writes_snapshot_valid_extension
        P snap snap' F run_with_cache_trace a args tr Hsafe Htrace
        Hext_by_writes) as Hext.
    iSplitL "Hauth".
    - iSplitL "Hauth".
      + iExact "Hauth".
      + iSplit.
        * iExact "Hown".
        * iPureIntro.
          exact Hsnap.
    - iPureIntro.
      exact Hext.
  Qed.

  Lemma generic_cache_history_interp_writes_valid_extension_alloc
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
    ∃ γ', generic_cache_history_interp γ' a snap'.
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
    iApply (generic_cache_history_interp_valid_extension_alloc with
      "Hinterp []").
    iPureIntro.
    exact Hext.
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
    ⌜r = F a args⌝ ∗
    generic_semantic_immutability_interp Stable γ o a snap.
  Proof.
    iIntros "Hsem %Hsafe %Hreads %Hexec".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(%Hstable & Hauth & #Hown & %Hsnap)".
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
      + iSplitL "Hauth".
        * iExact "Hauth".
        * iSplit.
          -- iExact "Hown".
          -- iPureIntro.
             exact Hsnap.
  Qed.

  Theorem generic_semantic_immutability_interp_method_post_valid_extension_alloc
      {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o a snap snap' args tr r :
    generic_semantic_immutability_interp Stable γ o a snap -∗
    ⌜CacheSafeMethod P F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromSnapshot P snap tr⌝ -∗
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    ∃ γ',
      ⌜r = F a args⌝ ∗
      generic_semantic_immutability_interp Stable γ' o a snap'.
  Proof.
    iIntros "Hsem %Hsafe %Hreads %Hexec %Hext".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(%Hstable & Hauth & #Hown & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_refines_pure
        P F run_with_cache_trace Hsafe a args tr r Htrace Hexec) as Hresult.
    unfold PureRecomputeResult in Hresult.
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (generic_cache_history_interp_alloc a snap' Hsnap')
      as (γ') "Hinterp'".
    iModIntro.
    iExists γ'.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable.
      + iExact "Hinterp'".
  Qed.

  Theorem generic_semantic_immutability_interp_method_post_valid_extension_alloc_post
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    ∃ γ',
      ⌜r = F a args⌝ ∗
      generic_semantic_immutability_interp Stable γ' o' a snap'.
  Proof.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(_ & Hauth & #Hown & %Hsnap)".
    pose proof
      (valid_trace_from_snapshot P snap a tr Hsnap Hreads) as Htrace.
    pose proof
      (cache_safe_method_refines_pure
        P F run_with_cache_trace Hsafe a args tr r Htrace Hexec) as Hresult.
    unfold PureRecomputeResult in Hresult.
    pose proof
      (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
      as Hsnap'.
    iMod (generic_cache_history_interp_alloc a snap' Hsnap')
      as (γ') "Hinterp'".
    iModIntro.
    iExists γ'.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable'.
      + iExact "Hinterp'".
  Qed.

  Theorem generic_semantic_immutability_interp_method_post_valid_extension_alloc_post_trace
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝ ==∗
    ∃ γ',
      ⌜r = F a args⌝ ∗
      generic_semantic_immutability_interp Stable γ' o' a snap'.
  Proof.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(_ & Hauth & #Hown & %Hsnap)".
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
    iMod (generic_cache_history_interp_alloc a snap' Hsnap')
      as (γ') "Hinterp'".
    iModIntro.
    iExists γ'.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable'.
      + iExact "Hinterp'".
  Qed.

  Theorem generic_trace_robust_semantic_immutability_interp_alloc_post
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
    ⌜weak_exec_matches_trace P run_with_cache_trace a args tr r⌝ -∗
    ⌜CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))⌝ ==∗
    ∃ γ',
      ⌜r = F a args⌝ ∗
      generic_semantic_immutability_interp Stable γ' o' a snap'.
  Proof.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext_by_writes".
    unfold generic_semantic_immutability_interp, generic_cache_history_interp.
    iDestruct "Hsem" as "(_ & Hauth & #Hown & %Hsnap)".
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
    iMod (generic_cache_history_interp_alloc a snap' Hsnap')
      as (γ') "Hinterp'".
    iModIntro.
    iExists γ'.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - unfold generic_semantic_immutability_interp.
      iSplit.
      + iPureIntro.
        exact Hstable'.
      + iExact "Hinterp'".
  Qed.
End generic_cache_ghost_state.

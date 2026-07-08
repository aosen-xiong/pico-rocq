From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import own.

Require Import Syntax PICOBridge.PicoMemoryModel.
Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState Core.GenericDerivedCache.

(** * Iris Adapter for PICO Derived-Cache Histories

    This file instantiates the generic Iris cache-history interpretation with
    the concrete PICO weak-memory history at one field address.  It connects
    [wm_read] observations to snapshot membership, then reuses the generic
    ghost-state lemmas to prove read validity and valid-trace facts. *)

(** Snapshot of the target derived-cache field in one weak-memory state. *)
Definition wm_derived_cache_snapshot
    (derived : list value -> nat) (addr : FieldAddr) (sigma : wm_state) :
    CacheHistorySnapshot (derived_cache_protocol derived) :=
  @cache_history_snapshot
    wm_state
    (list value)
    (derived_cache_protocol derived)
    (wm_derived_cache_history derived addr)
    sigma.

Section generic_derived_cache_iris.
  Context {PROP : bi}.

  Lemma wm_read_valid_via_generic_cache_hist_okI :
    forall `{CacheMemoryModel} sigma V addr v V' derived abs_vals
      (Hhist : CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        sigma
        abs_vals)
      (Hread : wm_read sigma V addr v V'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem sigma V addr v V' derived abs_vals Hhist Hread.
    iPureIntro.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  Qed.

  Lemma wm_cache_history_state_valid_extension_genericI :
    forall sigma sigma' addr derived abs_vals
      (Hstate' : wm_cache_history_state sigma' addr derived abs_vals),
      ⊢ (⌜CacheHistValidExtension
            (derived_cache_protocol derived)
            (wm_derived_cache_history derived addr)
            (wm_derived_cache_history derived addr)
            sigma
            sigma'
            abs_vals⌝ : PROP).
  Proof.
    intros sigma sigma' addr derived abs_vals Hstate'.
    iPureIntro.
    eapply wm_cache_history_state_valid_extension_generic; eauto.
  Qed.

  Lemma wm_steps_valid_extension_from_allowed_writes_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_transition_writes_allowed_for_cache
          (wc_state c1) (wc_state c2) addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ (⌜CacheHistValidExtension
            (derived_cache_protocol derived)
            (wm_derived_cache_history derived addr)
            (wm_derived_cache_history derived addr)
            (wc_state cfg)
            (wc_state cfg')
            abs_vals⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals
           Hsteps Hallowed Hstate.
    iPureIntro.
    eapply wm_steps_valid_extension_from_allowed_writes_generic; eauto.
  Qed.

  Lemma wm_steps_valid_extension_from_thread_allowed_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        forall i t,
          nth_error (wc_threads c1) i = Some t ->
          wm_thread_writes_allowed_for_cache t addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ (⌜CacheHistValidExtension
            (derived_cache_protocol derived)
            (wm_derived_cache_history derived addr)
            (wm_derived_cache_history derived addr)
            (wc_state cfg)
            (wc_state cfg')
            abs_vals⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals
           Hsteps Hallowed Hstate.
    iPureIntro.
    eapply wm_steps_valid_extension_from_thread_allowed_generic; eauto.
  Qed.

  Lemma wm_steps_valid_extension_from_config_allowed_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_config_threads_allowed_for_cache c1 addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ (⌜CacheHistValidExtension
            (derived_cache_protocol derived)
            (wm_derived_cache_history derived addr)
            (wm_derived_cache_history derived addr)
            (wc_state cfg)
            (wc_state cfg')
            abs_vals⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals
           Hsteps Hallowed Hstate.
    iPureIntro.
    eapply wm_steps_valid_extension_from_config_allowed_generic; eauto.
  Qed.

  Lemma wm_steps_valid_extension_from_closed_config_safe_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hsafe : cache_safe_config cfg addr derived abs_vals)
      (Hclosed : forall c1 c2,
        wm_step CT c1 c2 ->
        cache_safe_config c1 addr derived abs_vals ->
        cache_safe_config c2 addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ (⌜CacheHistValidExtension
            (derived_cache_protocol derived)
            (wm_derived_cache_history derived addr)
            (wm_derived_cache_history derived addr)
            (wc_state cfg)
            (wc_state cfg')
            abs_vals⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals
           Hsteps Hsafe Hclosed Hstate.
    iPureIntro.
    eapply wm_steps_valid_extension_from_closed_config_safe_generic; eauto.
  Qed.

End generic_derived_cache_iris.

(** ** Ghost-Backed PICO Derived-Cache Interpretation *)

Section generic_derived_cache_ghost.
  Context `{Hmem : CacheMemoryModel}.
  Context {Σ : gFunctors}.

(** Allocate a generic cache-history interpretation from a concrete PICO
    [CacheHistOK] fact. *)
  Lemma wm_derived_cache_history_interp_alloc :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma addr abs_vals
      (Hhist : CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        sigma
        abs_vals),
      ⊢ |==> ∃ γ,
        generic_cache_history_interp
          (derived_cache_protocol derived)
          γ
          abs_vals
          (wm_derived_cache_snapshot derived addr sigma).
  Proof.
    intros derived Hgeneric sigma addr abs_vals Hhist.
    apply generic_cache_history_interp_alloc.
    unfold wm_derived_cache_snapshot.
    eapply cache_hist_ok_snapshot.
    exact Hhist.
  Qed.

(** Allocate the same interpretation from the concrete
    [wm_cache_history_state] predicate. *)
  Lemma wm_cache_history_state_interp_alloc :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma addr abs_vals
      (Hstate : wm_cache_history_state sigma addr derived abs_vals),
      ⊢ |==> ∃ γ,
        generic_cache_history_interp
          (derived_cache_protocol derived)
          γ
          abs_vals
          (wm_derived_cache_snapshot derived addr sigma).
  Proof.
    intros derived Hgeneric sigma addr abs_vals Hstate.
    apply wm_derived_cache_history_interp_alloc.
    eapply wm_cache_history_state_generic.
    exact Hstate.
  Qed.

(** A weak-memory read of the target cache field appears in the snapshot. *)
  Lemma wm_read_in_derived_cache_snapshot :
    forall derived sigma V addr v V'
      (Hread : wm_read sigma V addr v V'),
      In v (wm_derived_cache_snapshot derived addr sigma DerivedCacheField).
  Proof.
    intros derived sigma V addr v V' Hread.
    unfold wm_derived_cache_snapshot.
    simpl.
    eapply wm_derived_cache_read_from_history.
    exists V, V'.
    exact Hread.
  Qed.

(** A concrete read trace from the target field is a snapshot-read trace for
    the generic protocol. *)
  Lemma wm_trace_reads_from_derived_cache_snapshot :
    forall derived sigma addr tr
      (Hreads : TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        sigma
        tr),
      TraceReadsFromSnapshot
        (derived_cache_protocol derived)
        (wm_derived_cache_snapshot derived addr sigma)
        tr.
  Proof.
    intros derived sigma addr tr Hreads.
    unfold TraceReadsFromHistory, TraceReadsFromSnapshot in *.
    induction Hreads as [|obs tr Hread _ IH]; constructor.
    - destruct obs as [[] v].
      simpl in *.
      destruct Hread as [V [V' Hread]].
      eapply wm_read_in_derived_cache_snapshot.
      exact Hread.
    - exact IH.
  Qed.

(** Ghost-backed read-validity theorem for one PICO derived-cache read. *)
  Lemma wm_derived_cache_history_interp_read_valid :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma V addr v V' abs_vals γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜wm_read sigma V addr v V'⌝ -∗
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝.
  Proof.
    intros derived Hgeneric sigma V addr v V' abs_vals γ.
    iIntros "Hinterp %Hread".
    iApply (generic_cache_history_interp_read_valid with "Hinterp").
    iPureIntro.
    eapply wm_read_in_derived_cache_snapshot.
    exact Hread.
  Qed.

  Lemma wm_derived_cache_history_interp_read_valid_preserve :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma V addr v V' abs_vals γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜wm_read sigma V addr v V'⌝ -∗
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝.
  Proof.
    intros derived Hgeneric sigma V addr v V' abs_vals γ.
    iIntros "Hinterp %Hread".
    iApply (generic_cache_history_interp_read_valid_preserve with "Hinterp").
    iPureIntro.
    eapply wm_read_in_derived_cache_snapshot.
    exact Hread.
  Qed.

(** Ghost-backed validity theorem for a whole PICO derived-cache read trace. *)
  Lemma wm_derived_cache_history_interp_valid_trace :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma addr abs_vals γ tr,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      ⌜ValidTrace (derived_cache_protocol derived) abs_vals tr⌝.
  Proof.
    intros derived Hgeneric sigma addr abs_vals γ tr.
    iIntros "Hinterp %Hreads".
    iApply (generic_cache_history_interp_valid_trace with "Hinterp").
    iPureIntro.
    eapply wm_trace_reads_from_derived_cache_snapshot.
    exact Hreads.
  Qed.

  Lemma wm_derived_cache_history_interp_valid_trace_preserve :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma addr abs_vals γ tr,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜ValidTrace (derived_cache_protocol derived) abs_vals tr⌝.
  Proof.
    intros derived Hgeneric sigma addr abs_vals γ tr.
    iIntros "Hinterp %Hreads".
    iApply (generic_cache_history_interp_valid_trace_preserve with "Hinterp").
    iPureIntro.
    eapply wm_trace_reads_from_derived_cache_snapshot.
    exact Hreads.
  Qed.

  Lemma wm_derived_cache_history_interp_valid_trace_post_extension :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma sigma' addr abs_vals γ tr,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheHistValidExtension
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          abs_vals⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma'
          tr⌝ -∗
      ⌜ValidTrace (derived_cache_protocol derived) abs_vals tr⌝.
  Proof.
    intros derived Hgeneric sigma sigma' addr abs_vals γ tr.
    iIntros "Hinterp %Hext %Hreads".
    iApply
      (generic_cache_history_interp_valid_trace_post_extension
        (derived_cache_protocol derived)
        with "Hinterp [] []").
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_valid_extension_snapshot.
      exact Hext.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
  Qed.

  Lemma wm_derived_cache_history_interp_valid_trace_post_extension_preserve :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      sigma sigma' addr abs_vals γ tr,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheHistValidExtension
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          abs_vals⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma'
          tr⌝ -∗
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜ValidTrace (derived_cache_protocol derived) abs_vals tr⌝.
  Proof.
    intros derived Hgeneric sigma sigma' addr abs_vals γ tr.
    iIntros "Hinterp %Hext %Hreads".
    iApply
      (generic_cache_history_interp_valid_trace_post_extension_preserve
        (derived_cache_protocol derived)
        with "Hinterp [] []").
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_valid_extension_snapshot.
      exact Hext.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
  Qed.

  Theorem wm_derived_cache_history_interp_refines_pure :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma addr abs_vals γ args tr r,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      ⌜weak_exec_matches_trace
          (derived_cache_protocol derived)
          run_with_cache_trace
          abs_vals
          args
          tr
          r⌝ -∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    intros derived Hgeneric Args Result F run sigma addr abs_vals γ args tr r.
    iIntros "Hinterp %Hsafe %Hreads %Hexec".
    iApply
      (generic_cache_history_interp_refines_pure
        (derived_cache_protocol derived)
        F
        run
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        args
        tr
        r
        with "Hinterp [] [] []").
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem wm_derived_cache_history_interp_refines_pure_preserve :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma addr abs_vals γ args tr r,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      ⌜weak_exec_matches_trace
          (derived_cache_protocol derived)
          run_with_cache_trace
          abs_vals
          args
          tr
          r⌝ -∗
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    intros derived Hgeneric Args Result F run sigma addr abs_vals γ args tr r.
    iIntros "Hinterp %Hsafe %Hreads %Hexec".
    iApply
      (generic_cache_history_interp_refines_pure_preserve
        (derived_cache_protocol derived)
        F
        run
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        args
        tr
        r
        with "Hinterp [] [] []").
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem wm_derived_cache_history_interp_refines_pure_post_extension :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma sigma' addr abs_vals γ args tr r,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
      ⌜CacheHistValidExtension
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          abs_vals⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma'
          tr⌝ -∗
      ⌜weak_exec_matches_trace
          (derived_cache_protocol derived)
          run_with_cache_trace
          abs_vals
          args
          tr
          r⌝ -∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    intros derived Hgeneric Args Result F run sigma sigma' addr abs_vals γ
      args tr r.
    iIntros "Hinterp %Hsafe %Hext %Hreads %Hexec".
    iApply
      (generic_cache_history_interp_refines_pure_post_extension
        (derived_cache_protocol derived)
        F
        run
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        (wm_derived_cache_snapshot derived addr sigma')
        args
        tr
        r
        with "Hinterp [] [] [] []").
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_valid_extension_snapshot.
      exact Hext.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem wm_derived_cache_history_interp_refines_pure_post_extension_preserve :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma sigma' addr abs_vals γ args tr r,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
      ⌜CacheHistValidExtension
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          abs_vals⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma'
          tr⌝ -∗
      ⌜weak_exec_matches_trace
          (derived_cache_protocol derived)
          run_with_cache_trace
          abs_vals
          args
          tr
          r⌝ -∗
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    intros derived Hgeneric Args Result F run sigma sigma' addr abs_vals γ
      args tr r.
    iIntros "Hinterp %Hsafe %Hext %Hreads %Hexec".
    iApply
      (generic_cache_history_interp_refines_pure_post_extension_preserve
        (derived_cache_protocol derived)
        F
        run
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        (wm_derived_cache_snapshot derived addr sigma')
        args
        tr
        r
        with "Hinterp [] [] [] []").
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_valid_extension_snapshot.
      exact Hext.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Lemma wm_derived_cache_history_interp_writes_valid_extension :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma sigma' addr abs_vals γ args tr,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      ⌜CacheHistExtendsByTrace
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          (run_writes (run_with_cache_trace abs_vals args tr))⌝ -∗
      ⌜CacheHistValidExtension
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          abs_vals⌝.
  Proof.
    intros derived Hgeneric Args Result F run sigma sigma' addr abs_vals γ
      args tr.
    iIntros "Hinterp %Hsafe %Hreads %Hext_by_writes".
    iDestruct
      (wm_derived_cache_history_interp_valid_trace
        derived sigma addr abs_vals γ tr with "Hinterp []")
      as %Htrace.
    {
      iPureIntro.
      exact Hreads.
    }
    iPureIntro.
    eapply cache_safe_method_writes_history_valid_extension; eauto.
  Qed.

  Lemma wm_derived_cache_history_interp_writes_valid_extension_alloc :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma sigma' addr abs_vals γ args tr,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      ⌜CacheHistExtendsByTrace
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          (run_writes (run_with_cache_trace abs_vals args tr))⌝ ==∗
      ∃ γ',
        generic_cache_history_interp
          (derived_cache_protocol derived)
          γ'
          abs_vals
          (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    intros derived Hgeneric Args Result F run sigma sigma' addr abs_vals γ
      args tr.
    iIntros "Hinterp %Hsafe %Hreads %Hext_by_writes".
    iApply
      (generic_cache_history_interp_writes_valid_extension_alloc
        (derived_cache_protocol derived)
        F
        run
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        (wm_derived_cache_snapshot derived addr sigma')
        args
        tr
        with "Hinterp [] [] []").
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_extends_by_trace_snapshot.
      exact Hext_by_writes.
  Qed.

  Theorem wm_derived_cache_semantic_immutability_method_post_valid_extension_alloc :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (Stable : StableAbs wm_state (list value))
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma sigma' addr abs_vals γ args tr r,
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ
        sigma
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜Stable sigma' abs_vals⌝ -∗
      ⌜CacheSafeMethod
          (derived_cache_protocol derived)
          F
          run_with_cache_trace⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      ⌜weak_exec_matches_trace
          (derived_cache_protocol derived)
          run_with_cache_trace
          abs_vals
          args
          tr
          r⌝ -∗
      ⌜CacheHistValidExtension
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          abs_vals⌝ ==∗
      ∃ γ',
        ⌜r = F abs_vals args⌝ ∗
        generic_semantic_immutability_interp
          (derived_cache_protocol derived)
          Stable
          γ'
          sigma'
          abs_vals
          (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    intros derived Hgeneric Args Result Stable F run sigma sigma' addr
           abs_vals γ args tr r.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext".
    iApply
      (generic_semantic_immutability_interp_method_post_valid_extension_alloc_post
        (derived_cache_protocol derived)
        Stable
        F
        run
        γ
        sigma
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        (wm_derived_cache_snapshot derived addr sigma')
        args
        tr
        r
        with "Hsem [] [] [] [] []").
    - iPureIntro.
      exact Hstable'.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_valid_extension_snapshot.
      exact Hext.
  Qed.

  Theorem wm_derived_cache_semantic_immutability_method_post_valid_extension_alloc_post_trace :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (Stable : StableAbs wm_state (list value))
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma sigma' addr abs_vals γ args tr r,
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ
        sigma
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜Stable sigma' abs_vals⌝ -∗
      ⌜CacheSafeMethod
          (derived_cache_protocol derived)
          F
          run_with_cache_trace⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma'
          tr⌝ -∗
      ⌜weak_exec_matches_trace
          (derived_cache_protocol derived)
          run_with_cache_trace
          abs_vals
          args
          tr
          r⌝ -∗
      ⌜CacheHistValidExtension
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          abs_vals⌝ ==∗
      ∃ γ',
        ⌜r = F abs_vals args⌝ ∗
        generic_semantic_immutability_interp
          (derived_cache_protocol derived)
          Stable
          γ'
          sigma'
          abs_vals
          (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    intros derived Hgeneric Args Result Stable F run sigma sigma' addr
           abs_vals γ args tr r.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext".
    iApply
      (generic_semantic_immutability_interp_method_post_valid_extension_alloc_post_trace
        (derived_cache_protocol derived)
        Stable
        F
        run
        γ
        sigma
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        (wm_derived_cache_snapshot derived addr sigma')
        args
        tr
        r
        with "Hsem [] [] [] [] []").
    - iPureIntro.
      exact Hstable'.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_valid_extension_snapshot.
      exact Hext.
  Qed.

  Theorem wm_derived_cache_trace_robust_semantic_immutability_alloc_post :
    forall derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      {Args Result : Type}
      (Stable : StableAbs wm_state (list value))
      (F : list value -> Args -> Result)
      (run_with_cache_trace :
        list value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      sigma sigma' addr abs_vals γ args tr r,
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ
        sigma
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) -∗
      ⌜Stable sigma' abs_vals⌝ -∗
      ⌜CacheSafeMethod
          (derived_cache_protocol derived)
          F
          run_with_cache_trace⌝ -∗
      ⌜TraceReadsFromHistory
          (derived_cache_protocol derived)
          (wm_derived_cache_read derived addr)
          sigma
          tr⌝ -∗
      ⌜weak_exec_matches_trace
          (derived_cache_protocol derived)
          run_with_cache_trace
          abs_vals
          args
          tr
          r⌝ -∗
      ⌜CacheHistExtendsByTrace
          (derived_cache_protocol derived)
          (wm_derived_cache_history derived addr)
          (wm_derived_cache_history derived addr)
          sigma
          sigma'
          (run_writes (run_with_cache_trace abs_vals args tr))⌝ ==∗
      ∃ γ',
        ⌜r = F abs_vals args⌝ ∗
        generic_semantic_immutability_interp
          (derived_cache_protocol derived)
          Stable
          γ'
          sigma'
          abs_vals
          (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    intros derived Hgeneric Args Result Stable F run sigma sigma' addr
           abs_vals γ args tr r.
    iIntros "Hsem %Hstable' %Hsafe %Hreads %Hexec %Hext_by_writes".
    iApply
      (generic_trace_robust_semantic_immutability_interp_alloc_post
        (derived_cache_protocol derived)
        Stable
        F
        run
        γ
        sigma
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma)
        (wm_derived_cache_snapshot derived addr sigma')
        args
        tr
        r
        with "Hsem [] [] [] [] []").
    - iPureIntro.
      exact Hstable'.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      eapply wm_trace_reads_from_derived_cache_snapshot.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      unfold wm_derived_cache_snapshot.
      eapply cache_hist_extends_by_trace_snapshot.
      exact Hext_by_writes.
  Qed.

End generic_derived_cache_ghost.

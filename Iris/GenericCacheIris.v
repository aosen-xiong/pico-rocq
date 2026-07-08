From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Require Import Core.GenericCacheProtocol.

(** * Pure Iris Facade for Generic Cache Protocols

    This file gives an Iris-facing view of the generic trace-robust cache
    theorem.  It is intentionally a pure wrapper: it exposes the final
    Hoare-style boundary as Iris propositions without committing yet to a
    ghost-state or WP encoding for cache protocols. *)

Section generic_cache_iris.
  Context {PROP : bi}.

(** Pure Iris proposition for the provider-side stable abstraction. *)
  Definition StableAbsI {Obj AbsVal : Type}
      (Stable : StableAbs Obj AbsVal) (o : Obj) (a : AbsVal) : PROP :=
    ⌜Stable o a⌝%I.

(** Pure Iris proposition for valid cache histories. *)
  Definition CacheHistOKI {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (o : Obj) (a : AbsVal) : PROP :=
    ⌜CacheHistOK P Hist o a⌝%I.

  Definition CacheHistValidExtensionI {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (o o' : Obj) (a : AbsVal) : PROP :=
    ⌜CacheHistValidExtension P Hist Hist' o o' a⌝%I.

  Definition CacheHistSnapshotValidExtensionI {AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (snap snap' : CacheHistorySnapshot P) (a : AbsVal) : PROP :=
    ⌜CacheHistSnapshotValidExtension P snap snap' a⌝%I.

  Definition ValidTraceI {AbsVal : Type}
      (P : CacheProtocol AbsVal) (a : AbsVal) (tr : CacheTrace P) : PROP :=
    ⌜ValidTrace P a tr⌝%I.

  Definition TraceContainsI {AbsVal : Type}
      (P : CacheProtocol AbsVal) (tr : CacheTrace P)
      (k : cache_field P) (v : cache_val P k) : PROP :=
    ⌜TraceContains P tr k v⌝%I.

  Definition CacheHistExtendsByTraceI {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (o o' : Obj) (tr : CacheTrace P) : PROP :=
    ⌜CacheHistExtendsByTrace P Hist Hist' o o' tr⌝%I.

  Definition CacheHistSnapshotExtendsByTraceI {AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (snap snap' : CacheHistorySnapshot P) (tr : CacheTrace P) : PROP :=
    ⌜CacheHistSnapshotExtendsByTrace P snap snap' tr⌝%I.

  Definition CacheSafeMethodI {AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result) : PROP :=
    ⌜CacheSafeMethod P F run_with_cache_trace⌝%I.

  Definition PureRecomputeResultI {AbsVal Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (a : AbsVal) (args : Args) (r : Result) : PROP :=
    ⌜PureRecomputeResult F a args r⌝%I.

  Definition CacheRefinesPureI {AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result) : PROP :=
    ⌜CacheRefinesPure P F run_with_cache_trace⌝%I.

  Definition SemImmI {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (Stable : StableAbs Obj AbsVal) (o : Obj) (a : AbsVal) : PROP :=
    (StableAbsI Stable o a ∗ CacheHistOKI P Hist o a)%I.

(** Postcondition shape for the pure Iris method boundary. *)
  Definition CacheMethodPostI {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (o : Obj) (a : AbsVal) (args : Args) (r : Result) : PROP :=
    (⌜r = F a args⌝ ∗ SemImmI P Hist Stable o a)%I.

(** Iris wrapper for the generic read-validity lemma. *)
  Lemma cache_read_validI :
    forall {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist o k))
      o a k (v : cache_val P k)
      (Hhist : CacheHistOK P Hist o a)
      (Hread : read_cache o k v),
      ⊢ (⌜cache_valid P a k v⌝ : PROP).
  Proof.
    intros Obj AbsVal P Hist read_cache read_from_history o a k v Hhist Hread.
    iPureIntro.
    eapply cache_read_valid; eauto.
  Qed.

  Lemma cache_hist_ok_valid_extensionI :
    forall {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P) o o' a
      (Hhist : CacheHistOK P Hist o a)
      (Hext : CacheHistValidExtension P Hist Hist' o o' a),
      ⊢ CacheHistOKI P Hist' o' a.
  Proof.
    intros Obj AbsVal P Hist Hist' o o' a Hhist Hext.
    iPureIntro.
    eapply cache_hist_ok_valid_extension; eauto.
  Qed.

  Lemma valid_trace_from_historyI :
    forall {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist o k))
      o a tr
      (Hhist : CacheHistOK P Hist o a)
      (Hreads : TraceReadsFromHistory P read_cache o tr),
      ⊢ ValidTraceI P a tr.
  Proof.
    intros Obj AbsVal P Hist read_cache read_from_history o a tr Hhist Hreads.
    iPureIntro.
    eapply valid_trace_from_history; eauto.
  Qed.

  Lemma valid_trace_from_post_history_with_valid_extensionI :
    forall {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_post_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist' o k))
      o o' a tr
      (Hhist : CacheHistOK P Hist o a)
      (Hext : CacheHistValidExtension P Hist Hist' o o' a)
      (Hreads : TraceReadsFromHistory P read_cache o' tr),
      ⊢ ValidTraceI P a tr.
  Proof.
    intros Obj AbsVal P Hist Hist' read_cache read_from_post_history
           o o' a tr Hhist Hext Hreads.
    iPureIntro.
    eapply valid_trace_from_post_history_with_valid_extension; eauto.
  Qed.

  Lemma valid_trace_from_post_snapshot_with_valid_extensionI :
    forall {AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (snap snap' : CacheHistorySnapshot P) a tr
      (Hsnap : CacheHistSnapshotOK P snap a)
      (Hext : CacheHistSnapshotValidExtension P snap snap' a)
      (Hreads : TraceReadsFromSnapshot P snap' tr),
      ⊢ ValidTraceI P a tr.
  Proof.
    intros AbsVal P snap snap' a tr Hsnap Hext Hreads.
    iPureIntro.
    eapply valid_trace_from_post_snapshot_with_valid_extension; eauto.
  Qed.

  Lemma valid_trace_contains_validI :
    forall {AbsVal : Type}
      (P : CacheProtocol AbsVal) a tr k (v : cache_val P k)
      (Htrace : ValidTrace P a tr)
      (Hin : TraceContains P tr k v),
      ⊢ (⌜cache_valid P a k v⌝ : PROP).
  Proof.
    intros AbsVal P a tr k v Htrace Hin.
    iPureIntro.
    eapply valid_trace_contains_valid; eauto.
  Qed.

  Lemma cache_hist_extends_by_valid_traceI :
    forall {Obj AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P) o o' a tr
      (Htrace : ValidTrace P a tr)
      (Hext : CacheHistExtendsByTrace P Hist Hist' o o' tr),
      ⊢ CacheHistValidExtensionI P Hist Hist' o o' a.
  Proof.
    intros Obj AbsVal P Hist Hist' o o' a tr Htrace Hext.
    iPureIntro.
    eapply cache_hist_extends_by_valid_trace; eauto.
  Qed.

  Lemma cache_hist_snapshot_extends_by_valid_traceI :
    forall {AbsVal : Type}
      (P : CacheProtocol AbsVal)
      (snap snap' : CacheHistorySnapshot P) a tr
      (Htrace : ValidTrace P a tr)
      (Hext : CacheHistSnapshotExtendsByTrace P snap snap' tr),
      ⊢ CacheHistSnapshotValidExtensionI P snap snap' a.
  Proof.
    intros AbsVal P snap snap' a tr Htrace Hext.
    iPureIntro.
    eapply cache_hist_snapshot_extends_by_valid_trace; eauto.
  Qed.

(** Iris wrapper for the generic refinement theorem. *)
  Theorem cache_safe_method_refines_pureI :
    forall {AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace),
      ⊢ CacheRefinesPureI P F run_with_cache_trace.
  Proof.
    intros AbsVal Args Result P F run Hsafe.
    iPureIntro.
    apply cache_safe_method_refines_pure.
    exact Hsafe.
  Qed.

  Theorem cache_safe_method_refines_pure_runI :
    forall {AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      a args tr r
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Htrace : ValidTrace P a tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r),
      ⊢ PureRecomputeResultI F a args r.
  Proof.
    intros AbsVal Args Result P F run a args tr r Hsafe Htrace Hexec.
    iPureIntro.
    eapply cache_safe_method_refines_pure; eauto.
  Qed.

  Theorem cache_safe_method_soundI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o a args tr r
      (Hstable : Stable o a)
      (Hhist : CacheHistOK P Hist o a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Htrace : ValidTrace P a tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r),
      ⊢ CacheMethodPostI P Hist Stable F o a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Stable F run o a args tr r
           Hstable Hhist Hsafe Htrace Hexec.
    destruct (cache_safe_method_sound
      P Hist Stable F run o a args tr r
      Hstable Hhist Hsafe Htrace Hexec) as [Hresult [Hstable' Hhist']].
    unfold CacheMethodPostI, SemImmI, StableAbsI, CacheHistOKI.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - iSplit; iPureIntro; assumption.
  Qed.

  Theorem cache_safe_method_sound_with_valid_history_extensionI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o o' a args tr r
      (Hstable : Stable o a)
      (Hstable' : Stable o' a)
      (Hhist : CacheHistOK P Hist o a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Htrace : ValidTrace P a tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r)
      (Hext : CacheHistValidExtension P Hist Hist' o o' a),
      ⊢ CacheMethodPostI P Hist' Stable F o' a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Hist' Stable F run o o' a args tr r
           Hstable Hstable' Hhist Hsafe Htrace Hexec Hext.
    destruct (cache_safe_method_sound_with_valid_history_extension
      P Hist Hist' Stable F run o o' a args tr r
      Hstable Hstable' Hhist Hsafe Htrace Hexec Hext) as
      [Hresult [Hstable_post Hhist']].
    unfold CacheMethodPostI, SemImmI, StableAbsI, CacheHistOKI.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - iSplit; iPureIntro; assumption.
  Qed.

  Theorem cache_safe_method_sound_from_historyI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (Stable : StableAbs Obj AbsVal)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist o k))
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o a args tr r
      (Hstable : Stable o a)
      (Hhist : CacheHistOK P Hist o a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromHistory P read_cache o tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r),
      ⊢ CacheMethodPostI P Hist Stable F o a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Stable read_cache read_from_history
           F run o a args tr r Hstable Hhist Hsafe Hreads Hexec.
    destruct (cache_safe_method_sound_from_history
      P Hist Stable read_cache read_from_history F run o a args tr r
      Hstable Hhist Hsafe Hreads Hexec) as [Hresult [Hstable' Hhist']].
    unfold CacheMethodPostI, SemImmI, StableAbsI, CacheHistOKI.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - iSplit; iPureIntro; assumption.
  Qed.

  Theorem cache_safe_method_sound_from_history_with_valid_extensionI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (Stable : StableAbs Obj AbsVal)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist o k))
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o o' a args tr r
      (Hstable : Stable o a)
      (Hstable' : Stable o' a)
      (Hhist : CacheHistOK P Hist o a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromHistory P read_cache o tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r)
      (Hext : CacheHistValidExtension P Hist Hist' o o' a),
      ⊢ CacheMethodPostI P Hist' Stable F o' a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Hist' Stable read_cache
           read_from_history F run o o' a args tr r Hstable Hstable'
           Hhist Hsafe Hreads Hexec Hext.
    destruct (cache_safe_method_sound_from_history_with_valid_extension
      P Hist Hist' Stable read_cache read_from_history F run o o' a args tr r
      Hstable Hstable' Hhist Hsafe Hreads Hexec Hext) as
      [Hresult [Hstable_post Hhist']].
    unfold CacheMethodPostI, SemImmI, StableAbsI, CacheHistOKI.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - iSplit; iPureIntro; assumption.
  Qed.

  Theorem cache_safe_method_sound_from_post_history_with_valid_extensionI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (Stable : StableAbs Obj AbsVal)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_post_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist' o k))
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o o' a args tr r
      (Hstable : Stable o a)
      (Hstable' : Stable o' a)
      (Hhist : CacheHistOK P Hist o a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromHistory P read_cache o' tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r)
      (Hext : CacheHistValidExtension P Hist Hist' o o' a),
      ⊢ CacheMethodPostI P Hist' Stable F o' a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Hist' Stable read_cache
           read_from_post_history F run o o' a args tr r Hstable Hstable'
           Hhist Hsafe Hreads Hexec Hext.
    destruct (cache_safe_method_sound_from_post_history_with_valid_extension
      P Hist Hist' Stable read_cache read_from_post_history
      F run o o' a args tr r
      Hstable Hstable' Hhist Hsafe Hreads Hexec Hext) as
      [Hresult [Hstable_post Hhist']].
    unfold CacheMethodPostI, SemImmI, StableAbsI, CacheHistOKI.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - iSplit; iPureIntro; assumption.
  Qed.

  Theorem trace_robust_semantic_immutabilityI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (Stable : StableAbs Obj AbsVal)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist o k))
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o o' a args tr r
      (Hsem : SemImm P Hist Stable o a)
      (Hstable' : Stable o' a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromHistory P read_cache o tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r)
      (Hext_by_writes : CacheHistExtendsByTrace
        P
        Hist
        Hist'
        o
        o'
        (run_writes (run_with_cache_trace a args tr))),
      ⊢ CacheMethodPostI P Hist' Stable F o' a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Hist' Stable read_cache
           read_from_history F run o o' a args tr r Hsem Hstable'
           Hsafe Hreads Hexec Hext_by_writes.
    destruct (trace_robust_semantic_immutability
      P Hist Hist' Stable read_cache read_from_history F run
      o o' a args tr r Hsem Hstable' Hsafe Hreads Hexec
      Hext_by_writes) as [Hresult [Hstable_post Hhist']].
    unfold CacheMethodPostI, SemImmI, StableAbsI, CacheHistOKI.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - iSplit; iPureIntro; assumption.
  Qed.

  Theorem trace_robust_semantic_immutability_after_history_extensionI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist_pre Hist' : @CacheHistory Obj AbsVal P)
      (Stable : StableAbs Obj AbsVal)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_pre_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist_pre o k))
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o o_pre o' a args tr r
      (Hsem : SemImm P Hist Stable o a)
      (Hstable_pre : Stable o_pre a)
      (Hstable' : Stable o' a)
      (Hpre_ext : CacheHistValidExtension P Hist Hist_pre o o_pre a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromHistory P read_cache o_pre tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r)
      (Hext_by_writes : CacheHistExtendsByTrace
        P
        Hist_pre
        Hist'
        o_pre
        o'
        (run_writes (run_with_cache_trace a args tr))),
      ⊢ CacheMethodPostI P Hist' Stable F o' a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Hist_pre Hist' Stable read_cache
           read_from_pre_history F run o o_pre o' a args tr r Hsem
           Hstable_pre Hstable' Hpre_ext Hsafe Hreads Hexec
           Hext_by_writes.
    destruct (trace_robust_semantic_immutability_after_history_extension
      P Hist Hist_pre Hist' Stable read_cache read_from_pre_history F run
      o o_pre o' a args tr r Hsem Hstable_pre Hstable' Hpre_ext Hsafe
      Hreads Hexec Hext_by_writes) as [Hresult [Hstable_post Hhist']].
    unfold CacheMethodPostI, SemImmI, StableAbsI, CacheHistOKI.
    iSplit.
    - iPureIntro.
      exact Hresult.
    - iSplit; iPureIntro; assumption.
  Qed.

  Theorem cache_safe_method_refines_pure_from_historyI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist o k))
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o a args tr r
      (Hhist : CacheHistOK P Hist o a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromHistory P read_cache o tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r),
      ⊢ PureRecomputeResultI F a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist read_cache read_from_history
           F run o a args tr r Hhist Hsafe Hreads Hexec.
    iPureIntro.
    eapply cache_safe_method_refines_pure_from_history; eauto.
  Qed.

  Theorem cache_safe_method_refines_pure_from_post_history_with_valid_extensionI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
      (read_from_post_history :
        forall o k (v : cache_val P k),
          read_cache o k v -> In v (Hist' o k))
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o o' a args tr r
      (Hhist : CacheHistOK P Hist o a)
      (Hext : CacheHistValidExtension P Hist Hist' o o' a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromHistory P read_cache o' tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r),
      ⊢ PureRecomputeResultI F a args r.
  Proof.
    intros Obj AbsVal Args Result P Hist Hist' read_cache
           read_from_post_history F run o o' a args tr r Hhist Hext
           Hsafe Hreads Hexec.
    iPureIntro.
    eapply cache_safe_method_refines_pure_from_post_history_with_valid_extension;
      eauto.
  Qed.

  Theorem cache_safe_method_writes_history_valid_extensionI :
    forall {Obj AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (Hist Hist' : @CacheHistory Obj AbsVal P)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      o o' a args tr
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Htrace : ValidTrace P a tr)
      (Hext : CacheHistExtendsByTrace
        P
        Hist
        Hist'
        o
        o'
        (run_writes (run_with_cache_trace a args tr))),
      ⊢ CacheHistValidExtensionI P Hist Hist' o o' a.
  Proof.
    intros Obj AbsVal Args Result P Hist Hist' F run o o' a args tr
           Hsafe Htrace Hext.
    iPureIntro.
    eapply cache_safe_method_writes_history_valid_extension; eauto.
  Qed.

  Theorem cache_safe_method_writes_snapshot_valid_extensionI :
    forall {AbsVal Args Result : Type}
      (P : CacheProtocol AbsVal)
      (snap snap' : CacheHistorySnapshot P)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      a args tr
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Htrace : ValidTrace P a tr)
      (Hext : CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))),
      ⊢ CacheHistSnapshotValidExtensionI P snap snap' a.
  Proof.
    intros AbsVal Args Result P snap snap' F run a args tr
           Hsafe Htrace Hext.
    iPureIntro.
    eapply cache_safe_method_writes_snapshot_valid_extension; eauto.
  Qed.

End generic_cache_iris.

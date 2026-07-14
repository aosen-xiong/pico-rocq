From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import own.

Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState.

(** * Iris Semantic Immutability Protocol

    This file is the public Iris protocol for the generic trace-robust cache
    theorem.  The detailed ghost-state lemmas remain in
    [GenericCacheGhostState].  This file exposes the proof story through a
    compact vocabulary:

    [[
      StableAbsI + CacheHistI = SemImmI
    ]]

    and through three protocol rules: cache reads observe valid values, valid
    cache writes preserve the semantic object predicate, and cache-safe methods
    preserve semantic immutability while returning the pure result.

    These rules are intentionally over abstract cache-read/cache-write steps,
    not ordinary heap_lang loads and stores.  That keeps the weak-memory
    boundary explicit: a cache read is justified by membership in the field
    history snapshot, and a cache write is justified by a valid history
    extension. *)

Section iris_semantic_bridge.
  Context {AbsVal : Type}.
  Context (P : CacheProtocol AbsVal).
  Context `{!genericCacheG P Σ}.

(** Pure provider abstraction as an Iris assertion. *)
  Definition StableAbsI {Obj : Type}
      (Stable : StableAbs Obj AbsVal) (o : Obj) (a : AbsVal) : iProp Σ :=
    ⌜Stable o a⌝.

(** Ghost-backed cache-history interpretation. *)
  Definition CacheHistI
      (γ : gname) (a : AbsVal) (snap : CacheHistorySnapshot P) : iProp Σ :=
    generic_cache_history_interp P γ a snap.

(** The public semantic immutability assertion used by Iris-facing theorems. *)
  Definition SemImmI {Obj : Type}
      (Stable : StableAbs Obj AbsVal)
      (γ : gname) (o : Obj) (a : AbsVal)
      (snap : CacheHistorySnapshot P) : iProp Σ :=
    StableAbsI Stable o a ∗ CacheHistI γ a snap.

(** Abstract read side condition for the Iris protocol.  It states that the
    observed value came from the cache-field history snapshot. *)
  Definition CacheReadStep
      (snap : CacheHistorySnapshot P) k (v : cache_val P k) : Prop :=
    In v (snap k).

(** Abstract write side condition for the Iris protocol.  It states both that
    the written value is valid for the cache protocol and that the post-snapshot
    is a valid extension of the pre-snapshot. *)
  Definition CacheWriteStep
      a (snap snap' : CacheHistorySnapshot P)
      k (v : cache_val P k) : Prop :=
    cache_valid P a k v /\
    CacheHistSnapshotValidExtension P snap snap' a.

  Global Instance stable_absI_persistent {Obj : Type}
      (Stable : StableAbs Obj AbsVal) o a :
    Persistent (StableAbsI Stable o a).
  Proof. apply _. Qed.

  Lemma semimmI_alloc {Obj : Type}
      (Stable : StableAbs Obj AbsVal) o a snap
      (Hstable : Stable o a)
      (Hsnap : CacheHistSnapshotOK P snap a) :
    ⊢ |==> ∃ γ, SemImmI Stable γ o a snap.
  Proof.
    iMod (generic_cache_history_interp_alloc P a snap Hsnap)
      as (γ) "Hhist".
    iModIntro.
    iExists γ.
    unfold SemImmI, StableAbsI, CacheHistI.
    iSplit.
    - iPureIntro.
      exact Hstable.
    - iExact "Hhist".
  Qed.

(** WP-shaped read rule for the abstract cache protocol: if the memory
    interface says the read returned a value from the field-history snapshot,
    then clients may use that value as protocol-valid and keep [SemImmI]. *)
  Lemma cache_read_valid_wp {Obj : Type}
      (Stable : StableAbs Obj AbsVal)
      γ o a snap k (v : cache_val P k) :
    SemImmI Stable γ o a snap -∗
    ⌜CacheReadStep snap k v⌝ -∗
    SemImmI Stable γ o a snap ∗
    ⌜cache_valid P a k v /\ cache_published P k v⌝.
  Proof.
    iIntros "Hsem %Hread".
    unfold SemImmI, StableAbsI, CacheHistI.
    iDestruct "Hsem" as "(#Hstable & Hhist)".
    iDestruct
      (generic_cache_history_interp_read_valid_preserve P
        with "Hhist []")
      as "[Hhist %Hvalid]".
    {
      iPureIntro.
      exact Hread.
    }
    iSplitL "Hhist".
    - iSplit.
      + iExact "Hstable".
      + iExact "Hhist".
    - iPureIntro. split; [exact Hvalid |].
      eapply cache_valid_published. exact Hvalid.
  Qed.

(** WP-shaped write rule for the abstract cache protocol: writing a
    protocol-valid cache value and moving to a valid history extension preserves
    the semantic immutable-object predicate. *)
  Lemma cache_write_valid_wp {Obj : Type}
      (Stable : StableAbs Obj AbsVal)
      γ o o' a snap snap' k (v : cache_val P k)
      (Hstable' : Stable o' a) :
    SemImmI Stable γ o a snap -∗
    ⌜CacheWriteStep a snap snap' k v⌝ ==∗
    SemImmI Stable γ o' a snap'.
  Proof.
    iIntros "Hsem %Hwrite".
    destruct Hwrite as [_ Hext].
    unfold SemImmI, StableAbsI, CacheHistI.
    iDestruct "Hsem" as "(_ & Hhist)".
    iMod
      (generic_cache_history_interp_valid_extension_update P
        with "Hhist []")
      as "Hhist'".
    {
      iPureIntro.
      exact Hext.
    }
    iModIntro.
    iSplit.
    - iPureIntro.
      exact Hstable'.
    - iExact "Hhist'".
  Qed.

(** Iris-style semantic method rule: a trace-robust cache-safe method returns
    the pure result and preserves semantic immutability across the history
    extension induced by its writes. *)
  Theorem cache_safe_method_wp {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o o' a snap snap' args tr r
      (Hstable' : Stable o' a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromSnapshot P snap tr)
      (Hexec : trace_result_matches P run_with_cache_trace a args tr r)
      (Hext : CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))) :
    SemImmI Stable γ o a snap ==∗
    ⌜r = F a args⌝ ∗
    SemImmI Stable γ o' a snap'.
  Proof.
    iIntros "Hsem".
    unfold SemImmI, StableAbsI, CacheHistI.
    iApply
      (generic_trace_robust_semantic_immutability_interp_update_post P
        with "[$Hsem] [] [] [] [] []").
    - iPureIntro.
      exact Hstable'.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext.
  Qed.
End iris_semantic_bridge.

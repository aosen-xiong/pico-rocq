From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import own.

Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState.

(** * Public Iris Semantic Bridge

    This file is a small public Iris bridge for the generic trace-robust cache
    theorem.  The detailed ghost-state lemmas remain in
    [GenericCacheGhostState].  This file exposes the proof story through a
    compact vocabulary:

    [[
      StableAbsI + CacheHistI = SemImmI
    ]]

    and through three rules: cache reads observe valid values, valid history
    extensions preserve the semantic object predicate, and cache-safe methods
    preserve semantic immutability while returning the pure result. *)

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

  Global Instance stable_absI_persistent {Obj : Type}
      (Stable : StableAbs Obj AbsVal) o a :
    Persistent (StableAbsI Stable o a).
  Proof. apply _. Qed.

  Lemma stable_absI_intro {Obj : Type}
      (Stable : StableAbs Obj AbsVal) o a
      (Hstable : Stable o a) :
    ⊢ StableAbsI Stable o a.
  Proof.
    iPureIntro.
    exact Hstable.
  Qed.

  Lemma cache_histI_alloc a snap
      (Hsnap : CacheHistSnapshotOK P snap a) :
    ⊢ |==> ∃ γ, CacheHistI γ a snap.
  Proof.
    iMod (generic_cache_history_interp_alloc P a snap Hsnap)
      as (γ) "Hhist".
    iModIntro.
    iExists γ.
    iExact "Hhist".
  Qed.

  Lemma semimmI_alloc {Obj : Type}
      (Stable : StableAbs Obj AbsVal) o a snap
      (Hstable : Stable o a)
      (Hsnap : CacheHistSnapshotOK P snap a) :
    ⊢ |==> ∃ γ, SemImmI Stable γ o a snap.
  Proof.
    iMod (cache_histI_alloc a snap Hsnap) as (γ) "Hhist".
    iModIntro.
    iExists γ.
    unfold SemImmI, StableAbsI, CacheHistI.
    iSplit.
    - iPureIntro.
      exact Hstable.
    - iExact "Hhist".
  Qed.

(** Cache reads preserve [SemImmI] and expose protocol validity of the observed
    value. *)
  Lemma cache_read_validI {Obj : Type}
      (Stable : StableAbs Obj AbsVal)
      γ o a snap k (v : cache_val P k)
      (Hin : In v (snap k)) :
    SemImmI Stable γ o a snap -∗
    SemImmI Stable γ o a snap ∗
    ⌜cache_valid P a k v⌝.
  Proof.
    iIntros "Hsem".
    unfold SemImmI, StableAbsI, CacheHistI.
    iDestruct "Hsem" as "(#Hstable & Hhist)".
    iDestruct
      (generic_cache_history_interp_read_valid_preserve P
        with "Hhist []")
      as "[Hhist %Hvalid]".
    {
      iPureIntro.
      exact Hin.
    }
    iSplitL "Hhist".
    - iSplit.
      + iExact "Hstable".
      + iExact "Hhist".
    - iPureIntro.
      exact Hvalid.
  Qed.

(** A valid cache-history extension can be reallocated as a fresh [SemImmI] for
    the post-state object. *)
  Lemma cache_history_valid_extension_preservesI {Obj : Type}
      (Stable : StableAbs Obj AbsVal)
      γ o o' a snap snap'
      (Hstable' : Stable o' a)
      (Hext : CacheHistSnapshotValidExtension P snap snap' a) :
    SemImmI Stable γ o a snap ==∗
    ∃ γ', SemImmI Stable γ' o' a snap'.
  Proof.
    iIntros "Hsem".
    unfold SemImmI, StableAbsI, CacheHistI.
    iDestruct "Hsem" as "(_ & Hhist)".
    iMod
      (generic_cache_history_interp_valid_extension_alloc P
        with "Hhist []")
      as (γ') "Hhist'".
    {
      iPureIntro.
      exact Hext.
    }
    iModIntro.
    iExists γ'.
    iSplit.
    - iPureIntro.
      exact Hstable'.
    - iExact "Hhist'".
  Qed.

(** Iris-style semantic method rule: a trace-robust cache-safe method returns
    the pure result and preserves semantic immutability across the history
    extension induced by its writes. *)
  Theorem cache_safe_method_wpI {Obj Args Result : Type}
      (Stable : StableAbs Obj AbsVal)
      (F : AbsVal -> Args -> Result)
      (run_with_cache_trace :
        AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      γ o o' a snap snap' args tr r
      (Hstable' : Stable o' a)
      (Hsafe : CacheSafeMethod P F run_with_cache_trace)
      (Hreads : TraceReadsFromSnapshot P snap tr)
      (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r)
      (Hext : CacheHistSnapshotExtendsByTrace
        P
        snap
        snap'
        (run_writes (run_with_cache_trace a args tr))) :
    SemImmI Stable γ o a snap ==∗
    ∃ γ',
      ⌜r = F a args⌝ ∗
      SemImmI Stable γ' o' a snap'.
  Proof.
    iIntros "Hsem".
    unfold SemImmI, StableAbsI, CacheHistI.
    iApply
      (generic_trace_robust_semantic_immutability_interp_alloc_post P
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

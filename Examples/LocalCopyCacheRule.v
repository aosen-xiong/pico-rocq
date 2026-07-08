From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import own.

Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState.
Require Import Core.GenericDerivedCache Iris.IrisSemanticBridge.

(** * Local-Copy Cache Rule Example

    This is a representative Iris-facing rule for the local-copy cache idiom.
    It is intentionally a small fragment, not a full PICO logical relation.  It
    shows how a concrete local-copy method proves [CacheSafeMethod] and then
    consumes the compact [SemImmI] bridge to obtain a method-style
    postcondition. *)

(** Trivial provider predicate for the standalone hash-cache example. *)
Definition hash_example_stable_abs (_ : unit) (_ : nat) : Prop := True.

(** The local-copy hash method satisfies the generic trace-robust method
    contract. *)
Theorem local_copy_hash_cache_safe_method :
  CacheSafeMethod
    hash_cache_protocol
    hash_pure_result
    good_hash_run.
Proof.
  exact good_hash_cache_safe_method.
Qed.

(** Therefore it refines pure hash recomputation. *)
Theorem local_copy_hash_refines_pure :
  CacheRefinesPure
    hash_cache_protocol
    hash_pure_result
    good_hash_run.
Proof.
  exact good_hash_refines_pure_recompute.
Qed.

Section local_copy_hash_iris_rule.
  Context {Σ : gFunctors}.
  Context `{!genericCacheG hash_cache_protocol Σ}.

(** Iris-style method rule for the local-copy hash example. *)
  Theorem local_copy_hash_cache_method_wpI
      γ snap snap' H tr r
      (Hreads : TraceReadsFromSnapshot hash_cache_protocol snap tr)
      (Hexec : weak_exec_matches_trace
        hash_cache_protocol
        good_hash_run
        H
        tt
        tr
        r)
      (Hext : CacheHistSnapshotExtendsByTrace
        hash_cache_protocol
        snap
        snap'
        (run_writes (good_hash_run H tt tr))) :
    SemImmI
      hash_cache_protocol
      hash_example_stable_abs
      γ
      tt
      H
      snap ==∗
    ∃ γ',
      ⌜r = hash_pure_result H tt⌝ ∗
      SemImmI
        hash_cache_protocol
        hash_example_stable_abs
        γ'
        tt
        H
        snap'.
  Proof.
    iIntros "Hsem".
    iApply
      (cache_safe_method_wpI
        hash_cache_protocol
        hash_example_stable_abs
        hash_pure_result
        good_hash_run
        γ
        tt
        tt
        H
        snap
        snap'
        tt
        tr
        r
        I
        local_copy_hash_cache_safe_method
        Hreads
        Hexec
        Hext
        with "Hsem").
  Qed.
End local_copy_hash_iris_rule.

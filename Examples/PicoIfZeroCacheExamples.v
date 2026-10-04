From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import own.

Require Import Syntax Helpers.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Iris.GenericCacheGhostState Iris.IrisSemanticBridge.
Require Export Examples.PicoIfZeroCache.

Section pico_local_copy_hash_semimm.
  Context {Σ : gFunctors}.
  Context `{!genericCacheG hash_cache_protocol Σ}.

  Theorem pico_local_copy_hash_semimm_wpI
      γ snap snap' H tr r
      (Hreads : TraceReadsFromSnapshot hash_cache_protocol snap tr)
      (Hexec : trace_result_matches
        hash_cache_protocol pico_local_copy_hash_run H tt tr r)
      (Hext : CacheHistSnapshotExtendsByTrace
        hash_cache_protocol snap snap'
        (run_writes (pico_local_copy_hash_run H tt tr))) :
    SemImmI
      hash_cache_protocol
      pico_hash_stable_abs
      γ H H snap ==∗
    ⌜r = hash_pure_result H tt⌝ ∗
    SemImmI
      hash_cache_protocol
      pico_hash_stable_abs
      γ H H snap'.
  Proof.
    iIntros "Hsem".
    iApply
      (cache_safe_method_wp
        hash_cache_protocol
        pico_hash_stable_abs
        hash_pure_result
        pico_local_copy_hash_run
        γ H H H snap snap' tt tr r eq_refl
        pico_local_copy_hash_cache_safe Hreads Hexec Hext
        with "Hsem").
  Qed.
End pico_local_copy_hash_semimm.

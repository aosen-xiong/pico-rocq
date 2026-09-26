From iris.proofmode Require Import proofmode.
From iris.base_logic Require Import own.

Require Import Syntax Helpers.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Iris.GenericCacheGhostState Iris.IrisSemanticBridge.

(** * PICO Source Shapes for Racy Derived Caches

    The cache protocol proves the semantic facts in [GenericDerivedCache].
    These source terms make the two relevant control-flow shapes explicit in
    PICO: the accepted method returns the first cache observation held in a
    local, while the rejected method reads the cache again after its branch. *)

Definition cache_receiver : var := 0.
Definition cache_tmp : var := 1.
Definition cache_result : var := 2.
Definition hash_cache_field : var := 0.

(** [compute] must place the pure derived value in [cache_tmp]. *)
Definition pico_local_copy_cache_branch (compute : stmt) : stmt :=
  SIfZero cache_tmp
    (SSeq compute (SFldWrite cache_receiver hash_cache_field cache_tmp))
    SSkip.

Definition pico_local_copy_cache_stmt (compute : stmt) : stmt :=
  SSeq
    (SVarAss cache_tmp (EField cache_receiver hash_cache_field))
    (SSeq (pico_local_copy_cache_branch compute)
      (SVarAss cache_result (EVar cache_tmp))).

(** This JDK-style double-read shape is deliberately rejected by the generic
    trace contract: a weak execution may first see a computed cache value and
    later see the default value. *)
Definition pico_double_read_cache_stmt (compute : stmt) : stmt :=
  SSeq
    (SVarAss cache_tmp (EField cache_receiver hash_cache_field))
    (SSeq
      (pico_local_copy_cache_branch compute)
      (SVarAss cache_result (EField cache_receiver hash_cache_field))).

Theorem pico_local_copy_cache_branch_steps
    `{CacheMemoryModel}
    CT rGamma h sigma V K compute :
  pico_core_int_guard rGamma cache_tmp ->
  exists e',
    pico_core_step CT
      (CoreRun rGamma (pico_local_copy_cache_branch compute) V K)
      (mkPicoCoreState h sigma) e' (mkPicoCoreState h sigma).
Proof.
  apply pico_core_int_guard_ifzero_step.
Qed.

Lemma pico_hash_cache_value_makes_tmp_guard :
  forall rGamma H v,
    cache_tmp < dom (vars rGamma) ->
    hash_cache_valid H HashField v ->
    pico_core_int_guard
      (set_vars rGamma (update cache_tmp v (vars rGamma)))
      cache_tmp.
Proof.
  intros rGamma H v Htmp Hvalid.
  destruct (hash_valid_value_shape H v Hvalid)
    as [Hzero | [Hknown _]].
  - subst v.
    right.
    exists 0.
    unfold pico_core_int_guard, runtime_getVal.
    change
      (nth_error (update cache_tmp (Int 0) (vars rGamma)) cache_tmp =
       Some (Int 0)).
    apply update_same.
    exact Htmp.
  - subst v.
    right.
    exists H.
    unfold pico_core_int_guard, runtime_getVal.
    change
      (nth_error (update cache_tmp (Int H) (vars rGamma)) cache_tmp =
       Some (Int H)).
    apply update_same.
    exact Htmp.
Qed.

Theorem pico_hash_cache_local_copy_branch_progress
    `{CacheMemoryModel}
    CT rGamma h sigma V K compute hash_value v :
  cache_tmp < dom (vars rGamma) ->
  hash_cache_valid hash_value HashField v ->
  exists e',
    pico_core_step CT
      (CoreRun
        (set_vars rGamma (update cache_tmp v (vars rGamma)))
        (pico_local_copy_cache_branch compute) V K)
      (mkPicoCoreState h sigma) e' (mkPicoCoreState h sigma).
Proof.
  intros Htmp Hvalid.
  apply pico_local_copy_cache_branch_steps.
  eapply pico_hash_cache_value_makes_tmp_guard; eauto.
Qed.

(** The source-level local-copy prefix has the intended weak execution:
    administratively enter the first sequence, perform one history-backed
    cache read, advance to the conditional, then take its selected branch. *)
Theorem pico_hash_cache_local_copy_prefix_steps
    `{CacheMemoryModel}
    CT rGamma h sigma V K compute old_tmp loc hash_value v V' :
  cache_tmp < dom (vars rGamma) ->
  runtime_getVal rGamma cache_tmp = Some old_tmp ->
  runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
  wm_read sigma V (loc, hash_cache_field) v V' ->
  hash_cache_valid hash_value HashField v ->
  exists rGamma_tmp e',
    pico_core_step CT
      (CoreRun rGamma (pico_local_copy_cache_stmt compute) V K)
      (mkPicoCoreState h sigma)
      (CoreRun rGamma
        (SVarAss cache_tmp (EField cache_receiver hash_cache_field))
        V
        (KSeq
          (SSeq
            (pico_local_copy_cache_branch compute)
            (SVarAss cache_result (EVar cache_tmp))) :: K))
      (mkPicoCoreState h sigma) /\
    pico_core_step CT
      (CoreRun rGamma
        (SVarAss cache_tmp (EField cache_receiver hash_cache_field))
        V
        (KSeq
          (SSeq
            (pico_local_copy_cache_branch compute)
            (SVarAss cache_result (EVar cache_tmp))) :: K))
      (mkPicoCoreState h sigma)
      (CoreRun rGamma_tmp SSkip V'
        (KSeq
          (SSeq
            (pico_local_copy_cache_branch compute)
            (SVarAss cache_result (EVar cache_tmp))) :: K))
      (mkPicoCoreState h sigma) /\
    pico_core_step CT
      (CoreRun rGamma_tmp SSkip V'
        (KSeq
          (SSeq
            (pico_local_copy_cache_branch compute)
            (SVarAss cache_result (EVar cache_tmp))) :: K))
      (mkPicoCoreState h sigma)
      (CoreRun rGamma_tmp
        (SSeq
          (pico_local_copy_cache_branch compute)
          (SVarAss cache_result (EVar cache_tmp))) V' K)
      (mkPicoCoreState h sigma) /\
    pico_core_step CT
      (CoreRun rGamma_tmp
        (SSeq
          (pico_local_copy_cache_branch compute)
          (SVarAss cache_result (EVar cache_tmp))) V' K)
      (mkPicoCoreState h sigma)
      (CoreRun rGamma_tmp
        (pico_local_copy_cache_branch compute) V'
        (KSeq (SVarAss cache_result (EVar cache_tmp)) :: K))
      (mkPicoCoreState h sigma) /\
    pico_core_step CT
      (CoreRun rGamma_tmp
        (pico_local_copy_cache_branch compute) V'
        (KSeq (SVarAss cache_result (EVar cache_tmp)) :: K))
      (mkPicoCoreState h sigma) e' (mkPicoCoreState h sigma).
Proof.
  intros Htmp Htmp_value Hreceiver Hread Hvalid.
  exists (set_vars rGamma (update cache_tmp v (vars rGamma))).
  assert (Hguard :
    pico_core_int_guard
      (set_vars rGamma (update cache_tmp v (vars rGamma)))
      cache_tmp).
  { eapply pico_hash_cache_value_makes_tmp_guard; eauto. }
  destruct
    (pico_local_copy_cache_branch_steps
      CT
      (set_vars rGamma (update cache_tmp v (vars rGamma)))
      h sigma V' (KSeq (SVarAss cache_result (EVar cache_tmp)) :: K)
      compute Hguard)
    as [e' Hbranch].
  exists e'.
  repeat split.
  - apply PCS_Seq.
  - eapply PCS_AssignField; eauto.
  - apply PCS_SkipSeq.
  - apply PCS_Seq.
  - exact Hbranch.
Qed.

(** The source-level operational model abstracts field reads to the generic
    cache-read trace.  It is intentionally separate from the CESK mechanics:
    the field-history interface, not an SC heap load, chooses each observation. *)
Definition pico_local_copy_hash_run := good_hash_run.
Definition pico_double_read_hash_run := bad_hash_run.
(** The semantic object's immutable abstraction determines the hash value.
    Concrete instantiations must therefore connect [pcsi_object] to [H], rather
    than satisfying stability vacuously. *)
Definition pico_hash_stable_abs (object_hash abstract_hash : nat) : Prop :=
  object_hash = abstract_hash.

Theorem pico_local_copy_hash_cache_safe :
  CacheSafeMethod
    hash_cache_protocol
    hash_pure_result
    pico_local_copy_hash_run.
Proof.
  exact good_hash_cache_safe_method.
Qed.

Theorem pico_local_copy_hash_refines_pure :
  CacheRefinesPure
    hash_cache_protocol
    hash_pure_result
    pico_local_copy_hash_run.
Proof.
  exact good_hash_refines_pure_recompute.
Qed.

(** A source method that returns a second field read inherits the generic
    [H; 0] weak-history counterexample. *)
Theorem pico_double_read_hash_not_cache_safe :
  forall H,
    H <> 0 ->
    ~ CacheSafeMethod
        hash_cache_protocol
        hash_pure_result
        pico_double_read_hash_run.
Proof.
  exact bad_hash_not_cache_safe.
Qed.

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

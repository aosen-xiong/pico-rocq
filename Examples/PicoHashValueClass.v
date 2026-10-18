From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoCacheMethodJudgment Examples.PicoHashCacheMethod
  Examples.PicoValueClasses Examples.PicoValueClassTheorem.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * The Hash Class is a Semantic Value Class

    Its state is complete, and its two methods are a cache method and a
    derivation method.  The class-level theorem therefore applies: any
    number of threads may call either method on a hash object. *)

Notation hash_is_cache_method :=
  (@is_cache_method pico_hash_concurrent_CT pico_hash_derivations
     pico_hash_concurrent_receiver pico_hash_concurrent_initial_heap
     pico_hash_concurrent_value).
Notation hash_is_derivation_method :=
  (@is_derivation_method pico_hash_concurrent_CT pico_hash_derivations
     pico_hash_concurrent_receiver pico_hash_concurrent_initial_heap).

Lemma hash_method_is_cache_method :
  hash_is_cache_method pico_hash_concurrent_method_def.
Proof.
  exists pico_hash_read_compute_stmt, pico_hash_witness_receiver_type,
    pico_hash_frame_senv, AbstractState.
  split; [reflexivity |]. split; [reflexivity |].
  split; [exact pico_hash_compute_deriv |].
  split; [exact pico_hash_compute_typing |].
  split; [exact pico_hash_frame_config_wf | exact pico_hash_compute_value].
Qed.

Lemma hash_derive_is_derivation_method :
  hash_is_derivation_method pico_hash_derive_method_def.
Proof.
  destruct (pico_hash_concurrent_derivation_table pico_hash_derive_method_def
    eq_refl) as [sGamma' Hderiv].
  have Htyping := pico_hash_derive_method_typing pico_hash_concurrent_CT
    pico_hash_concurrent_wf_env1 pico_hash_concurrent_wf_env2
    pico_hash_concurrent_payload_field_def.
  have Hsame := deriv_stmt_typing_env pico_hash_concurrent_CT
    pico_hash_derivations _ _ _ _ _ Hderiv Htyping.
  subst sGamma'.
  exists [pico_hash_witness_receiver_type; int_type], AbstractState.
  split; [exact Hderiv |]. split; [exact Htyping |].
  exact pico_hash_concurrent_config_wf.
Qed.

(** The methods of the hash class are exactly these two. *)
Lemma hash_class_methods :
  forall mn md,
    FindMethodWithName pico_hash_concurrent_CT pico_hash_witness_class mn md ->
    md = pico_hash_concurrent_method_def \/ md = pico_hash_derive_method_def.
Proof.
  intros mn md Hfind.
  inversion Hfind as
    [CT C def own m mdef Hclass Hown Hget
    | CT C def parent m mdef own Hclass Hown Hnot Hsuper Hparent]; subst.
  - assert (def = pico_hash_concurrent_class_def)
      by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
    subst def.
    unfold gget_method in Hget. simpl in Hget.
    repeat match type of Hget with
           | context [if ?c then _ else _] => destruct c
           end;
      try discriminate; injection Hget as <-; auto.
  - assert (def = pico_hash_concurrent_class_def)
      by (unfold find_class, gget in Hclass; simpl in Hclass; congruence).
    subst def.
    simpl in Hsuper. injection Hsuper as <-.
    inversion Hparent as
      [CT C def own m mdef Hclass0 Hown0 Hget0
      | CT C def parent m mdef own Hclass0 Hown0 Hnot0 Hsuper0 Hparent0]; subst.
    + assert (def = pico_hash_witness_root_def)
        by (unfold find_class, gget in Hclass0; simpl in Hclass0; congruence).
      subst def. unfold gget_method in Hget0. simpl in Hget0. discriminate.
    + assert (def = pico_hash_witness_root_def)
        by (unfold find_class, gget in Hclass0; simpl in Hclass0; congruence).
      subst def. simpl in Hsuper0. discriminate.
Qed.

Theorem hash_class_is_semantic_value_class :
  @pico_semantic_value_class pico_hash_concurrent_CT pico_hash_derivations
    pico_hash_concurrent_receiver pico_hash_concurrent_initial_heap
    pico_hash_concurrent_value
    (mkruntime_type Imm_r pico_hash_witness_class)
    (fun _ f => f = PicoIfZeroCache.hash_cache_field).
Proof.
  split; [exact hash_class_transitive |].
  intros mn md Hfind.
  destruct (hash_class_methods mn md Hfind) as [-> | ->].
  - left. exact hash_method_is_cache_method.
  - right. exact hash_derive_is_derivation_method.
Qed.

(** Any number of threads calling either method of a hash object: the object
    stays semantically immutable, and every call that returns normally
    returns the value of its method. *)
Theorem hash_class_calls_sound :
  forall specs cfg,
    Forall
      (@call_ok pico_hash_concurrent_CT pico_hash_concurrent_receiver
         (mkruntime_type Imm_r pico_hash_witness_class)) specs ->
    @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
      (mkPicoPoolConfig pico_hash_concurrent_initial_state
         (map call_control specs)) cfg ->
    CacheHistSnapshotOK hash_cache_protocol
      (pico_hash_snapshot pico_hash_concurrent_receiver (pool_state cfg))
      pico_hash_concurrent_value /\
    Forall2
      (fun sp e =>
         forall r rGamma V,
           e = CoreDone r rGamma V ->
           @call_result_ok pico_hash_concurrent_CT pico_hash_derivations
             pico_hash_concurrent_receiver pico_hash_concurrent_initial_heap
             pico_hash_concurrent_value sp (mkPicoCoreVal r rGamma V))
      specs (pool_threads cfg).
Proof.
  intros specs cfg Hcalls Hsteps.
  destruct (@semantic_value_class_sound history_cache_memory_model
    pico_hash_concurrent_CT pico_hash_derivations
    pico_hash_concurrent_receiver pico_hash_derive_method
    pico_hash_concurrent_initial_heap pico_hash_concurrent_value
    (mkruntime_type Imm_r pico_hash_witness_class) [Int 0; Int 7]
    (fun _ f => f = PicoIfZeroCache.hash_cache_field)
    pico_hash_concurrent_derivation_table eq_refl
    pico_hash_concurrent_cache_declared
    specs pico_hash_concurrent_initial_state cfg
    hash_class_is_semantic_value_class Hcalls
    (conj pico_hash_concurrent_initial_provider_inv
       (proj2 (proj2 pico_hash_concurrent_initial_provider_inv)))
    Hsteps) as [[_ Hsnap] Hresults].
  split; [exact Hsnap | exact Hresults].
Qed.

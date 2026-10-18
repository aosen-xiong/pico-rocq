From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoCacheMethodJudgment Examples.PicoHashCacheMethod.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoDerivationNoninterference.

(** * A Derivation That Computes

    Derivation code may use integer operations, since they read only
    locals.  This file gives a closed witness in the frame of the hash
    method: the statement reads the receiver's final payload [p] and
    computes [p * p + p].  It is well typed, it is derivation code, it
    evaluates to the expected value, and by the simulation theorem it
    evaluates to the same value in every heap that agrees with the
    reference heap on the receiver's abstract state. *)

Definition arith_derivation_stmt : stmt :=
  SSeq (SVarAss cache_tmp (EField cache_receiver 1))
    (SSeq (SVarAss cache_result (EBin BMul cache_tmp cache_tmp))
       (SVarAss cache_result (EBin BAdd cache_result cache_tmp))).

Definition arith_derivation_value : nat :=
  pico_hash_concurrent_value * pico_hash_concurrent_value
    + pico_hash_concurrent_value.

Lemma arith_bin_typing :
  forall op x y,
    (x = cache_tmp \/ x = cache_result) ->
    (y = cache_tmp \/ y = cache_result) ->
    stmt_typing pico_hash_concurrent_CT pico_hash_frame_senv AbstractState
      (SVarAss cache_result (EBin op x y)) pico_hash_frame_senv.
Proof.
  intros op x y Hx Hy.
  eapply ST_VarAss with (Te := int_type)
    (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
  - exact pico_hash_concurrent_wf_env3.
  - eapply ET_Bin with (Tx := int_type) (Ty := int_type).
    + exact pico_hash_concurrent_wf_env3.
    + destruct Hx as [-> | ->]; reflexivity.
    + reflexivity.
    + destruct Hy as [-> | ->]; reflexivity.
    + reflexivity.
  - reflexivity.
  - unfold cache_result. discriminate.
  - reflexivity.
  - apply qtype_refl; simpl; [reflexivity | discriminate].
Qed.

Lemma arith_derivation_typing :
  stmt_typing pico_hash_concurrent_CT pico_hash_frame_senv AbstractState
    arith_derivation_stmt pico_hash_frame_senv.
Proof.
  unfold arith_derivation_stmt.
  eapply ST_Seq; [exact pico_hash_concurrent_wf_env3 | |].
  - exact pico_hash_compute_typing.
  - eapply ST_Seq; [exact pico_hash_concurrent_wf_env3 | |].
    + apply arith_bin_typing; left; reflexivity.
    + apply arith_bin_typing; [right | left]; reflexivity.
Qed.

Lemma arith_derivation_deriv :
  deriv_stmt pico_hash_concurrent_CT pico_hash_derivations
    pico_hash_frame_senv arith_derivation_stmt pico_hash_frame_senv.
Proof.
  unfold arith_derivation_stmt.
  eapply DS_Seq; [exact pico_hash_compute_deriv |].
  eapply DS_Seq; apply DS_VarAss; apply TSERO_Bin.
Qed.

(** Evaluated in the reference heap, the statement leaves [p * p + p] in
    the result local. *)
Lemma arith_derivation_evaluates :
  exists rGamma1,
    eval_stmt pico_hash_concurrent_CT pico_hash_frame_env
      pico_hash_concurrent_initial_heap arith_derivation_stmt OK rGamma1
      pico_hash_concurrent_initial_heap /\
    runtime_getVal rGamma1 cache_result = Some (Int arith_derivation_value).
Proof.
  eexists. split.
  - unfold arith_derivation_stmt.
    eapply SBS_Seq.
    + eapply SBS_Assign with (v1 := Int 0); [reflexivity |].
      eapply EBS_Field; reflexivity.
    + eapply SBS_Seq.
      * eapply SBS_Assign with (v1 := Int 0); [reflexivity |].
        eapply EBS_Bin; reflexivity.
      * eapply SBS_Assign; [reflexivity |].
        eapply EBS_Bin; reflexivity.
  - reflexivity.
Qed.

(** The value does not depend on the heap outside the abstract state. *)
Theorem arith_derivation_stable :
  forall h2 P,
    abs_agree pico_hash_concurrent_CT P pico_hash_concurrent_initial_heap h2 ->
    env_in P pico_hash_frame_env ->
    exists rGamma1,
      eval_stmt pico_hash_concurrent_CT pico_hash_frame_env h2
        arith_derivation_stmt OK rGamma1 h2 /\
      runtime_getVal rGamma1 cache_result = Some (Int arith_derivation_value).
Proof.
  intros h2 P Hagree Henv.
  destruct arith_derivation_evaluates as (rGamma1 & Heval & Hval).
  exists rGamma1. split; [| exact Hval].
  destruct (derivation_simulation pico_hash_concurrent_CT pico_hash_derivations
    pico_hash_concurrent_derivation_table _ _ _ _ _ _ Heval
    pico_hash_frame_senv AbstractState pico_hash_frame_senv h2 P
    arith_derivation_deriv arith_derivation_typing pico_hash_frame_config_wf
    Hagree Henv) as (_ & Heval2 & _).
  exact Heval2.
Qed.

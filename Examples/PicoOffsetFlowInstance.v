From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoCacheMethodJudgment Examples.PicoHashCacheMethod
  Examples.PicoCacheFlowJudgment Examples.PicoHashFlowInstance
  Examples.PicoArithmeticDerivation.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoDerivationNoninterference.

(** * An Offset-Encoded Accessor Is Accepted

    An offset encoding stores one more than the result, so that the
    sentinel zero never collides with a result of zero, as
    [BigInteger.bitCountPlusOne] does.  The accessor reads the field once,
    computes and stores the encoded value on a miss, and returns the cached
    value minus one.

    The flow judgment is parameterized by the decoding of the cached value.
    With the predecessor as decoding, this accessor is accepted: the
    decoding step is derivation code that takes a local holding the derived
    value to one holding the decoded value.  All premises are discharged in
    the frame of the hash class, whose payload plays the encoded value.
    The soundness theorem of the judgment then applies to any class table
    that declares the accessor as its cache method; this file does not
    build such a class table. *)

Definition offset_dec (n : nat) : nat := n - 1.

(** [r = 1; r = t - r] *)
Definition offset_decode_stmt : stmt :=
  SSeq (SVarAss cache_result (EInt 1))
    (SVarAss cache_result (EBin BSub cache_tmp cache_result)).

Definition offset_accessor_stmt : stmt :=
  SSeq (SLocal int_type cache_tmp)
    (SSeq (SLocal int_type cache_result)
       (SSeq (SVarAss cache_tmp (EField cache_receiver hash_cache_field))
          (SSeq (pico_local_copy_cache_branch pico_hash_read_compute_stmt)
             offset_decode_stmt))).

Notation offset_flow :=
  (flow pico_hash_concurrent_CT pico_hash_derivations
     pico_hash_concurrent_receiver pico_hash_concurrent_initial_heap
     pico_hash_concurrent_value offset_dec AbstractState).
Notation offset_sem :=
  (sem pico_hash_concurrent_receiver pico_hash_concurrent_value offset_dec).

Lemma offset_one_typing :
  stmt_typing pico_hash_concurrent_CT pico_hash_frame_senv AbstractState
    (SVarAss cache_result (EInt 1)) pico_hash_frame_senv.
Proof.
  eapply ST_VarAss with (Te := int_type)
    (Tthis := pico_hash_witness_receiver_type) (Tx := int_type).
  - exact pico_hash_concurrent_wf_env3.
  - apply ET_Int. exact pico_hash_concurrent_wf_env3.
  - reflexivity.
  - unfold cache_result. discriminate.
  - reflexivity.
  - exact hash_int_subtype.
Qed.

Lemma offset_decode_typing :
  stmt_typing pico_hash_concurrent_CT pico_hash_frame_senv AbstractState
    offset_decode_stmt pico_hash_frame_senv.
Proof.
  eapply ST_Seq; [exact pico_hash_concurrent_wf_env3 | |].
  - exact offset_one_typing.
  - apply arith_bin_typing; [left | right]; reflexivity.
Qed.

Lemma offset_decode_deriv :
  deriv_stmt pico_hash_concurrent_CT pico_hash_derivations
    pico_hash_frame_senv offset_decode_stmt pico_hash_frame_senv.
Proof.
  eapply DS_Seq; apply DS_VarAss; [apply TSERO_Int | apply TSERO_Bin].
Qed.

(** The decoding step takes the derived value to the decoded value. *)
Lemma offset_decode_sem :
  forall rho rhob,
    offset_sem [OThis; ODerived; OOther] rho ->
    eval_stmt pico_hash_concurrent_CT rho pico_hash_concurrent_initial_heap
      offset_decode_stmt OK rhob pico_hash_concurrent_initial_heap ->
    offset_sem [OThis; ODerived; ODecoded] rhob.
Proof.
  intros [vs] rhob Hs Heval. unfold sem in Hs. simpl in Hs.
  repeat match goal with
         | Hf : Forall2 _ (_ :: _) _ |- _ => inversion Hf; subst; clear Hf
         | Hf : Forall2 _ [] _ |- _ => inversion Hf; subst; clear Hf
         end.
  simpl in *. subst.
  unfold offset_decode_stmt in Heval.
  inversion Heval; subst.
  repeat match goal with
         | He : eval_stmt _ _ _ (SVarAss _ _) OK _ _ |- _ =>
             inversion He; subst; clear He
         | He : eval_expr _ _ _ (EInt _) _ _ _ _ |- _ =>
             inversion He; subst; clear He
         | He : eval_expr _ _ _ (EBin _ _ _) _ _ _ _ |- _ =>
             inversion He; subst; clear He
         end.
  repeat match goal with
         | Hv : runtime_getVal _ _ = Some _ |- _ =>
             cbv in Hv; injection Hv as ?; subst
         end.
  unfold sem. simpl.
  constructor; [reflexivity |].
  constructor; [reflexivity |].
  constructor; [reflexivity | constructor].
Qed.

Theorem offset_accessor_flow :
  offset_flow [pico_hash_witness_receiver_type] [OThis]
    offset_accessor_stmt pico_hash_frame_senv [OThis; ODerived; ODecoded].
Proof.
  unfold offset_accessor_stmt, pico_local_copy_cache_branch.
  eapply F_Seq.
  { exact (flow_local_int _ _ _ _ _ _ _ _ [OThis] cache_tmp
             hash_local_tmp_typing). }
  { apply Forall2_refl_le. }
  eapply F_Seq.
  { exact (flow_local_int _ _ _ _ _ _ _ _ [OThis; OSentinel] cache_result
             hash_local_result_typing). }
  { apply Forall2_refl_le. }
  eapply F_Seq.
  { apply (F_Read _ _ _ _ _ _ _ pico_hash_frame_senv
             [OThis; OSentinel; OSentinel] cache_tmp cache_receiver);
      [reflexivity | exact hash_int_assign_typing]. }
  { apply Forall2_refl_le. }
  eapply F_Seq.
  { apply (F_If _ _ _ _ _ _ _ pico_hash_frame_senv
             [OThis; OUnchecked; OSentinel] cache_tmp _ _ pico_hash_frame_senv
             [OThis; ODerived; OOther] [OThis; ODerived; OSentinel]
             [OThis; ODerived; OOther]).
    - eapply F_Seq.
      + apply (F_Deriv _ _ _ _ _ _ _ pico_hash_frame_senv
                 [OThis; OSentinel; OSentinel] pico_hash_read_compute_stmt
                 pico_hash_frame_senv [OThis; ODerived; OOther]).
        * discriminate.
        * exact pico_hash_compute_deriv.
        * exact pico_hash_compute_typing.
        * exact (hash_compute_sem offset_dec).
      + apply Forall2_refl_le.
      + apply F_Write; reflexivity.
    - apply F_Skip.
    - apply Forall2_refl_le.
    - constructor; [apply origin_le_refl |].
      constructor; [apply origin_le_refl |].
      constructor; [right; left; reflexivity | constructor]. }
  { apply Forall2_refl_le. }
  apply (F_Deriv _ _ _ _ _ _ _ pico_hash_frame_senv
           [OThis; ODerived; OOther] offset_decode_stmt pico_hash_frame_senv
           [OThis; ODerived; ODecoded]).
  - discriminate.
  - exact offset_decode_deriv.
  - exact offset_decode_typing.
  - exact offset_decode_sem.
Qed.

(** The accessor returns the decoded value: its result local is decoded. *)
Corollary offset_accessor_returns_decoded :
  nth_error [OThis; ODerived; ODecoded] cache_result = Some ODecoded.
Proof. reflexivity. Qed.

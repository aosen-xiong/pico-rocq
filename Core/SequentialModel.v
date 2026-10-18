From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.

(** * The Sequential Model

    In a sequential execution, a read of a cache field returns the field's
    current value.  This file states the sequential invariant and the
    sequential form of the first correctness condition, relates both to their
    history-based, concurrent counterparts, and shows that the double-read
    hash method, which is not trace robust, is correct sequentially. *)

Section sequential_model.
  Context {Obj AbsVal : Type}.
  Context (P : CacheProtocol AbsVal).
  Context (Stable : StableAbs Obj AbsVal).

  (** The current contents of the cache fields of one object. *)
  Definition CacheContents : Type := forall k : cache_field P, cache_val P k.

  (** The sequential invariant: the abstract value is stable and every
      current cache value is valid. *)
  Definition SemImmSeq (o : Obj) (a : AbsVal) (cur : CacheContents) : Prop :=
    Stable o a /\ forall k, cache_valid P a k (cur k).

  (** The history invariant implies the sequential one for any contents
      drawn from the histories, in particular for the latest writes. *)
  Theorem semimm_seq_of_semimm :
    forall (Hist : CacheHistory P) o a (cur : CacheContents),
      SemImm P Hist Stable o a ->
      (forall k, In (cur k) (Hist o k)) ->
      SemImmSeq o a cur.
  Proof.
    intros Hist o a cur [Hstable Hhist] Hin.
    split; [exact Hstable |].
    intros k. exact (Hhist k (cur k) (Hin k)).
  Qed.

  (** A step that keeps the abstract value and leaves every cache field
      either unchanged or holding a valid value preserves the invariant. *)
  Theorem semimm_seq_preserved :
    forall o o' a (cur cur' : CacheContents),
      SemImmSeq o a cur ->
      Stable o' a ->
      (forall k, cur' k = cur k \/ cache_valid P a k (cur' k)) ->
      SemImmSeq o' a cur'.
  Proof.
    intros o o' a cur cur' [_ Hvalid] Hstable' Hstep.
    split; [exact Hstable' |].
    intros k. destruct (Hstep k) as [-> | Hk]; [exact (Hvalid k) | exact Hk].
  Qed.

  (** The trace of a sequential execution that reads the fields [ks] in
      order: every read returns the current contents. *)
  Definition seq_trace (cur : CacheContents) (ks : list (cache_field P)) :
      CacheTrace P :=
    map (fun k => @Build_CacheObs AbsVal P k (cur k)) ks.

  Lemma seq_trace_valid :
    forall a (cur : CacheContents) ks,
      (forall k, cache_valid P a k (cur k)) ->
      ValidTrace P a (seq_trace cur ks).
  Proof.
    intros a cur ks Hvalid.
    unfold ValidTrace, seq_trace.
    apply Forall_forall. intros obs Hin.
    apply in_map_iff in Hin. destruct Hin as [k [<- _]].
    unfold ValidObs. simpl. exact (Hvalid k).
  Qed.

  (** The first correctness condition in the sequential model, for a method
      that reads the fields [ks]: from valid contents, it returns the pure
      result and writes only valid values. *)
  Definition SeqCacheSafeMethod {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run : AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      (ks : list (cache_field P)) : Prop :=
    forall a args (cur : CacheContents),
      (forall k, cache_valid P a k (cur k)) ->
      run_result (run a args (seq_trace cur ks)) = F a args /\
      ValidTrace P a (run_writes (run a args (seq_trace cur ks))).

  (** Trace robustness implies the sequential condition: the sequential
      model is the special case in which every read returns the current
      value. *)
  Theorem cache_safe_method_sequential :
    forall {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run : AbsVal -> Args -> CacheTrace P -> CacheRun P Result) ks,
      CacheSafeMethod P F run ->
      SeqCacheSafeMethod F run ks.
  Proof.
    intros Args Result F run ks Hsafe a args cur Hvalid.
    exact (Hsafe a args (seq_trace cur ks) (seq_trace_valid a cur ks Hvalid)).
  Qed.
End sequential_model.

(** ** The double-read hash method is correct sequentially

    [bad_hash_run] reads the hash field twice.  It is not trace robust
    ([bad_hash_not_cache_safe]): a valid trace makes it return the sentinel.
    In the sequential model its two reads return the same current value, and
    it returns the hash. *)
Theorem double_read_hash_sequentially_correct :
  SeqCacheSafeMethod hash_cache_protocol hash_pure_result bad_hash_run
    [HashField; HashField].
Proof.
  intros a [] cur Hvalid.
  split; [| constructor].
  specialize (Hvalid HashField).
  unfold seq_trace, bad_hash_run, hash_pure_result, hash_obs_value. simpl.
  destruct Hvalid as [Hzero | [Hhash _]].
  - rewrite Hzero. reflexivity.
  - rewrite Hhash.
    destruct (cache_value_eq_zero (Int a)); reflexivity.
Qed.

(** The local-copy hash method is correct sequentially as well, as an
    instance of [cache_safe_method_sequential]. *)
Theorem local_copy_hash_sequentially_correct :
  forall ks,
    SeqCacheSafeMethod hash_cache_protocol hash_pure_result good_hash_run ks.
Proof.
  intros ks.
  apply cache_safe_method_sequential.
  exact good_hash_cache_safe_method.
Qed.

From Stdlib Require Import List.
Import ListNotations.

(** * Generic Trace-Robust Cache Protocols

    This file is intentionally independent of PICO, Java, and Iris.  It states
    the pure semantic core of the derived-cache argument:

    - a provider has a stable abstraction [StableAbs];
    - a cache protocol classifies admissible cache-field values;
    - field histories contain only values valid for that abstraction;
    - every cache-read trace admitted by the memory interface is valid; and
    - a trace-robust method refines pure recomputation.

    Later files instantiate this interface for the current PICO weak-memory
    shell and expose Iris-facing wrappers. *)

(** [StableAbs Obj AbsVal] is the provider-side semantic immutability predicate:
    object [o] represents the stable abstract value [a].  The generic theory
    treats this abstractly so it can be supplied by PICO final-field facts,
    object invariants, or another provider discipline. *)
Definition StableAbs (Obj AbsVal : Type) : Type := Obj -> AbsVal -> Prop.

(** A [CacheProtocol] describes the admissible values for each cache field.
    [cache_default_valid] records that the initial/default value is always
    protocol-valid, matching the field-history assumption that a read may
    observe either a complete prior write or the default value. *)
Record CacheProtocol (AbsVal : Type) : Type := {
  cache_field : Type;
  cache_val : cache_field -> Type;
  cache_default : forall k, cache_val k;
  cache_valid : AbsVal -> forall k, cache_val k -> Prop;
  cache_default_valid :
    forall a k, cache_valid a k (cache_default k)
}.

Arguments cache_field {_} _.
Arguments cache_val {_} _ _.
Arguments cache_default {_} _ _.
Arguments cache_valid {_} _ _ _ _.

(** ** Histories and History Validity *)

(** [CacheHistory P] is an object-indexed map from cache fields to the list of
    complete values written to that field.  It is intentionally per-field: the
    theory does not allow one field write to corrupt another field history. *)
Definition CacheHistory {Obj AbsVal : Type} (P : CacheProtocol AbsVal) : Type :=
  Obj -> forall k : cache_field P, list (cache_val P k).

(** A snapshot is the object-local view of a [CacheHistory].  Snapshot lemmas
    are useful for Iris state interpretations, where a single object/config is
    usually the owned resource. *)
Definition CacheHistorySnapshot {AbsVal : Type}
    (P : CacheProtocol AbsVal) : Type :=
  forall k : cache_field P, list (cache_val P k).

Definition cache_history_snapshot {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist : CacheHistory P) (o : Obj) :
    CacheHistorySnapshot P :=
  fun k => Hist o k.

(** [CacheHistOK P Hist o a] is the central field-history invariant: every
    value already present in every cache-field history for [o] is valid for
    abstract value [a]. *)
Definition CacheHistOK {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
    (o : Obj) (a : AbsVal) : Prop :=
  forall k (v : cache_val P k)
    (Hin : In v (Hist o k)),
    cache_valid P a k v.

Definition CacheHistSnapshotOK {AbsVal : Type}
    (P : CacheProtocol AbsVal) (snap : CacheHistorySnapshot P)
    (a : AbsVal) : Prop :=
  forall k (v : cache_val P k)
    (Hin : In v (snap k)),
    cache_valid P a k v.

(** A valid extension may keep old history entries and append new values, but
    any new value must itself satisfy [cache_valid].  This is the semantic side
    condition used when a method performs cache writes. *)
Definition CacheHistValidExtension {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist Hist' : CacheHistory P)
    (o o' : Obj) (a : AbsVal) : Prop :=
  forall k (v : cache_val P k)
    (Hnew : In v (Hist' o' k)),
    In v (Hist o k) \/ cache_valid P a k v.

Definition CacheHistSnapshotValidExtension {AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (snap snap' : CacheHistorySnapshot P) (a : AbsVal) : Prop :=
  forall k (v : cache_val P k)
    (Hnew : In v (snap' k)),
    In v (snap k) \/ cache_valid P a k v.

Lemma cache_hist_ok_snapshot :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist : CacheHistory P) o a
    (Hhist : CacheHistOK P Hist o a),
    CacheHistSnapshotOK
      P
      (@cache_history_snapshot Obj AbsVal P Hist o)
      a.
Proof.
  intros Obj AbsVal P Hist o a Hhist k v Hin.
  apply Hhist.
  exact Hin.
Qed.

Lemma cache_hist_snapshot_ok_history :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist : CacheHistory P) o a
    (Hsnap :
    CacheHistSnapshotOK
      P
      (@cache_history_snapshot Obj AbsVal P Hist o)
      a),
    CacheHistOK P Hist o a.
Proof.
  intros Obj AbsVal P Hist o a Hsnap k v Hin.
  apply Hsnap.
  exact Hin.
Qed.

Lemma cache_hist_valid_extension_snapshot :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (Hist Hist' : @CacheHistory Obj AbsVal P) o o' a
    (Hext : CacheHistValidExtension P Hist Hist' o o' a),
    CacheHistSnapshotValidExtension
      P
      (@cache_history_snapshot Obj AbsVal P Hist o)
      (@cache_history_snapshot Obj AbsVal P Hist' o')
      a.
Proof.
  intros Obj AbsVal P Hist Hist' o o' a Hext k v Hin.
  apply Hext.
  exact Hin.
Qed.

Lemma cache_hist_ok_valid_extension :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (Hist Hist' : @CacheHistory Obj AbsVal P) o o' a
    (Hhist : CacheHistOK P Hist o a)
    (Hext : CacheHistValidExtension P Hist Hist' o o' a),
    CacheHistOK P Hist' o' a.
Proof.
  intros Obj AbsVal P Hist Hist' o o' a Hhist Hext k v Hin.
  destruct (Hext k v Hin) as [Hold | Hvalid].
  - apply Hhist.
    exact Hold.
  - exact Hvalid.
Qed.

Lemma cache_hist_snapshot_ok_valid_extension :
  forall {AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (snap snap' : CacheHistorySnapshot P) a
    (Hsnap : CacheHistSnapshotOK P snap a)
    (Hext : CacheHistSnapshotValidExtension P snap snap' a),
    CacheHistSnapshotOK P snap' a.
Proof.
  intros AbsVal P snap snap' a Hsnap Hext k v Hin.
  destruct (Hext k v Hin) as [Hold | Hvalid].
  - apply Hsnap.
    exact Hold.
  - exact Hvalid.
Qed.

(** ** Cache-Read Traces *)

(** A cache observation records one field and the value read from it.  A trace
    is a list of such observations, abstracting away the concrete operational
    interleaving that produced the reads. *)
Record CacheObs {AbsVal : Type} (P : CacheProtocol AbsVal) : Type := {
  obs_field : cache_field P;
  obs_value : cache_val P obs_field
}.

Arguments obs_field {_ _} _.
Arguments obs_value {_ _} _.

Definition CacheTrace {AbsVal : Type} (P : CacheProtocol AbsVal) : Type :=
  list (CacheObs P).

Definition ValidObs {AbsVal : Type}
    (P : CacheProtocol AbsVal) (a : AbsVal) (obs : CacheObs P) : Prop :=
  cache_valid P a (obs_field obs) (obs_value obs).

Definition ValidTrace {AbsVal : Type}
    (P : CacheProtocol AbsVal) (a : AbsVal) (tr : CacheTrace P) : Prop :=
  Forall (ValidObs P a) tr.

Definition TraceReadsFromHistory {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
    (o : Obj) (tr : CacheTrace P) : Prop :=
  Forall
    (fun obs => read_cache o (obs_field obs) (obs_value obs))
    tr.

Definition TraceReadsFromSnapshot {AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (snap : CacheHistorySnapshot P) (tr : CacheTrace P) : Prop :=
  Forall
    (fun obs => In (obs_value obs) (snap (obs_field obs)))
    tr.

Definition TraceContains {AbsVal : Type}
    (P : CacheProtocol AbsVal) (tr : CacheTrace P)
    (k : cache_field P) (v : cache_val P k) : Prop :=
  In (@Build_CacheObs AbsVal P k v) tr.

(** [CacheHistExtendsByTrace] connects writes performed by a method to the
    history extension they induce: any appended value must appear in the
    method's write trace. *)
Definition CacheHistExtendsByTrace {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (Hist Hist' : @CacheHistory Obj AbsVal P)
    (o o' : Obj) (tr : CacheTrace P) : Prop :=
  forall k,
    exists added : list (cache_val P k),
      Hist' o' k = Hist o k ++ added /\
      forall v (Hin : In v added), TraceContains P tr k v.

Definition CacheHistSnapshotExtendsByTrace {AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (snap snap' : CacheHistorySnapshot P) (tr : CacheTrace P) : Prop :=
  forall k,
    exists added : list (cache_val P k),
      snap' k = snap k ++ added /\
      forall v (Hin : In v added), TraceContains P tr k v.

Lemma cache_hist_extends_by_trace_snapshot :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (Hist Hist' : @CacheHistory Obj AbsVal P) o o' tr
    (Hext : CacheHistExtendsByTrace P Hist Hist' o o' tr),
    CacheHistSnapshotExtendsByTrace
      P
      (@cache_history_snapshot Obj AbsVal P Hist o)
      (@cache_history_snapshot Obj AbsVal P Hist' o')
      tr.
Proof.
  intros Obj AbsVal P Hist Hist' o o' tr Hext k.
  destruct (Hext k) as [added [Heq Hadded]].
  exists added.
  split; assumption.
Qed.

(** [cache_read_valid] is the key memory-interface lemma.  If the memory model
    guarantees that a cache read returns a whole value from the field history,
    and the history is valid, then the observed value is protocol-valid. *)
Lemma cache_read_valid :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
    (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
    (read_from_history :
      forall o k (v : cache_val P k),
        read_cache o k v -> In v (Hist o k))
    o a k (v : cache_val P k)
    (Hhist : CacheHistOK P Hist o a)
    (Hread : read_cache o k v),
    cache_valid P a k v.
Proof.
  intros Obj AbsVal P Hist read_cache read_from_history o a k v Hhist Hread.
  apply Hhist.
  apply read_from_history.
  exact Hread.
Qed.

Lemma valid_trace_from_history :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
    (read_cache : Obj -> forall k : cache_field P, cache_val P k -> Prop)
    (read_from_history :
      forall o k (v : cache_val P k),
        read_cache o k v -> In v (Hist o k))
    o a tr
    (Hhist : CacheHistOK P Hist o a)
    (Hreads : TraceReadsFromHistory P read_cache o tr),
    ValidTrace P a tr.
Proof.
  intros Obj AbsVal P Hist read_cache read_from_history o a tr Hhist Hreads.
  unfold ValidTrace, TraceReadsFromHistory in *.
  induction Hreads as [|obs tr Hread _ IH]; constructor.
  - unfold ValidObs.
    eapply cache_read_valid; eauto.
  - exact IH.
Qed.

Lemma valid_trace_from_post_history_with_valid_extension :
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
    ValidTrace P a tr.
Proof.
  intros Obj AbsVal P Hist Hist' read_cache read_from_post_history
         o o' a tr Hhist Hext Hreads.
  pose proof
    (cache_hist_ok_valid_extension P Hist Hist' o o' a Hhist Hext)
    as Hhist'.
  eapply valid_trace_from_history; eauto.
Qed.

Lemma valid_trace_from_snapshot :
  forall {AbsVal : Type}
    (P : CacheProtocol AbsVal) (snap : CacheHistorySnapshot P) a tr
    (Hsnap : CacheHistSnapshotOK P snap a)
    (Hreads : TraceReadsFromSnapshot P snap tr),
    ValidTrace P a tr.
Proof.
  intros AbsVal P snap a tr Hsnap Hreads.
  unfold ValidTrace, TraceReadsFromSnapshot in *.
  induction Hreads as [|obs tr Hread _ IH]; constructor.
  - unfold ValidObs.
    apply Hsnap.
    exact Hread.
  - exact IH.
Qed.

Lemma valid_trace_from_post_snapshot_with_valid_extension :
  forall {AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (snap snap' : CacheHistorySnapshot P) a tr
    (Hsnap : CacheHistSnapshotOK P snap a)
    (Hext : CacheHistSnapshotValidExtension P snap snap' a)
    (Hreads : TraceReadsFromSnapshot P snap' tr),
    ValidTrace P a tr.
Proof.
  intros AbsVal P snap snap' a tr Hsnap Hext Hreads.
  pose proof
    (cache_hist_snapshot_ok_valid_extension P snap snap' a Hsnap Hext)
    as Hsnap'.
  eapply valid_trace_from_snapshot; eauto.
Qed.

Lemma valid_trace_contains_valid :
  forall {AbsVal : Type}
    (P : CacheProtocol AbsVal) a tr k (v : cache_val P k)
    (Htrace : ValidTrace P a tr)
    (Hin : TraceContains P tr k v),
    cache_valid P a k v.
Proof.
  intros AbsVal P a tr k v Htrace Hin.
  pose proof
    (proj1 (Forall_forall (ValidObs P a) tr) Htrace
      (@Build_CacheObs AbsVal P k v) Hin) as Hobs.
  unfold ValidObs in Hobs.
  cbn in Hobs.
  exact Hobs.
Qed.

Lemma cache_hist_extends_by_valid_trace :
  forall {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (Hist Hist' : @CacheHistory Obj AbsVal P) o o' a tr
    (Htrace : ValidTrace P a tr)
    (Hext : CacheHistExtendsByTrace P Hist Hist' o o' tr),
    CacheHistValidExtension P Hist Hist' o o' a.
Proof.
  intros Obj AbsVal P Hist Hist' o o' a tr Htrace Hext k v Hin.
  destruct (Hext k) as [added [Heq Hadded]].
  rewrite Heq in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hold | Hnew].
  - left.
    exact Hold.
  - right.
    eapply valid_trace_contains_valid.
    + exact Htrace.
    + apply Hadded.
      exact Hnew.
Qed.

Lemma cache_hist_snapshot_extends_by_valid_trace :
  forall {AbsVal : Type}
    (P : CacheProtocol AbsVal)
    (snap snap' : CacheHistorySnapshot P) a tr
    (Htrace : ValidTrace P a tr)
    (Hext : CacheHistSnapshotExtendsByTrace P snap snap' tr),
    CacheHistSnapshotValidExtension P snap snap' a.
Proof.
  intros AbsVal P snap snap' a tr Htrace Hext k v Hin.
  destruct (Hext k) as [added [Heq Hadded]].
  rewrite Heq in Hin.
  apply in_app_or in Hin.
  destruct Hin as [Hold | Hnew].
  - left.
    exact Hold.
  - right.
    eapply valid_trace_contains_valid.
    + exact Htrace.
    + apply Hadded.
      exact Hnew.
Qed.

(** ** Method Semantics and Trace-Robust Safety *)

(** [CacheRun] is the semantic footprint of one method execution under one
    cache-read trace: its result and the cache values it writes. *)
Record CacheRun {AbsVal : Type}
    (P : CacheProtocol AbsVal) (Result : Type) : Type := {
  run_result : Result;
  run_writes : CacheTrace P
}.

Arguments run_result {_ _ _} _.
Arguments run_writes {_ _ _} _.

(** [CacheSafeMethod] is the trace-robust method contract.  For every protocol-
    valid cache-read trace, the method returns the pure result and emits only
    protocol-valid cache writes. *)
Definition CacheSafeMethod {AbsVal Args Result : Type}
    (P : CacheProtocol AbsVal)
    (F : AbsVal -> Args -> Result)
    (run_with_cache_trace :
      AbsVal -> Args -> CacheTrace P -> CacheRun P Result) : Prop :=
  forall a args tr
    (Htrace : ValidTrace P a tr),
    run_result (run_with_cache_trace a args tr) = F a args /\
    ValidTrace P a (run_writes (run_with_cache_trace a args tr)).

(** Extract the result half of a [CacheSafeMethod]. *)
Lemma cache_safe_method_result :
  forall {AbsVal Args Result : Type}
    (P : CacheProtocol AbsVal)
    (F : AbsVal -> Args -> Result)
    (run_with_cache_trace :
      AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
    a args tr
    (Hsafe : CacheSafeMethod P F run_with_cache_trace)
    (Htrace : ValidTrace P a tr),
    run_result (run_with_cache_trace a args tr) = F a args.
Proof.
  intros AbsVal Args Result P F run a args tr Hsafe Htrace.
  destruct (Hsafe a args tr Htrace) as [Hresult _].
  exact Hresult.
Qed.

(** Extract the write-validity half of a [CacheSafeMethod]. *)
Lemma cache_safe_method_writes_valid :
  forall {AbsVal Args Result : Type}
    (P : CacheProtocol AbsVal)
    (F : AbsVal -> Args -> Result)
    (run_with_cache_trace :
      AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
    a args tr
    (Hsafe : CacheSafeMethod P F run_with_cache_trace)
    (Htrace : ValidTrace P a tr),
    ValidTrace P a (run_writes (run_with_cache_trace a args tr)).
Proof.
  intros AbsVal Args Result P F run a args tr Hsafe Htrace.
  destruct (Hsafe a args tr Htrace) as [_ Hwrites].
  exact Hwrites.
Qed.

(** If a cache-safe method's emitted writes are exactly the newly appended
    history entries, then the post-history is a valid extension. *)
Theorem cache_safe_method_writes_history_valid_extension :
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
    CacheHistValidExtension P Hist Hist' o o' a.
Proof.
  intros Obj AbsVal Args Result P Hist Hist' F run o o' a args tr
         Hsafe Htrace Hext.
  eapply cache_hist_extends_by_valid_trace.
  - eapply cache_safe_method_writes_valid; eauto.
  - exact Hext.
Qed.

(** Snapshot form of [cache_safe_method_writes_history_valid_extension], used
    by the Iris state-interpretation layer. *)
Theorem cache_safe_method_writes_snapshot_valid_extension :
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
    CacheHistSnapshotValidExtension P snap snap' a.
Proof.
  intros AbsVal Args Result P snap snap' F run a args tr
         Hsafe Htrace Hext.
  eapply cache_hist_snapshot_extends_by_valid_trace.
  - eapply cache_safe_method_writes_valid; eauto.
  - exact Hext.
Qed.

(** [weak_exec_matches_trace] relates an external operational execution to the
    abstract trace semantics used by the generic proof. *)
Definition weak_exec_matches_trace {AbsVal Args Result : Type}
    (P : CacheProtocol AbsVal)
    (run_with_cache_trace :
      AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
    (a : AbsVal) (args : Args) (tr : CacheTrace P) (r : Result) : Prop :=
  run_result (run_with_cache_trace a args tr) = r.

Definition PureRecomputeResult {AbsVal Args Result : Type}
    (F : AbsVal -> Args -> Result)
    (a : AbsVal) (args : Args) (r : Result) : Prop :=
  r = F a args.

Definition CacheRefinesPure {AbsVal Args Result : Type}
    (P : CacheProtocol AbsVal)
    (F : AbsVal -> Args -> Result)
    (run_with_cache_trace :
      AbsVal -> Args -> CacheTrace P -> CacheRun P Result) : Prop :=
  forall a args tr r
    (Htrace : ValidTrace P a tr)
    (Hexec : weak_exec_matches_trace P run_with_cache_trace a args tr r),
    PureRecomputeResult F a args r.

(** [SemImm] packages the two semantic facts preserved by the main theorem:
    the provider object still denotes the same stable abstraction and the cache
    history remains valid for that abstraction. *)
Definition SemImm {Obj AbsVal : Type}
    (P : CacheProtocol AbsVal) (Hist : CacheHistory P)
    (Stable : StableAbs Obj AbsVal) (o : Obj) (a : AbsVal) : Prop :=
  Stable o a /\ CacheHistOK P Hist o a.

(** A cache-safe method returns the pure recomputation result and preserves the
    semantic immutability predicate when run under a valid trace. *)
Theorem cache_safe_method_sound :
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
    r = F a args /\ SemImm P Hist Stable o a.
Proof.
  intros Obj AbsVal Args Result P Hist Stable F run o a args tr r
         Hstable Hhist Hsafe Htrace Hexec.
  unfold weak_exec_matches_trace in Hexec.
  destruct (Hsafe a args tr Htrace) as [Hresult _].
  split.
  - rewrite <- Hexec.
    exact Hresult.
  - split; assumption.
Qed.

(** This variant allows the final object/history pair to differ from the
    initial one, provided the new history is a valid extension and the provider
    still supplies the same stable abstraction. *)
Theorem cache_safe_method_sound_with_valid_history_extension :
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
    r = F a args /\ SemImm P Hist' Stable o' a.
Proof.
  intros Obj AbsVal Args Result P Hist Hist' Stable F run o o' a args tr r
         Hstable Hstable' Hhist Hsafe Htrace Hexec Hext.
  destruct (cache_safe_method_sound
    P Hist Stable F run o a args tr r
    Hstable Hhist Hsafe Htrace Hexec) as [Hresult _].
  split.
  - exact Hresult.
  - split.
    + exact Hstable'.
    + eapply cache_hist_ok_valid_extension; eauto.
Qed.

(** The refinement theorem: any [CacheSafeMethod] is observationally equivalent
    to pure recomputation for all valid cache-read traces. *)
Theorem cache_safe_method_refines_pure :
  forall {AbsVal Args Result : Type}
    (P : CacheProtocol AbsVal)
    (F : AbsVal -> Args -> Result)
    (run_with_cache_trace :
      AbsVal -> Args -> CacheTrace P -> CacheRun P Result),
    forall (Hsafe : CacheSafeMethod P F run_with_cache_trace),
    CacheRefinesPure P F run_with_cache_trace.
Proof.
  intros AbsVal Args Result P F run Hsafe a args tr r Htrace Hexec.
  unfold PureRecomputeResult, weak_exec_matches_trace in *.
  destruct (Hsafe a args tr Htrace) as [Hresult _].
  rewrite <- Hexec.
  exact Hresult.
Qed.

(** The first end-to-end theorem.  Whole-value reads from a valid history make
    the observed trace valid; trace-robust method safety then gives the pure
    result and preserves [SemImm]. *)
Theorem cache_safe_method_sound_from_history :
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
    r = F a args /\ SemImm P Hist Stable o a.
Proof.
  intros Obj AbsVal Args Result P Hist Stable read_cache read_from_history
         F run o a args tr r Hstable Hhist Hsafe Hreads Hexec.
  eapply cache_safe_method_sound; eauto.
  eapply valid_trace_from_history; eauto.
Qed.

Theorem cache_safe_method_sound_from_history_with_valid_extension :
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
    r = F a args /\ SemImm P Hist' Stable o' a.
Proof.
  intros Obj AbsVal Args Result P Hist Hist' Stable read_cache
         read_from_history F run o o' a args tr r Hstable Hstable'
         Hhist Hsafe Hreads Hexec Hext.
  eapply (cache_safe_method_sound_with_valid_history_extension
    P Hist Hist' Stable F run o o' a args tr r); eauto.
  eapply valid_trace_from_history; eauto.
Qed.

(** This variant first transports the invariant across a valid history
    extension, then reasons about a read trace from that post-history. *)
Theorem cache_safe_method_sound_from_post_history_with_valid_extension :
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
    r = F a args /\ SemImm P Hist' Stable o' a.
Proof.
  intros Obj AbsVal Args Result P Hist Hist' Stable read_cache
         read_from_post_history F run o o' a args tr r Hstable Hstable'
         Hhist Hsafe Hreads Hexec Hext.
  pose proof
    (cache_hist_ok_valid_extension P Hist Hist' o o' a Hhist Hext)
    as Hhist'.
  eapply (cache_safe_method_sound
    P Hist' Stable F run o' a args tr r); eauto.
  eapply valid_trace_from_history; eauto.
Qed.

(** [trace_robust_semantic_immutability] is the main generic story: if the
    provider abstraction is stable, reads come from valid histories, the method
    is safe for every valid trace, and its writes extend histories only with
    values it emitted, then the execution refines pure recomputation and the
    semantic immutability predicate is preserved. *)
Theorem trace_robust_semantic_immutability :
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
    r = F a args /\ SemImm P Hist' Stable o' a.
Proof.
  intros Obj AbsVal Args Result P Hist Hist' Stable read_cache
         read_from_history F run o o' a args tr r Hsem Hstable'
         Hsafe Hreads Hexec Hext_by_writes.
  destruct Hsem as [Hstable Hhist].
  pose proof
    (valid_trace_from_history
      P Hist read_cache read_from_history o a tr Hhist Hreads)
    as Htrace.
  pose proof
    (cache_safe_method_writes_history_valid_extension
      P Hist Hist' F run o o' a args tr Hsafe Htrace Hext_by_writes)
    as Hext.
  eapply (cache_safe_method_sound_with_valid_history_extension
    P Hist Hist' Stable F run o o' a args tr r); eauto.
Qed.

(** This version separates the pre-method history extension from the method's
    own write extension.  It is the shape used by weak executions that first
    take cache-safe steps and then run a method against the post-step history. *)
Theorem trace_robust_semantic_immutability_after_history_extension :
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
    r = F a args /\ SemImm P Hist' Stable o' a.
Proof.
  intros Obj AbsVal Args Result P Hist Hist_pre Hist' Stable read_cache
         read_from_pre_history F run o o_pre o' a args tr r Hsem
         Hstable_pre Hstable' Hpre_ext Hsafe Hreads Hexec Hext_by_writes.
  destruct Hsem as [_ Hhist].
  pose proof
    (cache_hist_ok_valid_extension
      P Hist Hist_pre o o_pre a Hhist Hpre_ext)
    as Hhist_pre.
  eapply (trace_robust_semantic_immutability
    P Hist_pre Hist' Stable read_cache read_from_pre_history F run
    o_pre o' a args tr r); eauto.
  split; assumption.
Qed.

Theorem cache_safe_method_refines_pure_from_history :
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
    PureRecomputeResult F a args r.
Proof.
  intros Obj AbsVal Args Result P Hist read_cache read_from_history
         F run o a args tr r Hhist Hsafe Hreads Hexec.
  eapply cache_safe_method_refines_pure; eauto.
  eapply valid_trace_from_history; eauto.
Qed.

Theorem cache_safe_method_refines_pure_from_post_history_with_valid_extension :
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
    PureRecomputeResult F a args r.
Proof.
  intros Obj AbsVal Args Result P Hist Hist' read_cache
         read_from_post_history F run o o' a args tr r Hhist Hext
         Hsafe Hreads Hexec.
  pose proof
    (cache_hist_ok_valid_extension P Hist Hist' o o' a Hhist Hext)
    as Hhist'.
  eapply cache_safe_method_refines_pure; eauto.
  eapply valid_trace_from_history; eauto.
Qed.

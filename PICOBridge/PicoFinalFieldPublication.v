From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers Bigstep DerivedCache Core.GenericDerivedCache.
Require Import PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoStableAbsPreservation.
Require Import MemoryModels.JMM.FinalFieldPublication.

(** * Published Final Snapshots Establish PICO Stable Abstractions *)

Definition pico_final_heap_snapshot
    (CT : class_table) (C : class_name) (abs_fields : list var)
    (h : heap) (loc : Loc) (snapshot : final_snapshot) : Prop :=
  exists object,
    runtime_getObj h loc = Some object /\
    rctype (rt_type object) = C /\
    final_fields CT C abs_fields /\
    field_reads h loc abs_fields snapshot.

(** The physical PICO snapshot and the publication observation agree on the
    same receiver, final fields, and values. *)
Definition pico_published_final_snapshot
    (CT : class_table) (C : class_name) (abs_fields : list var)
    (h : heap) (publication : final_publication_state)
    (observer : nat) (loc : Loc) (snapshot : final_snapshot) : Prop :=
  pico_final_heap_snapshot CT C abs_fields h loc snapshot /\
  final_snapshot_frozen publication loc snapshot /\
  final_snapshot_observed publication observer loc snapshot.

(** Stable abstraction as available to a particular observer.  The first
    conjunct is the PICO physical invariant; the second records visibility. *)
Definition pico_observer_stable_abs
    (CT : class_table) (C : class_name) (abs_fields : list var)
    (h : heap) (publication : final_publication_state)
    (observer : nat) (loc : Loc) (snapshot : final_snapshot) : Prop :=
  pico_stable_abs CT C abs_fields (h, loc) snapshot /\
  final_snapshot_observed publication observer loc snapshot.

Lemma pico_final_heap_snapshot_stable_abs :
  forall CT C abs_fields h loc snapshot,
    pico_final_heap_snapshot CT C abs_fields h loc snapshot ->
    pico_stable_abs CT C abs_fields (h, loc) snapshot.
Proof.
  intros CT C abs_fields h loc snapshot
    [object [Hobject [Hclass [Hfinal Hreads]]]].
  split; assumption.
Qed.

Theorem pico_published_final_snapshot_establishes_observer_stable_abs :
  forall CT C abs_fields h publication observer loc snapshot,
    pico_published_final_snapshot
      CT C abs_fields h publication observer loc snapshot ->
    pico_observer_stable_abs
      CT C abs_fields h publication observer loc snapshot.
Proof.
  intros CT C abs_fields h publication observer loc snapshot
    [Hheap [Hfrozen Hobserved]].
  split.
  - eapply pico_final_heap_snapshot_stable_abs. exact Hheap.
  - exact Hobserved.
Qed.

(** A complete publication execution derives observer-indexed stable state
    from the final-field heap snapshot and the observer's acquisition. *)
Theorem pico_publication_execution_establishes_observer_stable_abs :
  forall CT C abs_fields h final observer loc snapshot
    (Hsteps : final_publication_steps empty_final_publication_state final)
    (Hheap : pico_final_heap_snapshot CT C abs_fields h loc snapshot)
    (Hobserved : final_snapshot_observed final observer loc snapshot),
    pico_observer_stable_abs
      CT C abs_fields h final observer loc snapshot.
Proof.
  intros CT C abs_fields h final observer loc snapshot
    Hsteps Hheap Hobserved.
  pose proof (acquired_final_snapshot_is_frozen
    final observer loc snapshot Hsteps Hobserved) as Hfrozen.
  eapply pico_published_final_snapshot_establishes_observer_stable_abs.
  unfold pico_published_final_snapshot.
  exact (conj Hheap (conj Hfrozen Hobserved)).
Qed.

Corollary pico_publication_execution_establishes_core_stable_abs :
  forall CT C abs_fields state final observer loc snapshot
    (Hsteps : final_publication_steps empty_final_publication_state final)
    (Hheap : pico_final_heap_snapshot
      CT C abs_fields (pcs_heap state) loc snapshot)
    (Hobserved : final_snapshot_observed final observer loc snapshot),
    pico_core_stable_abs CT C abs_fields loc state snapshot.
Proof.
  intros CT C abs_fields [heap weak] final observer loc snapshot
    Hsteps Hheap Hobserved.
  unfold pico_core_stable_abs. simpl in *.
  destruct Hheap as [object [Hobject [Hclass [Hfinal Hreads]]]].
  exists object. split; [exact Hobject |].
  split; [exact Hclass |].
  pose proof (pico_publication_execution_establishes_observer_stable_abs
    CT C abs_fields heap final observer loc snapshot Hsteps) as Hpublished.
  apply Hpublished.
  - exists object. repeat split; assumption.
  - exact Hobserved.
Qed.

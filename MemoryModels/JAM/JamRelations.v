From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import PICOBridge.PicoMemoryModel MemoryModels.JAM.JamEvents
  MemoryModels.JAM.JamHistory.

(** * Constructive Plain JAM Relations

    This file reconstructs the plain-access specialization of JAM's
    visibility and derived coherence definitions.  JAM's atomic read-write
    generators are omitted because PICO cache accesses are ordinary reads and
    writes. *)

Inductive jam_plus {A : Type} (relation : A -> A -> Prop) : A -> A -> Prop :=
  | JamPlusOne : forall first second,
      relation first second ->
      jam_plus relation first second
  | JamPlusStep : forall first middle last,
      relation first middle ->
      jam_plus relation middle last ->
      jam_plus relation first last.

Arguments JamPlusOne {A relation first second} _.
Arguments JamPlusStep {A relation first middle last} _ _.

Definition jam_acyclic {A : Type} (relation : A -> A -> Prop) : Prop :=
  forall event, ~ jam_plus relation event event.

Lemma jam_plus_rank : forall {A : Type} (relation : A -> A -> Prop)
    (rank : A -> nat)
    (Hrank : forall first second,
      relation first second -> rank first < rank second)
    first second,
  jam_plus relation first second -> rank first < rank second.
Proof.
  intros A relation rank Hrank first second Hplus.
  induction Hplus.
  - eapply Hrank; eauto.
  - specialize (Hrank first middle H).
    lia.
Qed.

Lemma jam_ranked_relation_acyclic : forall {A : Type}
    (relation : A -> A -> Prop) (rank : A -> nat),
  (forall first second,
    relation first second -> rank first < rank second) ->
  jam_acyclic relation.
Proof.
  intros A relation rank Hrank event Hcycle.
  pose proof (jam_plus_rank relation rank Hrank event event Hcycle).
  lia.
Qed.

(** In the plain fragment, JAM visibility is the transitive closure of
    reads-from.  Opaque/release-acquire/volatile modes add further visibility
    generators in later fragments. *)
Definition jam_plain_visibility
    (execution : jam_execution) : jam_event -> jam_event -> Prop :=
  jam_plus (jam_reads_from execution).

Definition jam_plain_visible_or_po
    (execution : jam_execution) (first second : jam_event) : Prop :=
  jam_plain_visibility execution first second \/
  jam_program_order execution first second.

Definition jam_writes_to (event : jam_event) (addr : FieldAddr) : Prop :=
  jam_is_write event /\ jam_event_addr event = addr.

Definition jam_reads_at (event : jam_event) (addr : FieldAddr) : Prop :=
  jam_is_read event /\ jam_event_addr event = addr.

(** The four constructors are the non-atomic specialization of JAM's [co]:
    write/write, write/read, read/write, and read/read coherence. *)
Inductive jam_plain_coherence (execution : jam_execution) :
    jam_event -> jam_event -> Prop :=
  | JamPlainCoWW : forall first second addr,
      jam_plain_visible_or_po execution first second ->
      jam_writes_to first addr ->
      jam_writes_to second addr ->
      jam_plain_coherence execution first second
  | JamPlainCoWR : forall first selected read addr,
      jam_plain_visible_or_po execution first read ->
      jam_reads_from execution selected read ->
      jam_writes_to first addr ->
      jam_reads_at read addr ->
      first <> selected ->
      jam_plain_coherence execution first selected
  | JamPlainCoRW : forall first read second addr,
      jam_plain_visible_or_po execution first read ->
      jam_program_order execution read second ->
      jam_writes_to first addr ->
      jam_reads_at read addr ->
      jam_writes_to second addr ->
      jam_plain_coherence execution first second
  | JamPlainCoRR : forall first second first_read second_read addr,
      jam_reads_from execution first first_read ->
      jam_reads_from execution second second_read ->
      jam_program_order execution first_read second_read ->
      jam_writes_to first addr ->
      jam_writes_to second addr ->
      first <> second ->
      jam_plain_coherence execution first second.

Definition jam_plain_causality (execution : jam_execution) :
    jam_event -> jam_event -> Prop :=
  jam_reads_from execution.

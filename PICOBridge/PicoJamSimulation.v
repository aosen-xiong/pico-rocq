From Stdlib Require Import List PeanoNat.
Import ListNotations.

Require Import Syntax PICOBridge.PicoMemoryModel
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoLabeledExecution.
Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory
  MemoryModels.JAM.JamLegality MemoryModels.JAM.JamFieldHistoryBridge.

(** * PICO Access Traces Realized by JAM Histories

    A realization retains explicit reads-from choices in the JAM execution.
    This matters when duplicate writes carry the same value: values alone do
    not determine which write a stale read observed. *)

Definition pico_access_jam_kind (kind : pico_access_kind) : jam_access_kind :=
  match kind with
  | PicoRead => JamRead
  | PicoWrite => JamWrite
  end.

Definition pico_access_matches_jam
    (access : pico_access_event) (event : jam_event) : Prop :=
  jam_event_thread event = access_thread access /\
  jam_event_kind event = pico_access_jam_kind (access_kind access) /\
  jam_event_addr event = access_addr access /\
  jam_event_value event = access_value access /\
  jam_event_mode event = JamPlain.

Definition pico_jam_realization
    (accesses : list pico_access_event) (execution : jam_execution) : Prop :=
  exists initial_events access_events,
    jam_events execution = initial_events ++ access_events /\
    Forall
      (fun event =>
        jam_event_kind event = JamInit /\ jam_event_mode event = JamPlain)
      initial_events /\
    Forall2 pico_access_matches_jam accesses access_events.

Lemma Forall2_in_left_exists : forall {A B : Type} (R : A -> B -> Prop)
    left right x,
  Forall2 R left right ->
  In x left ->
  exists y, In y right /\ R x y.
Proof.
  intros A B R left right x Hrelated Hin.
  induction Hrelated as [|left_head right_head left_tail right_tail
    Hhead Htail IH]; simpl in Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst left_head. exists right_head. split; [left; reflexivity | assumption].
    + destruct (IH Hin) as [y [Hy HR]].
      exists y. split; [right; exact Hy | exact HR].
Qed.

Lemma pico_jam_access_event_in :
  forall accesses execution access
    (Hrealized : pico_jam_realization accesses execution)
    (Hin : In access accesses),
    exists event,
      jam_event_in execution event /\
      pico_access_matches_jam access event.
Proof.
  intros accesses execution access Hrealized Hin.
  destruct Hrealized as
    [initial_events [access_events [Hevents [Hinitial Hmatches]]]].
  destruct (Forall2_in_left_exists
    pico_access_matches_jam accesses access_events access Hmatches Hin) as
    [event [HinEvents Hmatch]].
  exists event. split; [|exact Hmatch].
  unfold jam_event_in. rewrite Hevents.
  apply in_or_app. right. exact HinEvents.
Qed.

Lemma pico_read_matches_jam_read : forall access event,
  pico_access_matches_jam access event ->
  access_kind access = PicoRead ->
  jam_is_read event.
Proof.
  intros access event
    [Hthread [Hkind [Haddr [Hvalue Hmode]]]] Hread.
  unfold jam_is_read.
  rewrite Hkind, Hread. reflexivity.
Qed.

Theorem pico_read_realized_by_jam_history :
  forall accesses execution access
    (Hrealized : pico_jam_realization accesses execution)
    (Hlegal : jam_plain_legal execution)
    (Hin : In access accesses)
    (Hread : access_kind access = PicoRead),
    In (access_value access)
      (jam_field_history execution (access_addr access)).
Proof.
  intros accesses execution access Hrealized Hlegal Hin Hread.
  destruct (pico_jam_access_event_in accesses execution access
    Hrealized Hin) as [event [Hevent Hmatches]].
  pose proof (pico_read_matches_jam_read access event Hmatches Hread) as
    Hevent_read.
  pose proof (jam_plain_read_from_same_field_history execution event
    Hlegal Hevent Hevent_read) as Hhistory.
  destruct Hmatches as
    [Hthread [Hkind [Haddr [Hvalue Hmode]]]].
  rewrite <- Hvalue, <- Haddr.
  exact Hhistory.
Qed.

Definition pico_access_observation (access : pico_access_event) :
    pico_access_kind * FieldAddr * value :=
  (access_kind access, access_addr access, access_value access).

Definition jam_access_observation (event : jam_event) :
    jam_access_kind * FieldAddr * value :=
  (jam_event_kind event, jam_event_addr event, jam_event_value event).

Theorem pico_jam_access_observations_correspond :
  forall accesses events,
    Forall2 pico_access_matches_jam accesses events ->
    map jam_access_observation events =
    map
      (fun access =>
        (pico_access_jam_kind (access_kind access),
         access_addr access,
         access_value access))
      accesses.
Proof.
  intros accesses events Hmatches.
  induction Hmatches as
    [|access event accesses events Hmatch Htail IH]; simpl; [reflexivity |].
  destruct Hmatch as
    [Hthread [Hkind [Haddr [Hvalue Hmode]]]].
  f_equal.
  - unfold jam_access_observation.
    rewrite Hkind, Haddr, Hvalue. reflexivity.
  - exact IH.
Qed.

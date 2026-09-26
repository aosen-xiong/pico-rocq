From Stdlib Require Import List PeanoNat.
Import ListNotations.

Require Import Syntax PICOBridge.PicoMemoryModel MemoryModels.JAM.JamEvents.

(** * JAM Histories and Reads-From

    A history is an ordered list of issued/executed memory events together with
    a reads-from relation.  The list order is the operational trace order used
    by the JAM history presentation. *)

Record jam_execution : Type := mkJamExecution {
  jam_events : list jam_event;
  jam_rf : jam_event -> jam_event -> Prop;
}.

Definition jam_event_in (execution : jam_execution) (event : jam_event) : Prop :=
  In event (jam_events execution).

Definition jam_reads_from
    (execution : jam_execution) (write read : jam_event) : Prop :=
  jam_rf execution write read.

(** List position is the operational trace order.  Event identifiers are also
    required to increase along that order; this prevents an execution from
    assigning an earlier identifier to an event that occurs later in the trace. *)
Definition jam_list_before
    (events : list jam_event) (first second : jam_event) : Prop :=
  exists prefix middle suffix,
    events = prefix ++ first :: middle ++ second :: suffix.

Definition jam_trace_before
    (events : list jam_event) (first second : jam_event) : Prop :=
  In first events /\
  In second events /\
  jam_event_id first < jam_event_id second /\
  jam_list_before events first second.

Definition jam_program_order
    (execution : jam_execution) (first second : jam_event) : Prop :=
  jam_event_thread first = jam_event_thread second /\
  jam_trace_before (jam_events execution) first second.

Fixpoint jam_field_history_events
    (events : list jam_event) (addr : FieldAddr) : list value :=
  match events with
  | [] => []
  | event :: tail =>
      match jam_event_kind event with
      | JamRead => jam_field_history_events tail addr
      | JamInit | JamWrite =>
          if field_addr_eqb (jam_event_addr event) addr
          then jam_event_value event :: jam_field_history_events tail addr
          else jam_field_history_events tail addr
      end
  end.

Definition jam_field_history
    (execution : jam_execution) (addr : FieldAddr) : list value :=
  jam_field_history_events (jam_events execution) addr.

Lemma field_addr_eqb_true : forall left right,
  field_addr_eqb left right = true -> left = right.
Proof.
  intros [left_loc left_field] [right_loc right_field].
  unfold field_addr_eqb. simpl.
  rewrite Bool.andb_true_iff.
  intros [Hloc Hfield].
  apply Nat.eqb_eq in Hloc.
  apply Nat.eqb_eq in Hfield.
  subst. reflexivity.
Qed.

Lemma field_addr_eqb_refl : forall addr,
  field_addr_eqb addr addr = true.
Proof.
  intros [loc field].
  unfold field_addr_eqb. simpl.
  rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma jam_write_in_field_history : forall events event addr,
  In event events ->
  jam_is_write event ->
  jam_event_addr event = addr ->
  In (jam_event_value event) (jam_field_history_events events addr).
Proof.
  intros events event addr Hin Hwrite Haddr.
  induction events as [|head tail IH]; simpl in Hin; [contradiction |].
  destruct Hin as [Heq | Hin].
  - subst event.
    destruct (jam_event_kind head) eqn:Hkind; simpl.
    + rewrite Hkind, Haddr, field_addr_eqb_refl. apply in_eq.
    + unfold jam_is_write in Hwrite.
      rewrite Hkind in Hwrite.
      destruct Hwrite as [Hfalse | Hfalse]; discriminate.
    + rewrite Hkind, Haddr, field_addr_eqb_refl. apply in_eq.
  - destruct (jam_event_kind head) eqn:Hkind; simpl.
    + rewrite Hkind.
      destruct (field_addr_eqb (jam_event_addr head) addr); simpl; auto.
    + rewrite Hkind. apply IH; assumption.
    + rewrite Hkind.
      destruct (field_addr_eqb (jam_event_addr head) addr); simpl; auto.
Qed.

Lemma jam_execution_write_in_field_history :
  forall execution event,
    jam_event_in execution event ->
    jam_is_write event ->
    In (jam_event_value event)
      (jam_field_history execution (jam_event_addr event)).
Proof.
  intros execution event Hin Hwrite.
  unfold jam_field_history.
  eapply jam_write_in_field_history; eauto.
Qed.

From Stdlib Require Import List PeanoNat.

Require Import Syntax PICOBridge.PicoMemoryModel.

(** * Java Access Mode Events

    This module reconstructs, in modern Rocq, the event vocabulary needed from
    Bender and Palsberg's Java Access Modes (JAM) history semantics.  It is a
    clean formalization against PICO's concrete [FieldAddr] and [value] types;
    it does not import the original Coq 8.6 development or its axioms.

    The plain fragment is sufficient for the current racy-cache examples.  The
    remaining constructors make the boundary explicit for later extensions. *)

Inductive jam_mode : Type :=
  | JamPlain
  | JamOpaque
  | JamReleaseAcquire
  | JamVolatile.

Inductive jam_access_kind : Type :=
  | JamInit
  | JamRead
  | JamWrite.

Record jam_event : Type := mkJamEvent {
  jam_event_id : nat;
  jam_event_thread : nat;
  jam_event_kind : jam_access_kind;
  jam_event_addr : FieldAddr;
  jam_event_value : value;
  jam_event_mode : jam_mode;
}.

Definition jam_is_read (event : jam_event) : Prop :=
  jam_event_kind event = JamRead.

Definition jam_is_write (event : jam_event) : Prop :=
  jam_event_kind event = JamInit \/ jam_event_kind event = JamWrite.

Definition jam_is_plain (event : jam_event) : Prop :=
  jam_event_mode event = JamPlain.

Definition jam_same_location (first second : jam_event) : Prop :=
  jam_event_addr first = jam_event_addr second.

Definition jam_same_value (first second : jam_event) : Prop :=
  jam_event_value first = jam_event_value second.

Definition jam_event_ids (events : list jam_event) : list nat :=
  map jam_event_id events.


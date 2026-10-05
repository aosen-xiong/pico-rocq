From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep.
Require Import Core.GenericCacheProtocol Core.RelyGuarantee
  Core.GenericDerivedCache Core.SemanticValue.
Require Import Examples.PicoIfZeroCache
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoRefCacheExample Examples.PicoRefViewExample.
Require Import PICOBridge.PicoMemoryModel.

(** * Semantic Value Classes: Instances

    The hash class is a semantic value class in the generic sense: its
    protocol is derived, and its accessor is trace robust.

    For PICO classes, the state-completeness half of the definition is a
    condition on the class table: every field of the class is an
    abstract-state field or a declared derived field.  The example classes
    of the development satisfy it. *)

(** ** The hash class, generically *)

Definition hash_derive (a : nat) (k : cache_field hash_cache_protocol)
    : cache_val hash_cache_protocol k := Int a.

Lemma hash_protocol_derived : DerivedProtocol hash_cache_protocol hash_derive.
Proof.
  intros a k v [-> | [-> _]]; [left | right]; reflexivity.
Qed.

Definition hash_value_method (_ : unit) : ValueMethod hash_cache_protocol :=
  {| vm_args := unit;
     vm_result := value;
     vm_spec := hash_pure_result;
     vm_run := good_hash_run |}.

Definition hash_value_class :
    SemanticValueClass hash_cache_protocol hash_value_method :=
  mkSemanticValueClass hash_cache_protocol unit hash_value_method
    hash_derive hash_protocol_derived
    (fun _ => good_hash_cache_safe_method).

(** Two hash objects with the same abstract value return the same hash code,
    whatever each of them reads from its cache. *)
Theorem hash_objects_equal_results :
  forall (Obj : Type) (Stable : StableAbs Obj nat) a
    (s1 s2 : @CacheState Obj nat hash_cache_protocol) tr1 tr2,
    SemanticValueObject hash_cache_protocol Stable a s1 ->
    SemanticValueObject hash_cache_protocol Stable a s2 ->
    ReadsFrom hash_cache_protocol s1 tr1 ->
    ReadsFrom hash_cache_protocol s2 tr2 ->
    run_result (good_hash_run a tt tr1) = run_result (good_hash_run a tt tr2).
Proof.
  intros Obj Stable a s1 s2 tr1 tr2 H1 H2 Hr1 Hr2.
  exact (value_objects_equal_results hash_cache_protocol Stable
    hash_value_method hash_value_class tt a s1 s2 tt tr1 tr2 H1 H2 Hr1 Hr2).
Qed.

(** ** State completeness for PICO classes *)

(** Every field of class [C] is an abstract-state field or a derived field:
    an assignable field in the declared set [derived]. *)
Definition value_class_fields
    (CT : class_table) (C : class_name) (derived : var -> Prop) : Prop :=
  forall f fdef,
    FieldLookup CT C f fdef ->
    abstract_field CT C f \/ (derived f /\ derived_cache_field CT C f).

Lemma field_lookup_cases :
  forall CT C fields f fdef,
    CollectFields CT C fields ->
    FieldLookup CT C f fdef ->
    nth_error fields f = Some fdef.
Proof.
  intros CT C fields f fdef Hcf Hlookup.
  inversion Hlookup as [CT0 C0 fields0 f0 fdef0 Hcf0 Hget]; subst.
  have Heq := collect_fields_deterministic_rel CT _ _ _ Hcf Hcf0.
  subst fields0. exact Hget.
Qed.

(** The hash class: the payload is abstract state, the cache is derived. *)
Theorem hash_class_fields :
  value_class_fields pico_hash_concurrent_CT pico_hash_witness_class
    (fun f => f = PicoIfZeroCache.hash_cache_field).
Proof.
  intros f fdef Hlookup.
  have Hnth := field_lookup_cases _ _ _ _ _
    pico_hash_concurrent_collect_fields Hlookup.
  destruct f as [| [| f]]; simpl in Hnth.
  - right. split; [reflexivity | exact pico_hash_concurrent_cache_declared].
  - left. exact (pico_hash_payload_abstract pico_hash_concurrent_CT
      pico_hash_concurrent_payload_field_def).
  - destruct f; discriminate.
Qed.

(** The class with a cached view: its only field is derived. *)
Theorem rv_class_fields :
  value_class_fields rv_CT rv_class (fun f => f = rv_cache_field).
Proof.
  intros f fdef Hlookup.
  have Hnth := field_lookup_cases _ _ _ _ _ rv_collect_fields Hlookup.
  destruct f as [| f]; simpl in Hnth; [| destruct f; discriminate].
  right. split; [reflexivity |].
  exists rv_cache_def.
  split; [eapply FL_Found; [exact rv_collect_fields | reflexivity] | reflexivity].
Qed.

(** The view class: its only field is abstract state. *)
Theorem rv_view_class_fields :
  value_class_fields rv_CT rv_view_class (fun _ => False).
Proof.
  intros f fdef Hlookup.
  have Hnth := field_lookup_cases _ _ _ _ _ rv_view_collect_fields Hlookup.
  destruct f as [| f]; simpl in Hnth; [| destruct f; discriminate].
  left. exact rv_outer_abstract.
Qed.

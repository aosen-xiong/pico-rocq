From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Reachability.
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

(** ** Transitive completeness

    A value object has only abstract and derived state, transitively: the
    condition must hold for the class of every object it can reach, through
    abstract-state fields and through derived fields alike.  A field may
    hold an object of a subclass of its declared class, so reachability
    between classes follows field types and descends to subclasses. *)

Inductive class_reaches (CT : class_table) : class_name -> class_name -> Prop :=
  | ClassReaches_Refl : forall C,
      class_reaches CT C C
  | ClassReaches_Field : forall C f fdef D E,
      FieldLookup CT C f fdef ->
      f_base_type (ftype fdef) = TRef D ->
      class_reaches CT D E ->
      class_reaches CT C E
  | ClassReaches_Sub : forall C D E,
      class_subtype CT D C ->
      class_reaches CT D E ->
      class_reaches CT C E.

Lemma class_reaches_trans :
  forall CT C D E,
    class_reaches CT C D -> class_reaches CT D E -> class_reaches CT C E.
Proof.
  intros CT C D E H1 H2. induction H1.
  - exact H2.
  - eapply ClassReaches_Field; eauto.
  - eapply ClassReaches_Sub; eauto.
Qed.

(** [derived C f] says that [f] is a declared derived field of class [C]. *)
Definition transitive_value_class
    (CT : class_table) (derived : class_name -> var -> Prop)
    (C : class_name) : Prop :=
  forall D, class_reaches CT C D -> value_class_fields CT D (derived D).

(** At run time: every object reachable in the heap from an object of a
    transitive value class, through any fields, belongs to a class all of
    whose fields are abstract state or derived state. *)
Theorem reachable_objects_value_classes :
  forall CT derived C h,
    wf_heap CT h ->
    transitive_value_class CT derived C ->
    forall l l',
      reachable h l l' ->
      forall rt,
        r_type h l = Some rt ->
        class_reaches CT C (rctype rt) ->
        exists rt',
          r_type h l' = Some rt' /\
          class_reaches CT C (rctype rt') /\
          value_class_fields CT (rctype rt') (derived (rctype rt')).
Proof.
  intros CT derived C h Hheap Hvalue l l' Hreach.
  induction Hreach as
    [l Hdom | l0 l1 obj f Hdom Hobj Hfield | l0 l1 l2 H1 IH1 H2 IH2];
    intros rt Hrt Hclass.
  - exists rt. split; [exact Hrt |]. split; [exact Hclass | exact (Hvalue _ Hclass)].
  - unfold r_type in Hrt. rewrite Hobj in Hrt. injection Hrt as <-.
    have Hwf := Hheap l0 (runtime_getObj_dom _ _ _ Hobj).
    unfold wf_obj in Hwf. rewrite Hobj in Hwf.
    destruct Hwf as (_ & field_defs & Hcf & Hlen & Hall).
    unfold getVal in Hfield.
    assert (Hdef : exists fdef, nth_error field_defs f = Some fdef).
    { destruct (nth_error field_defs f) as [fdef |] eqn:Hnth; [eauto |].
      apply nth_error_None in Hnth.
      assert (f < length (fields_map obj))
        by (apply nth_error_Some; congruence).
      lia. }
    destruct Hdef as [fdef Hnth].
    assert (Hpair : exists rqt,
      r_type h l1 = Some rqt /\
      base_subtype CT (TRef (rctype rqt)) (f_base_type (ftype fdef))).
    { clear -Hall Hfield Hnth.
      revert f Hfield Hnth.
      induction Hall as [| v d vs ds Hvd Hrest IH]; intros f Hfield Hnth.
      - destruct f; discriminate.
      - destruct f as [| f]; simpl in Hfield, Hnth.
        + injection Hfield as ->. injection Hnth as ->.
          destruct (runtime_getObj h l1); [| contradiction].
          destruct Hvd as (rqt & Hr & Hb & _). eauto.
        + eapply IH; eassumption. }
    destruct Hpair as (rqt & Hrqt & Hbase).
    destruct (base_subtype_from_ref CT _ _ Hbase) as (D & HD & Hsub).
    assert (Hclass' : class_reaches CT C (rctype rqt)).
    { eapply class_reaches_trans; [exact Hclass |].
      eapply ClassReaches_Field.
      - eapply FL_Found; [exact Hcf | exact Hnth].
      - exact HD.
      - eapply ClassReaches_Sub; [exact Hsub | apply ClassReaches_Refl]. }
    exists rqt. split; [exact Hrqt |].
    split; [exact Hclass' | exact (Hvalue _ Hclass')].
  - destruct (IH1 rt Hrt Hclass) as (rt1 & Hrt1 & Hclass1 & _).
    exact (IH2 rt1 Hrt1 Hclass1).
Qed.

(** A class without subclasses has only itself below it. *)
Lemma class_subtype_no_children :
  forall CT D C,
    class_subtype CT D C ->
    (forall C', parent_lookup CT C' <> Some C) ->
    D = C.
Proof.
  intros CT D C Hsub.
  induction Hsub as [CT C _ | CT C D E _ IH1 _ IH2 | CT C D _ _ Hparent];
    intros Hnone.
  - reflexivity.
  - have HE := IH2 Hnone. subst D. exact (IH1 Hnone).
  - exfalso. exact (Hnone C Hparent).
Qed.

(** The hash class is a transitive value class: its fields are integers and
    it has no subclasses. *)
Theorem hash_class_transitive :
  transitive_value_class pico_hash_concurrent_CT
    (fun _ f => f = PicoIfZeroCache.hash_cache_field) pico_hash_witness_class.
Proof.
  assert (Hclosed : forall C D,
    class_reaches pico_hash_concurrent_CT C D ->
    C = pico_hash_witness_class -> D = pico_hash_witness_class).
  { intros C D Hreach. induction Hreach as
      [C | C f fdef D E Hlookup Hbase _ IH | C D E Hsub _ IH]; intros ->.
    - reflexivity.
    - have Hnth := field_lookup_cases _ _ _ _ _
        pico_hash_concurrent_collect_fields Hlookup.
      destruct f as [| [| f]]; simpl in Hnth;
        [injection Hnth as <-; discriminate
        | injection Hnth as <-; discriminate
        | destruct f; discriminate].
    - apply IH.
      eapply class_subtype_no_children; [exact Hsub |].
      intros [| [| C']]; cbv; try discriminate.
      destruct C'; discriminate. }
  intros D Hreach. rewrite (Hclosed _ _ Hreach eq_refl).
  exact hash_class_fields.
Qed.

(** The class with a cached view and its view class reach only each other,
    and both have only abstract and derived fields. *)
Theorem rv_class_transitive :
  transitive_value_class rv_CT
    (fun C f => C = rv_class /\ f = rv_cache_field) rv_class.
Proof.
  assert (Hclosed : forall C D,
    class_reaches rv_CT C D ->
    C = rv_class \/ C = rv_view_class ->
    D = rv_class \/ D = rv_view_class).
  { intros C D Hreach. induction Hreach as
      [C | C f fdef D E Hlookup Hbase _ IH | C D E Hsub _ IH]; intros HC.
    - exact HC.
    - apply IH. destruct HC as [-> | ->].
      + have Hnth := field_lookup_cases _ _ _ _ _ rv_collect_fields Hlookup.
        destruct f as [| f]; simpl in Hnth; [| destruct f; discriminate].
        injection Hnth as <-. simpl in Hbase. injection Hbase as <-.
        right. reflexivity.
      + have Hnth := field_lookup_cases _ _ _ _ _ rv_view_collect_fields Hlookup.
        destruct f as [| f]; simpl in Hnth; [| destruct f; discriminate].
        injection Hnth as <-. simpl in Hbase. injection Hbase as <-.
        left. reflexivity.
    - apply IH.
      assert (Hnone : forall K, K = rv_class \/ K = rv_view_class ->
        forall C', parent_lookup rv_CT C' <> Some K).
      { intros K [-> | ->] [| [| [| C']]]; cbv; try discriminate;
          destruct C'; discriminate. }
      rewrite (class_subtype_no_children _ _ _ Hsub (Hnone C HC)). exact HC. }
  intros D Hreach.
  destruct (Hclosed _ _ Hreach (or_introl eq_refl)) as [-> | ->].
  - intros f fdef Hlookup.
    destruct (rv_class_fields f fdef Hlookup) as [Habs | [Hf Hd]];
      [left; exact Habs | right; split; [split; [reflexivity | exact Hf] | exact Hd]].
  - intros f fdef Hlookup.
    destruct (rv_view_class_fields f fdef Hlookup) as [Habs | [[] _]].
    left. exact Habs.
Qed.

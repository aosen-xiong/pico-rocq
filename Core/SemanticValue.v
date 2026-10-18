From Stdlib Require Import List.
Import ListNotations.

Require Import Core.GenericCacheProtocol Core.RelyGuarantee.

(** * Semantic Value Classes and Objects

    Semantic immutability concerns one object and one cache protocol: the
    abstract value is stable and every cached value is valid.  It allows
    protocols with several valid values, and it says nothing about the
    methods of the object as a whole.

    A semantic value class asks for more.  All of its excluded state is
    derived state: the protocol has, for each field, exactly one valid value
    besides the default, computed from the abstract value.  And every method
    of the class is trace robust.  An object of such a class then behaves as
    a function of its abstract value: its method results and its derived
    state are determined by that value alone, whichever cached values the
    methods happen to read, and two objects with the same abstract value are
    indistinguishable by method results. *)

Section semantic_value.
  Context {Obj AbsVal : Type}.
  Context (P : CacheProtocol AbsVal).
  Context (Stable : StableAbs Obj AbsVal).

  (** One method of a class: its pure specification and its behavior on a
      trace of cache reads. *)
  Record ValueMethod : Type := mkValueMethod {
    vm_args : Type;
    vm_result : Type;
    vm_spec : AbsVal -> vm_args -> vm_result;
    vm_run : AbsVal -> vm_args -> CacheTrace P -> CacheRun P vm_result
  }.

  (** A semantic value class over the protocol [P]: the protocol is derived,
      and every method is trace robust. *)
  Record SemanticValueClass {Method : Type} (method : Method -> ValueMethod)
      : Type := mkSemanticValueClass {
    svc_derive : AbsVal -> forall k, cache_val P k;
    svc_derived : DerivedProtocol P svc_derive;
    svc_robust :
      forall m,
        CacheSafeMethod P (vm_spec (method m)) (vm_run (method m))
  }.

  (** A semantic value object with abstract value [a]: an object of a
      semantic value class that is semantically immutable at [a]. *)
  Definition SemanticValueObject (a : AbsVal) (s : @CacheState Obj AbsVal P) : Prop :=
    SemImmAt P Stable a s.

  (** The reads of a trace come from the object's cache histories. *)
  Definition ReadsFrom (s : @CacheState Obj AbsVal P) (tr : CacheTrace P) : Prop :=
    Forall
      (fun obs => In (obs_value obs) (cs_hist P s (cs_obj P s) (obs_field obs)))
      tr.

  Lemma value_object_reads_valid :
    forall a s tr,
      SemanticValueObject a s ->
      ReadsFrom s tr ->
      ValidTrace P a tr.
  Proof.
    intros a s tr [_ Hhist] Hreads.
    unfold ValidTrace, ReadsFrom in *.
    rewrite Forall_forall in *. intros obs Hin.
    exact (Hhist _ _ (Hreads obs Hin)).
  Qed.

  Section with_class.
    Context {Method : Type} (method : Method -> ValueMethod).
    Context (C : SemanticValueClass method).

    (** A semantic value object is semantically immutable. *)
    Theorem value_object_semantically_immutable :
      forall a s, SemanticValueObject a s -> SemImmAt P Stable a s.
    Proof. intros a s H. exact H. Qed.

    (** It stays a semantic value object under the rely. *)
    Theorem value_object_stable :
      forall a s s',
        SemanticValueObject a s ->
        CacheRely P Stable a s s' ->
        SemanticValueObject a s'.
    Proof.
      intros a s s' Hobj Hrely.
      exact (semimm_stable_under_rely P Stable a s s' Hobj Hrely).
    Qed.

    (** Method results are functions of the abstract value: whatever values
        a method reads from the object's cache histories, it returns its
        specification applied to the abstract value. *)
    Theorem value_object_result :
      forall m a s args tr,
        SemanticValueObject a s ->
        ReadsFrom s tr ->
        run_result (vm_run (method m) a args tr) = vm_spec (method m) a args.
    Proof.
      intros m a s args tr Hobj Hreads.
      eapply cache_safe_method_result; [exact (svc_robust method C m) |].
      eapply value_object_reads_valid; eassumption.
    Qed.

    (** Two objects with the same abstract value give the same results, for
        every method and every pair of read traces, however different their
        cache states are. *)
    Theorem value_objects_equal_results :
      forall m a s1 s2 args tr1 tr2,
        SemanticValueObject a s1 ->
        SemanticValueObject a s2 ->
        ReadsFrom s1 tr1 ->
        ReadsFrom s2 tr2 ->
        run_result (vm_run (method m) a args tr1) =
        run_result (vm_run (method m) a args tr2).
    Proof.
      intros m a s1 s2 args tr1 tr2 H1 H2 Hr1 Hr2.
      rewrite (value_object_result m a s1 args tr1 H1 Hr1).
      rewrite (value_object_result m a s2 args tr2 H2 Hr2).
      reflexivity.
    Qed.

    (** Derived state is a function of the abstract value: every cached
        value is the default or the derived one. *)
    Theorem value_object_derived_state :
      forall a s k v,
        SemanticValueObject a s ->
        In v (cs_hist P s (cs_obj P s) k) ->
        v = cache_default P k \/ v = svc_derive method C a k.
    Proof.
      intros a s k v Hobj Hin.
      exact (semimm_cache_value_derived P Stable (svc_derive method C) a s k v
        (svc_derived method C) Hobj Hin).
    Qed.

    (** Two objects with the same abstract value cache the same values. *)
    Theorem value_objects_equal_derived_state :
      forall a s1 s2 k v1 v2,
        SemanticValueObject a s1 ->
        SemanticValueObject a s2 ->
        In v1 (cs_hist P s1 (cs_obj P s1) k) ->
        In v2 (cs_hist P s2 (cs_obj P s2) k) ->
        v1 <> cache_default P k ->
        v2 <> cache_default P k ->
        v1 = v2.
    Proof.
      intros a s1 s2 k v1 v2 H1 H2 Hin1 Hin2 Hd1 Hd2.
      destruct (value_object_derived_state a s1 k v1 H1 Hin1) as [-> | ->];
        [contradiction |].
      destruct (value_object_derived_state a s2 k v2 H2 Hin2) as [-> | ->];
        [contradiction |].
      reflexivity.
    Qed.
  End with_class.
End semantic_value.

(** ** Semantic immutability does not imply the value property

    A protocol in which every value is valid makes every object with a
    stable abstract value semantically immutable, but it is not derived: two
    different non-default values are both valid.  So no class over it is a
    semantic value class. *)
Definition any_value_protocol : CacheProtocol unit.
Proof.
  refine {|
    cache_field := unit;
    cache_field_eq_dec := _;
    cache_val := fun _ => nat;
    cache_default := fun _ => 0;
    cache_valid := fun _ _ _ => True;
    cache_published := fun _ _ => True;
    cache_default_valid := _;
    cache_valid_published := _
  |}.
  - decide equality.
  - intros; exact I.
  - intros; exact I.
Defined.

Theorem any_value_semantically_immutable :
  forall (Obj : Type) (Stable : StableAbs Obj unit) (s : @CacheState Obj unit any_value_protocol),
    Stable (cs_obj any_value_protocol s) tt ->
    SemImmAt any_value_protocol Stable tt s.
Proof.
  intros Obj Stable s Hstable. split; [exact Hstable |].
  intros k v Hin. exact I.
Qed.

Theorem any_value_not_derived :
  forall derive, ~ DerivedProtocol any_value_protocol derive.
Proof.
  intros derive Hderived.
  destruct (Hderived tt tt 1 I) as [H1 | H1]; [discriminate |].
  destruct (Hderived tt tt 2 I) as [H2 | H2]; [discriminate |].
  simpl in *. congruence.
Qed.

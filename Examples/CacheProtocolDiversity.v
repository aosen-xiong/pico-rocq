From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Core.GenericCacheProtocol Core.CacheLRVerticalSlice.

(** * Distinct Instances of the Generic Cache Theory

    These examples exercise protocol features not present in the String-like
    hash instance: offset sentinel encodings and independently stale fields.
    They remain independent of PICO and Iris so that the reusable semantic
    obligations are visible directly. *)

(** ** Offset-Encoded Numeric Cache *)

Inductive offset_cache_field : Type :=
  | OffsetField.

Definition offset_cache_valid
    (a : nat) (_ : offset_cache_field) (v : nat) : Prop :=
  v = 0 \/ v = S a.

Definition offset_cache_protocol : CacheProtocol nat.
Proof.
  refine {|
    cache_field := offset_cache_field;
    cache_field_eq_dec := _;
    cache_val := fun _ => nat;
    cache_default := fun _ => 0;
    cache_valid := offset_cache_valid;
    cache_published := fun _ _ => True
  |}.
  - decide equality.
  - intros a []. left. reflexivity.
  - intros. exact I.
Defined.

Definition offset_obs (v : nat) : CacheObs offset_cache_protocol :=
  @Build_CacheObs nat offset_cache_protocol OffsetField v.

Definition offset_pure_result (a : nat) (_ : unit) : nat := a.

Definition offset_cache_run
    (a : nat) (_ : unit) (tr : CacheTrace offset_cache_protocol) :
    CacheRun offset_cache_protocol nat :=
  match tr with
  | [] => {| run_result := a; run_writes := [offset_obs (S a)] |}
  | first :: _ =>
      let cached := obs_value first in
      if Nat.eqb cached 0 then
        {| run_result := a; run_writes := [offset_obs (S a)] |}
      else
        {| run_result := pred cached; run_writes := [] |}
  end.

Lemma offset_cache_run_safe :
  CacheSafeMethod
    offset_cache_protocol offset_pure_result offset_cache_run.
Proof.
  intros a [] tr Htrace.
  destruct tr as [|first rest].
  - split; [reflexivity |].
    constructor.
    + unfold ValidObs, offset_obs, offset_cache_valid. simpl.
      right. reflexivity.
    + constructor.
  - inversion Htrace as [|? ? Hfirst _]; subst.
    destruct first as [[] cached].
    unfold ValidObs, offset_cache_valid in Hfirst; simpl in Hfirst.
    destruct Hfirst as [-> | ->].
    + split; [reflexivity |].
      constructor.
      * unfold ValidObs, offset_obs, offset_cache_valid. simpl.
        right. reflexivity.
      * constructor.
    + simpl.
      split; [reflexivity | constructor].
Qed.

Theorem offset_cache_refines_pure :
  CacheRefinesPure
    offset_cache_protocol offset_pure_result offset_cache_run.
Proof.
  apply cache_safe_method_refines_pure.
  exact offset_cache_run_safe.
Qed.

(** The same offset idiom is also accepted by the source-method judgment.  In
    particular, cache safety is a conclusion of [source_cache_stmt_fundamental]
    after the initializer is shown deterministic and abstract-only. *)
Definition offset_flat_protocol :
    FlatCacheProtocol nat offset_cache_field nat.
Proof.
  refine {|
    flat_valid_cache := offset_cache_valid;
    flat_default_val := fun _ => 0
  |}.
  intros a []. left. reflexivity.
Defined.

Definition offset_source_spec :
    cache_method_spec nat unit offset_cache_field nat :=
  {|
    cms_field := OffsetField;
    cms_ret_ty := CoreTInt;
    cms_is_hit := fun v => negb (Nat.eqb v 0);
    cms_decode := fun v => CoreVInt (pred v);
    cms_encode := fun result =>
      match result with
      | CoreVInt n => S n
      | _ => 0
      end;
    cms_pure := fun a _ => CoreVInt a
  |}.

Definition offset_initializer :
    CacheInitializer nat unit core_val offset_cache_field :=
  fun a _ result deps =>
    result = CoreVInt a /\ deps = [InitReadAbstract].

Definition offset_source_method :=
  source_cache_method_of_spec offset_source_spec offset_initializer.

Lemma offset_initializer_safe :
  cache_initializer_safe offset_initializer (cms_pure offset_source_spec).
Proof.
  constructor.
  - intros a [] result deps [-> _]. reflexivity.
  - intros a [] result deps [_ ->] k Hin.
    simpl in Hin. destruct Hin as [Hbad | []]. discriminate.
Qed.

Lemma offset_source_method_typed :
  source_cache_method_typing
    offset_flat_protocol offset_source_spec offset_initializer
    offset_source_method.
Proof.
  constructor.
  - reflexivity.
  - exact offset_initializer_safe.
  - intros. exact I.
  - intros. exact I.
  - intros a [] v Hvalid Hhit.
    unfold offset_source_spec in Hhit |- *. simpl in Hhit |- *.
    destruct Hvalid as [-> | ->].
    + discriminate.
    + reflexivity.
  - intros. right. reflexivity.
Qed.

Theorem offset_source_method_cache_safe :
  semantic_cache_stmt
    offset_flat_protocol offset_source_spec offset_source_method.
Proof.
  eapply source_cache_stmt_fundamental.
  exact offset_source_method_typed.
Qed.

(** ** Two Independently Stale Cache Fields *)

Inductive pair_cache_field : Type :=
  | PairLeft
  | PairRight.

Definition pair_component (a : nat * nat) (k : pair_cache_field) : nat :=
  match k with
  | PairLeft => fst a
  | PairRight => snd a
  end.

Definition pair_cache_valid
    (a : nat * nat) (k : pair_cache_field) (v : nat) : Prop :=
  v = 0 \/ v = S (pair_component a k).

Definition pair_cache_protocol : CacheProtocol (nat * nat).
Proof.
  refine {|
    cache_field := pair_cache_field;
    cache_field_eq_dec := _;
    cache_val := fun _ => nat;
    cache_default := fun _ => 0;
    cache_valid := pair_cache_valid;
    cache_published := fun _ _ => True
  |}.
  - decide equality.
  - intros a k. left. reflexivity.
  - intros. exact I.
Defined.

Definition pair_obs (k : pair_cache_field) (v : nat) :
    CacheObs pair_cache_protocol :=
  @Build_CacheObs (nat * nat) pair_cache_protocol k v.

Definition pair_pure_result (a : nat * nat) (_ : unit) : nat :=
  fst a + snd a.

Definition pair_decode
    (a : nat * nat) (k : pair_cache_field) (v : nat) : nat :=
  if Nat.eqb v 0 then pair_component a k else pred v.

Lemma pair_decode_valid : forall a k v
    (Hvalid : pair_cache_valid a k v),
    pair_decode a k v = pair_component a k.
Proof.
  intros a k v [-> | ->].
  - reflexivity.
  - unfold pair_decode. simpl. reflexivity.
Qed.

(** The robust method may observe both fields, but it decodes each observation
    against that field's protocol.  If the trace does not have the expected
    left-then-right shape, it falls back to pure recomputation. *)
Definition pair_cache_run
    (a : nat * nat) (_ : unit) (tr : CacheTrace pair_cache_protocol) :
    CacheRun pair_cache_protocol nat :=
  match tr with
  | first :: second :: _ =>
      match obs_field first, obs_field second with
      | PairLeft, PairRight =>
          {| run_result :=
               pair_decode a PairLeft (obs_value first) +
               pair_decode a PairRight (obs_value second);
             run_writes := [] |}
      | _, _ => {| run_result := fst a + snd a; run_writes := [] |}
      end
  | _ => {| run_result := fst a + snd a; run_writes := [] |}
  end.

Lemma pair_cache_run_safe :
  CacheSafeMethod pair_cache_protocol pair_pure_result pair_cache_run.
Proof.
  intros a [] tr Htrace.
  destruct tr as [|first [|second rest]]; try (split; [reflexivity | constructor]).
  inversion Htrace as [|? ? Hfirst Htail]; subst.
  inversion Htail as [|? ? Hsecond _]; subst.
  destruct first as [k1 v1], second as [k2 v2].
  destruct k1, k2; simpl in *; try (split; [reflexivity | constructor]).
  split; [|constructor].
  rewrite (pair_decode_valid a PairLeft v1 Hfirst).
  rewrite (pair_decode_valid a PairRight v2 Hsecond).
  reflexivity.
Qed.

Theorem pair_cache_refines_pure :
  CacheRefinesPure pair_cache_protocol pair_pure_result pair_cache_run.
Proof.
  apply cache_safe_method_refines_pure.
  exact pair_cache_run_safe.
Qed.

(** A snapshot-dependent implementation treats a hit in the left field as
    evidence that the right field is also initialized, then returns the raw
    right observation.  Independent histories permit a left-hit/right-miss
    trace, so this implementation is not cache safe. *)
Definition bad_pair_cache_run
    (a : nat * nat) (_ : unit) (tr : CacheTrace pair_cache_protocol) :
    CacheRun pair_cache_protocol nat :=
  match tr with
  | first :: second :: _ =>
      match obs_field first, obs_field second with
      | PairLeft, PairRight =>
          if Nat.eqb (obs_value first) 0 then
            {| run_result := fst a + snd a; run_writes := [] |}
          else
            {| run_result := obs_value second; run_writes := [] |}
      | _, _ => {| run_result := fst a + snd a; run_writes := [] |}
      end
  | _ => {| run_result := fst a + snd a; run_writes := [] |}
  end.

Definition bad_pair_trace (a : nat * nat) : CacheTrace pair_cache_protocol :=
  [pair_obs PairLeft (S (fst a)); pair_obs PairRight 0].

Lemma bad_pair_trace_valid : forall a,
  ValidTrace pair_cache_protocol a (bad_pair_trace a).
Proof.
  intros [left right].
  constructor.
  - unfold ValidObs, pair_obs, pair_cache_valid, pair_component. simpl.
    right. reflexivity.
  - constructor.
    + unfold ValidObs, pair_obs, pair_cache_valid. simpl.
      left. reflexivity.
    + constructor.
Qed.

Lemma bad_pair_trace_wrong : forall left right,
  left + right <> 0 ->
  run_result
    (bad_pair_cache_run (left, right) tt (bad_pair_trace (left, right))) <>
  pair_pure_result (left, right) tt.
Proof.
  intros left right Hnonzero.
  unfold bad_pair_cache_run, bad_pair_trace, pair_obs, pair_pure_result.
  simpl. lia.
Qed.

Theorem bad_pair_cache_not_safe : forall left right,
  left + right <> 0 ->
  ~ CacheSafeMethod
      pair_cache_protocol pair_pure_result bad_pair_cache_run.
Proof.
  intros left right Hnonzero Hsafe.
  destruct (Hsafe (left, right) tt (bad_pair_trace (left, right))
    (bad_pair_trace_valid (left, right))) as [Hresult _].
  exact (bad_pair_trace_wrong left right Hnonzero Hresult).
Qed.

(** ** Safely Published Reference-Valued Cache

    Atomicity of a reference read only identifies one whole reference.  The
    protocol below additionally records that the referenced object is safely
    published and represents the derived abstract value.  Unlike the numeric
    examples above, [cache_published] is therefore not [True]. *)

Inductive published_cache_value : Type :=
  | PublishedUnset
  | PublishedRef (location contents : nat).

Inductive published_cache_field : Type :=
  | PublishedField.

Section published_reference_cache.
  Context (derive : nat -> nat).
  Context (safely_published : nat -> nat -> Prop).

  Definition published_cache_published
      (_ : published_cache_field) (v : published_cache_value) : Prop :=
    match v with
    | PublishedUnset => True
    | PublishedRef location contents => safely_published location contents
    end.

  Definition published_cache_valid
      (a : nat) (_ : published_cache_field)
      (v : published_cache_value) : Prop :=
    v = PublishedUnset \/
    exists location,
      v = PublishedRef location (derive a) /\
      safely_published location (derive a).

  Definition published_cache_protocol : CacheProtocol nat.
  Proof.
    refine {|
      cache_field := published_cache_field;
      cache_field_eq_dec := _;
      cache_val := fun _ => published_cache_value;
      cache_default := fun _ => PublishedUnset;
      cache_valid := published_cache_valid;
      cache_published := published_cache_published
    |}.
    - decide equality.
    - intros a []. left. reflexivity.
    - intros a [] v Hvalid.
      destruct Hvalid as [-> | [location [-> Hpublished]]].
      + exact I.
      + exact Hpublished.
  Defined.

  Definition published_obs (v : published_cache_value) :
      CacheObs published_cache_protocol :=
    @Build_CacheObs nat published_cache_protocol PublishedField v.

  Definition published_pure_result (a : nat) (_ : unit) : nat := derive a.

  Definition published_cache_run
      (fresh_location : nat) (a : nat) (_ : unit)
      (tr : CacheTrace published_cache_protocol) :
      CacheRun published_cache_protocol nat :=
    match tr with
    | [] =>
        {| run_result := derive a;
           run_writes :=
             [published_obs (PublishedRef fresh_location (derive a))] |}
    | first :: _ =>
        match obs_value first with
        | PublishedUnset =>
            {| run_result := derive a;
               run_writes :=
                 [published_obs (PublishedRef fresh_location (derive a))] |}
        | PublishedRef _ contents =>
            {| run_result := contents; run_writes := [] |}
        end
    end.

  Theorem published_reference_cache_safe : forall fresh_location
      (Hfresh_published :
        forall a, safely_published fresh_location (derive a)),
    CacheSafeMethod
      published_cache_protocol published_pure_result
      (published_cache_run fresh_location).
  Proof.
    intros fresh_location Hfresh_published a [] tr Htrace.
    destruct tr as [|first rest].
    - split; [reflexivity |].
      constructor.
      + unfold ValidObs, published_obs, published_cache_valid. simpl.
        right. exists fresh_location. split; [reflexivity |].
        apply Hfresh_published.
      + constructor.
    - inversion Htrace as [|? ? Hfirst _]; subst.
      destruct first as [[] observed].
      unfold ValidObs, published_cache_valid in Hfirst; simpl in Hfirst.
      destruct Hfirst as [-> | [location [-> Hpublished]]].
      + split; [reflexivity |].
        constructor.
        * unfold ValidObs, published_obs, published_cache_valid. simpl.
          right. exists fresh_location. split; [reflexivity |].
          apply Hfresh_published.
        * constructor.
      + split; [reflexivity | constructor].
  Qed.

  Theorem published_reference_cache_refines_pure : forall fresh_location
      (Hfresh_published :
        forall a, safely_published fresh_location (derive a)),
    CacheRefinesPure
      published_cache_protocol published_pure_result
      (published_cache_run fresh_location).
  Proof.
    intros fresh_location Hfresh_published.
    apply cache_safe_method_refines_pure.
    apply published_reference_cache_safe.
    exact Hfresh_published.
  Qed.
End published_reference_cache.

From Stdlib Require Import List PeanoNat.
Import ListNotations.

Require Import Syntax Typing Bigstep DerivedCache PICOBridge.PicoMemoryModel Core.GenericCacheProtocol.

(** * Generic Derived-Cache Instances

    This file instantiates [GenericCacheProtocol] for the current PICO value
    language.  It has four roles:

    - package the existing [unknown-or-derived] integer-cache discipline as a
      [CacheProtocol];
    - connect the PICO weak-memory field histories to the generic history
      predicates;
    - encode the motivating bad-hash and good-local-copy trace examples; and
    - show how PICO final-field facts provide the generic [StableAbs] premise. *)

(** ** The Existing Derived-Integer Cache Protocol *)

(** The current derived-cache examples have one abstract cache field. *)
Inductive derived_cache_field_id : Type :=
  | DerivedCacheField.

(** A derived integer cache value is valid when it is still unknown/default, or
    when it is the nonzero value computed from the stable abstract fields. *)
Definition derived_cache_valid
    (derived : list value -> nat) (abs_vals : list value)
    (_ : derived_cache_field_id) (v : value) : Prop :=
  cache_value_unknown v \/ cache_value_known derived abs_vals v.

(** The existing [unknown-or-derived] discipline as a generic [CacheProtocol]. *)
Definition derived_cache_protocol
    (derived : list value -> nat) : CacheProtocol (list value).
Proof.
  refine {|
    cache_field := derived_cache_field_id;
    cache_val := fun _ => value;
    cache_default := fun _ => Int 0;
    cache_valid := derived_cache_valid derived;
    cache_default_valid := _
  |}.
  intros abs_vals [].
  left.
  reflexivity.
Defined.

(** Bridge from the protocol predicate back to the old specialized predicate. *)
Lemma derived_cache_valid_unknown_or_derived :
  forall derived abs_vals v
    (Hvalid : cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v),
    cache_value_unknown v \/ cache_value_known derived abs_vals v.
Proof.
  intros derived abs_vals v Hvalid.
  cbn in Hvalid.
  exact Hvalid.
Qed.

(** Bridge from the old specialized predicate into the generic protocol. *)
Lemma unknown_or_derived_cache_valid :
  forall derived abs_vals v
    (Hvalid : cache_value_unknown v \/ cache_value_known derived abs_vals v),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros derived abs_vals v Hvalid.
  cbn.
  exact Hvalid.
Qed.

Lemma derived_cache_msg_ok_cache_valid :
  forall derived abs_vals v
    (Hvalid : derived_cache_msg_ok derived abs_vals v),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros derived abs_vals v Hvalid.
  apply unknown_or_derived_cache_valid.
  unfold derived_cache_msg_ok, derived_int_cache_value in Hvalid.
  exact Hvalid.
Qed.

Lemma cache_valid_derived_cache_msg_ok :
  forall derived abs_vals v
    (Hvalid : cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros derived abs_vals v Hvalid.
  unfold derived_cache_msg_ok, derived_int_cache_value.
  apply derived_cache_valid_unknown_or_derived.
  exact Hvalid.
Qed.

Definition derived_cache_obs
    (derived : list value -> nat) (v : value) :
    CacheObs (derived_cache_protocol derived) :=
  @Build_CacheObs
    (list value)
    (derived_cache_protocol derived)
    DerivedCacheField
    v.

(** ** Weak-Memory Histories as Generic Cache Histories *)

(** The generic history for a PICO weak-memory state reads the concrete
    field-address history at [addr] and forgets message metadata. *)
Definition wm_derived_cache_history
    (derived : list value -> nat) (addr : FieldAddr) :
    CacheHistory (derived_cache_protocol derived) :=
  fun sigma _ => values_written_to sigma addr.

(** Generic read predicate for the target cache field.  The only memory-model
    assumption used later is [wm_read_from_history], supplied by the
    [CacheMemoryModel] interface. *)
Definition wm_derived_cache_read
    `{CacheMemoryModel} (derived : list value -> nat) (addr : FieldAddr)
    (sigma : wm_state)
    (_ : cache_field (derived_cache_protocol derived)) (v : value) : Prop :=
  exists V V', wm_read sigma V addr v V'.

(** Any weak-memory read of the target cache field observes a value in that
    field's concrete write history.  This is the whole-value read side
    condition used by the generic theorem. *)
Lemma wm_derived_cache_read_from_history :
  forall `{CacheMemoryModel} derived addr sigma
    (k : cache_field (derived_cache_protocol derived)) v
    (Hread : wm_derived_cache_read derived addr sigma k v),
    In v (wm_derived_cache_history derived addr sigma k).
Proof.
  intros Hmem derived addr sigma [] v [V [V' Hread]].
  unfold wm_derived_cache_history, values_written_to.
  destruct (wm_read_from_history sigma V addr v V' Hread) as
    [msg [Hin Hval]].
  rewrite <- Hval.
  apply in_map.
  exact Hin.
Qed.

(** Convert the concrete PICO cache-history invariant into the generic
    [CacheHistOK] predicate. *)
Lemma wm_cache_history_state_generic :
  forall sigma addr derived abs_vals
    (Hstate : wm_cache_history_state sigma addr derived abs_vals),
    CacheHistOK
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      sigma
      abs_vals.
Proof.
  intros sigma addr derived abs_vals Hstate [] v Hin.
  unfold wm_cache_history_state, derived_cache_history_ok,
    history_values_ok in Hstate.
  apply in_map_iff in Hin.
  destruct Hin as [msg [Hmsg Hin]].
  subst v.
  pose proof
    (proj1 (Forall_forall
      (fun msg0 => derived_cache_msg_ok derived abs_vals (msg_val msg0))
      (history_of sigma addr)) Hstate msg Hin) as Hvalid.
  apply derived_cache_msg_ok_cache_valid.
  exact Hvalid.
Qed.

(** Convert the generic [CacheHistOK] predicate back to the concrete PICO
    cache-history invariant. *)
Lemma generic_cache_hist_ok_wm_cache_history_state :
  forall sigma addr derived abs_vals
    (Hhist : CacheHistOK
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      sigma
      abs_vals),
    wm_cache_history_state sigma addr derived abs_vals.
Proof.
  intros sigma addr derived abs_vals Hhist.
  unfold wm_cache_history_state, derived_cache_history_ok,
    history_values_ok.
  apply Forall_forall.
  intros msg Hin.
  apply cache_valid_derived_cache_msg_ok.
  apply Hhist with (k := DerivedCacheField).
  unfold wm_derived_cache_history, values_written_to.
  apply in_map.
  exact Hin.
Qed.

(** Reads are valid by composing the PICO read-from-history interface with the
    generic [cache_read_valid] theorem. *)
Lemma wm_read_valid_via_generic_cache_hist_ok :
  forall `{CacheMemoryModel} sigma V addr v V' derived abs_vals
    (Hhist : CacheHistOK
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      sigma
      abs_vals)
    (Hread : wm_read sigma V addr v V'),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros Hmem sigma V addr v V' derived abs_vals Hhist Hread.
  eapply (@cache_read_valid
    wm_state
    (list value)
    (derived_cache_protocol derived)
    (wm_derived_cache_history derived addr)
    (wm_derived_cache_read derived addr)
    (wm_derived_cache_read_from_history derived addr)
    sigma
    abs_vals
    DerivedCacheField
    v).
  - exact Hhist.
  - exists V, V'.
    exact Hread.
Qed.

Lemma wm_cache_history_state_valid_extension_generic :
  forall sigma sigma' addr derived abs_vals
    (Hstate' : wm_cache_history_state sigma' addr derived abs_vals),
    CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      sigma
      sigma'
      abs_vals.
Proof.
  intros sigma sigma' addr derived abs_vals Hstate' [] v Hin.
  right.
  pose proof
    (wm_cache_history_state_generic sigma' addr derived abs_vals Hstate')
    as Hhist.
  eapply Hhist.
  exact Hin.
Qed.

Lemma wm_write_allowed_read_valid_generic :
  forall `{CacheMemoryModel}
         sigma sigma' Vw Vw' Vr addr write_addr val_y v Vr'
         derived abs_vals
         (Hstate : wm_cache_history_state sigma addr derived abs_vals)
         (Hwrite : wm_write sigma sigma' Vw Vw' write_addr val_y)
         (Hallowed :
           wm_write_allowed_for_cache write_addr addr val_y derived abs_vals)
         (Hread : wm_read sigma' Vr addr v Vr'),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros Hmem sigma sigma' Vw Vw' Vr addr write_addr val_y v Vr'
         derived abs_vals Hstate Hwrite Hallowed Hread.
  assert (Hstate' :
    wm_cache_history_state sigma' addr derived abs_vals).
  {
    eapply wm_write_allowed_preserves_cache_history; eauto.
  }
  eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  apply wm_cache_history_state_generic.
  exact Hstate'.
Qed.

(** These extension theorems lift the existing weak-memory preservation results
    into the generic protocol language: after any execution whose writes are
    allowed for the cache, the final cache history is a valid extension of the
    initial one. *)
Theorem wm_steps_valid_extension_from_allowed_writes_generic :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hallowed_all : forall c1 c2,
      wm_step CT c1 c2 ->
      wm_transition_writes_allowed_for_cache
        (wc_state c1) (wc_state c2) addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      (wc_state cfg')
      abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals
         Hsteps Hallowed_all Hstate.
  eapply wm_cache_history_state_valid_extension_generic.
  eapply wm_steps_preserve_cache_history_from_allowed_writes; eauto.
Qed.

Theorem wm_steps_valid_extension_from_thread_allowed_generic :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_threads : forall c1 c2,
      wm_step CT c1 c2 ->
      forall i t,
        nth_error (wc_threads c1) i = Some t ->
        wm_thread_writes_allowed_for_cache t addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      (wc_state cfg')
      abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals
         Hsteps Hall_threads Hstate.
  eapply wm_cache_history_state_valid_extension_generic.
  eapply wm_steps_preserve_cache_history_from_thread_allowed; eauto.
Qed.

Theorem wm_steps_valid_extension_from_config_allowed_generic :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_configs : forall c1 c2,
      wm_step CT c1 c2 ->
      wm_config_threads_allowed_for_cache c1 addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      (wc_state cfg')
      abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals
         Hsteps Hall_configs Hstate.
  eapply wm_cache_history_state_valid_extension_generic.
  eapply wm_steps_preserve_cache_history_from_config_allowed; eauto.
  apply wm_steps_allowed_configs_from_global.
  exact Hall_configs.
Qed.

Theorem wm_steps_valid_extension_from_closed_config_safe_generic :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hsafe_cfg : cache_safe_config cfg addr derived abs_vals)
    (Hclosed : forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals ->
      cache_safe_config c2 addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      (wc_state cfg')
      abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals
         Hsteps Hsafe_cfg Hclosed Hstate.
  eapply wm_cache_history_state_valid_extension_generic.
  eapply wm_steps_preserve_cache_history_from_closed_config_safe; eauto.
Qed.

(** These read-validity theorems are the operational form of the main field-
    history lemma: after a cache-safe weak-memory execution, any later read of
    the target cache field observes a protocol-valid value. *)
Theorem wm_steps_read_valid_from_allowed_writes_generic :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hallowed_all : forall c1 c2,
      wm_step CT c1 c2 ->
      wm_transition_writes_allowed_for_cache
        (wc_state c1) (wc_state c2) addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hallowed_all Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_allowed_writes; eauto.
  }
  eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  apply wm_cache_history_state_generic.
  exact Hstate'.
Qed.

Theorem wm_steps_read_valid_from_thread_allowed_generic :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_threads : forall c1 c2,
      wm_step CT c1 c2 ->
      forall i t,
        nth_error (wc_threads c1) i = Some t ->
        wm_thread_writes_allowed_for_cache t addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hall_threads Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_thread_allowed; eauto.
  }
  eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  apply wm_cache_history_state_generic.
  exact Hstate'.
Qed.

Theorem wm_steps_read_valid_from_config_allowed_generic :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_configs : forall c1 c2,
      wm_step CT c1 c2 ->
      wm_config_threads_allowed_for_cache c1 addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hall_configs Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_config_allowed; eauto.
    apply wm_steps_allowed_configs_from_global.
    exact Hall_configs.
  }
  eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  apply wm_cache_history_state_generic.
  exact Hstate'.
Qed.

Theorem wm_steps_read_valid_from_closed_config_safe_generic :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hsafe_cfg : cache_safe_config cfg addr derived abs_vals)
    (Hclosed : forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals ->
      cache_safe_config c2 addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    cache_valid
      (derived_cache_protocol derived)
      abs_vals
      DerivedCacheField
      v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hsafe_cfg Hclosed Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_closed_config_safe; eauto.
  }
  eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  apply wm_cache_history_state_generic.
  exact Hstate'.
Qed.

(** ** Hash-Cache Trace Examples *)

(** A one-field protocol for a hash cache.  Valid values are the default
    [Int 0] or the nonzero hash [Int a]. *)
Inductive hash_cache_field : Type :=
  | HashField.

Definition hash_cache_valid (a : nat) (_ : hash_cache_field) (v : value) : Prop :=
  v = Int 0 \/ (v = Int a /\ a <> 0).

Definition hash_cache_protocol : CacheProtocol nat.
Proof.
  refine {|
    cache_field := hash_cache_field;
    cache_val := fun _ => value;
    cache_default := fun _ => Int 0;
    cache_valid := hash_cache_valid;
    cache_default_valid := _
  |}.
  intros a [].
  left.
  reflexivity.
Defined.

Definition hash_obs (v : value) : CacheObs hash_cache_protocol :=
  @Build_CacheObs nat hash_cache_protocol HashField v.

(** The bad trace reads the computed hash and then rereads the default value.
    This trace is protocol-valid, so methods must be correct even for it. *)
Definition bad_hash_trace (H : nat) : CacheTrace hash_cache_protocol :=
  [hash_obs (Int H); hash_obs (Int 0)].

Definition cache_value_eq_zero (v : value) : bool :=
  match v with
  | Int 0 => true
  | _ => false
  end.

Definition hash_obs_value (obs : CacheObs hash_cache_protocol) : value :=
  obs_value obs.

Definition bad_hash_run
    (a : nat) (_ : unit) (tr : CacheTrace hash_cache_protocol) :
    CacheRun hash_cache_protocol value :=
  let r :=
    match tr with
    | [] => Int 0
    | first :: rest =>
        if cache_value_eq_zero (hash_obs_value first) then
          Int a
        else
          match rest with
          | [] => hash_obs_value first
          | second :: _ => hash_obs_value second
          end
    end in
  {| run_result := r; run_writes := [] |}.

Definition good_hash_run
    (a : nat) (_ : unit) (tr : CacheTrace hash_cache_protocol) :
    CacheRun hash_cache_protocol value :=
  match tr with
  | [] => {| run_result := Int a; run_writes := [] |}
  | first :: _ =>
      let h := hash_obs_value first in
      if cache_value_eq_zero h then
        {| run_result := Int a; run_writes := [hash_obs (Int a)] |}
      else
        {| run_result := h; run_writes := [] |}
  end.

Definition hash_pure_result (a : nat) (_ : unit) : value := Int a.

(** The bad trace is admissible by the protocol when [H] is nonzero. *)
Lemma bad_hash_trace_valid :
  forall H
    (Hnz : H <> 0),
    ValidTrace hash_cache_protocol H (bad_hash_trace H).
Proof.
  intros H Hnz.
  unfold bad_hash_trace, ValidTrace.
  constructor.
  - unfold ValidObs, hash_obs, hash_cache_valid; simpl.
    right.
    split; [reflexivity | assumption].
  - constructor.
    + unfold ValidObs, hash_obs, hash_cache_valid; simpl.
      left.
      reflexivity.
    + constructor.
Qed.

(** A method that reads the racy cache twice can return the second value and
    therefore fail to refine pure hash recomputation. *)
Lemma bad_hash_trace_returns_wrong :
  forall H
    (Hnz : H <> 0),
    run_result (bad_hash_run H tt (bad_hash_trace H)) <> Int H.
Proof.
  intros [|H] Hnz.
  - contradiction Hnz.
    reflexivity.
  - unfold bad_hash_trace, bad_hash_run, hash_obs_value,
      cache_value_eq_zero, hash_obs.
    simpl.
    discriminate.
Qed.

(** The previous two facts show that the double-read method is not
    [CacheSafeMethod]. *)
Lemma bad_hash_not_cache_safe :
  forall H
    (Hnz : H <> 0),
    ~ CacheSafeMethod
        hash_cache_protocol
        hash_pure_result
        bad_hash_run.
Proof.
  intros H Hnz Hsafe.
  destruct (Hsafe H tt (bad_hash_trace H)
    (bad_hash_trace_valid H Hnz)) as [Hresult _].
  apply (bad_hash_trace_returns_wrong H Hnz).
  exact Hresult.
Qed.

Lemma hash_valid_value_shape :
  forall H v
    (Hvalid : hash_cache_valid H HashField v),
    v = Int 0 \/ (v = Int H /\ H <> 0).
Proof.
  intros H v Hvalid.
  exact Hvalid.
Qed.

Lemma good_hash_run_result :
  forall H tr
    (Hnz : H <> 0)
    (Htrace : ValidTrace hash_cache_protocol H tr),
    run_result (good_hash_run H tt tr) = Int H.
Proof.
  intros H tr Hnz Htrace.
  destruct tr as [|first rest].
  - reflexivity.
  - inversion Htrace as [|? ? Hfirst _]; subst.
    unfold good_hash_run.
    destruct first as [[] v].
    simpl in *.
    destruct Hfirst as [Hzero | [Hknown _]].
    + subst v.
      reflexivity.
    + subst v.
      unfold cache_value_eq_zero.
      destruct H.
      * contradiction.
      * reflexivity.
Qed.

Lemma good_hash_writes_valid :
  forall H tr
    (Hnz : H <> 0)
    (Htrace : ValidTrace hash_cache_protocol H tr),
    ValidTrace hash_cache_protocol H (run_writes (good_hash_run H tt tr)).
Proof.
  intros H tr Hnz Htrace.
  destruct tr as [|first rest].
  - constructor.
  - inversion Htrace as [|? ? Hfirst _]; subst.
    unfold good_hash_run.
    destruct first as [[] v].
    simpl in *.
    destruct Hfirst as [Hzero | [Hknown _]].
    + subst v.
      constructor.
      * unfold ValidObs, hash_obs, hash_cache_valid; simpl.
        right.
        split; [reflexivity | assumption].
      * constructor.
    + subst v.
      unfold cache_value_eq_zero.
      destruct H.
      * contradiction.
      * constructor.
Qed.

(** The local-copy method is the accepted proof shape: read the racy cache at
    most once, branch on that local value, and write only protocol-valid cache
    values. *)
Lemma good_hash_cache_safe_method :
  CacheSafeMethod
    hash_cache_protocol
    hash_pure_result
    good_hash_run.
Proof.
  intros H [] tr Htrace.
  destruct (Nat.eq_dec H 0) as [Hzero | Hnz].
  - subst H.
    destruct tr as [|first rest].
    + split; [reflexivity | constructor].
    + inversion Htrace as [|? ? Hfirst _]; subst.
      unfold good_hash_run, hash_pure_result.
      destruct first as [[] v].
      simpl in Hfirst.
      destruct Hfirst as [Hzero_v | [_ Hfalse]].
      * subst v.
        split; [reflexivity |].
        constructor.
        -- unfold ValidObs, hash_obs, hash_cache_valid; simpl.
           left.
           reflexivity.
        -- constructor.
      * contradiction.
  - split.
    + apply good_hash_run_result; assumption.
    + apply good_hash_writes_valid; assumption.
Qed.

(** The local-copy hash method refines pure recomputation for every valid
    cache-read trace. *)
Theorem good_hash_refines_pure_recompute :
  CacheRefinesPure
    hash_cache_protocol
    hash_pure_result
    good_hash_run.
Proof.
  apply cache_safe_method_refines_pure.
  exact good_hash_cache_safe_method.
Qed.

Theorem good_hash_refines_pure_recompute_run :
  forall H tr r
    (Htrace : ValidTrace hash_cache_protocol H tr)
    (Hexec : weak_exec_matches_trace hash_cache_protocol good_hash_run H tt tr r),
    PureRecomputeResult hash_pure_result H tt r.
Proof.
  intros H tr r Htrace Hexec.
  eapply good_hash_refines_pure_recompute; eauto.
Qed.

(** ** PICO as a Provider of Stable Abstractions *)

(** PICO objects provide [StableAbs] through final-field facts and stable reads
    of the abstract fields. *)
Definition pico_object : Type := (heap * Loc)%type.
Definition pico_abs_value : Type := list value.

Definition pico_stable_abs
    (CT : class_table) (C : class_name) (abs_fields : list var)
    (o : pico_object) (abs_vals : pico_abs_value) : Prop :=
  final_fields CT C abs_fields /\
  field_reads (fst o) (snd o) abs_fields abs_vals.

Lemma pico_stable_abs_intro :
  forall CT C abs_fields h loc abs_vals
    (Hfinals : final_fields CT C abs_fields)
    (Hreads : field_reads h loc abs_fields abs_vals),
    pico_stable_abs CT C abs_fields (h, loc) abs_vals.
Proof.
  intros CT C abs_fields h loc abs_vals Hfinals Hreads.
  split; assumption.
Qed.

Definition wm_field_history_contains
    (sigma : wm_state) (addr : FieldAddr) (v : value) : Prop :=
  In v (values_written_to sigma addr).

Definition wm_field_history_stable_value
    (sigma : wm_state) (addr : FieldAddr) (v : value) : Prop :=
  wm_field_history_contains sigma addr v /\
  Forall (fun msg => msg_val msg = v) (history_of sigma addr).

Definition wm_field_histories_read
    (sigma : wm_state) (loc : Loc) (fs : list var) (vs : list value) : Prop :=
  Forall2 (fun f v => wm_field_history_stable_value sigma (loc, f) v) fs vs.

Definition pico_wm_stable_abs
    (CT : class_table) (C : class_name) (loc : Loc) (abs_fields : list var) :
    StableAbs wm_state (list value) :=
  fun sigma abs_vals =>
    final_fields CT C abs_fields /\
    wm_field_histories_read sigma loc abs_fields abs_vals.

Lemma wm_field_history_contains_history_eq :
  forall sigma sigma' addr v
    (Hhist : history_of sigma' addr = history_of sigma addr)
    (Hcontains : wm_field_history_contains sigma addr v),
    wm_field_history_contains sigma' addr v.
Proof.
  intros sigma sigma' addr v Hhist Hcontains.
  unfold wm_field_history_contains, values_written_to in *.
  rewrite Hhist.
  exact Hcontains.
Qed.

Lemma wm_field_history_stable_value_history_eq :
  forall sigma sigma' addr v
    (Hhist : history_of sigma' addr = history_of sigma addr)
    (Hstable : wm_field_history_stable_value sigma addr v),
    wm_field_history_stable_value sigma' addr v.
Proof.
  intros sigma sigma' addr v Hhist Hstable.
  unfold wm_field_history_stable_value, wm_field_history_contains,
    values_written_to in *.
  rewrite Hhist.
  exact Hstable.
Qed.

Definition wm_histories_preserve_fields
    (sigma sigma' : wm_state) (loc : Loc) (fs : list var) : Prop :=
  forall f, In f fs -> history_of sigma' (loc, f) = history_of sigma (loc, f).

Definition wm_write_avoids_fields
    (write_addr : FieldAddr) (loc : Loc) (fs : list var) : Prop :=
  forall f, In f fs -> write_addr <> (loc, f).

Definition wm_histories_only_extend_field
    (sigma sigma' : wm_state) (target : FieldAddr) : Prop :=
  forall addr, addr <> target -> history_of sigma' addr = history_of sigma addr.

Lemma wm_histories_only_extend_field_refl :
  forall sigma target,
    wm_histories_only_extend_field sigma sigma target.
Proof.
  intros sigma target addr _.
  reflexivity.
Qed.

Lemma wm_write_histories_only_extend_field :
  forall sigma sigma' V V' target v
    (Hwrite : wm_write sigma sigma' V V' target v),
    wm_histories_only_extend_field sigma sigma' target.
Proof.
  intros sigma sigma' V V' target v Hwrite addr Hneq.
  eapply wm_write_history_other; eauto.
Qed.

Lemma wm_histories_only_extend_field_preserves_fields :
  forall sigma sigma' target loc fs
    (Honly : wm_histories_only_extend_field sigma sigma' target)
    (Havoid : wm_write_avoids_fields target loc fs),
    wm_histories_preserve_fields sigma sigma' loc fs.
Proof.
  intros sigma sigma' target loc fs Honly Havoid f Hin.
  apply Honly.
  intro Heq.
  apply (Havoid f Hin).
  symmetry.
  exact Heq.
Qed.

Definition wm_transition_writes_only_to_field
    (sigma sigma' : wm_state) (target : FieldAddr) : Prop :=
  forall V V' write_addr val,
    wm_write sigma sigma' V V' write_addr val ->
    write_addr = target.

Lemma wm_thread_step_histories_only_extend_field_from_target_writes :
  forall `{CacheMemoryModel} CT sigma sigma' t t' target
    (Hstep : wm_thread_step CT sigma t sigma' t')
    (Honly : wm_transition_writes_only_to_field sigma sigma' target),
    wm_histories_only_extend_field sigma sigma' target.
Proof.
  intros Hmem CT sigma sigma' t t' target Hstep Honly.
  induction Hstep.
  - apply wm_histories_only_extend_field_refl.
  - apply wm_histories_only_extend_field_refl.
  - match goal with
    | Hwrite : wm_write _ _ ?V ?V' ?write_addr ?val |- _ =>
        pose proof (Honly V V' write_addr val Hwrite) as Htarget;
        subst target;
        eapply wm_write_histories_only_extend_field; eauto
    end.
  - apply wm_histories_only_extend_field_refl.
  - apply IHHstep.
    exact Honly.
Qed.

Lemma wm_thread_step_fldwrite_histories_only_extend_field :
  forall `{CacheMemoryModel} CT sigma sigma' rΓ V x f y t' loc_x
    (Hstep : wm_thread_step CT sigma
      (mkWMThread rΓ (SFldWrite x f y) V)
      sigma'
      t')
    (Hx : Helpers.runtime_getVal rΓ x = Some (Iot loc_x)),
    wm_histories_only_extend_field sigma sigma' (loc_x, f).
Proof.
  intros Hmem CT sigma sigma' rΓ V x f y t' loc_x Hstep Hx.
  inversion Hstep; subst.
  match goal with
  | Hrx : Helpers.runtime_getVal rΓ x = Some (Iot ?loc0) |- _ =>
      assert (loc0 = loc_x) by congruence;
      subst loc0
  end.
  match goal with
  | Hwrite : wm_write _ _ _ _ (loc_x, f) _ |- _ =>
      eapply wm_write_histories_only_extend_field; eauto
  end.
Qed.

Lemma wm_step_selected_fldwrite_histories_only_extend_field :
  forall `{CacheMemoryModel} CT sigma sigma' threads threads'
         rΓ V x f y t' i loc_x
    (Hnth : nth_error threads i = Some (mkWMThread rΓ (SFldWrite x f y) V))
    (Hthread : wm_thread_step CT sigma
      (mkWMThread rΓ (SFldWrite x f y) V)
      sigma'
      t')
    (Hthreads : threads' = Helpers.update i t' threads)
    (Hx : Helpers.runtime_getVal rΓ x = Some (Iot loc_x)),
    wm_histories_only_extend_field
      (wc_state (mkWMConfig sigma threads))
      (wc_state (mkWMConfig sigma' threads'))
      (loc_x, f).
Proof.
  intros Hmem CT sigma sigma' threads threads' rΓ V x f y t' i loc_x
    _ Hthread Hthreads Hx.
  simpl.
  eapply wm_thread_step_fldwrite_histories_only_extend_field; eauto.
Qed.

Lemma wm_field_histories_read_preserved :
  forall sigma sigma' loc fs vs
    (Hpres : wm_histories_preserve_fields sigma sigma' loc fs)
    (Hreads : wm_field_histories_read sigma loc fs vs),
    wm_field_histories_read sigma' loc fs vs.
Proof.
  intros sigma sigma' loc fs.
  induction fs as [|f fs IH]; intros vs Hpres Hreads.
  - inversion Hreads; constructor.
  - inversion Hreads as [|? ? v vs' Hhead Htail]; subst.
    constructor.
    + eapply wm_field_history_stable_value_history_eq.
      * apply Hpres.
        simpl.
        left.
        reflexivity.
      * exact Hhead.
    + eapply IH.
      * intros f0 Hin.
        apply Hpres.
        simpl.
        right.
        exact Hin.
      * exact Htail.
Qed.

Lemma pico_wm_stable_abs_intro :
  forall CT C loc abs_fields sigma abs_vals
    (Hfinals : final_fields CT C abs_fields)
    (Hreads : wm_field_histories_read sigma loc abs_fields abs_vals),
    pico_wm_stable_abs CT C loc abs_fields sigma abs_vals.
Proof.
  intros CT C loc abs_fields sigma abs_vals Hfinals Hreads.
  split; assumption.
Qed.

Lemma pico_wm_stable_abs_preserved_by_histories :
  forall CT C loc abs_fields sigma sigma' abs_vals
    (Hpres : wm_histories_preserve_fields sigma sigma' loc abs_fields)
    (Hstable : pico_wm_stable_abs CT C loc abs_fields sigma abs_vals),
    pico_wm_stable_abs CT C loc abs_fields sigma' abs_vals.
Proof.
  intros CT C loc abs_fields sigma sigma' abs_vals Hpres [Hfinals Hreads].
  split.
  - exact Hfinals.
  - eapply wm_field_histories_read_preserved; eauto.
Qed.

Lemma wm_write_preserves_field_histories_other :
  forall sigma sigma' V V' write_addr val loc fs
    (Hwrite : wm_write sigma sigma' V V' write_addr val)
    (Hother : forall f, In f fs -> write_addr <> (loc, f)),
    wm_histories_preserve_fields sigma sigma' loc fs.
Proof.
  intros sigma sigma' V V' write_addr val loc fs Hwrite Hother f Hin.
  eapply wm_write_history_other; eauto.
  intro Heq.
  apply (Hother f Hin).
  symmetry.
  exact Heq.
Qed.

Lemma pico_wm_stable_abs_preserved_by_other_write :
  forall CT C loc abs_fields sigma sigma' V V' write_addr val abs_vals
    (Hwrite : wm_write sigma sigma' V V' write_addr val)
    (Hother : forall f, In f abs_fields -> write_addr <> (loc, f))
    (Hstable : pico_wm_stable_abs CT C loc abs_fields sigma abs_vals),
    pico_wm_stable_abs CT C loc abs_fields sigma' abs_vals.
Proof.
  intros CT C loc abs_fields sigma sigma' V V' write_addr val abs_vals
    Hwrite Hother Hstable.
  eapply pico_wm_stable_abs_preserved_by_histories; eauto.
  eapply wm_write_preserves_field_histories_other; eauto.
Qed.

Definition wm_transition_writes_avoid_fields
    (sigma sigma' : wm_state) (loc : Loc) (fs : list var) : Prop :=
  forall V V' write_addr val,
    wm_write sigma sigma' V V' write_addr val ->
    wm_write_avoids_fields write_addr loc fs.

Definition wm_steps_writes_avoid_fields
    `{CacheMemoryModel} (CT : class_table)
    (cfg cfg' : wm_config) (loc : Loc) (fs : list var) : Prop :=
  forall c1 c2,
    wm_steps CT cfg c1 ->
    wm_step CT c1 c2 ->
    wm_steps CT c2 cfg' ->
    forall V V' write_addr val,
      wm_write (wc_state c1) (wc_state c2) V V' write_addr val ->
      wm_write_avoids_fields write_addr loc fs.

Lemma wm_thread_step_preserves_field_histories_from_avoiding_writes :
  forall `{CacheMemoryModel} CT sigma sigma' t t' loc fs
    (Hstep : wm_thread_step CT sigma t sigma' t')
    (Havoid : wm_transition_writes_avoid_fields sigma sigma' loc fs),
    wm_histories_preserve_fields sigma sigma' loc fs.
Proof.
  intros Hmem CT sigma sigma' t t' loc fs Hstep Havoid.
  induction Hstep.
  - unfold wm_histories_preserve_fields.
    intros f0 Hin.
    reflexivity.
  - unfold wm_histories_preserve_fields.
    intros f0 Hin.
    reflexivity.
  - eapply wm_write_preserves_field_histories_other; eauto.
    intros f0 Hin.
    unfold wm_transition_writes_avoid_fields,
      wm_write_avoids_fields in Havoid.
    eapply Havoid; eauto.
  - unfold wm_histories_preserve_fields.
    intros f0 Hin.
    reflexivity.
  - apply IHHstep.
    exact Havoid.
Qed.

Lemma wm_step_preserves_field_histories_from_avoiding_writes :
  forall `{CacheMemoryModel} CT cfg cfg' loc fs
    (Hstep : wm_step CT cfg cfg')
    (Havoid : wm_transition_writes_avoid_fields
      (wc_state cfg)
      (wc_state cfg')
      loc
      fs),
    wm_histories_preserve_fields (wc_state cfg) (wc_state cfg') loc fs.
Proof.
  intros Hmem CT cfg cfg' loc fs Hstep Havoid.
  inversion Hstep as
    [sigma sigma' threads threads' i t t' Hnth Hthread Hthreads]; subst.
  eapply wm_thread_step_preserves_field_histories_from_avoiding_writes;
    eauto.
Qed.

Lemma wm_steps_preserve_field_histories_from_avoiding_writes :
  forall `{CacheMemoryModel} CT cfg cfg' loc fs
    (Hsteps : wm_steps CT cfg cfg')
    (Havoid_all : wm_steps_writes_avoid_fields CT cfg cfg' loc fs),
    wm_histories_preserve_fields (wc_state cfg) (wc_state cfg') loc fs.
Proof.
  intros Hmem CT cfg cfg' loc fs Hsteps Havoid_all.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH].
  - unfold wm_histories_preserve_fields.
    intros f Hin.
    reflexivity.
  - pose proof
      (wm_step_preserves_field_histories_from_avoiding_writes
        CT cfg1 cfg2 loc fs Hstep) as Hpres_step.
    assert (Havoid_step :
      wm_transition_writes_avoid_fields
        (wc_state cfg1) (wc_state cfg2) loc fs).
    {
      unfold wm_transition_writes_avoid_fields.
      intros V V' write_addr val Hwrite.
      eapply Havoid_all.
      - apply WMS_Refl.
      - exact Hstep.
      - exact Hsteps_tail.
      - exact Hwrite.
    }
    specialize (Hpres_step Havoid_step).
    assert (Havoid_tail :
      wm_steps_writes_avoid_fields CT cfg2 cfg3 loc fs).
    {
      unfold wm_steps_writes_avoid_fields in *.
      intros c1 c2 Hpre Hstep_tail Hpost V V' write_addr val Hwrite.
      eapply Havoid_all.
      - eapply WMS_Step.
        + exact Hstep.
        + exact Hpre.
      - exact Hstep_tail.
      - exact Hpost.
      - exact Hwrite.
    }
    specialize (IH Havoid_tail).
    unfold wm_histories_preserve_fields in *.
    intros f Hin.
    rewrite (IH f Hin).
    exact (Hpres_step f Hin).
Qed.

Lemma pico_wm_stable_abs_preserved_by_steps_avoiding_writes :
  forall `{CacheMemoryModel} CTstep CTabs C loc abs_fields cfg cfg' abs_vals
    (Hsteps : wm_steps CTstep cfg cfg')
    (Havoid : wm_steps_writes_avoid_fields CTstep cfg cfg' loc abs_fields)
    (Hstable :
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals),
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg') abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' abs_vals
    Hsteps Havoid Hstable.
  eapply pico_wm_stable_abs_preserved_by_histories; eauto.
  eapply wm_steps_preserve_field_histories_from_avoiding_writes; eauto.
Qed.

Lemma runtime_vpa_assignability_final_not_assignable :
  forall q,
    runtime_vpa_assignability q Final <> Assignable.
Proof.
  intros q Hassignable.
  destruct q; discriminate.
Qed.

Lemma final_fields_field_final :
  forall CT C fs f
    (Hfinals : final_fields CT C fs)
    (Hin : In f fs),
    final_field CT C f.
Proof.
  intros CT C fs f Hfinals Hin.
  unfold final_fields in Hfinals.
  eapply Forall_forall; eauto.
Qed.

Lemma wm_thread_step_preserves_get_type :
  forall `{CacheMemoryModel} CT sigma sigma' t t' loc
    (Hstep : wm_thread_step CT sigma t sigma' t'),
    wm_get_type sigma' loc = wm_get_type sigma loc.
Proof.
  intros Hmem CT sigma sigma' t t' loc Hstep.
  induction Hstep.
  - reflexivity.
  - reflexivity.
  - eapply wm_write_get_type; eauto.
  - reflexivity.
  - exact IHHstep.
Qed.

Lemma wm_step_preserves_get_type :
  forall `{CacheMemoryModel} CT cfg cfg' loc
    (Hstep : wm_step CT cfg cfg'),
    wm_get_type (wc_state cfg') loc = wm_get_type (wc_state cfg) loc.
Proof.
  intros Hmem CT cfg cfg' loc Hstep.
  inversion Hstep as
    [sigma sigma' threads threads' i t t' Hnth Hthread Hthreads]; subst.
  eapply wm_thread_step_preserves_get_type; eauto.
Qed.

Lemma wm_thread_step_preserves_pico_wm_stable_abs_from_final_fields :
  forall `{CacheMemoryModel} CTstep CTabs C loc abs_fields sigma sigma' t t'
    (Hstep : wm_thread_step CTstep sigma t sigma' t'),
    forall rt_abs abs_vals
      (Htype : wm_get_type sigma loc = Some rt_abs)
      (HC : rctype rt_abs = C)
      (Hfinals : final_fields CTstep C abs_fields)
      (Hstable : pico_wm_stable_abs CTabs C loc abs_fields sigma abs_vals),
      pico_wm_stable_abs CTabs C loc abs_fields sigma' abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields sigma sigma' t t' Hstep.
  induction Hstep; intros rt_abs abs_vals Htype HC Hfinals Hstable.
  - exact Hstable.
  - exact Hstable.
  - eapply pico_wm_stable_abs_preserved_by_other_write; eauto.
    intros f_abs Hin Heq.
    inversion Heq; subst loc_x f.
    assert (rt = rt_abs) as Hrt_eq by congruence.
    subst rt.
    rewrite HC in H1.
    pose proof
      (final_fields_field_final CTstep C abs_fields f_abs Hfinals Hin)
      as Hfinal.
    unfold final_field in Hfinal.
    pose proof
      (sf_assignability_deterministic_rel CTstep C f_abs a Final
        H1 Hfinal) as Ha.
    subst a.
    eapply runtime_vpa_assignability_final_not_assignable; eauto.
  - exact Hstable.
  - eapply IHHstep; eauto.
Qed.

Lemma wm_step_preserves_pico_wm_stable_abs_from_final_fields :
  forall `{CacheMemoryModel} CTstep CTabs C loc abs_fields cfg cfg'
    (Hstep : wm_step CTstep cfg cfg'),
    forall rt_abs abs_vals
      (Htype : wm_get_type (wc_state cfg) loc = Some rt_abs)
      (HC : rctype rt_abs = C)
      (Hfinals : final_fields CTstep C abs_fields)
      (Hstable :
        pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals),
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg') abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' Hstep
    rt_abs abs_vals Htype HC Hfinals Hstable.
  inversion Hstep as
    [sigma sigma' threads threads' i t t' Hnth Hthread Hthreads]; subst.
  eapply wm_thread_step_preserves_pico_wm_stable_abs_from_final_fields;
    eauto.
Qed.

Lemma wm_steps_preserve_pico_wm_stable_abs_from_final_fields :
  forall `{CacheMemoryModel} CTstep CTabs C loc abs_fields cfg cfg'
    (Hsteps : wm_steps CTstep cfg cfg'),
    forall rt_abs abs_vals
      (Htype : wm_get_type (wc_state cfg) loc = Some rt_abs)
      (HC : rctype rt_abs = C)
      (Hfinals : final_fields CTstep C abs_fields)
      (Hstable :
        pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals),
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg') abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' Hsteps.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH];
    intros rt_abs abs_vals Htype HC Hfinals Hstable.
  - exact Hstable.
  - pose proof
      (wm_step_preserves_pico_wm_stable_abs_from_final_fields
        CTstep CTabs C loc abs_fields cfg1 cfg2 Hstep
        rt_abs abs_vals Htype HC Hfinals Hstable) as Hstable2.
    assert (Htype2 : wm_get_type (wc_state cfg2) loc = Some rt_abs).
    {
      rewrite (wm_step_preserves_get_type CTstep cfg1 cfg2 loc Hstep).
      exact Htype.
    }
    eapply IH; eauto.
Qed.

(** The main PICO/provider bridge for the generic theorem.  After weak-memory
    steps preserve the final-field abstraction and the cache history is a valid
    extension, a trace-robust cache method returns the pure result and preserves
    semantic immutability in the final weak-memory state. *)
Theorem pico_wm_stable_cache_safe_method_sound_after_steps_post_history :
  forall `{CacheMemoryModel}
    CTstep CTabs C loc abs_fields cfg cfg' rt_abs addr derived abs_vals
    {Args Result : Type}
    (F : list value -> Args -> Result)
    (run_with_cache_trace :
      list value -> Args ->
      CacheTrace (derived_cache_protocol derived) ->
      CacheRun (derived_cache_protocol derived) Result)
    args tr r
    (Hsteps : wm_steps CTstep cfg cfg')
    (Htype : wm_get_type (wc_state cfg) loc = Some rt_abs)
    (HC : rctype rt_abs = C)
    (Hfinals : final_fields CTstep C abs_fields)
    (Hstable :
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals)
    (Hhist : CacheHistOK
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      abs_vals)
    (Hext : CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      (wc_state cfg')
      abs_vals)
    (Hsafe : CacheSafeMethod
      (derived_cache_protocol derived)
      F
      run_with_cache_trace)
    (Hreads : TraceReadsFromHistory
      (derived_cache_protocol derived)
      (wm_derived_cache_read derived addr)
      (wc_state cfg')
      tr)
    (Hexec : weak_exec_matches_trace
      (derived_cache_protocol derived)
      run_with_cache_trace
      abs_vals
      args
      tr
      r),
    r = F abs_vals args /\
    SemImm
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (pico_wm_stable_abs CTabs C loc abs_fields)
      (wc_state cfg')
      abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' rt_abs addr
    derived abs_vals Args Result F run args tr r Hsteps Htype HC Hfinals
    Hstable Hhist Hext Hsafe Hreads Hexec.
  pose proof
    (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
      CTstep CTabs C loc abs_fields cfg cfg' Hsteps rt_abs abs_vals
      Htype HC Hfinals Hstable) as Hstable'.
  eapply (@cache_safe_method_sound_from_post_history_with_valid_extension
    wm_state
    (list value)
    Args
    Result
    (derived_cache_protocol derived)
    (wm_derived_cache_history derived addr)
    (wm_derived_cache_history derived addr)
    (pico_wm_stable_abs CTabs C loc abs_fields)
    (wm_derived_cache_read derived addr)
    (@wm_derived_cache_read_from_history Hmem derived addr)
    F
    run
    (wc_state cfg)
    (wc_state cfg')
    abs_vals
    args
    tr
    r); eauto.
Qed.

(** Closed-config version of
    [pico_wm_stable_cache_safe_method_sound_after_steps_post_history]: the
    cache-history extension premise is derived from a closed cache-safe config
    invariant. *)
Theorem pico_wm_stable_cache_safe_method_sound_from_closed_steps_post_history :
  forall `{CacheMemoryModel}
    CTstep CTabs C loc abs_fields cfg cfg' rt_abs addr derived abs_vals
    {Args Result : Type}
    (F : list value -> Args -> Result)
    (run_with_cache_trace :
      list value -> Args ->
      CacheTrace (derived_cache_protocol derived) ->
      CacheRun (derived_cache_protocol derived) Result)
    args tr r
    (Hsteps : wm_steps CTstep cfg cfg')
    (Htype : wm_get_type (wc_state cfg) loc = Some rt_abs)
    (HC : rctype rt_abs = C)
    (Hfinals : final_fields CTstep C abs_fields)
    (Hstable :
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hsafe_cfg : cache_safe_config cfg addr derived abs_vals)
    (Hclosed : forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals ->
      cache_safe_config c2 addr derived abs_vals)
    (Hsafe : CacheSafeMethod
      (derived_cache_protocol derived)
      F
      run_with_cache_trace)
    (Hreads : TraceReadsFromHistory
      (derived_cache_protocol derived)
      (wm_derived_cache_read derived addr)
      (wc_state cfg')
      tr)
    (Hexec : weak_exec_matches_trace
      (derived_cache_protocol derived)
      run_with_cache_trace
      abs_vals
      args
      tr
      r),
    r = F abs_vals args /\
    SemImm
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (pico_wm_stable_abs CTabs C loc abs_fields)
      (wc_state cfg')
      abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' rt_abs addr
    derived abs_vals Args Result F run args tr r Hsteps Htype HC Hfinals
    Hstable Hstate Hsafe_cfg Hclosed Hsafe Hreads Hexec.
  pose proof
    (wm_cache_history_state_generic
      (wc_state cfg) addr derived abs_vals Hstate) as Hhist.
  pose proof
    (wm_steps_valid_extension_from_closed_config_safe_generic
      CTstep cfg cfg' addr derived abs_vals Hsteps Hsafe_cfg Hclosed Hstate)
    as Hext.
  eapply pico_wm_stable_cache_safe_method_sound_after_steps_post_history;
    eauto.
Qed.

(** Version where the method's own writes are represented as a post-step
    history extension generated by the method write trace. *)
Theorem pico_wm_stable_cache_safe_method_sound_after_steps_write_extension :
  forall `{CacheMemoryModel}
    CTstep CTabs C loc abs_fields cfg cfg' sigma' rt_abs addr
    derived abs_vals
    {Args Result : Type}
    (F : list value -> Args -> Result)
    (run_with_cache_trace :
      list value -> Args ->
      CacheTrace (derived_cache_protocol derived) ->
      CacheRun (derived_cache_protocol derived) Result)
    args tr r
    (Hsteps : wm_steps CTstep cfg cfg')
    (Htype : wm_get_type (wc_state cfg) loc = Some rt_abs)
    (HC : rctype rt_abs = C)
    (Hfinals : final_fields CTstep C abs_fields)
    (Hstable :
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals)
    (Hhist : CacheHistOK
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      abs_vals)
    (Hpre_ext : CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      (wc_state cfg')
      abs_vals)
    (Hstable_post : pico_wm_stable_abs CTabs C loc abs_fields sigma' abs_vals)
    (Hsafe : CacheSafeMethod
      (derived_cache_protocol derived)
      F
      run_with_cache_trace)
    (Hreads : TraceReadsFromHistory
      (derived_cache_protocol derived)
      (wm_derived_cache_read derived addr)
      (wc_state cfg')
      tr)
    (Hexec : weak_exec_matches_trace
      (derived_cache_protocol derived)
      run_with_cache_trace
      abs_vals
      args
      tr
      r)
    (Hext_by_writes : CacheHistExtendsByTrace
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg')
      sigma'
      (run_writes (run_with_cache_trace abs_vals args tr))),
    r = F abs_vals args /\
    SemImm
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (pico_wm_stable_abs CTabs C loc abs_fields)
      sigma'
      abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' sigma' rt_abs addr
    derived abs_vals Args Result F run args tr r Hsteps Htype HC Hfinals
    Hstable Hhist Hpre_ext Hstable_post Hsafe Hreads Hexec Hext_by_writes.
  pose proof
    (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
      CTstep CTabs C loc abs_fields cfg cfg' Hsteps rt_abs abs_vals
      Htype HC Hfinals Hstable) as Hstable_pre.
  eapply (@trace_robust_semantic_immutability_after_history_extension
    wm_state
    (list value)
    Args
    Result
    (derived_cache_protocol derived)
    (wm_derived_cache_history derived addr)
    (wm_derived_cache_history derived addr)
    (wm_derived_cache_history derived addr)
    (pico_wm_stable_abs CTabs C loc abs_fields)
    (wm_derived_cache_read derived addr)
    (@wm_derived_cache_read_from_history Hmem derived addr)
    F
    run
    (wc_state cfg)
    (wc_state cfg')
    sigma'
    abs_vals
    args
    tr
    r); eauto.
  split; assumption.
Qed.

(** Cache-only write-extension variant.  The extra side condition says the
    method's writes only extend the target cache field, so the provider's
    abstract-field histories remain stable. *)
Theorem pico_wm_stable_cache_safe_method_sound_after_steps_cache_only_write_extension :
  forall `{CacheMemoryModel}
    CTstep CTabs C loc abs_fields cfg cfg' sigma' rt_abs addr
    derived abs_vals
    {Args Result : Type}
    (F : list value -> Args -> Result)
    (run_with_cache_trace :
      list value -> Args ->
      CacheTrace (derived_cache_protocol derived) ->
      CacheRun (derived_cache_protocol derived) Result)
    args tr r
    (Hsteps : wm_steps CTstep cfg cfg')
    (Htype : wm_get_type (wc_state cfg) loc = Some rt_abs)
    (HC : rctype rt_abs = C)
    (Hfinals : final_fields CTstep C abs_fields)
    (Hstable :
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals)
    (Hhist : CacheHistOK
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      abs_vals)
    (Hpre_ext : CacheHistValidExtension
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg)
      (wc_state cfg')
      abs_vals)
    (Honly : wm_histories_only_extend_field (wc_state cfg') sigma' addr)
    (Havoid : wm_write_avoids_fields addr loc abs_fields)
    (Hsafe : CacheSafeMethod
      (derived_cache_protocol derived)
      F
      run_with_cache_trace)
    (Hreads : TraceReadsFromHistory
      (derived_cache_protocol derived)
      (wm_derived_cache_read derived addr)
      (wc_state cfg')
      tr)
    (Hexec : weak_exec_matches_trace
      (derived_cache_protocol derived)
      run_with_cache_trace
      abs_vals
      args
      tr
      r)
    (Hext_by_writes : CacheHistExtendsByTrace
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg')
      sigma'
      (run_writes (run_with_cache_trace abs_vals args tr))),
    r = F abs_vals args /\
    SemImm
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (pico_wm_stable_abs CTabs C loc abs_fields)
      sigma'
      abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' sigma' rt_abs addr
    derived abs_vals Args Result F run args tr r Hsteps Htype HC Hfinals
    Hstable Hhist Hpre_ext Honly Havoid Hsafe Hreads Hexec Hext_by_writes.
  pose proof
    (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
      CTstep CTabs C loc abs_fields cfg cfg' Hsteps rt_abs abs_vals
      Htype HC Hfinals Hstable) as Hstable_pre.
  pose proof
    (wm_histories_only_extend_field_preserves_fields
      (wc_state cfg') sigma' addr loc abs_fields Honly Havoid) as Hpres.
  pose proof
    (pico_wm_stable_abs_preserved_by_histories
      CTabs C loc abs_fields (wc_state cfg') sigma' abs_vals
      Hpres Hstable_pre) as Hstable_post.
  eapply pico_wm_stable_cache_safe_method_sound_after_steps_write_extension;
    eauto.
Qed.

(** Fully packaged closed-config theorem for the cache-only extension shape. *)
Theorem pico_wm_stable_cache_safe_method_sound_from_closed_steps_cache_only_write_extension :
  forall `{CacheMemoryModel}
    CTstep CTabs C loc abs_fields cfg cfg' sigma' rt_abs addr
    derived abs_vals
    {Args Result : Type}
    (F : list value -> Args -> Result)
    (run_with_cache_trace :
      list value -> Args ->
      CacheTrace (derived_cache_protocol derived) ->
      CacheRun (derived_cache_protocol derived) Result)
    args tr r
    (Hsteps : wm_steps CTstep cfg cfg')
    (Htype : wm_get_type (wc_state cfg) loc = Some rt_abs)
    (HC : rctype rt_abs = C)
    (Hfinals : final_fields CTstep C abs_fields)
    (Hstable :
      pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hsafe_cfg : cache_safe_config cfg addr derived abs_vals)
    (Hclosed : forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals ->
      cache_safe_config c2 addr derived abs_vals)
    (Honly : wm_histories_only_extend_field (wc_state cfg') sigma' addr)
    (Havoid : wm_write_avoids_fields addr loc abs_fields)
    (Hsafe : CacheSafeMethod
      (derived_cache_protocol derived)
      F
      run_with_cache_trace)
    (Hreads : TraceReadsFromHistory
      (derived_cache_protocol derived)
      (wm_derived_cache_read derived addr)
      (wc_state cfg')
      tr)
    (Hexec : weak_exec_matches_trace
      (derived_cache_protocol derived)
      run_with_cache_trace
      abs_vals
      args
      tr
      r)
    (Hext_by_writes : CacheHistExtendsByTrace
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (wm_derived_cache_history derived addr)
      (wc_state cfg')
      sigma'
      (run_writes (run_with_cache_trace abs_vals args tr))),
    r = F abs_vals args /\
    SemImm
      (derived_cache_protocol derived)
      (wm_derived_cache_history derived addr)
      (pico_wm_stable_abs CTabs C loc abs_fields)
      sigma'
      abs_vals.
Proof.
  intros Hmem CTstep CTabs C loc abs_fields cfg cfg' sigma' rt_abs addr
    derived abs_vals Args Result F run args tr r Hsteps Htype HC Hfinals
    Hstable Hstate Hsafe_cfg Hclosed Honly Havoid Hsafe Hreads Hexec
    Hext_by_writes.
  pose proof
    (wm_cache_history_state_generic
      (wc_state cfg) addr derived abs_vals Hstate) as Hhist.
  pose proof
    (wm_steps_valid_extension_from_closed_config_safe_generic
      CTstep cfg cfg' addr derived abs_vals Hsteps Hsafe_cfg Hclosed Hstate)
    as Hpre_ext.
  eapply pico_wm_stable_cache_safe_method_sound_after_steps_cache_only_write_extension;
    eauto.
Qed.

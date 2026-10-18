From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability
  AbstractStatePreservation.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety
  Examples.PicoCacheMethodJudgment Examples.PicoHashCacheMethod.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * Clients of a Cached Object

    A thread can break the derivation-defined provider's invariant only by
    writing the cache field itself.  Every other successful write targets a
    field outside the abstract state, because the machine checks
    assignability and the footprint is immutable, and allocation touches no
    existing object.

    Any control that never writes the cache field directly is therefore an
    admissible client, whatever else it does and whether or not it is well
    typed, and it may run alongside any number of cache-method calls. *)

Section cache_clients.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).

  Let footprint := reachable_abs CT h0 receiver.

  (** The footprint of the receiver is immutable in the reference heap. *)
  Hypothesis Himm : forall l, footprint l ->
    exists C vals,
      runtime_getObj h0 l = Some (mkObj (mkruntime_type Imm_r C) vals).

  Notation hash_machine := (pico_concrete_hash_semimm CT receiver m h0 H).
  Notation hash_inv :=
    (machine_inv hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).
  Notation hash_reach :=
    (inv_reach CT hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).

  Lemma noncache_addr_unmapped :
    forall addr,
      addr <> (receiver, hash_cache_field) ->
      pico_core_cache_field hash_cache_protocol
        (pico_hash_cache_adapter receiver) addr = None.
  Proof.
    intros addr Hneq.
    unfold pico_hash_cache_adapter; simpl.
    destruct (field_addr_eqb addr (pico_hash_cache_addr receiver)) eqn:Heq;
      [| reflexivity].
    apply field_addr_eqb_eq in Heq. contradiction.
  Qed.

  (** A step that is not a write to the cache field preserves the
      invariant. *)
  Theorem noncache_step_preserves_inv :
    forall e S e' S',
      hash_inv S ->
      pico_core_step CT e S e' S' ->
      (forall rGamma x f y V K loc,
         e = CoreRun rGamma (SFldWrite x f y) V K ->
         runtime_getVal rGamma x = Some (Iot loc) ->
         (loc, f) <> (receiver, hash_cache_field)) ->
      hash_inv S'.
  Proof.
    intros e S e' S' Hinv Hstep Hnocache.
    inversion Hstep; subst; try exact Hinv.
    - (* a successful field write *)
      destruct Hinv as [Hstate Hsnap].
      match goal with
      | Hx : runtime_getVal _ _ = Some (Iot ?l),
        Hobj : runtime_getObj _ ?l = Some ?o,
        Hassign : sf_assignability_rel CT _ ?fld ?a,
        Hrun : runtime_vpa_assignability _ ?a = Assignable,
        Hw : wm_write _ _ _ _ (?l, ?fld) _ |- _ =>
          have Hneq := Hnocache _ _ _ _ _ _ _ eq_refl Hx;
          have Hnone := noncache_addr_unmapped _ Hneq;
          assert (Hnotabs : ~ pico_hash_abstract_field CT h0 receiver (l, fld))
            by (destruct Hstate as (_ & (_ & _ & Habs & _) & _);
                exact (assignable_write_outside_footprint CT footprint h0 Himm
                  _ _ _ _ _ Habs Hobj Hassign Hrun));
          destruct (pcsi_unrelated_write_effect hash_cache_protocol
            pico_hash_stable_abs H (pico_hash_cache_adapter receiver)
            hash_machine _ _ _ _ _ _ _ _ _
            Hstate eq_refl Hw Hnone Hnotabs) as (_ & Hsnap_eq & Hstate')
      end.
      split; [exact Hstate' |].
      cbv zeta in Hsnap_eq. rewrite Hsnap_eq. exact Hsnap.
    - (* allocation *)
      destruct Hinv as [Hstate Hsnap].
      match goal with
      | |- hash_inv (mkPicoCoreState (?h ++ [?o]) (pico_core_alloc_weak ?sg _ ?V)) =>
          destruct (pcsi_alloc_unchanged hash_cache_protocol
            pico_hash_stable_abs H (pico_hash_cache_adapter receiver)
            hash_machine h sg o V Hstate) as (_ & Hsnap_eq & Hstate')
      end.
      split; [exact Hstate' |].
      cbv zeta in Hsnap_eq. rewrite Hsnap_eq. exact Hsnap.
  Qed.

  (** The control never writes the cache field directly. *)
  Definition no_direct_cache_write (e0 : pico_core_expr) : Prop :=
    forall e rGamma x f y V K loc,
      hash_reach e0 e ->
      e = CoreRun rGamma (SFldWrite x f y) V K ->
      runtime_getVal rGamma x = Some (Iot loc) ->
      (loc, f) <> (receiver, hash_cache_field).

  Theorem no_direct_cache_write_client :
    forall e0,
      no_direct_cache_write e0 ->
      protocol_client CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine e0.
  Proof.
    intros e0 Hno e S e' S' Hreach Hinv Hstep.
    eapply noncache_step_preserves_inv; [exact Hinv | exact Hstep |].
    intros rGamma x f y V K loc Heq Hx.
    exact (Hno e rGamma x f y V K loc Hreach Heq Hx).
  Qed.
End cache_clients.

(** ** Hash calls alongside direct readers

    A reader thread reads the cache field directly, with no local-copy
    discipline at all.  It never writes the field, so it is an admissible
    client: any number of hash calls and any number of such readers preserve
    semantic immutability under every interleaving. *)

Definition pico_hash_reader : pico_core_expr :=
  CoreRun (mkr_env [Iot pico_hash_concurrent_receiver; Int 0])
    (SVarAss 1 (EField 0 hash_cache_field)) 0 [].

Notation concurrent_machine :=
  (@pico_concrete_hash_semimm history_cache_memory_model
     pico_hash_concurrent_CT pico_hash_concurrent_receiver
     pico_hash_derive_method pico_hash_concurrent_initial_heap
     pico_hash_concurrent_value).

Lemma pico_hash_concurrent_footprint_immutable :
  forall l,
    reachable_abs pico_hash_concurrent_CT pico_hash_concurrent_initial_heap
      pico_hash_concurrent_receiver l ->
    exists C vals,
      runtime_getObj pico_hash_concurrent_initial_heap l =
        Some (mkObj (mkruntime_type Imm_r C) vals).
Proof.
  intros l Hreach.
  eapply reachable_abs_from_imm_points_to_imm;
    [exact pico_hash_concurrent_config_wf | | exact Hreach].
  reflexivity.
Qed.

Lemma pico_hash_reader_reach :
  forall e,
    @inv_reach history_cache_memory_model pico_hash_concurrent_CT _ _
      hash_cache_protocol pico_hash_stable_abs pico_hash_concurrent_value
      (pico_hash_cache_adapter pico_hash_concurrent_receiver)
      concurrent_machine pico_hash_reader e ->
    (exists rGamma s V,
       e = CoreRun rGamma s V [] /\
       (s = SVarAss 1 (EField 0 hash_cache_field) \/ s = SSkip)) \/
    (exists r rGamma V, e = CoreDone r rGamma V).
Proof.
  intros e Hreach.
  induction Hreach as [| e S e' S' Hreach IH Hinv Hstep].
  - left. do 3 eexists. split; [reflexivity | left; reflexivity].
  - destruct IH as [(rGamma & s & V & -> & [-> | ->]) | (r & rGamma & V & ->)].
    + inversion Hstep; subst.
      * left. do 3 eexists. split; [reflexivity | right; reflexivity].
      * right. do 3 eexists. reflexivity.
    + inversion Hstep; subst. right. do 3 eexists. reflexivity.
    + inversion Hstep.
Qed.

Lemma pico_hash_reader_client :
  @protocol_client history_cache_memory_model pico_hash_concurrent_CT _ _
    hash_cache_protocol pico_hash_stable_abs pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    concurrent_machine pico_hash_reader.
Proof.
  apply no_direct_cache_write_client.
  - exact pico_hash_concurrent_footprint_immutable.
  - intros e rGamma x f y V K loc Hreach Heq _.
    destruct (pico_hash_reader_reach e Hreach)
      as [(rG & s & V1 & Heq' & [-> | ->]) | (r & rG & V1 & Heq')];
      rewrite Heq' in Heq; discriminate.
Qed.

Definition pico_hash_calls_and_readers (n k : nat) : pico_pool_config :=
  mkPicoPoolConfig pico_hash_concurrent_initial_state
    (repeat (pico_hash_phase_control HashCall) n ++ repeat pico_hash_reader k).

Theorem pico_hash_calls_and_readers_semimm : forall n k cfg,
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    (pico_hash_calls_and_readers n k) cfg ->
  CacheHistSnapshotOK hash_cache_protocol
    (pico_hash_snapshot pico_hash_concurrent_receiver (pool_state cfg))
    pico_hash_concurrent_value.
Proof.
  intros n k cfg Hsteps.
  assert (Hpool : @mixed_pool history_cache_memory_model
    pico_hash_concurrent_CT _ _ hash_cache_protocol pico_hash_stable_abs
    pico_hash_concurrent_value
    (pico_hash_cache_adapter pico_hash_concurrent_receiver)
    concurrent_machine
    (cache_call_result_ok pico_hash_concurrent_value 1)
    (pico_hash_calls_and_readers n k)).
  { split.
    - split; [exact pico_hash_concurrent_initial_provider_inv |].
      exact (proj2 (proj2 pico_hash_concurrent_initial_provider_inv)).
    - simpl. apply Forall_app. split; apply Forall_forall;
        intros e Hin; apply repeat_spec in Hin; subst e.
      + left. apply machine_local_start.
        exact (pico_hash_call_trace_robust_by_judgment 0).
      + right. exists pico_hash_reader.
        split; [exact pico_hash_reader_client | constructor]. }
  exact (proj2 (machine_mixed_pool_semimm _ _ _ _ _ _ _ _ _ Hpool Hsteps)).
Qed.

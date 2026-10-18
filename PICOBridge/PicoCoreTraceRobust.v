From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Core.GenericCacheProtocol.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreInvariant PICOBridge.PicoCoreSemImm
  PICOBridge.PicoSemanticConcurrency.

(** * Trace Robustness on the Core Machine

    The generic cache theory states trace robustness for an abstract function
    from read traces to results.  This file states it for controls of the core
    machine, for an arbitrary cache protocol and provider, and proves the
    generic theory's conclusions as theorems about small-step executions of
    any number of threads.

    A thread's run is recorded together with the trace of its cache reads.
    In that run a read of a cache field may return any value that the memory
    model can return in some state: the trace is not tied to the current
    heap or to one history, so older values and reads that disagree are
    included.  A control is trace
    robust on the machine when, after every valid read trace, each field
    write it is about to perform respects the protocol and each result it
    has produced meets its contract. *)

Section machine_trace_robust.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context {AbsVal Obj : Type}.
  Context (P : CacheProtocol AbsVal).
  Context (Stable : StableAbs Obj AbsVal).
  Context (a : AbsVal).
  Context (A : PicoCoreCacheAdapter P).
  Context (M : PicoCoreSemImmInstantiation P Stable a A).
  Context (ResultOK : pico_core_val -> Prop).

  (** The shared invariant: the provider's invariant, and every value in the
      history of a cache field is valid for the abstract value. *)
  Definition machine_inv (S : pico_core_state) : Prop :=
    pcsi_state_inv P Stable a A M S /\
    CacheHistSnapshotOK P (pcsi_snapshot P Stable a A M S) a.

  (** The control is about to read a cache field. *)
  Definition cache_read_control (e : pico_core_expr) : Prop :=
    exists rGamma x y f V K loc k,
      e = CoreRun rGamma (SVarAss x (EField y f)) V K /\
      runtime_getVal rGamma y = Some (Iot loc) /\
      pico_core_cache_field P A (loc, f) = Some k.

  Lemma classic_cache_read :
    forall e, cache_read_control e \/ ~ cache_read_control e.
  Proof.
    intros e.
    destruct e as [rGamma s V K | r rGamma V];
      [| right; intros (? & ? & ? & ? & ? & ? & ? & ? & Heq & _); discriminate].
    destruct s;
      try (right; intros (? & ? & ? & ? & ? & ? & ? & ? & Heq & _);
           discriminate).
    destruct e;
      try (right; intros (? & ? & ? & ? & ? & ? & ? & ? & Heq & _);
           discriminate).
    destruct (runtime_getVal rGamma v0) as [[| loc | n] |] eqn:Hy;
      try (right; intros (? & ? & ? & ? & ? & ? & ? & ? & Heq & Hy' & _);
           injection Heq as <- <- <- <- <- <-; congruence).
    destruct (pico_core_cache_field P A (loc, v1)) as [k |] eqn:Hfield.
    - left. do 8 eexists. split; [reflexivity |]. split; eassumption.
    - right. intros (? & ? & ? & ? & ? & ? & ? & ? & Heq & Hy' & Hf).
      injection Heq as <- <- <- <- <- <-.
      rewrite Hy in Hy'. injection Hy' as <-. congruence.
  Qed.

  (** A thread's run from [e0], with the trace of its cache reads.  A cache
      read returns any value readable in some memory state.  Every other
      step is a machine step from an arbitrary state satisfying the
      invariant, which accounts for the steps of other threads in between. *)
  Inductive thread_run (e0 : pico_core_expr) :
      CacheTrace P -> pico_core_expr -> Prop :=
    | ThreadRun_Start :
        thread_run e0 [] e0
    | ThreadRun_CacheRead :
        forall tr rGamma x y f V V' K old loc k v (cv : cache_val P k) sigma,
          thread_run e0 tr (CoreRun rGamma (SVarAss x (EField y f)) V K) ->
          runtime_getVal rGamma x = Some old ->
          runtime_getVal rGamma y = Some (Iot loc) ->
          wm_read sigma V (loc, f) v V' ->
          pico_core_cache_field P A (loc, f) = Some k ->
          pico_core_cache_value P A k v = Some cv ->
          thread_run e0
            (tr ++ [{| obs_field := k; obs_value := cv |}])
            (CoreRun (set_vars rGamma (update x v (vars rGamma))) SSkip V' K)
    | ThreadRun_Step :
        forall tr e S e' S',
          thread_run e0 tr e ->
          ~ cache_read_control e ->
          machine_inv S ->
          pico_core_step CT e S e' S' ->
          thread_run e0 tr e'.

  (** A write respects the protocol when it targets a field that is neither
      a cache field nor part of the abstract state, or stores a valid value
      in a cache field. *)
  Definition write_respects_protocol (addr : FieldAddr) (v : value) : Prop :=
    (pico_core_cache_field P A addr = None /\ ~ pcsi_abstract_field P Stable a A M addr) \/
    (exists k (cv : cache_val P k),
       pico_core_cache_field P A addr = Some k /\
       pico_core_cache_value P A k v = Some cv /\
       cache_valid P a k cv).

  (** Trace robustness of a control: after every valid read trace, its next
      field write respects the protocol and its result meets the contract. *)
  Definition machine_cache_safe (e0 : pico_core_expr) : Prop :=
    forall tr e,
      thread_run e0 tr e ->
      ValidTrace P a tr ->
      (forall rGamma x f y V K loc v,
         e = CoreRun rGamma (SFldWrite x f y) V K ->
         runtime_getVal rGamma x = Some (Iot loc) ->
         runtime_getVal rGamma y = Some v ->
         write_respects_protocol (loc, f) v) /\
      (forall r rGamma V,
         e = CoreDone r rGamma V ->
         ResultOK (mkPicoCoreVal r rGamma V)).

  (** Read validity on the machine: under the invariant, every weak read of a
      cache field returns a valid value, whichever message the memory model
      selects. *)
  Theorem machine_cache_read_valid :
    forall S V addr v V' k,
      machine_inv S ->
      wm_read (pcs_weak S) V addr v V' ->
      pico_core_cache_field P A addr = Some k ->
      exists cv : cache_val P k,
        pico_core_cache_value P A k v = Some cv /\
        cache_valid P a k cv.
  Proof.
    intros S V addr v V' k [Hinv Hsnap] Hread Hfield.
    destruct (pico_core_semimm_cache_read_from_history P Stable a A M S V
      addr v V' k Hinv Hread Hfield) as (k' & cv & Hfield' & Hvalue & Hin).
    rewrite Hfield in Hfield'. injection Hfield' as <-.
    exists cv. split; [exact Hvalue |].
    exact (Hsnap k cv Hin).
  Qed.

  (** A step whose field write respects the protocol preserves the
      invariant. *)
  Lemma machine_step_preserves_inv :
    forall e S e' S',
      machine_inv S ->
      (forall rGamma x f y V K loc v,
         e = CoreRun rGamma (SFldWrite x f y) V K ->
         runtime_getVal rGamma x = Some (Iot loc) ->
         runtime_getVal rGamma y = Some v ->
         write_respects_protocol (loc, f) v) ->
      pico_core_step CT e S e' S' ->
      machine_inv S'.
  Proof.
    intros e S e' S' Hinv Hwrite Hstep.
    inversion Hstep; subst; try exact Hinv.
    - (* field write *)
      destruct Hinv as [Hstate Hsnap].
      match goal with
      | Hx : runtime_getVal _ _ = Some (Iot ?l),
        Hy : runtime_getVal _ _ = Some ?val,
        Hw : wm_write _ _ _ _ (?l, ?fld) ?val |- _ =>
          destruct (Hwrite _ _ _ _ _ _ _ _ eq_refl Hx Hy)
            as [[Hnone Hnotabs] | (k & cv & Hfield & Hvalue & Hvalid)];
          [ destruct (pcsi_unrelated_write_effect P Stable a A M _ _ _ _ _ _ _ _ _
              Hstate eq_refl Hw Hnone Hnotabs) as (_ & Hsnap_eq & Hstate')
          | destruct (pcsi_valid_cache_write_effect P Stable a A M _ _ _ _ _ _ _ _ _ _ _
              Hstate eq_refl Hw Hfield Hvalue Hvalid) as [Hwstep Hstate'] ]
      end.
      + split; [exact Hstate' |].
        simpl in Hsnap_eq. rewrite Hsnap_eq. exact Hsnap.
      + split; [exact Hstate' |].
        destruct Hwstep as (k' & cv' & _ & _ & _ & Hext).
        eapply cache_hist_snapshot_ok_valid_extension; eauto.
    - (* allocation *)
      destruct Hinv as [Hstate Hsnap].
      destruct (pcsi_alloc_unchanged P Stable a A M h sigma
        (mkObj (mkruntime_type (vpa_mutability_object_creation qthisr qc) C)
          vals) V Hstate) as (_ & Hsnap_eq & Hstate').
      split; [exact Hstate' |].
      simpl in Hsnap_eq. rewrite Hsnap_eq. exact Hsnap.
  Qed.

  (** The thread-local assertion: the control is reached by a run of a trace
      robust control whose read trace is valid.  It does not mention the
      shared state, so it is stable under the steps of other threads. *)
  Definition machine_local (e : pico_core_expr) (_ : pico_core_state) : Prop :=
    exists e0 tr,
      machine_cache_safe e0 /\
      ValidTrace P a tr /\
      thread_run e0 tr e.

  Lemma machine_own_step :
    forall e S e' S',
      machine_inv S ->
      machine_local e S ->
      pico_core_step CT e S e' S' ->
      machine_inv S' /\ machine_local e' S'.
  Proof.
    intros e S e' S' Hinv (e0 & tr & Hsafe & Hvalid & Hrun) Hstep.
    destruct (Hsafe tr e Hrun Hvalid) as [Hwrite _].
    split; [eapply machine_step_preserves_inv; eauto |].
    exists e0.
    destruct (classic_cache_read e) as [Hread | Hnoread].
    - (* a cache read: extend the trace by a valid observation *)
      destruct Hread as (rGamma & x & y & f & V & K & loc & k & -> & Hy & Hfield).
      inversion Hstep; subst; try congruence.
      match goal with
      | Hy' : runtime_getVal rGamma y = Some (Iot ?l) |- _ =>
          rewrite Hy in Hy'; injection Hy' as <-
      end.
      match goal with
      | Hr : wm_read _ _ _ ?val _ |- _ =>
          destruct (machine_cache_read_valid _ _ _ _ _ _ Hinv Hr Hfield)
            as (cv & Hvalue & Hcv)
      end.
      exists (tr ++ [{| obs_field := k; obs_value := cv |}]).
      split; [exact Hsafe |].
      split.
      + apply Forall_app. split; [exact Hvalid |].
        constructor; [exact Hcv | constructor].
      + eapply ThreadRun_CacheRead; eauto.
    - exists tr.
      split; [exact Hsafe |]. split; [exact Hvalid |].
      eapply ThreadRun_Step; eauto.
  Qed.

  (** ** The generic theory on the machine

      From a pool whose state satisfies the invariant and whose controls are
      all trace robust, every scheduler execution preserves the invariant,
      and every finished control meets its result contract. *)
  Definition machine_pool (cfg : pico_pool_config) : Prop :=
    pool_rg_inv machine_inv machine_local cfg.

  Theorem machine_trace_robust_pool :
    forall cfg cfg',
      machine_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      machine_pool cfg'.
  Proof.
    intros cfg cfg' Hpool Hsteps.
    exact (pool_rely_guarantee CT machine_inv machine_local
      (fun _ S' => machine_inv S')
      machine_own_step
      (fun S S' _ Hinv' => Hinv')
      (fun e S S' _ Hlocal _ => Hlocal)
      cfg cfg' Hpool Hsteps).
  Qed.

  (** Semantic immutability is preserved: the object keeps its abstract
      value and every cache history stays valid. *)
  Theorem machine_trace_robust_semimm :
    forall cfg cfg',
      machine_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      Stable (pcsi_object P Stable a A M (pool_state cfg')) a /\
      CacheHistSnapshotOK P (pcsi_snapshot P Stable a A M (pool_state cfg')) a.
  Proof.
    intros cfg cfg' Hpool Hsteps.
    destruct (machine_trace_robust_pool cfg cfg' Hpool Hsteps)
      as [[Hstate Hsnap] _].
    split; [exact (pcsi_stable P Stable a A M _ Hstate) | exact Hsnap].
  Qed.

  (** Cache-independent results: every finished control meets its
      contract. *)
  Theorem machine_trace_robust_results :
    forall cfg cfg',
      machine_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      pico_pool_results_satisfy ResultOK cfg'.
  Proof.
    intros cfg cfg' Hpool Hsteps.
    refine (pool_rely_guarantee_results CT machine_inv machine_local
      (fun _ S' => machine_inv S')
      machine_own_step
      (fun S S' _ Hinv' => Hinv')
      (fun e S S' _ Hlocal _ => Hlocal)
      ResultOK cfg cfg' _ Hpool Hsteps).
    - intros e S r _ (e0 & tr & Hsafe & Hvalid & Hrun) Hval.
      destruct (Hsafe tr e Hrun Hvalid) as [_ Hresult].
      destruct e as [rGamma s V K | res rGamma V]; simpl in Hval;
        [discriminate |].
      injection Hval as <-. eapply Hresult. reflexivity.
  Qed.

  (** Refinement to pure recomputation.  If the result of every finished run
      of [e0] is the result that a trace function assigns to the run's read
      trace, and the trace function is trace robust in the generic sense,
      then every finished run with a valid read trace returns the pure
      result [F a args]. *)
  Theorem machine_result_refines_pure :
    forall {Args Result : Type}
      (F : AbsVal -> Args -> Result)
      (run : AbsVal -> Args -> CacheTrace P -> CacheRun P Result)
      (args : Args)
      (ResultRel : pico_core_val -> Result -> Prop)
      (e0 : pico_core_expr),
      CacheSafeMethod P F run ->
      (forall tr r rGamma V,
         thread_run e0 tr (CoreDone r rGamma V) ->
         ResultRel (mkPicoCoreVal r rGamma V)
           (run_result (run a args tr))) ->
      forall tr r rGamma V,
        thread_run e0 tr (CoreDone r rGamma V) ->
        ValidTrace P a tr ->
        ResultRel (mkPicoCoreVal r rGamma V) (F a args).
  Proof.
    intros Args Result F run args ResultRel e0 Hsafe Hrefines
      tr r rGamma V Hrun Hvalid.
    rewrite <- (proj1 (Hsafe a args tr Hvalid)).
    exact (Hrefines tr r rGamma V Hrun).
  Qed.

  (** A trace robust control at its start satisfies the local assertion. *)
  Lemma machine_local_start :
    forall e0 S, machine_cache_safe e0 -> machine_local e0 S.
  Proof.
    intros e0 S Hsafe. exists e0, (@nil (CacheObs P)). split; [exact Hsafe |].
    split; [constructor | constructor].
  Qed.

  (** ** Clients

      A client is any other control: it need not be a cache method and need
      not be trace robust.  It is admitted when each of its steps, from every
      control it can reach, preserves the invariant.  Providers discharge
      this for controls that never write a cache field directly. *)
  Inductive inv_reach (e0 : pico_core_expr) : pico_core_expr -> Prop :=
    | InvReach_Refl :
        inv_reach e0 e0
    | InvReach_Step : forall e S e' S',
        inv_reach e0 e ->
        machine_inv S ->
        pico_core_step CT e S e' S' ->
        inv_reach e0 e'.

  Definition protocol_client (e0 : pico_core_expr) : Prop :=
    forall e S e' S',
      inv_reach e0 e ->
      machine_inv S ->
      pico_core_step CT e S e' S' ->
      machine_inv S'.

  Definition client_local (e : pico_core_expr) : Prop :=
    exists e0, protocol_client e0 /\ inv_reach e0 e.

  Definition mixed_local (e : pico_core_expr) (S : pico_core_state) : Prop :=
    machine_local e S \/ client_local e.

  Definition mixed_pool (cfg : pico_pool_config) : Prop :=
    pool_rg_inv machine_inv mixed_local cfg.

  Lemma mixed_own_step :
    forall e S e' S',
      machine_inv S ->
      mixed_local e S ->
      pico_core_step CT e S e' S' ->
      machine_inv S' /\ mixed_local e' S'.
  Proof.
    intros e S e' S' Hinv [Hrobust | (e0 & Hclient & Hreach)] Hstep.
    - destruct (machine_own_step e S e' S' Hinv Hrobust Hstep) as [Hinv' Hl].
      split; [exact Hinv' | left; exact Hl].
    - split; [exact (Hclient e S e' S' Hreach Hinv Hstep) |].
      right. exists e0. split; [exact Hclient |].
      eapply InvReach_Step; eassumption.
  Qed.

  (** Trace robust controls and clients together: every scheduler execution
      preserves the invariant. *)
  Theorem machine_mixed_pool :
    forall cfg cfg',
      mixed_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      mixed_pool cfg'.
  Proof.
    intros cfg cfg' Hpool Hsteps.
    exact (pool_rely_guarantee CT machine_inv mixed_local
      (fun _ S' => machine_inv S')
      mixed_own_step
      (fun S S' _ Hinv' => Hinv')
      (fun e S S' _ Hlocal _ => Hlocal)
      cfg cfg' Hpool Hsteps).
  Qed.

  Theorem machine_mixed_pool_semimm :
    forall cfg cfg',
      mixed_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      Stable (pcsi_object P Stable a A M (pool_state cfg')) a /\
      CacheHistSnapshotOK P (pcsi_snapshot P Stable a A M (pool_state cfg')) a.
  Proof.
    intros cfg cfg' Hpool Hsteps.
    destruct (machine_mixed_pool cfg cfg' Hpool Hsteps) as [[Hstate Hsnap] _].
    split; [exact (pcsi_stable P Stable a A M _ Hstate) | exact Hsnap].
  Qed.

  (** A finished trace robust control meets the result contract, also in a
      mixed pool; clients carry no contract. *)
  Lemma machine_local_result :
    forall r rGamma V S,
      machine_local (CoreDone r rGamma V) S ->
      ResultOK (mkPicoCoreVal r rGamma V).
  Proof.
    intros r rGamma V S (e0 & tr & Hsafe & Hvalid & Hrun).
    destruct (Hsafe tr _ Hrun Hvalid) as [_ Hresult].
    eapply Hresult. reflexivity.
  Qed.
End machine_trace_robust.

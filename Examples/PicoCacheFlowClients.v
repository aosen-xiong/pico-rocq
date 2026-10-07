From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Reachability.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider Examples.PicoCacheMethodJudgment
  Examples.PicoCacheFlowJudgment Examples.PicoCacheClients.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping
  PICOBridge.PicoCoreLanguage PICOBridge.PicoCoreSemImm
  PICOBridge.PicoDerivationNoninterference PICOBridge.PicoDerivationSmallStep
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTraceRobust.

(** * A Class-Table Discipline for the Cache Field

    The client theorem of [PicoCacheClients] assumes of each client that no
    control it reaches writes the cache field.  This file replaces that
    assumption by a syntactic condition on the program.

    A statement is quiet when it contains no write to the cache field and
    no call to the cache method.  The class table is disciplined when the
    body of every method other than the cache method is quiet.  In a
    disciplined class table, every control that starts quiet stays quiet,
    so it never writes the cache field, whatever it calls.

    Hence a pool of calls to a cache method accepted by the flow judgment,
    together with any number of quiet threads, keeps the receiver
    semantically immutable under every interleaving.  Quiet code may read
    the cache field: a read cannot break the invariant, although nothing is
    proved about what the reading thread computes from it.  Quiet code may
    not call the cache method; only the threads of the pool do. *)

Section quiet_code.
  Context (mc : method_name).

  Fixpoint quiet (s : stmt) : Prop :=
    match s with
    | SFldWrite _ f _ => f <> hash_cache_field
    | SCall _ m' _ _ => m' <> mc
    | SSeq s1 s2 => quiet s1 /\ quiet s2
    | SIfZero _ s0 s1 => quiet s0 /\ quiet s1
    | _ => True
    end.

  Definition quiet_frame (fr : pico_core_frame) : Prop :=
    match fr with
    | KSeq s => quiet s
    | KCall _ _ _ => True
    end.

  Definition quiet_control (e : pico_core_expr) : Prop :=
    match e with
    | CoreRun _ s _ K => quiet s /\ Forall quiet_frame K
    | CoreDone _ _ _ => True
    end.

  (** Every method other than the cache method has a quiet body. *)
  Definition quiet_table (CT : class_table) : Prop :=
    forall C m' md,
      FindMethodWithName CT C m' md ->
      m' <> mc ->
      quiet (mbody_stmt (mbody md)).

  Lemma quiet_step :
    forall `{Hmem : CacheMemoryModel} CT e S e' S',
      quiet_table CT ->
      quiet_control e ->
      pico_core_step CT e S e' S' ->
      quiet_control e'.
  Proof.
    intros Hmem CT e S e' S' Htable Hq Hstep.
    inversion Hstep; subst; simpl in *; auto;
      repeat match goal with
             | H : _ /\ _ |- _ => destruct H
             | H : Forall quiet_frame (_ :: _) |- _ =>
                 inversion H; subst; clear H
             end;
      simpl in *; eauto.
    split; [eapply Htable; eassumption | constructor; [exact I | assumption]].
  Qed.
End quiet_code.

Section flow_clients.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table) (D : method_def -> Prop).
  Context (receiver : Loc) (m : method_name) (h0 : heap) (H : nat).
  Context (mc : method_name) (mdef : method_def).
  Context (Trecv : qualified_type) (mt : method_scope).
  Context (rt0 : runtime_type) (fs0 : fields_mapping).

  Let footprint := reachable_abs CT h0 receiver.

  Notation hash_machine := (pico_concrete_hash_semimm CT receiver m h0 H).
  Notation hash_inv :=
    (machine_inv hash_cache_protocol pico_hash_stable_abs H
       (pico_hash_cache_adapter receiver) hash_machine).

  (** The footprint of the receiver is immutable in the reference heap. *)
  Hypothesis Himm : forall l, footprint l ->
    exists C vals,
      runtime_getObj h0 l = Some (mkObj (mkruntime_type Imm_r C) vals).

  (** The class table is disciplined. *)
  Hypothesis Hquiet : quiet_table mc CT.

  Lemma quiet_reach :
    forall e0 e,
      quiet_control mc e0 ->
      inv_reach CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine e0 e ->
      quiet_control mc e.
  Proof.
    intros e0 e Hq Hreach.
    induction Hreach as [| e S e' S' _ IH _ Hstep]; [exact Hq |].
    eapply quiet_step; eassumption.
  Qed.

  (** A quiet control is an admissible client. *)
  Theorem quiet_control_client :
    forall e0,
      quiet_control mc e0 ->
      protocol_client CT hash_cache_protocol pico_hash_stable_abs H
        (pico_hash_cache_adapter receiver) hash_machine e0.
  Proof.
    intros e0 Hq.
    apply (no_direct_cache_write_client CT receiver m h0 H Himm).
    intros e rGamma x f y V K loc Hreach -> _ Heq.
    have Hqe := quiet_reach _ _ Hq Hreach.
    simpl in Hqe. destruct Hqe as [Hf _].
    injection Heq as _ Hfeq. exact (Hf Hfeq).
  Qed.

  (** ** Calls of an accepted cache method alongside quiet threads *)

  (** The cache method is accepted by the flow judgment. *)
  Hypothesis Htable : derivation_table CT D.
  Hypothesis Hwf1 : wf_r_config CT [Trecv] (mkr_env [Iot receiver]) h0.
  Hypothesis Hobj0 : runtime_getObj h0 receiver = Some (mkObj rt0 fs0).
  Hypothesis Hcachefield :
    derived_cache_field CT (rctype rt0) hash_cache_field.
  Hypothesis Hfind : FindMethodWithName CT (rctype rt0) mc mdef.
  Variables (sGbody : s_env) (Gbody : list origin).
  Hypothesis Hflow :
    flow CT D receiver h0 H mt [Trecv] [OThis]
      (mbody_stmt (mbody mdef)) sGbody Gbody.
  Hypothesis Hreturn :
    nth_error Gbody (mreturn (mbody mdef)) = Some ODerived.

  (** A call of the cache method on the receiver, with a slot for its
      result. *)
  Definition cache_call (x : var) (e : pico_core_expr) : Prop :=
    exists caller y V0,
      e = CoreRun caller (SCall x mc y []) V0 [] /\
      runtime_getVal caller y = Some (Iot receiver) /\
      x < dom (vars caller).

  Theorem disciplined_pool_semimm :
    forall x S0 threads cfg,
      hash_inv S0 ->
      Forall (fun e => cache_call x e \/ quiet_control mc e) threads ->
      pico_pool_steps CT (mkPicoPoolConfig S0 threads) cfg ->
      CacheHistSnapshotOK hash_cache_protocol
        (pico_hash_snapshot receiver (pool_state cfg)) H.
  Proof.
    intros x S0 threads cfg Hinv Hthreads Hsteps.
    assert (Hpool : mixed_pool CT hash_cache_protocol pico_hash_stable_abs H
      (pico_hash_cache_adapter receiver) hash_machine
      (cache_call_result_ok H x) (mkPicoPoolConfig S0 threads)).
    { split; [exact Hinv |]. simpl.
      eapply Forall_impl; [| exact Hthreads].
      intros e [(caller & y & V0 & -> & Hy & Hx) | Hq].
      - left. apply machine_local_start.
        exact (flow_cache_method_trace_robust CT D receiver m h0 H mc mdef
          Trecv mt rt0 fs0 caller x y Htable Hwf1 Hobj0 Hcachefield Hfind Hy
          sGbody Gbody Hflow Hreturn Hx V0).
      - right. exists e. split; [| constructor].
        apply quiet_control_client. exact Hq. }
    exact (proj2 (machine_mixed_pool_semimm _ _ _ _ _ _ _ _ _ Hpool Hsteps)).
  Qed.
End flow_clients.

Require Import Syntax Helpers Typing DerivedCache PICOBridge.PicoMemoryModel.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.

From Stdlib Require Import List.
Import ListNotations.

(** * PICO Cache Typing to Semantic Cache Safety

    This file bridges PICO typing-shaped premises to the semantic cache-safety
    layer in [PicoMemoryModel].

    The general bridge captures the common derived-cache update shape:

    [[
      compute;
      receiver.cache_f = tmp
    ]]

    where [compute] is any statement verified to put the nonzero derived value
    in [tmp].  The literal [tmp = EInt n] update shape is a small instance of
    this record. *)

(** [verified_cache_compute] is the method-local proof obligation for the
    computation phase: it is typed, it stores [Int n] in [tmp], and [n] is the
    nonzero derived value for the stable abstract fields. *)
Record verified_cache_compute
    (CT : class_table) (sΓ sΓ_mid : s_env) (mt : method_type)
    (rΓ rΓ_mid : r_env) (compute : stmt) (tmp : var)
    (derived : list value -> nat) (abs_vals : list value) (n : nat) : Prop :=
  mkVerifiedCacheCompute {
    vcc_type_compute :
      stmt_typing CT sΓ mt compute sΓ_mid;
    vcc_tmp_value :
      runtime_getVal rΓ_mid tmp = Some (Int n);
    vcc_derived :
      n = derived abs_vals;
    vcc_nonzero :
      n <> 0
  }.

(** Pure result used by the generic cache protocol for PICO derived integer
    caches. *)
Definition pico_cache_compute_pure_result
    (derived : list value -> nat) (abs_vals : list value) (_ : unit) : value :=
  Int (derived abs_vals).

Definition pico_cache_compute_run
    (derived : list value -> nat)
    (abs_vals : list value) (_ : unit)
    (_ : CacheTrace (derived_cache_protocol derived)) :
    CacheRun (derived_cache_protocol derived) value :=
  let n := derived abs_vals in
  {|
    run_result := Int n;
    run_writes :=
      match n with
      | 0 => []
      | S _ => [derived_cache_obs derived (Int n)]
      end
  |}.

(** The generic trace model for the compute phase is cache-safe: it returns the
    pure result and writes only a valid nonzero derived value when needed. *)
Lemma pico_cache_compute_run_safe :
  forall derived,
    CacheSafeMethod
      (derived_cache_protocol derived)
      (pico_cache_compute_pure_result derived)
      (pico_cache_compute_run derived).
Proof.
  intros derived abs_vals [] tr _.
  unfold pico_cache_compute_run, pico_cache_compute_pure_result.
  split.
  - reflexivity.
  - destruct (derived abs_vals) eqn:Hderived.
    + constructor.
    + constructor.
      * unfold ValidObs, derived_cache_obs, derived_cache_valid; simpl.
        right.
        unfold cache_value_known.
        exists (S n).
        split.
        -- reflexivity.
        -- split.
           ++ symmetry.
              exact Hderived.
           ++ discriminate.
      * constructor.
Qed.

(** The compute phase refines pure recomputation for every valid cache trace. *)
Theorem pico_cache_compute_refines_pure :
  forall derived,
    CacheRefinesPure
      (derived_cache_protocol derived)
      (pico_cache_compute_pure_result derived)
      (pico_cache_compute_run derived).
Proof.
  intros derived.
  apply cache_safe_method_refines_pure.
  apply pico_cache_compute_run_safe.
Qed.

Lemma verified_cache_compute_pure_result :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n
    (Hcompute : verified_cache_compute
      CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n),
    PureRecomputeResult
      (pico_cache_compute_pure_result derived)
      abs_vals
      tt
      (Int n).
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n Hcompute.
  destruct Hcompute as [_ _ Hderived _].
  unfold PureRecomputeResult, pico_cache_compute_pure_result.
  rewrite Hderived.
  reflexivity.
Qed.

Lemma verified_cache_compute_matches_generic_run :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n
         (tr : CacheTrace (derived_cache_protocol derived))
         (Hcompute :
           verified_cache_compute
             CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n),
    weak_exec_matches_trace
      (derived_cache_protocol derived)
      (pico_cache_compute_run derived)
      abs_vals
      tt
      tr
      (Int n).
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n tr Hcompute.
  destruct Hcompute as [_ _ Hderived _].
  unfold weak_exec_matches_trace, pico_cache_compute_run.
  rewrite Hderived.
  reflexivity.
Qed.

Theorem verified_cache_compute_refines_pure_via_generic :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n
         (tr : CacheTrace (derived_cache_protocol derived))
         (Hcompute :
           verified_cache_compute
             CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n)
         (Htrace : ValidTrace (derived_cache_protocol derived) abs_vals tr),
    PureRecomputeResult
      (pico_cache_compute_pure_result derived)
      abs_vals
      tt
      (Int n).
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n tr
         Hcompute Htrace.
  eapply pico_cache_compute_refines_pure.
  - exact Htrace.
  - eapply verified_cache_compute_matches_generic_run.
    exact Hcompute.
Qed.

(** [cache_compute_write_safe] adds the cache-write tail: after a verified
    compute phase, [receiver.cache_f = tmp] is typed and the receiver is the
    target object location. *)
Record cache_compute_write_safe
    (CT : class_table) (sΓ sΓ_mid : s_env) (mt : method_type)
    (rΓ rΓ_mid : r_env) (loc : Loc) (cache_f receiver tmp : var)
    (compute : stmt)
    (derived : list value -> nat) (abs_vals : list value) (n : nat) : Prop :=
  mkCacheComputeWriteSafe {
    ccws_compute :
      verified_cache_compute
        CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n;
    ccws_type_write :
      stmt_typing CT sΓ_mid mt (SFldWrite receiver cache_f tmp) sΓ_mid;
    ccws_receiver_value :
      runtime_getVal rΓ_mid receiver = Some (Iot loc)
  }.

(** The typing-shaped compute/write premise inherits pure recomputation
    refinement from the generic trace-robust method theorem. *)
Theorem cache_compute_write_safe_refines_pure_via_generic :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n
         (tr : CacheTrace (derived_cache_protocol derived))
         (Hsafe : cache_compute_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n)
         (Htrace : ValidTrace (derived_cache_protocol derived) abs_vals tr),
    PureRecomputeResult
      (pico_cache_compute_pure_result derived)
      abs_vals
      tt
      (Int n).
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n tr Hsafe Htrace.
  destruct Hsafe as [Hcompute _ _].
  eapply verified_cache_compute_refines_pure_via_generic; eauto.
Qed.

(** The write tail is syntactically cache-safe: it writes the verified nonzero
    derived value to the target cache field. *)
Theorem cache_compute_write_safe_implies_cache_safe_tail :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n
         (Hsafe : cache_compute_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n),
    cache_safe_stmt
      rΓ_mid
      (loc, cache_f)
      derived
      abs_vals
      (SFldWrite receiver cache_f tmp).
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n Hsafe.
  destruct Hsafe as
    [[_ Htmp Hderived Hnz] _ Hreceiver].
  eapply cache_safe_fldwrite_target_known; eauto.
Qed.

Theorem cache_compute_write_safe_implies_cache_safe_thread_tail :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n V
         (Hsafe : cache_compute_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n),
    cache_safe_thread
      (mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V)
      (loc, cache_f)
      derived
      abs_vals.
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n V Hsafe.
  unfold cache_safe_thread.
  eapply cache_compute_write_safe_implies_cache_safe_tail; eauto.
Qed.

(** Whole [compute; write] proof package.  The compute phase and the write
    phase are both cache-safe statements, and the write phase is tied to the
    verified compute result. *)
Record cache_compute_then_write_safe
    (CT : class_table) (sΓ sΓ_mid : s_env) (mt : method_type)
    (rΓ rΓ_mid : r_env) (loc : Loc) (cache_f receiver tmp : var)
    (compute : stmt)
    (derived : list value -> nat) (abs_vals : list value) (n : nat) : Prop :=
  mkCacheComputeThenWriteSafe {
    cctws_compute_write :
      cache_compute_write_safe
        CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals n;
    cctws_compute_stmt_safe :
      cache_safe_stmt rΓ (loc, cache_f) derived abs_vals compute;
    cctws_write_stmt_safe :
      cache_safe_stmt
        rΓ_mid
        (loc, cache_f)
        derived
        abs_vals
        (SFldWrite receiver cache_f tmp)
  }.

(** Build the whole-statement package from a verified compute/write tail plus a
    cache-safety proof for the compute phase itself. *)
Theorem cache_compute_write_safe_implies_compute_then_write_safe :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n
         (Hsafe : cache_compute_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n)
         (Hcompute_safe :
           cache_safe_stmt rΓ (loc, cache_f) derived abs_vals compute),
    cache_compute_then_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n.
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n Hsafe Hcompute_safe.
  constructor.
  - exact Hsafe.
  - exact Hcompute_safe.
  - eapply cache_compute_write_safe_implies_cache_safe_tail; eauto.
Qed.

Definition cache_compute_then_write_stmt
    (compute : stmt) (receiver cache_f tmp : var) : stmt :=
  SSeq compute (SFldWrite receiver cache_f tmp).

(** Phase-level statement that both halves of [compute; write] are cache-safe. *)
Definition cache_compute_then_write_phases_safe
    (rΓ rΓ_mid : r_env) (addr : FieldAddr)
    (receiver cache_f tmp : var) (compute : stmt)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  cache_safe_stmt rΓ addr derived abs_vals compute /\
  cache_safe_stmt
    rΓ_mid
    addr
    derived
    abs_vals
    (SFldWrite receiver cache_f tmp).

(** The whole-statement package exposes exactly the two cache-safe phases. *)
Theorem cache_compute_then_write_safe_implies_cache_safe_phases :
  forall CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n
         (Hsafe : cache_compute_then_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n),
    cache_compute_then_write_phases_safe
      rΓ
      rΓ_mid
      (loc, cache_f)
      receiver
      cache_f
      tmp
      compute
      derived
      abs_vals.
Proof.
  intros CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n Hsafe.
  destruct Hsafe as [_ Hcompute Hwrite].
  split; assumption.
Qed.

(** Same-environment specialization: when the compute and write environments
    coincide, the full sequence is a [cache_safe_stmt]. *)
Theorem cache_compute_then_write_safe_implies_cache_safe_stmt_same_env :
  forall CT sΓ sΓ_mid mt rΓ loc cache_f receiver tmp compute
         derived abs_vals n
         (Hsafe : cache_compute_then_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ loc cache_f receiver tmp compute
      derived abs_vals n),
    cache_safe_stmt
      rΓ
      (loc, cache_f)
      derived
      abs_vals
      (cache_compute_then_write_stmt compute receiver cache_f tmp).
Proof.
  intros CT sΓ sΓ_mid mt rΓ loc cache_f receiver tmp compute
         derived abs_vals n Hsafe.
  destruct
    (cache_compute_then_write_safe_implies_cache_safe_phases
      CT sΓ sΓ_mid mt rΓ rΓ loc cache_f receiver tmp compute
      derived abs_vals n Hsafe) as [Hcompute Hwrite].
  unfold cache_compute_then_write_stmt.
  apply cache_safe_seq; assumption.
Qed.

(** Existential wrapper for a thread whose residual statement is exactly the
    verified cache-write tail.  This lets lists of such threads imply
    config-level cache safety. *)
Definition cache_compute_write_safe_tail_thread
    (addr : FieldAddr) (derived : list value -> nat)
    (abs_vals : list value) (t : wm_thread) : Prop :=
  exists CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute n V,
    addr = (loc, cache_f) /\
    t = mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V /\
    cache_compute_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n.

(** Tail-thread wrappers imply actual [cache_safe_thread] facts. *)
Theorem cache_compute_write_safe_tail_thread_implies_cache_safe_thread :
  forall addr derived abs_vals t
    (Htail : cache_compute_write_safe_tail_thread addr derived abs_vals t),
    cache_safe_thread t addr derived abs_vals.
Proof.
  intros addr derived abs_vals t Htail.
  destruct Htail as
    [CT [sΓ [sΓ_mid [mt [rΓ [rΓ_mid [loc [cache_f [receiver [tmp Htail]]]]]]]]]].
  destruct Htail as [compute [n [V [Haddr [Ht Hsafe]]]]].
  subst addr t.
  eapply cache_compute_write_safe_implies_cache_safe_thread_tail; eauto.
Qed.

(** A pool of verified cache-write-tail threads forms a [cache_safe_config]. *)
Theorem cache_compute_write_safe_tail_threads_imply_cache_safe_config :
  forall sigma threads addr derived abs_vals
    (Hthreads : Forall
      (cache_compute_write_safe_tail_thread addr derived abs_vals)
      threads),
    cache_safe_config
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals.
Proof.
  intros sigma threads addr derived abs_vals Hthreads.
  unfold cache_safe_config.
  induction Hthreads as [|t ts Ht Hts IH].
  - constructor.
  - constructor.
    + apply cache_compute_write_safe_tail_thread_implies_cache_safe_thread.
      exact Ht.
    + exact IH.
Qed.

Theorem cache_compute_write_safe_tail_threads_semantic_cache_safe :
  forall `{CacheMemoryModel} CT sigma threads addr derived abs_vals
    (Hthreads : Forall
      (cache_compute_write_safe_tail_thread addr derived abs_vals)
      threads),
    wm_semantic_cache_safe_under
      CT
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals
      (fun cfg => cache_safe_config cfg addr derived abs_vals).
Proof.
  intros Hmem CT sigma threads addr derived abs_vals _.
  apply cache_safe_config_semantic_cache_safe.
Qed.

Theorem cache_compute_write_safe_semantic_cache_safe_tail :
  forall `{CacheMemoryModel}
         CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n V sigma
         (Hsafe : cache_compute_write_safe
      CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals n),
    wm_semantic_cache_safe_under
      CT
      (mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V])
      (loc, cache_f)
      derived
      abs_vals
      (fun cfg => cache_safe_config cfg (loc, cache_f) derived abs_vals).
Proof.
  intros Hmem CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
         derived abs_vals n V sigma Hsafe.
  apply cache_safe_config_semantic_cache_safe.
Qed.

(** ** Literal Cache-Update Sequence Instance *)

(** The concrete legacy update sequence assigns a literal derived value into a
    temporary variable and then writes that temporary into the receiver cache
    field. *)
Definition cache_update_sequence_stmt
    (tmp receiver cache_f : var) (n : nat) : stmt :=
  SSeq (SVarAss tmp (EInt n)) (SFldWrite receiver cache_f tmp).

(** Proof obligations for the literal [tmp = EInt n; receiver.cache = tmp]
    instance of the general compute/write bridge. *)
Record cache_update_sequence_safe
    (CT : class_table) (sΓ : s_env) (mt : method_type)
    (rΓ : r_env) (loc : Loc) (cache_f receiver tmp : var)
    (derived : list value -> nat) (abs_vals : list value) (n : nat) : Prop :=
  mkCacheUpdateSequenceSafe {
    cuss_type_compute :
      stmt_typing CT sΓ mt (SVarAss tmp (EInt n)) sΓ;
    cuss_type_write :
      stmt_typing CT sΓ mt (SFldWrite receiver cache_f tmp) sΓ;
    cuss_receiver_tmp_distinct :
      receiver <> tmp;
    cuss_receiver_value :
      runtime_getVal rΓ receiver = Some (Iot loc);
    cuss_tmp_in_dom :
      tmp < dom (vars rΓ);
    cuss_derived :
      n = derived abs_vals;
    cuss_nonzero :
      n <> 0
  }.

(** Literal update sequences are syntactically cache-safe at the write tail. *)
Theorem cache_update_sequence_safe_implies_cache_safe_tail :
  forall CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n
    (Hsafe :
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n),
    cache_safe_stmt
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      (loc, cache_f)
      derived
      abs_vals
      (SFldWrite receiver cache_f tmp).
Proof.
  intros CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe.
  destruct Hsafe as
    [_ _ Hneq Hreceiver Htmp_dom Hderived Hnz].
  eapply cache_safe_fldwrite_target_after_assign_int; eauto.
Qed.

(** Literal update sequences are instances of [cache_compute_write_safe]. *)
Theorem cache_update_sequence_safe_implies_cache_compute_write_safe :
  forall CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n
    (Hsafe :
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n),
    cache_compute_write_safe
      CT
      sΓ
      sΓ
      mt
      rΓ
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      loc
      cache_f
      receiver
      tmp
      (SVarAss tmp (EInt n))
      derived
      abs_vals
      n.
Proof.
  intros CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe.
  destruct Hsafe as
    [Htype_compute Htype_write Hneq Hreceiver Htmp_dom Hderived Hnz].
  constructor.
  - constructor.
    + exact Htype_compute.
    + apply runtime_getVal_set_vars_update_same.
      exact Htmp_dom.
    + exact Hderived.
    + exact Hnz.
  - exact Htype_write.
  - rewrite runtime_getVal_set_vars_update_diff; eauto.
Qed.

(** Therefore literal update sequences refine pure recomputation by the generic
    cache-safe-method theorem. *)
Theorem cache_update_sequence_safe_refines_pure_via_generic :
  forall CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n
         (tr : CacheTrace (derived_cache_protocol derived))
         (Hsafe :
           cache_update_sequence_safe
             CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n)
         (Htrace : ValidTrace (derived_cache_protocol derived) abs_vals tr),
    PureRecomputeResult
      (pico_cache_compute_pure_result derived)
      abs_vals
      tt
      (Int n).
Proof.
  intros CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n tr
         Hsafe Htrace.
  eapply
    (cache_compute_write_safe_refines_pure_via_generic
      CT
      sΓ
      sΓ
      mt
      rΓ
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      loc
      cache_f
      receiver
      tmp
      (SVarAss tmp (EInt n))
      derived
      abs_vals
      n
      tr).
  - apply cache_update_sequence_safe_implies_cache_compute_write_safe.
    exact Hsafe.
  - exact Htrace.
Qed.

Theorem cache_update_sequence_safe_implies_compute_then_write_safe :
  forall CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n
    (Hsafe :
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n),
    cache_compute_then_write_safe
      CT
      sΓ
      sΓ
      mt
      rΓ
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      loc
      cache_f
      receiver
      tmp
      (SVarAss tmp (EInt n))
      derived
      abs_vals
      n.
Proof.
  intros CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe.
  apply cache_compute_write_safe_implies_compute_then_write_safe.
  - apply cache_update_sequence_safe_implies_cache_compute_write_safe.
    exact Hsafe.
  - constructor.
Qed.

Theorem cache_update_sequence_safe_implies_cache_safe_phases :
  forall CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n
    (Hsafe :
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n),
    cache_compute_then_write_phases_safe
      rΓ
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      (loc, cache_f)
      receiver
      cache_f
      tmp
      (SVarAss tmp (EInt n))
      derived
      abs_vals.
Proof.
  intros CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe.
  eapply cache_compute_then_write_safe_implies_cache_safe_phases.
  apply cache_update_sequence_safe_implies_compute_then_write_safe.
  exact Hsafe.
Qed.

Theorem cache_update_sequence_safe_implies_cache_safe_thread_tail :
  forall CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
    (Hsafe :
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n),
    cache_safe_thread
      (mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V)
      (loc, cache_f)
      derived
      abs_vals.
Proof.
  intros CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V Hsafe.
  unfold cache_safe_thread.
  eapply cache_update_sequence_safe_implies_cache_safe_tail; eauto.
Qed.

Theorem cache_update_sequence_safe_semantic_cache_safe_tail :
  forall `{CacheMemoryModel}
         CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma
         (Hsafe :
           cache_update_sequence_safe
             CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n),
    wm_semantic_cache_safe_under
      CT
      (mkWMConfig
        sigma
        [mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V])
      (loc, cache_f)
      derived
      abs_vals
      (fun cfg => cache_safe_config cfg (loc, cache_f) derived abs_vals).
Proof.
  intros Hmem CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma
         Hsafe.
  apply cache_safe_config_semantic_cache_safe.
Qed.

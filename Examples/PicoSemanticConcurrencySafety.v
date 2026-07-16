From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep DerivedCache
  Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCacheExamples
  Examples.PicoSemanticCacheAPIExamples
  Examples.PicoConcreteHashModel
  Examples.PicoSemanticConcurrencyExamples.
Require Import PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoIrisSemImmLogicalRelation
  PICOBridge.PicoSemanticConcurrency.

(** * Universal Safety of the Two-Invocation Hash Pool

    The existential schedule in [PicoSemanticConcurrencyExamples] witnesses
    the race.  This file proves the universal half: every scheduler
    interleaving of the same two controls remains inside the finite protocol
    below.  The protocol records CESK control, not a new source construct. *)

Definition pico_hash_env1 : r_env := mkr_env [Iot 0].
Definition pico_hash_env2 : r_env := mkr_env [Iot 0; Int 0].
Definition pico_hash_env3 : r_env := mkr_env [Iot 0; Int 0; Int 0].
Definition pico_hash_env7 : r_env := mkr_env [Iot 0; Int 7; Int 0].
Definition pico_hash_env_done : r_env := mkr_env [Iot 0; Int 7; Int 7].
Definition pico_hash_caller_done : r_env := mkr_env [Iot 0; Int 7].

Definition pico_hash_outer_tail : stmt :=
  SSeq (SLocal int_type cache_result)
    (pico_hash_method_core_stmt pico_hash_concurrent_value).

Definition pico_hash_final_stmt : stmt :=
  SVarAss cache_result (EVar cache_tmp).

Definition pico_hash_branch_stmt : stmt :=
  pico_local_copy_cache_branch
    (pico_hash_compute_stmt pico_hash_concurrent_value).

Definition pico_hash_miss_stmt : stmt :=
  SSeq (pico_hash_compute_stmt pico_hash_concurrent_value)
    (SFldWrite cache_receiver hash_cache_field cache_tmp).

Inductive pico_hash_phase : Type :=
  | HashCall
  | HashMethod
  | HashLocalTmp
  | HashAfterLocalTmp
  | HashLocalResultSeq
  | HashLocalResult
  | HashAfterLocalResult
  | HashCore
  | HashRead
  | HashReadZeroDone
  | HashReadHitDone
  | HashAfterReadZero
  | HashAfterReadHit
  | HashBranchZero
  | HashBranchHit
  | HashMissSeq
  | HashCompute
  | HashAfterCompute
  | HashWrite
  | HashAfterWrite
  | HashHitSkip
  | HashFinal
  | HashAfterFinal
  | HashCallerResume
  | HashDone.

Definition pico_hash_phase_control (phase : pico_hash_phase) :
    pico_core_expr :=
  match phase with
  | HashCall =>
      pico_invocation_control (pico_hash_concurrent_invocation 0)
  | HashMethod =>
      CoreRun pico_hash_env1
        (pico_hash_method_stmt pico_hash_concurrent_value) 0
        pico_hash_concurrent_call_cont
  | HashLocalTmp =>
      CoreRun pico_hash_env1 (SLocal int_type cache_tmp) 0
        (KSeq pico_hash_outer_tail :: pico_hash_concurrent_call_cont)
  | HashAfterLocalTmp =>
      CoreRun pico_hash_env2 SSkip 0
        (KSeq pico_hash_outer_tail :: pico_hash_concurrent_call_cont)
  | HashLocalResultSeq =>
      CoreRun pico_hash_env2 pico_hash_outer_tail 0
        pico_hash_concurrent_call_cont
  | HashLocalResult =>
      CoreRun pico_hash_env2 (SLocal int_type cache_result) 0
        (KSeq (pico_hash_method_core_stmt pico_hash_concurrent_value) ::
          pico_hash_concurrent_call_cont)
  | HashAfterLocalResult =>
      CoreRun pico_hash_env3 SSkip 0
        (KSeq (pico_hash_method_core_stmt pico_hash_concurrent_value) ::
          pico_hash_concurrent_call_cont)
  | HashCore =>
      CoreRun pico_hash_env3
        (pico_hash_method_core_stmt pico_hash_concurrent_value) 0
        pico_hash_concurrent_call_cont
  | HashRead => pico_hash_concurrent_read_control
  | HashReadZeroDone => pico_hash_concurrent_after_read_control
  | HashReadHitDone =>
      CoreRun pico_hash_env7 SSkip 0 pico_hash_concurrent_read_cont
  | HashAfterReadZero =>
      CoreRun pico_hash_env3 pico_hash_concurrent_after_read_stmt 0
        pico_hash_concurrent_call_cont
  | HashAfterReadHit =>
      CoreRun pico_hash_env7 pico_hash_concurrent_after_read_stmt 0
        pico_hash_concurrent_call_cont
  | HashBranchZero =>
      CoreRun pico_hash_env3 pico_hash_branch_stmt 0
        pico_hash_concurrent_write_cont
  | HashBranchHit =>
      CoreRun pico_hash_env7 pico_hash_branch_stmt 0
        pico_hash_concurrent_write_cont
  | HashMissSeq =>
      CoreRun pico_hash_env3 pico_hash_miss_stmt 0
        pico_hash_concurrent_write_cont
  | HashCompute =>
      CoreRun pico_hash_env3
        (pico_hash_compute_stmt pico_hash_concurrent_value) 0
        (KSeq (SFldWrite cache_receiver hash_cache_field cache_tmp) ::
          pico_hash_concurrent_write_cont)
  | HashAfterCompute =>
      CoreRun pico_hash_env7 SSkip 0
        (KSeq (SFldWrite cache_receiver hash_cache_field cache_tmp) ::
          pico_hash_concurrent_write_cont)
  | HashWrite => pico_hash_concurrent_write_control
  | HashAfterWrite => pico_hash_concurrent_after_write_control
  | HashHitSkip =>
      CoreRun pico_hash_env7 SSkip 0 pico_hash_concurrent_write_cont
  | HashFinal =>
      CoreRun pico_hash_env7 pico_hash_final_stmt 0
        pico_hash_concurrent_call_cont
  | HashAfterFinal =>
      CoreRun pico_hash_env_done SSkip 0 pico_hash_concurrent_call_cont
  | HashCallerResume =>
      CoreRun pico_hash_caller_done SSkip 0 []
  | HashDone => CoreDone OK pico_hash_caller_done 0
  end.

Definition pico_hash_thread_safe (control : pico_core_expr) : Prop :=
  exists phase, control = pico_hash_phase_control phase.

Definition pico_hash_pool_inv (cfg : pico_pool_config) : Prop :=
  pico_hash_provider_inv pico_hash_concurrent_CT 0
    pico_hash_witness_function pico_hash_concurrent_value
    (pool_state cfg) /\
  Forall pico_hash_thread_safe (pool_threads cfg).

Lemma pico_hash_initial_history_read_shape :
  forall state V v V',
    pico_hash_provider_inv pico_hash_concurrent_CT 0
      pico_hash_witness_function pico_hash_concurrent_value state ->
    @wm_read history_cache_memory_model (pcs_weak state) V
      (0, hash_cache_field) v V' ->
    v = Int 0 \/ v = Int pico_hash_concurrent_value.
Proof.
  intros state V v V' (_ & _ & Hhist) Hread.
  destruct (wm_read_from_history _ _ _ _ _ Hread) as
    [msg [Hin Hvalue]].
  assert (Hin_value : List.In v
    (values_written_to (pcs_weak state) (0, hash_cache_field))).
  { unfold values_written_to. apply in_map_iff.
    exists msg. split.
    - exact Hvalue.
    - exact Hin. }
  specialize (Hhist HashField v Hin_value).
  unfold hash_cache_valid in Hhist.
  destruct Hhist as [Hzero | [Hhash _]]; auto.
Qed.

Lemma pico_hash_initial_pool_inv :
  pico_hash_pool_inv pico_hash_concurrent_initial_pool.
Proof.
  split; [exact pico_hash_concurrent_initial_provider_inv |].
  repeat constructor.
  - exists HashCall. reflexivity.
  - exists HashCall. reflexivity.
Qed.

Lemma pico_hash_concurrent_cache_owner_unique : forall C,
  derived_cache_field pico_hash_concurrent_CT C hash_cache_field ->
  C = pico_hash_witness_class.
Proof.
  intros C Hcache.
  unfold derived_cache_field, cache_field, sf_assignability_rel in Hcache.
  destruct Hcache as [fdef [Hlookup _]].
  inversion Hlookup as [CT C0 fields f fdef0 Hcollect Hget]; subst.
  destruct C as [|[|C]].
  - assert (Hroot : CollectFields pico_hash_concurrent_CT 0 []).
    { eapply CF_Object with (def := pico_hash_witness_root_def); reflexivity. }
    pose proof (collect_fields_deterministic_rel _ _ _ _ Hcollect Hroot)
      as ->. simpl in Hget. discriminate.
  - reflexivity.
  - assert (Hnone : find_class pico_hash_concurrent_CT (S (S C)) = None).
    { unfold pico_hash_concurrent_CT, find_class, gget. simpl.
      rewrite nth_error_nil. reflexivity. }
    assert (Hmissing : CollectFields pico_hash_concurrent_CT (S (S C)) []).
    { apply CF_NotFound. exact Hnone. }
    pose proof (collect_fields_deterministic_rel _ _ _ _ Hcollect Hmissing)
      as ->. simpl in Hget. discriminate.
Qed.

Lemma pico_hash_concurrent_field_assignability_unique : forall C a,
  sf_assignability_rel pico_hash_concurrent_CT C hash_cache_field a ->
  C = pico_hash_witness_class /\ a = Assignable.
Proof.
  intros C a Hassign.
  assert (Howner : C = pico_hash_witness_class).
  { unfold sf_assignability_rel in Hassign.
    destruct Hassign as [fdef [Hlookup Hqual]].
    inversion Hlookup as [CT C0 fields f fdef0 Hcollect Hget]; subst.
    destruct C as [|[|C]].
    - assert (Hroot : CollectFields pico_hash_concurrent_CT 0 []).
      { eapply CF_Object with (def := pico_hash_witness_root_def);
          reflexivity. }
      pose proof (collect_fields_deterministic_rel _ _ _ _ Hcollect Hroot)
        as ->. simpl in Hget. discriminate.
    - reflexivity.
    - assert (Hnone : find_class pico_hash_concurrent_CT (S (S C)) = None).
      { unfold pico_hash_concurrent_CT, find_class, gget. simpl.
        rewrite nth_error_nil. reflexivity. }
      assert (Hmissing : CollectFields pico_hash_concurrent_CT (S (S C)) []).
      { apply CF_NotFound. exact Hnone. }
      pose proof (collect_fields_deterministic_rel _ _ _ _ Hcollect Hmissing)
        as ->. simpl in Hget. discriminate. }
  subst C. split; [reflexivity |].
  eapply sf_assignability_deterministic_rel;
    [exact Hassign | exact pico_hash_concurrent_cache_assignable].
Qed.

Lemma pico_hash_provider_receiver_class : forall state,
  pico_hash_provider_inv pico_hash_concurrent_CT 0
    pico_hash_witness_function pico_hash_concurrent_value state ->
  r_basetype (pcs_heap state) 0 = Some pico_hash_witness_class.
Proof.
  intros [h sigma] [Hagree [Hrepr Hhist]].
  destruct Hrepr as
    [o [cache_value [abstract_values [rt
      [Hobj [Hfields [Hhash [Htype Hdecl]]]]]]]].
  destruct Hagree as [_ Htypes].
  pose proof (Htypes 0 o Hobj) as Htype_object.
  rewrite Htype in Htype_object. inversion Htype_object; subst rt.
  pose proof (pico_hash_concurrent_cache_owner_unique _ Hdecl) as Hclass.
  unfold r_basetype. rewrite Hobj. simpl. rewrite Hclass. reflexivity.
Qed.

Theorem pico_hash_phase_step_preserves :
  forall phase state control' state',
    pico_hash_provider_inv pico_hash_concurrent_CT 0
      pico_hash_witness_function pico_hash_concurrent_value state ->
    @pico_core_step history_cache_memory_model pico_hash_concurrent_CT
      (pico_hash_phase_control phase) state control' state' ->
    pico_hash_provider_inv pico_hash_concurrent_CT 0
      pico_hash_witness_function pico_hash_concurrent_value state' /\
    pico_hash_thread_safe control'.
Proof.
  intros phase state control' state' Hinv Hstep.
  destruct phase; simpl in Hstep.
  - inversion Hstep; subst.
    + assert (Hmdef : mdef = pico_hash_concurrent_method_def).
      { assert (HC : C = pico_hash_witness_class).
        { pose proof (pico_hash_provider_receiver_class _ Hinv) as Hbase.
          simpl in H6. inversion H6; subst loc_y.
          rewrite Hbase in H10. inversion H10. reflexivity. }
        subst C.
        eapply find_method_with_name_deterministic;
          [exact H11 | exact pico_hash_concurrent_find_method]. }
      subst mdef. simpl in H6, H15.
      inversion H6; subst loc_y. inversion H15; subst vals.
      simpl in *.
      split; [exact Hinv | exists HashMethod; reflexivity].
    + match goal with
      | Hnull : runtime_getVal pico_hash_concurrent_caller 0 = Some Null_a |- _ =>
          simpl in Hnull; discriminate
      end.
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashLocalTmp; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashAfterLocalTmp; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashLocalResultSeq; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashLocalResult; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashAfterLocalResult; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashCore; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashRead; reflexivity].
  - inversion Hstep; subst.
    + simpl in H9. inversion H9; subst loc_y.
      pose proof (pico_hash_initial_history_read_shape
        (mkPicoCoreState h sigma) 0 v V' Hinv H10) as Hshape.
      destruct H10 as [Hview _]. subst V'.
      destruct Hshape as [-> | ->].
      * split; [exact Hinv | exists HashReadZeroDone; reflexivity].
      * split; [exact Hinv |]. exists HashReadHitDone.
        unfold pico_hash_phase_control, pico_hash_env7,
          pico_hash_concurrent_method_env, set_vars, cache_tmp.
        reflexivity.
    + match goal with
      | Hnull : runtime_getVal pico_hash_concurrent_method_env
          cache_receiver = Some Null_a |- _ =>
          unfold pico_hash_concurrent_method_env, cache_receiver in Hnull;
          simpl in Hnull; discriminate
      end.
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashAfterReadZero; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashAfterReadHit; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashBranchZero; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashBranchHit; reflexivity].
  - inversion Hstep; subst; simpl in *; try discriminate.
    split; [exact Hinv | exists HashMissSeq; reflexivity].
  - inversion Hstep; subst; simpl in *; try discriminate.
    split; [exact Hinv | exists HashHitSkip; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashCompute; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashAfterCompute; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashWrite; reflexivity].
  - inversion Hstep; subst.
    + unfold pico_hash_concurrent_hash_env,
        pico_hash_concurrent_method_env, cache_receiver, cache_tmp,
        set_vars in H5, H11.
      simpl in H5, H11. inversion H5; subst loc_x.
      inversion H11; subst val_y.
      pose proof H14 as Hwrite.
      destruct H14 as [_ Hview]. subst V'.
      split.
      *
        eapply pico_hash_concurrent_valid_write_preserves_provider;
          eauto.
      * exists HashAfterWrite. reflexivity.
    + match goal with
      | Hnull : runtime_getVal pico_hash_concurrent_hash_env
          cache_receiver = Some Null_a |- _ =>
          unfold pico_hash_concurrent_hash_env,
            pico_hash_concurrent_method_env, cache_receiver, cache_tmp,
            set_vars in Hnull; simpl in Hnull; discriminate
      end.
    + unfold pico_hash_concurrent_hash_env,
        pico_hash_concurrent_method_env, cache_receiver, cache_tmp,
        set_vars in *; simpl in *.
      destruct (pico_hash_concurrent_field_assignability_unique _ _ H10)
        as [_ ->]. unfold runtime_vpa_assignability in H12.
      destruct (rqtype (rt_type o)); discriminate.
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashFinal; reflexivity].
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashFinal; reflexivity].
  - inversion Hstep; subst.
    unfold pico_hash_env7, cache_tmp in H8. simpl in H8.
    inversion H8; subst val_y.
    split; [exact Hinv |]. exists HashAfterFinal.
    unfold pico_hash_phase_control, pico_hash_env_done,
      pico_hash_env7, cache_result, set_vars. reflexivity.
  - inversion Hstep; subst.
    unfold pico_hash_env_done, cache_result in H8. simpl in H8.
    inversion H8; subst retval.
    split; [exact Hinv |]. exists HashCallerResume.
    unfold pico_hash_phase_control, pico_hash_caller_done,
      pico_hash_concurrent_caller, set_vars. reflexivity.
  - inversion Hstep; subst.
    split; [exact Hinv | exists HashDone; reflexivity].
  - inversion Hstep.
Qed.

Lemma Forall_update_existing : forall {A : Type} (P : A -> Prop)
    xs tid old new,
  Forall P xs ->
  nth_error xs tid = Some old ->
  P new ->
  Forall P (update tid new xs).
Proof.
  intros A P xs.
  induction xs as [|head tail IH]; intros [|tid] old new Hall Hnth Hnew;
    inversion Hall; simpl in Hnth; try discriminate; simpl.
  - constructor; assumption.
  - constructor; [assumption |].
    eapply IH; eauto.
Qed.

Theorem pico_hash_pool_step_preserves_inv : forall cfg cfg',
  @pico_pool_step history_cache_memory_model pico_hash_concurrent_CT
    cfg cfg' ->
  pico_hash_pool_inv cfg ->
  pico_hash_pool_inv cfg'.
Proof.
  intros cfg cfg' Hpool [Hstate Hthreads].
  inversion Hpool; subst; simpl in *.
  assert (Hselected : pico_hash_thread_safe e).
  { eapply Forall_nth_error; eauto. }
  destruct Hselected as [phase Heq]. subst e.
  destruct (pico_hash_phase_step_preserves phase state e' state'
    Hstate H0) as [Hstate' Hsafe'].
  split; [exact Hstate' |].
  eapply Forall_update_existing; eauto.
Qed.

Lemma pico_hash_pool_steps_preserve_inv_from : forall cfg cfg',
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    cfg cfg' ->
  pico_hash_pool_inv cfg ->
  pico_hash_pool_inv cfg'.
Proof.
  intros cfg cfg' Hsteps Hinitial.
  induction Hsteps.
  - exact Hinitial.
  - apply IHHsteps.
    eapply pico_hash_pool_step_preserves_inv; eauto.
Qed.

Theorem pico_hash_pool_steps_preserve_inv : forall cfg,
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    pico_hash_concurrent_initial_pool cfg ->
  pico_hash_pool_inv cfg.
Proof.
  intros cfg Hsteps.
  eapply pico_hash_pool_steps_preserve_inv_from;
    [exact Hsteps | exact pico_hash_initial_pool_inv].
Qed.

Definition pico_hash_result_ok (result : pico_core_val) : Prop :=
  pcv_result result = OK /\
  runtime_getVal (pcv_env result) 1 =
    Some (Int pico_hash_concurrent_value).

Lemma pico_hash_safe_done_result : forall result rGamma V,
  pico_hash_thread_safe (CoreDone result rGamma V) ->
  result = OK /\
  runtime_getVal rGamma 1 = Some (Int pico_hash_concurrent_value).
Proof.
  intros result rGamma V [phase Heq].
  destruct phase; simpl in Heq; try discriminate.
  inversion Heq; subst.
  unfold pico_hash_caller_done, pico_hash_concurrent_value,
    runtime_getVal. simpl. split; reflexivity.
Qed.

Lemma pico_hash_finished_threads_results : forall threads,
  Forall pico_hash_thread_safe threads ->
  Forall
    (fun control => exists result rGamma V,
      control = CoreDone result rGamma V) threads ->
  Forall pico_hash_result_ok
    (fold_right
      (fun control results =>
        match pico_core_to_val control with
        | Some result => result :: results
        | None => results
        end)
      [] threads).
Proof.
  intros threads Hsafe Hfinished.
  induction Hsafe as [|control threads Hcontrol Hsafe IH].
  - constructor.
  - inversion Hfinished as [|control0 threads0 Hdone Htail]; subst.
    destruct Hdone as [result [rGamma [V ->]]].
    simpl. constructor.
    + unfold pico_hash_result_ok. simpl.
      exact (pico_hash_safe_done_result result rGamma V Hcontrol).
    + apply IH. exact Htail.
Qed.

Theorem pico_hash_pool_results_correct : forall cfg,
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    pico_hash_concurrent_initial_pool cfg ->
  pico_pool_results_satisfy pico_hash_result_ok cfg.
Proof.
  intros cfg Hsteps Hfinished.
  pose proof (pico_hash_pool_steps_preserve_inv cfg Hsteps) as [_ Hsafe].
  unfold pico_pool_results.
  eapply pico_hash_finished_threads_results; eauto.
Qed.

Theorem pico_two_hash_invocations_benign_race :
  @pico_semantic_benign_race history_cache_memory_model
    pico_hash_concurrent_CT pico_hash_concurrent_initial_pool
    (pico_hash_provider_inv pico_hash_concurrent_CT 0
      pico_hash_witness_function pico_hash_concurrent_value)
    pico_hash_result_ok.
Proof.
  split; [exact pico_two_hash_invocations_exhibit_race |].
  split.
  - intros cfg Hsteps.
    exact (proj1 (pico_hash_pool_steps_preserve_inv cfg Hsteps)).
  - intros cfg Hsteps.
    exact (pico_hash_pool_results_correct cfg Hsteps).
Qed.

(** The invariant above is definitionally the state interpretation supplied
    by the concrete [PicoCoreSemImmInstantiation].  This spelling exposes the
    connection to the Iris [SemImmI] provider without changing the pure pool
    semantics or claiming Java/JMM adequacy. *)
Theorem pico_two_hash_invocations_semimm_benign_race :
  @pico_semantic_benign_race history_cache_memory_model
    pico_hash_concurrent_CT pico_hash_concurrent_initial_pool
    (@pcsi_state_inv pico_hash_concurrent_CT nat nat hash_cache_protocol
      pico_hash_stable_abs pico_hash_concurrent_value
      (pico_hash_cache_adapter 0)
      (pico_concrete_hash_semimm pico_hash_concurrent_CT 0
        pico_hash_witness_function pico_hash_concurrent_value))
    pico_hash_result_ok.
Proof.
  exact pico_two_hash_invocations_benign_race.
Qed.

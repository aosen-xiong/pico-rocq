From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Examples.PicoIfZeroCache Examples.PicoHashMethod.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreInvariant.

(** * Read-Labeled CESK Executions for Hash Caches

    The local-copy method's hit and miss executions produce the reads and
    writes of the trace interpreter, and the double-read method executes the
    bad trace to completion.  This file uses no Iris. *)

Section hash_trace_execution.
  Context `{CacheMemoryModel}.
  Context (CT : class_table) (receiver : Loc).

  Inductive pico_hash_observed_step :
      pico_core_expr -> pico_core_state -> option value ->
      pico_core_expr -> pico_core_state -> Prop :=
    | PHOS_Read : forall rGamma x old v V V' K h sigma,
        runtime_getVal rGamma x = Some old ->
        runtime_getVal rGamma cache_receiver = Some (Iot receiver) ->
        wm_read sigma V (receiver, hash_cache_field) v V' ->
        pico_hash_observed_step
          (CoreRun rGamma
            (SVarAss x (EField cache_receiver hash_cache_field)) V K)
          (mkPicoCoreState h sigma) (Some v)
          (CoreRun (set_vars rGamma (update x v (vars rGamma))) SSkip V' K)
          (mkPicoCoreState h sigma)
    | PHOS_ReadNPE : forall rGamma x old V K state,
        runtime_getVal rGamma x = Some old ->
        runtime_getVal rGamma cache_receiver = Some Null_a ->
        pico_hash_observed_step
          (CoreRun rGamma
            (SVarAss x (EField cache_receiver hash_cache_field)) V K)
          state None (CoreDone NPE rGamma V) state
    | PHOS_Silent : forall e state e' state',
        pico_core_step CT e state e' state' ->
        (forall rGamma x V K,
          e <> CoreRun rGamma
            (SVarAss x (EField cache_receiver hash_cache_field)) V K) ->
        pico_hash_observed_step e state None e' state'.

  Inductive pico_hash_observed_steps :
      pico_core_expr -> pico_core_state -> list value ->
      pico_core_expr -> pico_core_state -> Prop :=
    | PHOS_Refl : forall e state,
        pico_hash_observed_steps e state [] e state
    | PHOS_SilentStep : forall e state e1 state1 e2 state2 tr,
        pico_hash_observed_step e state None e1 state1 ->
        pico_hash_observed_steps e1 state1 tr e2 state2 ->
        pico_hash_observed_steps e state tr e2 state2
    | PHOS_ReadStep : forall e state e1 state1 e2 state2 v tr,
        pico_hash_observed_step e state (Some v) e1 state1 ->
        pico_hash_observed_steps e1 state1 tr e2 state2 ->
        pico_hash_observed_steps e state (v :: tr) e2 state2.

  Lemma pico_hash_observed_step_core : forall e state event e' state',
    pico_hash_observed_step e state event e' state' ->
    pico_core_step CT e state e' state'.
  Proof.
    intros e state event e' state' Hstep.
    inversion Hstep; subst; eauto using pico_core_step.
  Qed.

  Lemma pico_hash_observed_steps_core : forall e state tr e' state',
    pico_hash_observed_steps e state tr e' state' ->
    pico_core_steps CT e state e' state'.
  Proof.
    intros e state tr e' state' Hsteps.
    induction Hsteps.
    - constructor.
    - econstructor; [eapply pico_hash_observed_step_core; eauto | exact IHHsteps].
    - econstructor; [eapply pico_hash_observed_step_core; eauto | exact IHHsteps].
  Qed.
End hash_trace_execution.

Definition pico_hash_entry (receiver : Loc) : r_env :=
  mkr_env [Iot receiver].

Definition pico_hash_bad_final_env (receiver : Loc) (H : nat) : r_env :=
  mkr_env [Iot receiver; Int H; Int 0].

(** The concrete double-read body realizes the generic bad trace. *)
Theorem pico_double_read_cesk_matches_bad_trace
    `{CacheMemoryModel} : forall CT h sigma receiver hash_value V0 V1 V2
    (Hnonzero : hash_value <> 0)
    (Hread_first : wm_read sigma V0
      (receiver, hash_cache_field) (Int hash_value) V1)
    (Hread_second : wm_read sigma V1
      (receiver, hash_cache_field) (Int 0) V2),
  pico_hash_observed_steps CT receiver
    (CoreRun (pico_hash_entry receiver)
      (pico_double_read_hash_method_stmt hash_value) V0 [])
    (mkPicoCoreState h sigma)
    [Int hash_value; Int 0]
    (CoreDone OK (pico_hash_bad_final_env receiver hash_value) V2)
    (mkPicoCoreState h sigma) /\
  map hash_obs [Int hash_value; Int 0] = bad_hash_trace hash_value /\
  ValidTrace hash_cache_protocol hash_value (bad_hash_trace hash_value) /\
  run_result (pico_double_read_hash_run hash_value tt
    (bad_hash_trace hash_value)) = Int 0.
Proof.
  intros CT h sigma receiver hash_value V0 V1 V2
    Hnonzero Hread_first Hread_second.
  split.
  2: { split.
       - reflexivity.
       - split; [apply bad_hash_trace_valid; exact Hnonzero |].
         unfold pico_double_read_hash_run, bad_hash_run, bad_hash_trace,
       hash_obs, hash_obs_value, cache_value_eq_zero; simpl.
         destruct hash_value; [contradiction | reflexivity]. }
  unfold pico_double_read_hash_method_stmt, pico_double_read_cache_stmt,
    pico_local_copy_cache_branch, pico_hash_compute_stmt,
    pico_hash_entry, pico_hash_bad_final_env.
  eapply PHOS_SilentStep.
  - apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
  - eapply PHOS_SilentStep.
    + apply PHOS_Silent; [apply PCS_Local; reflexivity |]. intros; discriminate.
    + eapply PHOS_SilentStep.
      * apply PHOS_Silent; [apply PCS_SkipSeq |]. intros; discriminate.
      * eapply PHOS_SilentStep.
        -- apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
        -- eapply PHOS_SilentStep.
           ++ apply PHOS_Silent; [apply PCS_Local; reflexivity |].
              intros; discriminate.
           ++ eapply PHOS_SilentStep.
              ** apply PHOS_Silent; [apply PCS_SkipSeq |].
                 intros; discriminate.
              ** eapply PHOS_SilentStep.
                 --- apply PHOS_Silent; [apply PCS_Seq |].
                     intros; discriminate.
                 --- eapply PHOS_ReadStep.
                     +++ eapply PHOS_Read with (old := Int 0); simpl; eauto.
                     +++ eapply PHOS_SilentStep.
                         *** apply PHOS_Silent; [apply PCS_SkipSeq |].
                             intros; discriminate.
                         *** eapply PHOS_SilentStep.
                             ---- apply PHOS_Silent; [apply PCS_Seq |].
                                  intros; discriminate.
                             ---- eapply PHOS_SilentStep.
                                  ++++ apply PHOS_Silent.
                                       { destruct hash_value as [|hash_pred];
                                           [contradiction |].
                                         apply PCS_IfNonzero with (n := hash_pred).
                                         reflexivity. }
                                       intros; discriminate.
                                  ++++ eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipSeq |].
                                         intros; discriminate. }
                                       eapply PHOS_ReadStep.
                                       { eapply PHOS_Read with (old := Int 0);
                                         simpl; eauto. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipDone |].
                                         intros; discriminate. }
                                       constructor.
Qed.

Definition pico_hash_good_final_env (receiver : Loc) (H : nat) : r_env :=
  mkr_env [Iot receiver; Int H; Int H].

Theorem pico_local_copy_cesk_refines_trace_on_hit
    `{CacheMemoryModel} : forall CT h sigma receiver hash_value V0 V1
    (Hnonzero : hash_value <> 0)
    (Hread : wm_read sigma V0
      (receiver, hash_cache_field) (Int hash_value) V1),
  pico_hash_observed_steps CT receiver
    (CoreRun (pico_hash_entry receiver)
      (pico_hash_method_stmt hash_value) V0 [])
    (mkPicoCoreState h sigma)
    [Int hash_value]
    (CoreDone OK (pico_hash_good_final_env receiver hash_value) V1)
    (mkPicoCoreState h sigma) /\
  ValidTrace hash_cache_protocol hash_value (map hash_obs [Int hash_value]) /\
  trace_result_matches hash_cache_protocol pico_local_copy_hash_run
    hash_value tt (map hash_obs [Int hash_value]) (Int hash_value).
Proof.
  intros CT h sigma receiver hash_value V0 V1 Hnonzero Hread.
  split.
  2: { split.
       - constructor; [right; auto | constructor].
       - unfold trace_result_matches, pico_local_copy_hash_run, good_hash_run,
           hash_obs, hash_obs_value, cache_value_eq_zero; simpl.
         destruct hash_value; [contradiction | reflexivity]. }
  unfold pico_hash_method_stmt, pico_hash_method_stmt_with,
    pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt,
    pico_local_copy_cache_branch, pico_hash_compute_stmt,
    pico_hash_entry, pico_hash_good_final_env.
  eapply PHOS_SilentStep.
  - apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
  - eapply PHOS_SilentStep.
    + apply PHOS_Silent; [apply PCS_Local; reflexivity |]. intros; discriminate.
    + eapply PHOS_SilentStep.
      * apply PHOS_Silent; [apply PCS_SkipSeq |]. intros; discriminate.
      * eapply PHOS_SilentStep.
        -- apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
        -- eapply PHOS_SilentStep.
           ++ apply PHOS_Silent; [apply PCS_Local; reflexivity |].
              intros; discriminate.
           ++ eapply PHOS_SilentStep.
              ** apply PHOS_Silent; [apply PCS_SkipSeq |].
                 intros; discriminate.
              ** eapply PHOS_SilentStep.
                 --- apply PHOS_Silent; [apply PCS_Seq |].
                     intros; discriminate.
                 --- eapply PHOS_ReadStep.
                     +++ eapply PHOS_Read with (old := Int 0); simpl; eauto.
                     +++ eapply PHOS_SilentStep.
                         *** apply PHOS_Silent; [apply PCS_SkipSeq |].
                             intros; discriminate.
                         *** eapply PHOS_SilentStep.
                             ---- apply PHOS_Silent; [apply PCS_Seq |].
                                  intros; discriminate.
                             ---- eapply PHOS_SilentStep.
                                  ++++ apply PHOS_Silent.
                                       { destruct hash_value as [|hash_pred];
                                           [contradiction |].
                                         apply PCS_IfNonzero with (n := hash_pred).
                                         reflexivity. }
                                       intros; discriminate.
                                  ++++ eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipSeq |].
                                         intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent.
                                         - apply PCS_AssignVar with
                                             (old_v := Int 0) (val_y := Int hash_value);
                                             reflexivity.
                                         - intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipDone |].
                                         intros; discriminate. }
                                       constructor.
Qed.

Theorem pico_local_copy_cesk_refines_trace_on_miss
    `{CacheMemoryModel} : forall CT h h' sigma sigma' receiver hash_value
    V0 V1 V2 o assign
    (Hread : wm_read sigma V0
      (receiver, hash_cache_field) (Int 0) V1)
    (Hobj : runtime_getObj h receiver = Some o)
    (Hassign : sf_assignability_rel CT (rctype (rt_type o))
      hash_cache_field assign)
    (Hassignable : runtime_vpa_assignability (rqtype (rt_type o)) assign =
      Assignable)
    (Hheap : h' = update_field h receiver hash_cache_field (Int hash_value))
    (Hwrite : wm_write sigma sigma' V1 V2
      (receiver, hash_cache_field) (Int hash_value)),
  pico_hash_observed_steps CT receiver
    (CoreRun (pico_hash_entry receiver)
      (pico_hash_method_stmt hash_value) V0 [])
    (mkPicoCoreState h sigma)
    [Int 0]
    (CoreDone OK (pico_hash_good_final_env receiver hash_value) V2)
    (mkPicoCoreState h' sigma') /\
  ValidTrace hash_cache_protocol hash_value (map hash_obs [Int 0]) /\
  trace_result_matches hash_cache_protocol pico_local_copy_hash_run
    hash_value tt (map hash_obs [Int 0]) (Int hash_value).
Proof.
  intros CT h h' sigma sigma' receiver hash_value V0 V1 V2 o assign
    Hread Hobj Hassign Hassignable Hheap Hwrite.
  split.
  2: { split.
       - constructor; [left; reflexivity | constructor].
       - unfold trace_result_matches, pico_local_copy_hash_run, good_hash_run,
           hash_obs, hash_obs_value, cache_value_eq_zero; simpl. reflexivity. }
  unfold pico_hash_method_stmt, pico_hash_method_stmt_with,
    pico_hash_method_core_stmt_with, pico_local_copy_cache_stmt,
    pico_local_copy_cache_branch, pico_hash_compute_stmt,
    pico_hash_entry, pico_hash_good_final_env.
  eapply PHOS_SilentStep.
  - apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
  - eapply PHOS_SilentStep.
    + apply PHOS_Silent; [apply PCS_Local; reflexivity |]. intros; discriminate.
    + eapply PHOS_SilentStep.
      * apply PHOS_Silent; [apply PCS_SkipSeq |]. intros; discriminate.
      * eapply PHOS_SilentStep.
        -- apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
        -- eapply PHOS_SilentStep.
           ++ apply PHOS_Silent; [apply PCS_Local; reflexivity |].
              intros; discriminate.
           ++ eapply PHOS_SilentStep.
              ** apply PHOS_Silent; [apply PCS_SkipSeq |].
                 intros; discriminate.
              ** eapply PHOS_SilentStep.
                 --- apply PHOS_Silent; [apply PCS_Seq |].
                     intros; discriminate.
                 --- eapply PHOS_ReadStep.
                     +++ eapply PHOS_Read with (old := Int 0); simpl; eauto.
                     +++ eapply PHOS_SilentStep.
                         *** apply PHOS_Silent; [apply PCS_SkipSeq |].
                             intros; discriminate.
                         *** eapply PHOS_SilentStep.
                             ---- apply PHOS_Silent; [apply PCS_Seq |].
                                  intros; discriminate.
                             ---- eapply PHOS_SilentStep.
                                  ++++ apply PHOS_Silent.
                                       { apply PCS_IfZero. reflexivity. }
                                       intros; discriminate.
                                  ++++ eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_Seq |].
                                         intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent.
                                         - apply PCS_AssignInt with
                                             (old_v := Int 0). reflexivity.
                                         - intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipSeq |].
                                         intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent.
                                         - eapply PCS_FldWrite with
                                             (o := o) (a := assign);
                                             simpl; eauto; reflexivity.
                                         - intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipSeq |].
                                         intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent.
                                         - apply PCS_AssignVar with
                                             (old_v := Int 0)
                                             (val_y := Int hash_value);
                                             reflexivity.
                                         - intros; discriminate. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipDone |].
                                         intros; discriminate. }
                                       constructor.
Qed.

Theorem pico_double_read_cesk_matches_bad_trace_callable
    `{CacheMemoryModel} : forall CT h sigma receiver hash_value V0 V1 V2 caller target
    (Hnonzero : hash_value <> 0)
    (Hread_first : wm_read sigma V0
      (receiver, hash_cache_field) (Int hash_value) V1)
    (Hread_second : wm_read sigma V1
      (receiver, hash_cache_field) (Int 0) V2),
  pico_hash_observed_steps CT receiver
    (CoreRun (pico_hash_entry receiver)
      (pico_double_read_hash_method_stmt hash_value) V0
      [KCall caller target cache_result])
    (mkPicoCoreState h sigma)
    [Int hash_value; Int 0]
    (CoreRun
      (set_vars caller (update target (Int 0) (vars caller))) SSkip V2 [])
    (mkPicoCoreState h sigma) /\
  map hash_obs [Int hash_value; Int 0] = bad_hash_trace hash_value /\
  ValidTrace hash_cache_protocol hash_value (bad_hash_trace hash_value) /\
  run_result (pico_double_read_hash_run hash_value tt
    (bad_hash_trace hash_value)) = Int 0.
Proof.
  intros CT h sigma receiver hash_value V0 V1 V2 caller target
    Hnonzero Hread_first Hread_second.
  split.
  2: { split.
       - reflexivity.
       - split; [apply bad_hash_trace_valid; exact Hnonzero |].
         unfold pico_double_read_hash_run, bad_hash_run, bad_hash_trace,
       hash_obs, hash_obs_value, cache_value_eq_zero; simpl.
         destruct hash_value; [contradiction | reflexivity]. }
  unfold pico_double_read_hash_method_stmt, pico_double_read_cache_stmt,
    pico_local_copy_cache_branch, pico_hash_compute_stmt,
    pico_hash_entry, pico_hash_bad_final_env.
  eapply PHOS_SilentStep.
  - apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
  - eapply PHOS_SilentStep.
    + apply PHOS_Silent; [apply PCS_Local; reflexivity |]. intros; discriminate.
    + eapply PHOS_SilentStep.
      * apply PHOS_Silent; [apply PCS_SkipSeq |]. intros; discriminate.
      * eapply PHOS_SilentStep.
        -- apply PHOS_Silent; [apply PCS_Seq |]. intros; discriminate.
        -- eapply PHOS_SilentStep.
           ++ apply PHOS_Silent; [apply PCS_Local; reflexivity |].
              intros; discriminate.
           ++ eapply PHOS_SilentStep.
              ** apply PHOS_Silent; [apply PCS_SkipSeq |].
                 intros; discriminate.
              ** eapply PHOS_SilentStep.
                 --- apply PHOS_Silent; [apply PCS_Seq |].
                     intros; discriminate.
                 --- eapply PHOS_ReadStep.
                     +++ eapply PHOS_Read with (old := Int 0); simpl; eauto.
                     +++ eapply PHOS_SilentStep.
                         *** apply PHOS_Silent; [apply PCS_SkipSeq |].
                             intros; discriminate.
                         *** eapply PHOS_SilentStep.
                             ---- apply PHOS_Silent; [apply PCS_Seq |].
                                  intros; discriminate.
                             ---- eapply PHOS_SilentStep.
                                  ++++ apply PHOS_Silent.
                                       { destruct hash_value as [|hash_pred];
                                           [contradiction |].
                                         apply PCS_IfNonzero with (n := hash_pred).
                                         reflexivity. }
                                       intros; discriminate.
                                  ++++ eapply PHOS_SilentStep.
                                       { apply PHOS_Silent; [apply PCS_SkipSeq |].
                                         intros; discriminate. }
                                       eapply PHOS_ReadStep.
                                       { eapply PHOS_Read with (old := Int 0);
                                         simpl; eauto. }
                                       eapply PHOS_SilentStep.
                                       { apply PHOS_Silent.
                                         { apply PCS_SkipCall. reflexivity. }
                                         intros; discriminate. }
                                       constructor.
Qed.

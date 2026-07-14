From iris.program_logic Require Import language adequacy ownp.
From iris.proofmode Require Import proofmode.

From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.
Require Import Iris.GenericCacheGhostState Iris.IrisSemanticBridge.
Require Import Examples.PicoIfZeroCacheExamples
  Examples.PicoSemanticCacheAPIExamples Examples.PicoConcreteHashModel.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisTypingFundamental
  PICOBridge.PicoIrisSemanticAPI
  PICOBridge.PicoIrisSemImmOperations
  PICOBridge.PicoIrisSemImmLogicalRelation
  PICOBridge.PicoIrisSemImmAdequacy.

(** * Read-Labeled CESK Executions for Hash Caches *)

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
                                             simpl; eauto.
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

Lemma pico_core_steps_erased_steps
    `{CacheMemoryModel} : forall CT e state e' state',
  pico_core_steps CT e state e' state' ->
  rtc (@erased_step (pico_core_language CT)) ([e], state) ([e'], state').
Proof.
  intros CT e state e' state' Hsteps.
  induction Hsteps.
  - constructor.
  - eapply rtc_l; [| exact IHHsteps].
    exists (@nil unit).
    eapply step_atomic with
      (e1 := e) (e2 := e1) (σ1 := sigma) (σ2 := sigma1)
      (efs := []) (t1 := []) (t2 := []); simpl; eauto.
    eapply pico_core_step_is_prim_step; eauto.
Qed.

Lemma pico_core_steps_snoc
    `{CacheMemoryModel} : forall CT e state e' state' e'' state'',
  pico_core_steps CT e state e' state' ->
  pico_core_step CT e' state' e'' state'' ->
  pico_core_steps CT e state e'' state''.
Proof.
  intros CT e state e' state' e'' state'' Hsteps Hlast.
  induction Hsteps.
  - econstructor; [exact Hlast | constructor].
  - econstructor; eauto.
Qed.

Definition pico_hash_callable_result (hash_value : nat)
    (result : pico_core_val) : Prop :=
  pcv_result result = OK /\
  runtime_getVal (pcv_env result) 0 = Some (Int hash_value).

Theorem pico_double_read_callable_refutes_result_adequacy
    `{CacheMemoryModel} : forall CT h sigma receiver hash_value V0 V1 V2
    (Hnonzero : hash_value <> 0)
    (Hread_first : wm_read sigma V0
      (receiver, hash_cache_field) (Int hash_value) V1)
    (Hread_second : wm_read sigma V1
      (receiver, hash_cache_field) (Int 0) V2),
  ~ @adequate (pico_core_language CT) NotStuck
      (CoreRun (pico_hash_entry receiver)
        (pico_double_read_hash_method_stmt hash_value) V0
        [KCall (mkr_env [Int 0]) 0 cache_result])
      (mkPicoCoreState h sigma)
      (fun result _ => pico_hash_callable_result hash_value result).
Proof.
  intros CT h sigma receiver hash_value V0 V1 V2
    Hnonzero Hread_first Hread_second Hadequate.
  destruct (pico_double_read_cesk_matches_bad_trace_callable
    CT h sigma receiver hash_value V0 V1 V2 (mkr_env [Int 0]) 0
    Hnonzero Hread_first Hread_second) as [Hobserved _].
  pose proof (pico_hash_observed_steps_core CT receiver _ _ _ _ _ Hobserved)
    as Hcore.
  assert (Hdone : pico_core_step CT
    (CoreRun (set_vars (mkr_env [Int 0])
      (update 0 (Int 0) (vars (mkr_env [Int 0])))) SSkip V2 [])
    (mkPicoCoreState h sigma)
    (CoreDone OK (set_vars (mkr_env [Int 0])
      (update 0 (Int 0) (vars (mkr_env [Int 0])))) V2)
    (mkPicoCoreState h sigma)) by apply PCS_SkipDone.
  pose proof (pico_core_steps_snoc CT _ _ _ _ _ _ Hcore Hdone) as Hcore_done.
  pose proof (pico_core_steps_erased_steps CT _ _ _ _ Hcore_done) as Herased.
  pose proof (@adequate_result (pico_core_language CT) NotStuck
    _ _ _ Hadequate [] (mkPicoCoreState h sigma)
    (mkPicoCoreVal OK (set_vars (mkr_env [Int 0])
      (update 0 (Int 0) (vars (mkr_env [Int 0])))) V2) Herased) as Hpost.
  destruct Hpost as [_ Hresult].
  unfold runtime_getVal, set_vars in Hresult; simpl in Hresult.
  inversion Hresult. subst hash_value. contradiction.
Qed.

(** A concrete terminating CESK execution violates the deterministic method
    postcondition.  Since Iris WP adequacy validates every reachable value,
    this also rules out any sound closed WP installation of that contract for
    the displayed initial state. *)
Theorem pico_double_read_cesk_refutes_contract_adequacy
    `{CacheMemoryModel} : forall CT h sigma receiver hash_value V0 V1 V2
    (Hnonzero : hash_value <> 0)
    (Hread_first : wm_read sigma V0
      (receiver, hash_cache_field) (Int hash_value) V1)
    (Hread_second : wm_read sigma V1
      (receiver, hash_cache_field) (Int 0) V2),
  ~ @adequate (pico_core_language CT) NotStuck
      (CoreRun (pico_hash_entry receiver)
        (pico_double_read_hash_method_stmt hash_value) V0 [])
      (mkPicoCoreState h sigma)
      (fun result _ =>
        psmc_post (pico_hash_method_contract hash_value)
          (pico_hash_entry receiver) result).
Proof.
  intros CT h sigma receiver hash_value V0 V1 V2
    Hnonzero Hread_first Hread_second Hadequate.
  destruct (pico_double_read_cesk_matches_bad_trace
    CT h sigma receiver hash_value V0 V1 V2 Hnonzero
    Hread_first Hread_second) as [Hobserved _].
  pose proof (pico_hash_observed_steps_core CT receiver _ _ _ _ _ Hobserved)
    as Hcore.
  pose proof (pico_core_steps_erased_steps CT _ _ _ _ Hcore) as Herased.
  pose proof (@adequate_result (pico_core_language CT) NotStuck
    _ _ _ Hadequate [] (mkPicoCoreState h sigma)
    (mkPicoCoreVal OK (pico_hash_bad_final_env receiver hash_value) V2)
    Herased) as Hpost.
  unfold pico_hash_method_contract, pico_hash_bad_final_env,
    pico_hash_decode_result, hash_pure_result, runtime_getVal in Hpost.
  simpl in Hpost.
  destruct Hpost as [_ [returned [Hreturned Heq]]].
  inversion Hreturned; subst returned.
  inversion Heq.
  apply Hnonzero.
  symmetry.
  assumption.
Qed.

Theorem pico_double_read_callable_method_uninhabited
    `{Hmem : CacheMemoryModel}
    `{Hprogress : @CacheMemoryModelProgress Hmem} :
  forall CT
    (A : PicoCoreCacheAdapter hash_cache_protocol) hash_value
    (M : PicoCoreSemImmInstantiation CT hash_cache_protocol
      pico_hash_stable_abs hash_value A)
    receiver_type method h sigma receiver V0 V1 V2
    (Sigma : gFunctors)
    `{!ownPGpreS (@pico_core_language Hmem CT) Sigma}
    `{!genericCacheG hash_cache_protocol Sigma}
    (Hnonzero : hash_value <> 0)
    (Henv : pico_core_typed_env CT [receiver_type]
      (pico_hash_entry receiver) h)
    (Hstate : @pico_core_lr_state Hmem CT (mkPicoCoreState h sigma))
    (Hinst : pcsi_state_inv CT hash_cache_protocol pico_hash_stable_abs
      hash_value A M (mkPicoCoreState h sigma))
    (Hsnapshot : CacheHistSnapshotOK hash_cache_protocol
      (pcsi_snapshot CT hash_cache_protocol pico_hash_stable_abs
        hash_value A M (mkPicoCoreState h sigma)) hash_value)
    (Hread_first : @wm_read Hmem sigma V0
      (receiver, hash_cache_field) (Int hash_value) V1)
    (Hread_second : @wm_read Hmem sigma V1
      (receiver, hash_cache_field) (Int 0) V2)
    (Hcallable : forall
      (Hown : ownPGS (@pico_core_language Hmem CT) Sigma),
      ⊢ @pico_callable_methodI Hmem CT Sigma Hown
        (pico_core_semimm_worldI CT hash_cache_protocol
          pico_hash_stable_abs hash_value A M)
        (pico_hash_method_contract hash_value)
        (pico_double_read_hash_method_def receiver_type method hash_value)),
    False.
Proof.
  intros CT A hash_value M receiver_type method h sigma receiver V0 V1 V2
    Sigma Hown_pre Hcache Hnonzero Henv Hstate Hinst Hsnapshot
    Hread_first Hread_second Hcallable.
  apply (pico_double_read_callable_refutes_result_adequacy
    CT h sigma receiver hash_value V0 V1 V2 Hnonzero
    Hread_first Hread_second).
  eapply (pico_core_ownP_adequacy CT Sigma NotStuck
    (CoreRun (pico_hash_entry receiver)
      (pico_double_read_hash_method_stmt hash_value) V0
      [KCall (mkr_env [Int 0]) 0 cache_result])
    (mkPicoCoreState h sigma) (pico_hash_callable_result hash_value)).
  intros Hown.
  iIntros "Hown".
  iMod (semimmI_alloc hash_cache_protocol pico_hash_stable_abs
    (pcsi_object CT hash_cache_protocol pico_hash_stable_abs hash_value A M
      (mkPicoCoreState h sigma)) hash_value
    (pcsi_snapshot CT hash_cache_protocol pico_hash_stable_abs hash_value A M
      (mkPicoCoreState h sigma))
    (pcsi_stable CT hash_cache_protocol pico_hash_stable_abs hash_value A M
      (mkPicoCoreState h sigma) Hinst) Hsnapshot) as (gamma) "Hsem".
  iPoseProof (Hcallable Hown) as "#Hmethod".
  iEval (unfold pico_callable_methodI) in "Hmethod".
  iEval (simpl) in "Hmethod".
  iApply ("Hmethod" $! (pico_hash_entry receiver) (mkr_env [Int 0]) 0
    receiver h sigma V0 [] top
    (fun result => ⌜pico_hash_callable_result hash_value result⌝)%I
    with "[] [] [] [] [Hsem] Hown").
  - iPureIntro. exact Henv.
  - iPureIntro. reflexivity.
  - iPureIntro. exact Hstate.
  - iPureIntro. exists receiver. split; [reflexivity | exact I].
  - unfold pico_core_semimm_worldI.
    iExists gamma. iSplit; [iPureIntro; exact Hinst | iExact "Hsem"].
  - iNext.
    iIntros (callee_done final_state V' returned)
      "%Hevidence %Hpost Hworld Hown".
    destruct Hevidence as
      (body_sGamma' & body_ret_type & Hret_static & Hret_sub &
       Hcallee_typed & Hcallee_receiver & Hextend & Hstate_final & Hreturn).
    unfold pico_hash_method_contract in Hpost; simpl in Hpost.
    destruct Hpost as [_ [contract_return [Hcontract_return Hderived]]].
    unfold pico_hash_decode_result, hash_pure_result in Hderived.
    destruct contract_return; simpl in Hderived; try discriminate.
    inversion Hderived; subst n.
    simpl in Hreturn.
    assert (returned = Int hash_value) by congruence. subst returned.
    set (caller_done := set_vars (mkr_env [Int 0])
      (update 0 (Int hash_value) (vars (mkr_env [Int 0])))).
    assert (Hdone : pico_core_step CT
      (CoreRun caller_done SSkip V' []) final_state
      (CoreDone OK caller_done V') final_state).
    { apply PCS_SkipDone. }
    assert (Hdone_unique : forall next state', pico_core_step CT
      (CoreRun caller_done SSkip V' []) final_state next state' ->
      next = CoreDone OK caller_done V' /\ state' = final_state).
    { intros next state' Hactual.
      exact (pico_core_skip_done_unique CT _ _ _ _ _ Hactual). }
    iApply (@pico_hash_same_state_step_wpEI Hmem Hprogress CT Sigma Hown
      (pico_core_semimm_worldI CT hash_cache_protocol
        pico_hash_stable_abs hash_value A M)
      (fun result => ⌜pico_hash_callable_result hash_value result⌝)%I top
      (CoreRun caller_done SSkip V' []) (CoreDone OK caller_done V')
      final_state Hdone Hdone_unique with "Hworld Hown").
    iNext. iIntros "Hworld Hown".
    iApply (@wp_value' _ (pico_core_language CT) Sigma _ NotStuck top
      (fun result => ⌜pico_hash_callable_result hash_value result⌝)%I
      (mkPicoCoreVal OK caller_done V')).
    iPureIntro. split; [reflexivity |].
    unfold caller_done, runtime_getVal, set_vars; simpl. reflexivity.
Qed.

(** The closed provider witness reaches a state whose cache history is
    [[Int 0; Int 7]]. The canonical adversarial history model can therefore
    read the complete write [Int 7] and then the older complete write [Int 0]. *)
Lemma pico_hash_witness_bad_read_hash :
  @wm_read history_cache_memory_model pico_hash_witness_bad_weak 0
    (0, hash_cache_field) (Int 7) 0.
Proof.
  unfold history_read. split; [reflexivity |].
  exists (mkWriteMsg (Int 7) 1 0). split; [|reflexivity].
  unfold pico_hash_witness_bad_weak.
  rewrite history_of_append_write_same.
  apply in_or_app. right. left. reflexivity.
Qed.

Lemma pico_hash_witness_bad_read_default :
  @wm_read history_cache_memory_model pico_hash_witness_bad_weak 0
    (0, hash_cache_field) (Int 0) 0.
Proof.
  unfold history_read. split; [reflexivity |].
  exists (mkWriteMsg (Int 0) 0 0). split; [|reflexivity].
  unfold pico_hash_witness_bad_weak.
  rewrite history_of_append_write_same.
  apply in_or_app. left.
  unfold pico_hash_witness_initial_weak, pico_hash_witness_object,
    pico_core_alloc_weak, empty_wm_state, history_of. simpl.
  left. reflexivity.
Qed.

(** Closed non-vacuity corollary for the negative API result. The state,
    provider, typed frame, and both weak reads are concrete; only the callable
    Iris proposition being refuted remains universally quantified. *)
Theorem pico_hash_witness_double_read_callable_uninhabited :
  forall (Sigma : gFunctors)
    `{!ownPGpreS
      (@pico_core_language history_cache_memory_model pico_hash_witness_CT)
      Sigma}
    `{!genericCacheG hash_cache_protocol Sigma},
    (forall
      (Hown : ownPGS
        (@pico_core_language history_cache_memory_model pico_hash_witness_CT)
        Sigma),
      ⊢ @pico_callable_methodI history_cache_memory_model
        pico_hash_witness_CT Sigma Hown
        (pico_core_semimm_worldI pico_hash_witness_CT hash_cache_protocol
          pico_hash_stable_abs 7 (pico_hash_cache_adapter 0)
          (pico_concrete_hash_semimm pico_hash_witness_CT 0
            pico_hash_witness_function 7))
        (pico_hash_method_contract 7)
        (pico_double_read_hash_method_def
          pico_hash_witness_receiver_type 0 7)) ->
    False.
Proof.
  intros Sigma Hpre Hcache Hcallable.
  eapply (@pico_double_read_callable_method_uninhabited
    history_cache_memory_model history_cache_memory_model_progress
    pico_hash_witness_CT (pico_hash_cache_adapter 0) 7
    (pico_concrete_hash_semimm pico_hash_witness_CT 0
      pico_hash_witness_function 7)
    pico_hash_witness_receiver_type 0
    pico_hash_witness_bad_heap pico_hash_witness_bad_weak 0
    0 0 0 Sigma Hpre Hcache).
  - discriminate.
  - exact pico_hash_witness_bad_typed_env.
  - exact pico_hash_witness_bad_state_wf.
  - exact pico_hash_witness_bad_provider_inv.
  - exact (proj2 (proj2 pico_hash_witness_bad_provider_inv)).
  - exact pico_hash_witness_bad_read_hash.
  - exact pico_hash_witness_bad_read_default.
  - exact Hcallable.
Qed.

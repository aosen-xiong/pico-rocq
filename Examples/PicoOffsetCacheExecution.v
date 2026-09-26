From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Bigstep.
Require Import Examples.CacheProtocolDiversity Examples.PicoIfZeroCacheExamples
  Examples.PicoConcreteHashModel Examples.PicoSemanticConcurrencyExamples.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage.

(** * Concrete CESK Execution of an Offset-Encoded Cache

    PICO has no primitive predecessor expression.  As with hash
    recomputation, the concrete example therefore isolates the derived
    computation behind a semantic contract.  For the fixed represented value
    seven, assigning seven implements decoding on every protocol-valid
    nonzero observation, because the only such observation is eight. *)

Definition pico_offset_abstract_value : nat := 7.
Definition pico_offset_encoded_value : nat := S pico_offset_abstract_value.

Definition offset_receiver : var := 0.
Definition offset_cached : var := 1.
Definition offset_result : var := 2.

Definition pico_offset_hit_compute : stmt :=
  SVarAss offset_result (EInt pico_offset_abstract_value).

Definition pico_offset_miss_compute : stmt :=
  SSeq
    (SVarAss offset_result (EInt pico_offset_abstract_value))
    (SSeq
      (SVarAss offset_cached (EInt pico_offset_encoded_value))
      (SFldWrite offset_receiver hash_cache_field offset_cached)).

Definition pico_offset_method_stmt : stmt :=
  SSeq
    (SVarAss offset_cached (EField offset_receiver hash_cache_field))
    (SIfZero offset_cached pico_offset_miss_compute pico_offset_hit_compute).

Lemma pico_offset_hit_compute_contract : forall observed,
  offset_cache_valid pico_offset_abstract_value OffsetField observed ->
  observed <> 0 ->
  Nat.pred observed = pico_offset_abstract_value.
Proof.
  intros observed [-> | ->] Hnonzero.
  - contradiction.
  - reflexivity.
Qed.

Definition pico_offset_entry_env : r_env :=
  mkr_env [Iot 0; Int 0; Int 0].

Definition pico_offset_hit_read_env : r_env :=
  set_vars pico_offset_entry_env
    (update offset_cached (Int pico_offset_encoded_value)
      (vars pico_offset_entry_env)).

Definition pico_offset_hit_final_env : r_env :=
  set_vars pico_offset_hit_read_env
    (update offset_result (Int pico_offset_abstract_value)
      (vars pico_offset_hit_read_env)).

Definition pico_offset_miss_result_env : r_env :=
  set_vars pico_offset_entry_env
    (update offset_result (Int pico_offset_abstract_value)
      (vars pico_offset_entry_env)).

Definition pico_offset_miss_write_env : r_env :=
  set_vars pico_offset_miss_result_env
    (update offset_cached (Int pico_offset_encoded_value)
      (vars pico_offset_miss_result_env)).

Definition pico_offset_hit_weak : wm_state :=
  append_write_msg pico_hash_witness_initial_weak
    (0, hash_cache_field)
    (mkWriteMsg (Int pico_offset_encoded_value) 1 0).

Definition pico_offset_miss_heap : heap :=
  update_field pico_hash_witness_initial_heap 0 hash_cache_field
    (Int pico_offset_encoded_value).

Definition pico_offset_miss_weak : wm_state :=
  append_write_msg pico_hash_witness_initial_weak
    (0, hash_cache_field)
    (mkWriteMsg (Int pico_offset_encoded_value)
      (length
        (history_of pico_hash_witness_initial_weak
          (0, hash_cache_field))) 0).

Lemma pico_offset_read_default :
  @wm_read history_cache_memory_model pico_hash_witness_initial_weak 0
    (0, hash_cache_field) (Int 0) 0.
Proof.
  change (history_read pico_hash_witness_initial_weak 0
    (0, hash_cache_field) (Int 0) 0).
  split; [reflexivity |].
  exists (mkWriteMsg (Int 0) 0 0).
  split; [|reflexivity].
  unfold pico_hash_witness_initial_weak, history_of. simpl.
  left. reflexivity.
Qed.

Lemma pico_offset_read_hit :
  @wm_read history_cache_memory_model pico_offset_hit_weak 0
    (0, hash_cache_field) (Int pico_offset_encoded_value) 0.
Proof.
  change (history_read pico_offset_hit_weak 0
    (0, hash_cache_field) (Int pico_offset_encoded_value) 0).
  split; [reflexivity |].
  exists (mkWriteMsg (Int pico_offset_encoded_value) 1 0).
  split; [|reflexivity].
  unfold pico_offset_hit_weak.
  rewrite history_of_append_write_same.
  apply in_or_app. right. simpl. auto.
Qed.

Lemma pico_offset_write_encoded :
  wm_write pico_hash_witness_initial_weak pico_offset_miss_weak 0 0
    (0, hash_cache_field) (Int pico_offset_encoded_value).
Proof.
  split; reflexivity.
Qed.

Theorem pico_offset_hit_cesk_execution :
  @pico_core_steps history_cache_memory_model pico_hash_concurrent_CT
    (CoreRun pico_offset_entry_env pico_offset_method_stmt 0 [])
    (mkPicoCoreState pico_hash_witness_initial_heap pico_offset_hit_weak)
    (CoreDone OK pico_offset_hit_final_env 0)
    (mkPicoCoreState pico_hash_witness_initial_heap pico_offset_hit_weak).
Proof.
  unfold pico_offset_method_stmt.
  eapply PicoCoreStepsStep.
  - apply PCS_Seq.
  - eapply PicoCoreStepsStep.
    + eapply PCS_AssignField.
      * reflexivity.
      * reflexivity.
      * apply pico_offset_read_hit.
    + eapply PicoCoreStepsStep.
      * apply PCS_SkipSeq.
      * eapply PicoCoreStepsStep.
        -- apply PCS_IfNonzero with (n := pico_offset_abstract_value).
           reflexivity.
        -- eapply PicoCoreStepsStep.
           ++ eapply PCS_AssignInt. reflexivity.
           ++ eapply PicoCoreStepsStep.
              ** apply PCS_SkipDone.
              ** apply PicoCoreStepsRefl.
Qed.

Theorem pico_offset_miss_cesk_execution :
  @pico_core_steps history_cache_memory_model pico_hash_concurrent_CT
    (CoreRun pico_offset_entry_env pico_offset_method_stmt 0 [])
    (mkPicoCoreState pico_hash_witness_initial_heap
      pico_hash_witness_initial_weak)
    (CoreDone OK pico_offset_miss_write_env 0)
    (mkPicoCoreState pico_offset_miss_heap pico_offset_miss_weak).
Proof.
  unfold pico_offset_method_stmt, pico_offset_miss_compute.
  eapply PicoCoreStepsStep.
  - apply PCS_Seq.
  - eapply PicoCoreStepsStep.
    + eapply PCS_AssignField.
      * reflexivity.
      * reflexivity.
      * apply pico_offset_read_default.
    + eapply PicoCoreStepsStep.
      * apply PCS_SkipSeq.
      * eapply PicoCoreStepsStep.
        -- apply PCS_IfZero. reflexivity.
        -- eapply PicoCoreStepsStep.
           ++ apply PCS_Seq.
           ++ eapply PicoCoreStepsStep.
              ** eapply PCS_AssignInt. reflexivity.
              ** eapply PicoCoreStepsStep.
                 --- apply PCS_SkipSeq.
                 --- eapply PicoCoreStepsStep.
                     +++ apply PCS_Seq.
                     +++ eapply PicoCoreStepsStep.
                         *** eapply PCS_AssignInt. reflexivity.
                         *** eapply PicoCoreStepsStep.
                             ---- apply PCS_SkipSeq.
                             ---- eapply PicoCoreStepsStep.
                                  ++++ eapply PCS_FldWrite.
                                       { reflexivity. }
                                       { reflexivity. }
                                       { exact
                                           pico_hash_concurrent_cache_assignable. }
                                       { reflexivity. }
                                       { reflexivity. }
                                       { reflexivity. }
                                       { apply pico_offset_write_encoded. }
                                  ++++ eapply PicoCoreStepsStep.
                                       { apply PCS_SkipDone. }
                                       { apply PicoCoreStepsRefl. }
Qed.

Theorem pico_offset_operational_refinement :
  runtime_getVal pico_offset_hit_final_env offset_result =
    Some (Int (offset_pure_result pico_offset_abstract_value tt)) /\
  runtime_getVal pico_offset_miss_write_env offset_result =
    Some (Int (offset_pure_result pico_offset_abstract_value tt)) /\
  history_of pico_offset_miss_weak (0, hash_cache_field) =
    history_of pico_hash_witness_initial_weak (0, hash_cache_field) ++
      [mkWriteMsg (Int pico_offset_encoded_value)
        (length
          (history_of pico_hash_witness_initial_weak
            (0, hash_cache_field))) 0].
Proof.
  split; [reflexivity |].
  split; [reflexivity |].
  unfold pico_offset_miss_weak.
  apply history_of_append_write_same.
Qed.

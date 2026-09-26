From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Bigstep.
Require Import Core.GenericCacheProtocol.
Require Import Examples.CacheProtocolDiversity.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage.

(** * Operational Witnesses for Protocol Diversity

    The pure two-field protocol permits independently stale observations.  This
    file shows that the same left-hit/right-default combination is realized by
    the history-backed PICO CESK machine, and that a snapshot-dependent source
    body consequently returns the wrong value. *)

Definition pair_left_addr : FieldAddr := (0, 0).
Definition pair_right_addr : FieldAddr := (0, 1).

Definition pair_initial_weak : wm_state :=
  mkWMState []
    (fun addr =>
      if field_addr_eqb addr pair_left_addr then
        [mkWriteMsg (Int 0) 0 0]
      else if field_addr_eqb addr pair_right_addr then
        [mkWriteMsg (Int 0) 0 0]
      else []).

Definition pair_incoherent_weak (left : nat) : wm_state :=
  append_write_msg pair_initial_weak pair_left_addr
    (mkWriteMsg (Int (S left)) 1 0).

Lemma pair_incoherent_read_left : forall left,
  @wm_read history_cache_memory_model (pair_incoherent_weak left) 0
    pair_left_addr (Int (S left)) 0.
Proof.
  intros left.
  change (history_read (pair_incoherent_weak left) 0 pair_left_addr
    (Int (S left)) 0).
  split; [reflexivity |].
  exists (mkWriteMsg (Int (S left)) 1 0).
  split; [|reflexivity].
  unfold pair_incoherent_weak.
  rewrite history_of_append_write_same.
  apply in_or_app. right. simpl. auto.
Qed.

Lemma pair_incoherent_read_right : forall left,
  @wm_read history_cache_memory_model (pair_incoherent_weak left) 0
    pair_right_addr (Int 0) 0.
Proof.
  intros left.
  change (history_read (pair_incoherent_weak left) 0 pair_right_addr
    (Int 0) 0).
  split; [reflexivity |].
  exists (mkWriteMsg (Int 0) 0 0).
  split; [|reflexivity].
  unfold pair_incoherent_weak.
  rewrite history_of_append_write_other.
  - unfold pair_initial_weak, history_of. simpl.
    left. reflexivity.
  - discriminate.
Qed.

Definition pair_receiver : var := 0.
Definition pair_left_local : var := 1.
Definition pair_right_local : var := 2.
Definition pair_result_local : var := 3.

Definition pico_bad_pair_stmt (left right : nat) : stmt :=
  SSeq
    (SVarAss pair_left_local (EField pair_receiver 0))
    (SSeq
      (SVarAss pair_right_local (EField pair_receiver 1))
      (SIfZero pair_left_local
        (SVarAss pair_result_local (EInt (left + right)))
        (SVarAss pair_result_local (EVar pair_right_local)))).

Definition pair_entry_env : r_env :=
  mkr_env [Iot 0; Int 0; Int 0; Int 0].

Definition pair_left_env (left : nat) : r_env :=
  set_vars pair_entry_env
    (update pair_left_local (Int (S left)) (vars pair_entry_env)).

Definition pair_both_env (left : nat) : r_env :=
  set_vars (pair_left_env left)
    (update pair_right_local (Int 0) (vars (pair_left_env left))).

Definition pair_bad_final_env (left : nat) : r_env :=
  set_vars (pair_both_env left)
    (update pair_result_local (Int 0) (vars (pair_both_env left))).

Theorem pico_bad_pair_incoherent_execution : forall left right,
  @pico_core_steps history_cache_memory_model []
    (CoreRun pair_entry_env (pico_bad_pair_stmt left right) 0 [])
    (mkPicoCoreState [] (pair_incoherent_weak left))
    (CoreDone OK (pair_bad_final_env left) 0)
    (mkPicoCoreState [] (pair_incoherent_weak left)).
Proof.
  intros left right.
  unfold pico_bad_pair_stmt.
  eapply PicoCoreStepsStep.
  - apply PCS_Seq.
  - eapply PicoCoreStepsStep.
    + eapply PCS_AssignField.
      * reflexivity.
      * reflexivity.
      * apply pair_incoherent_read_left.
    + eapply PicoCoreStepsStep.
      * apply PCS_SkipSeq.
      * eapply PicoCoreStepsStep.
        -- apply PCS_Seq.
        -- eapply PicoCoreStepsStep.
           ++ eapply PCS_AssignField.
              ** reflexivity.
              ** reflexivity.
              ** apply pair_incoherent_read_right.
           ++ eapply PicoCoreStepsStep.
              ** apply PCS_SkipSeq.
              ** eapply PicoCoreStepsStep.
                 --- apply PCS_IfNonzero with (n := left). reflexivity.
                 --- eapply PicoCoreStepsStep.
                     +++ eapply PCS_AssignVar; reflexivity.
                     +++ eapply PicoCoreStepsStep.
                         *** apply PCS_SkipDone.
                         *** apply PicoCoreStepsRefl.
Qed.

Theorem pico_bad_pair_operational_counterexample : forall left right,
  left + right <> 0 ->
  ValidTrace pair_cache_protocol (left, right)
    (bad_pair_trace (left, right)) /\
  @pico_core_steps history_cache_memory_model []
    (CoreRun pair_entry_env (pico_bad_pair_stmt left right) 0 [])
    (mkPicoCoreState [] (pair_incoherent_weak left))
    (CoreDone OK (pair_bad_final_env left) 0)
    (mkPicoCoreState [] (pair_incoherent_weak left)) /\
  runtime_getVal (pair_bad_final_env left) pair_result_local = Some (Int 0) /\
  Int 0 <> Int (pair_pure_result (left, right) tt).
Proof.
  intros left right Hnonzero.
  split.
  - apply bad_pair_trace_valid.
  - split.
    + apply pico_bad_pair_incoherent_execution.
    + split.
      * reflexivity.
      * unfold pair_pure_result. intro Heq. injection Heq as Heq.
        apply Hnonzero. symmetry. exact Heq.
Qed.

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage.

(** * Semantic Concurrency for Sequential PICO

    PICO source statements remain sequential.  This module supplies an
    external execution context that installs method invocations as CESK
    controls and schedules them over one shared heap/history state.  Thus
    concurrency is a property of whole executions, not a source construct. *)

Record pico_invocation := mkPicoInvocation {
  invocation_caller : r_env;
  invocation_target : var;
  invocation_receiver : var;
  invocation_method : var;
  invocation_args : list var;
  invocation_view : view;
}.

Definition pico_invocation_control (call : pico_invocation) : pico_core_expr :=
  CoreRun
    (invocation_caller call)
    (SCall
      (invocation_target call)
      (invocation_receiver call)
      (invocation_method call)
      (invocation_args call))
    (invocation_view call) [].

Definition pico_invocation_pool (calls : list pico_invocation) :
    list pico_core_expr :=
  map pico_invocation_control calls.

Record pico_pool_config := mkPicoPoolConfig {
  pool_state : pico_core_state;
  pool_threads : list pico_core_expr;
}.

Definition pico_initial_pool
    (state : pico_core_state) (calls : list pico_invocation) :
    pico_pool_config :=
  mkPicoPoolConfig state (pico_invocation_pool calls).

(** A semantic scheduler step chooses one installed control.  [pico_core_step]
    performs the chosen thread's sequential CESK step and updates the shared
    state; all other controls remain unchanged. *)
Inductive pico_pool_step `{CacheMemoryModel} (CT : class_table) :
    pico_pool_config -> pico_pool_config -> Prop :=
  | PicoPoolStep : forall state state' threads threads' tid e e',
      nth_error threads tid = Some e ->
      pico_core_step CT e state e' state' ->
      threads' = update tid e' threads ->
      pico_pool_step CT
        (mkPicoPoolConfig state threads)
        (mkPicoPoolConfig state' threads').

Inductive pico_pool_steps `{CacheMemoryModel} (CT : class_table) :
    pico_pool_config -> pico_pool_config -> Prop :=
  | PicoPoolStepsRefl : forall cfg,
      pico_pool_steps CT cfg cfg
  | PicoPoolStepsStep : forall cfg1 cfg2 cfg3,
      pico_pool_step CT cfg1 cfg2 ->
      pico_pool_steps CT cfg2 cfg3 ->
      pico_pool_steps CT cfg1 cfg3.

Lemma pico_pool_steps_trans :
  forall `{CacheMemoryModel} CT cfg1 cfg2 cfg3,
    pico_pool_steps CT cfg1 cfg2 ->
    pico_pool_steps CT cfg2 cfg3 ->
    pico_pool_steps CT cfg1 cfg3.
Proof.
  intros Hmem CT cfg1 cfg2 cfg3 H12 H23.
  induction H12.
  - exact H23.
  - econstructor; eauto.
Qed.

Lemma pico_invocation_pool_length : forall calls,
  length (pico_invocation_pool calls) = length calls.
Proof.
  intros calls.
  unfold pico_invocation_pool.
  apply length_map.
Qed.

Lemma pico_pool_step_thread_count :
  forall `{CacheMemoryModel} CT cfg cfg',
    pico_pool_step CT cfg cfg' ->
    length (pool_threads cfg') = length (pool_threads cfg).
Proof.
  intros Hmem CT cfg cfg' Hstep.
  inversion Hstep; subst; simpl.
  apply update_length.
Qed.

Theorem pico_pool_steps_thread_count :
  forall `{CacheMemoryModel} CT cfg cfg',
    pico_pool_steps CT cfg cfg' ->
    length (pool_threads cfg') = length (pool_threads cfg).
Proof.
  intros Hmem CT cfg cfg' Hsteps.
  induction Hsteps.
  - reflexivity.
  - rewrite IHHsteps.
    eapply pico_pool_step_thread_count; eauto.
Qed.

Lemma pico_pool_step_selected :
  forall `{CacheMemoryModel} CT state state' threads tid e e',
    nth_error threads tid = Some e ->
    pico_core_step CT e state e' state' ->
    pico_pool_step CT
      (mkPicoPoolConfig state threads)
      (mkPicoPoolConfig state' (update tid e' threads)).
Proof.
  intros Hmem CT state state' threads tid e e' Hthread Hstep.
  econstructor; eauto.
Qed.

Lemma update_existing_value : forall {A : Type} (xs : list A) tid x,
  nth_error xs tid = Some x ->
  update tid x xs = xs.
Proof.
  intros A xs.
  induction xs as [|head tail IH]; intros [|tid] x Hnth; simpl in *;
    try discriminate.
  - inversion Hnth. reflexivity.
  - f_equal. eapply IH. exact Hnth.
Qed.

Lemma update_overwrite : forall {A : Type} (xs : list A) tid x y,
  update tid y (update tid x xs) = update tid y xs.
Proof.
  intros A xs.
  induction xs as [|head tail IH]; intros [|tid] x y; simpl; auto.
  f_equal. apply IH.
Qed.

(** A finite execution of one installed CESK control lifts to a scheduler
    execution while every other installed control is left untouched. *)
Lemma pico_pool_steps_lift_thread :
  forall `{CacheMemoryModel} CT state state' threads tid e e',
    nth_error threads tid = Some e ->
    pico_core_steps CT e state e' state' ->
    pico_pool_steps CT
      (mkPicoPoolConfig state threads)
      (mkPicoPoolConfig state' (update tid e' threads)).
Proof.
  intros Hmem CT state state' threads tid e e' Hthread Hsteps.
  revert threads Hthread.
  induction Hsteps as [e0 state0 | e0 state0 e1 state1 e2 state2 Hstep Htail IH];
    intros threads Hthread.
  - rewrite (update_existing_value threads tid e0 Hthread).
    constructor.
  - eapply PicoPoolStepsStep with
      (cfg2 := mkPicoPoolConfig state1 (update tid e1 threads)).
    + eapply pico_pool_step_selected; eauto.
    + assert (Hupdated : nth_error (update tid e1 threads) tid = Some e1).
      { apply update_same.
        apply nth_error_Some.
        rewrite Hthread. discriminate. }
      specialize (IH (update tid e1 threads) Hupdated).
      rewrite update_overwrite in IH.
      exact IH.
Qed.

(** Any invariant preserved by every one-thread CESK transition is preserved
    by arbitrary scheduler interleavings. *)
Theorem pico_pool_steps_preserve_state_invariant :
  forall `{CacheMemoryModel} CT (Inv : pico_core_state -> Prop) cfg cfg',
    pico_pool_steps CT cfg cfg' ->
    (forall e state e' state',
      pico_core_step CT e state e' state' ->
      Inv state ->
      Inv state') ->
    Inv (pool_state cfg) ->
    Inv (pool_state cfg').
Proof.
  intros Hmem CT Inv cfg cfg' Hsteps Hpreserved Hinitial.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps IH].
  - exact Hinitial.
  - apply IH.
    inversion Hstep; subst; simpl in *.
    eapply Hpreserved; eauto.
Qed.

Theorem pico_pool_steps_preserve_heap_wm_type_agree :
  forall `{CacheMemoryModel} CT cfg cfg',
    pico_pool_steps CT cfg cfg' ->
    heap_wm_type_agree
      (pcs_heap (pool_state cfg)) (pcs_weak (pool_state cfg)) ->
    heap_wm_type_agree
      (pcs_heap (pool_state cfg')) (pcs_weak (pool_state cfg')).
Proof.
  intros Hmem CT cfg cfg' Hsteps Hagree.
  eapply pico_pool_steps_preserve_state_invariant; eauto.
  intros e state e' state' Hstep Hstate.
  eapply pico_core_step_preserves_heap_wm_type_agree; eauto.
Qed.

Inductive pico_access_kind :=
  | PicoRead
  | PicoWrite.

Record pico_access_event := mkPicoAccessEvent {
  access_thread : nat;
  access_kind : pico_access_kind;
  access_addr : FieldAddr;
  access_value : value;
}.

(** Successful shared-memory accesses carried by scheduler steps.  Failed
    null dereferences are not accesses. *)
Inductive pico_pool_access `{CacheMemoryModel} (CT : class_table) :
    pico_pool_config -> pico_access_event -> pico_pool_config -> Prop :=
  | PicoPoolRead : forall state threads tid rGamma x y f old loc v
      V V' K h sigma,
      state = mkPicoCoreState h sigma ->
      nth_error threads tid = Some
        (CoreRun rGamma (SVarAss x (EField y f)) V K) ->
      runtime_getVal rGamma x = Some old ->
      runtime_getVal rGamma y = Some (Iot loc) ->
      wm_read sigma V (loc, f) v V' ->
      pico_pool_access CT
        (mkPicoPoolConfig state threads)
        (mkPicoAccessEvent tid PicoRead (loc, f) v)
        (mkPicoPoolConfig state
          (update tid
            (CoreRun
              (set_vars rGamma (update x v (vars rGamma))) SSkip V' K)
            threads))
  | PicoPoolWrite : forall threads tid rGamma x f y loc o assign v
      h h' sigma sigma' V V' K,
      nth_error threads tid = Some
        (CoreRun rGamma (SFldWrite x f y) V K) ->
      runtime_getVal rGamma x = Some (Iot loc) ->
      runtime_getObj h loc = Some o ->
      sf_assignability_rel CT (rctype (rt_type o)) f assign ->
      runtime_getVal rGamma y = Some v ->
      runtime_vpa_assignability (rqtype (rt_type o)) assign = Assignable ->
      h' = update_field h loc f v ->
      wm_write sigma sigma' V V' (loc, f) v ->
      pico_pool_access CT
        (mkPicoPoolConfig (mkPicoCoreState h sigma) threads)
        (mkPicoAccessEvent tid PicoWrite (loc, f) v)
        (mkPicoPoolConfig (mkPicoCoreState h' sigma')
          (update tid (CoreRun rGamma SSkip V' K) threads)).

Lemma pico_pool_access_is_step :
  forall `{CacheMemoryModel} CT cfg event cfg',
    pico_pool_access CT cfg event cfg' ->
    pico_pool_step CT cfg cfg'.
Proof.
  intros Hmem CT cfg event cfg' Haccess.
  inversion Haccess; subst.
  - eapply pico_pool_step_selected; eauto.
    eapply PCS_AssignField; eauto.
  - eapply pico_pool_step_selected; eauto.
    eapply PCS_FldWrite with (o := o) (a := assign); eauto.
Qed.

Definition pico_accesses_conflict
    (first second : pico_access_event) : Prop :=
  access_thread first <> access_thread second /\
  access_addr first = access_addr second /\
  (access_kind first = PicoWrite \/ access_kind second = PicoWrite).

(** A race is witnessed by two conflicting accesses from distinct installed
    controls in one scheduler execution.  There is no synchronization syntax
    or synchronization relation in this semantic layer. *)
Definition pico_semantic_race `{CacheMemoryModel} (CT : class_table)
    (initial : pico_pool_config) : Prop :=
  exists before_first after_first before_second after_second first second,
    pico_pool_steps CT initial before_first /\
    pico_pool_access CT before_first first after_first /\
    pico_pool_steps CT after_first before_second /\
    pico_pool_access CT before_second second after_second /\
    pico_accesses_conflict first second.

(** A poised read and write in two distinct controls form a concrete race
    witness.  The read is scheduled first only because the operational model
    is interleaving; no synchronization edge is introduced between them. *)
Theorem pico_pool_read_write_race :
  forall `{CacheMemoryModel} CT initial h sigma threads
    reader_tid writer_tid reader_env writer_env
    read_target read_receiver field old_read receiver_loc read_value
    read_view read_view' read_cont
    write_receiver write_value writer_obj assign written_value
    write_view write_view' write_cont h' sigma',
    pico_pool_steps CT initial
      (mkPicoPoolConfig (mkPicoCoreState h sigma) threads) ->
    reader_tid <> writer_tid ->
    nth_error threads reader_tid = Some
      (CoreRun reader_env
        (SVarAss read_target (EField read_receiver field))
        read_view read_cont) ->
    nth_error threads writer_tid = Some
      (CoreRun writer_env
        (SFldWrite write_receiver field write_value)
        write_view write_cont) ->
    runtime_getVal reader_env read_target = Some old_read ->
    runtime_getVal reader_env read_receiver = Some (Iot receiver_loc) ->
    wm_read sigma read_view (receiver_loc, field) read_value read_view' ->
    runtime_getVal writer_env write_receiver = Some (Iot receiver_loc) ->
    runtime_getObj h receiver_loc = Some writer_obj ->
    sf_assignability_rel CT (rctype (rt_type writer_obj)) field assign ->
    runtime_getVal writer_env write_value = Some written_value ->
    runtime_vpa_assignability (rqtype (rt_type writer_obj)) assign =
      Assignable ->
    h' = update_field h receiver_loc field written_value ->
    wm_write sigma sigma' write_view write_view'
      (receiver_loc, field) written_value ->
    pico_semantic_race CT initial.
Proof.
  intros Hmem CT initial h sigma threads
    reader_tid writer_tid reader_env writer_env
    read_target read_receiver field old_read receiver_loc read_value
    read_view read_view' read_cont
    write_receiver write_value writer_obj assign written_value
    write_view write_view' write_cont h' sigma'
    Hreach Hdistinct Hreader Hwriter Hread_target Hread_receiver Hread
    Hwrite_receiver Hobj Hassign Hwrite_value Hassignable Hheap Hwrite.
  set (reader_done := CoreRun
    (set_vars reader_env (update read_target read_value (vars reader_env)))
    SSkip read_view' read_cont).
  set (threads_after_read := update reader_tid reader_done threads).
  set (after_read := mkPicoPoolConfig
    (mkPicoCoreState h sigma) threads_after_read).
  set (writer_done := CoreRun writer_env SSkip write_view' write_cont).
  set (after_write := mkPicoPoolConfig
    (mkPicoCoreState h' sigma')
    (update writer_tid writer_done threads_after_read)).
  exists
    (mkPicoPoolConfig (mkPicoCoreState h sigma) threads),
    after_read, after_read, after_write,
    (mkPicoAccessEvent reader_tid PicoRead
      (receiver_loc, field) read_value),
    (mkPicoAccessEvent writer_tid PicoWrite
      (receiver_loc, field) written_value).
  split; [exact Hreach |].
  split.
  - subst after_read threads_after_read reader_done.
    econstructor; eauto.
  - split; [constructor |].
    split.
    + subst after_read after_write threads_after_read writer_done.
      econstructor; eauto.
      rewrite update_diff; [exact Hwriter | exact Hdistinct].
    + unfold pico_accesses_conflict; simpl.
      split; [exact Hdistinct |].
      split; [reflexivity |].
      right. reflexivity.
Qed.

Definition pico_pool_finished (cfg : pico_pool_config) : Prop :=
  Forall (fun e => exists result rGamma V, e = CoreDone result rGamma V)
    (pool_threads cfg).

Definition pico_pool_results (cfg : pico_pool_config) : list pico_core_val :=
  fold_right
    (fun e results =>
      match pico_core_to_val e with
      | Some result => result :: results
      | None => results
      end)
    [] (pool_threads cfg).

Definition pico_pool_safe_under `{CacheMemoryModel} (CT : class_table)
    (initial : pico_pool_config) (Inv : pico_core_state -> Prop) : Prop :=
  forall cfg,
    pico_pool_steps CT initial cfg ->
    Inv (pool_state cfg).

Definition pico_pool_results_satisfy
    (ResultOK : pico_core_val -> Prop) (cfg : pico_pool_config) : Prop :=
  pico_pool_finished cfg ->
  Forall ResultOK (pico_pool_results cfg).

(** A benign race is an actual semantic race whose shared-state invariant is
    preserved and whose completed thread results satisfy the client contract. *)
Definition pico_semantic_benign_race `{CacheMemoryModel} (CT : class_table)
    (initial : pico_pool_config)
    (Inv : pico_core_state -> Prop)
    (ResultOK : pico_core_val -> Prop) : Prop :=
  pico_semantic_race CT initial /\
  pico_pool_safe_under CT initial Inv /\
  forall cfg,
    pico_pool_steps CT initial cfg ->
    pico_pool_results_satisfy ResultOK cfg.

Theorem pico_semantic_race_with_contract_is_benign :
  forall `{CacheMemoryModel} CT initial Inv ResultOK,
    pico_semantic_race CT initial ->
    Inv (pool_state initial) ->
    (forall e state e' state',
      pico_core_step CT e state e' state' ->
      Inv state ->
      Inv state') ->
    (forall cfg,
      pico_pool_steps CT initial cfg ->
      pico_pool_results_satisfy ResultOK cfg) ->
    pico_semantic_benign_race CT initial Inv ResultOK.
Proof.
  intros Hmem CT initial Inv ResultOK Hrace Hinitial Hpreserved Hresults.
  split; [exact Hrace |].
  split; [| exact Hresults].
  intros cfg Hsteps.
  eapply pico_pool_steps_preserve_state_invariant; eauto.
Qed.

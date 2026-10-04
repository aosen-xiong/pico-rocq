From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoSemanticConcurrency.

(** * Access-Labeled PICO Pool Executions

    The existing pool semantics remains the source of operational steps.  This
    relation additionally records every successful shared field access, while
    allocation, calls, returns, local assignments, and control steps are
    silent. *)

Inductive pico_pool_labeled_step `{CacheMemoryModel} (CT : class_table) :
    pico_pool_config -> option pico_access_event -> pico_pool_config -> Prop :=
  | PicoPoolLabeledAccess : forall cfg event cfg',
      pico_pool_access CT cfg event cfg' ->
      pico_pool_labeled_step CT cfg (Some event) cfg'
  | PicoPoolLabeledSilent : forall cfg cfg',
      pico_pool_step CT cfg cfg' ->
      (forall event, ~ pico_pool_access CT cfg event cfg') ->
      pico_pool_labeled_step CT cfg None cfg'.

Inductive pico_pool_access_trace `{CacheMemoryModel} (CT : class_table) :
    pico_pool_config -> list pico_access_event -> pico_pool_config -> Prop :=
  | PicoPoolAccessTraceRefl : forall cfg,
      pico_pool_access_trace CT cfg [] cfg
  | PicoPoolAccessTraceSilent : forall cfg1 cfg2 cfg3 accesses,
      pico_pool_labeled_step CT cfg1 None cfg2 ->
      pico_pool_access_trace CT cfg2 accesses cfg3 ->
      pico_pool_access_trace CT cfg1 accesses cfg3
  | PicoPoolAccessTraceAccess : forall cfg1 cfg2 cfg3 event accesses,
      pico_pool_labeled_step CT cfg1 (Some event) cfg2 ->
      pico_pool_access_trace CT cfg2 accesses cfg3 ->
      pico_pool_access_trace CT cfg1 (event :: accesses) cfg3.

Lemma pico_pool_labeled_step_erases :
  forall `{CacheMemoryModel} CT cfg label cfg',
    pico_pool_labeled_step CT cfg label cfg' ->
    pico_pool_step CT cfg cfg'.
Proof.
  intros Hmem CT cfg label cfg' Hstep.
  inversion Hstep; subst.
  - eapply pico_pool_access_is_step; eauto.
  - assumption.
Qed.

Theorem pico_pool_access_trace_erases :
  forall `{CacheMemoryModel} CT cfg accesses cfg',
    pico_pool_access_trace CT cfg accesses cfg' ->
    pico_pool_steps CT cfg cfg'.
Proof.
  intros Hmem CT cfg accesses cfg' Htrace.
  induction Htrace.
  - constructor.
  - econstructor; [eapply pico_pool_labeled_step_erases; eauto | exact IHHtrace].
  - econstructor; [eapply pico_pool_labeled_step_erases; eauto | exact IHHtrace].
Qed.

Lemma pico_pool_access_trace_trans :
  forall `{CacheMemoryModel} CT cfg1 cfg2 cfg3 first second,
    pico_pool_access_trace CT cfg1 first cfg2 ->
    pico_pool_access_trace CT cfg2 second cfg3 ->
    pico_pool_access_trace CT cfg1 (first ++ second) cfg3.
Proof.
  intros Hmem CT cfg1 cfg2 cfg3 first second Hfirst Hsecond.
  induction Hfirst as
    [cfg
    | cfg1 cfg2 cfg_mid accesses Hlabel Htail IH
    | cfg1 cfg2 cfg_mid event accesses Hlabel Htail IH].
  - simpl. exact Hsecond.
  - eapply PicoPoolAccessTraceSilent; [exact Hlabel |].
    apply IH. exact Hsecond.
  - simpl. eapply PicoPoolAccessTraceAccess; [exact Hlabel |].
    apply IH. exact Hsecond.
Qed.

Lemma pico_pool_access_trace_one :
  forall `{CacheMemoryModel} CT cfg event cfg',
    pico_pool_access CT cfg event cfg' ->
    pico_pool_access_trace CT cfg [event] cfg'.
Proof.
  intros Hmem CT cfg event cfg' Haccess.
  eapply PicoPoolAccessTraceAccess.
  - eapply PicoPoolLabeledAccess. exact Haccess.
  - constructor.
Qed.

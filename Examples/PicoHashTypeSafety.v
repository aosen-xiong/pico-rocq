From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep ViewpointAdaptation.
Require Import Examples.PicoIfZeroCache
  Examples.PicoHashMethod
  Examples.PicoConcreteHashProvider
  Examples.PicoSemanticConcurrencyExamples
  Examples.PicoSemanticConcurrencySafety.
Require Import PICOBridge.PicoCoreLanguage
  PICOBridge.PicoMemoryModel PICOBridge.PicoCoreInvariant
  PICOBridge.PicoSemanticConcurrency PICOBridge.PicoCoreTypeSafety.

(** * Type Safety of the Concurrent Hash Calls

    The pool of any number of hash calls on one receiver is a typed pool, so
    the type-safety theorem applies to it: in every interleaving, every call
    stays well typed and none raises the mutation exception. *)

Definition pico_hash_caller_senv : s_env :=
  [pico_hash_witness_receiver_type; int_type].

Lemma pico_hash_concurrent_initial_state_wf :
  pico_core_state_wf
    pico_hash_concurrent_initial_state.
Proof.
  assert (Hempty : pico_core_state_wf
    (mkPicoCoreState [] empty_wm_state)).
  {
    split.
    - split; [reflexivity |]. intros loc o Hobj.
      unfold runtime_getObj in Hobj. destruct loc; discriminate.
    - intros loc o f current Hobj.
      unfold runtime_getObj in Hobj. destruct loc; discriminate.
  }
  assert (Howner : pico_core_state_wf
    (mkPicoCoreState ([] ++ [pico_hash_concurrent_owner])
      (pico_core_alloc_weak empty_wm_state pico_hash_concurrent_owner 0))).
  { apply pico_core_state_wf_alloc. exact Hempty. }
  change (pico_core_state_wf
    (mkPicoCoreState
      (([] ++ [pico_hash_concurrent_owner]) ++ [pico_hash_witness_object])
      (pico_core_alloc_weak
        (pico_core_alloc_weak empty_wm_state pico_hash_concurrent_owner 0)
        pico_hash_witness_object 0))).
  apply pico_core_state_wf_alloc. exact Howner.
Qed.

Lemma pico_hash_concurrent_initial_histories_typed :
  histories_typed pico_hash_concurrent_CT
    pico_hash_concurrent_initial_state.
Proof.
  intros loc f v Hin.
  assert (Hheap : exists o,
    runtime_getObj pico_hash_concurrent_initial_heap loc = Some o /\
    nth_error (fields_map o) f = Some v /\ v <> Null_a).
  {
    destruct loc as [| [| loc]].
    - destruct f; cbv in Hin; contradiction.
    - exists pico_hash_witness_object.
      destruct f as [| [| f]]; cbv in Hin.
      + destruct Hin as [<- | Hfalse]; [| contradiction].
        repeat split; discriminate.
      + destruct Hin as [<- | Hfalse]; [| contradiction].
        repeat split; discriminate.
      + destruct f; contradiction.
    - destruct loc; cbv in Hin; contradiction.
  }
  destruct Hheap as (o & Hobj & Hfield & Hnonnull).
  eapply wf_heap_field_value_ok; eauto.
  - exact pico_hash_concurrent_heap_wf.
  - intros Hnull. contradiction.
Qed.

Lemma pico_hash_concurrent_initial_typed_state :
  typed_state_inv pico_hash_concurrent_CT
    pico_hash_concurrent_initial_state.
Proof.
  split; [exact pico_hash_concurrent_initial_histories_typed |].
  split; [exact pico_hash_concurrent_initial_state_wf |].
  exact pico_hash_concurrent_heap_wf.
Qed.

Lemma pico_hash_caller_config_wf :
  wf_r_config pico_hash_concurrent_CT pico_hash_caller_senv
    pico_hash_concurrent_caller pico_hash_concurrent_initial_heap.
Proof.
  unfold wf_r_config.
  split; [exact pico_hash_concurrent_class_table_wf |].
  split; [exact pico_hash_concurrent_heap_wf |].
  split.
  - unfold wf_renv, pico_hash_concurrent_initial_heap,
      pico_hash_concurrent_caller, pico_hash_concurrent_receiver. simpl.
    split; [lia |]. split.
    + exists 1. split; reflexivity || lia.
    + constructor; [simpl; trivial | constructor; [trivial | constructor]].
  - split.
    + exact pico_hash_concurrent_wf_env2.
    + split; [reflexivity |].
      intros receiver qcontext Hreceiver Hmut i Hi T Htype.
      simpl in Hreceiver. inversion Hreceiver; subst receiver.
      unfold pico_hash_concurrent_initial_heap, pico_hash_witness_object,
        r_muttype, runtime_getObj in Hmut. simpl in Hmut.
      inversion Hmut; subst qcontext.
      destruct i as [| [| i]]; [| | simpl in Hi; lia].
      * simpl in Htype. inversion Htype; subst T. simpl.
        unfold wf_r_typable, r_type, pico_hash_concurrent_initial_heap,
          pico_hash_witness_object, runtime_getObj. simpl.
        split.
        -- apply base_ref. apply class_refl.
           unfold pico_hash_witness_class. simpl. lia.
        -- trivial.
      * simpl in Htype. inversion Htype; subst T. reflexivity.
Qed.

Lemma pico_hash_caller_typed_env :
  pico_core_typed_env pico_hash_concurrent_CT pico_hash_caller_senv
    pico_hash_concurrent_caller pico_hash_concurrent_initial_heap.
Proof.
  exists Imm_r, pico_hash_concurrent_receiver.
  split; [exact pico_hash_caller_config_wf |].
  split; [reflexivity |].
  split; [reflexivity |].
  intros x T Hx.
  destruct x as [| [| x]]; simpl in Hx.
  - inversion Hx; subst T.
    exists (Iot pico_hash_concurrent_receiver). split; [reflexivity |].
    simpl.
    unfold wf_r_typable, r_type, pico_hash_concurrent_initial_heap,
      pico_hash_witness_object, runtime_getObj. simpl.
    split.
    + apply base_ref. apply class_refl.
      unfold pico_hash_witness_class. simpl. lia.
    + trivial.
  - inversion Hx; subst T.
    exists (Int 0). split; reflexivity.
  - destruct x; discriminate.
Qed.

Lemma pico_hash_call_typing :
  stmt_typing pico_hash_concurrent_CT pico_hash_caller_senv AbstractState
    (SCall 1 pico_hash_concurrent_method 0 []) pico_hash_caller_senv.
Proof.
  eapply ST_Call with
    (Tx := int_type) (Ty := pico_hash_witness_receiver_type)
    (argtypes := []) (Tthis := pico_hash_witness_receiver_type)
    (C := pico_hash_witness_class)
    (mdef := pico_hash_concurrent_method_def).
  - exact pico_hash_concurrent_wf_env2.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact pico_hash_concurrent_find_method.
  - discriminate.
  - apply qtype_refl; [reflexivity | discriminate].
  - left. apply qtype_refl; [| discriminate].
    unfold wf_qualified_base. simpl.
    unfold pico_hash_witness_class, pico_hash_concurrent_CT. simpl. lia.
  - constructor.
  - left. reflexivity.
Qed.

Lemma pico_hash_n_call_pool_typed : forall n,
  typed_pool pico_hash_concurrent_CT
    (pico_hash_n_call_pool n).
Proof.
  intros n.
  split; [exact pico_hash_concurrent_initial_typed_state |].
  simpl. apply Forall_forall.
  intros e Hin. apply repeat_spec in Hin. subst e.
  eapply thread_typed_start.
  - exact pico_hash_call_typing.
  - exact pico_hash_caller_typed_env.
Qed.

(** In every interleaving of any number of hash calls, every call stays well
    typed and no call raises the mutation exception. *)
Theorem pico_hash_n_calls_type_safe : forall n cfg,
  @pico_pool_steps history_cache_memory_model pico_hash_concurrent_CT
    (pico_hash_n_call_pool n) cfg ->
  typed_pool pico_hash_concurrent_CT cfg /\
  forall r rGamma V,
    List.In (CoreDone r rGamma V) (pool_threads cfg) ->
    r <> MUTATIONEXP.
Proof.
  intros n cfg Hsteps.
  split.
  - eapply typed_pool_preservation; eauto.
    apply pico_hash_n_call_pool_typed.
  - intros r rGamma V Hin.
    eapply typed_pool_no_mutation_exception; eauto.
    apply pico_hash_n_call_pool_typed.
Qed.

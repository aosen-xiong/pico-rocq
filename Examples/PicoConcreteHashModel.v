From Stdlib Require Import List Lia PeanoNat FunctionalExtensionality.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import ownp.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep Core.GenericCacheProtocol
  Core.GenericDerivedCache Examples.PicoIfZeroCacheExamples.
Require Import Iris.GenericCacheGhostState.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisSemImmOperations
  PICOBridge.PicoIrisSemImmLogicalRelation PICOBridge.PicoIrisSemanticAPI
  PICOBridge.PicoCacheTyping PICOBridge.PicoIrisTypingFundamental.
Require Import Reachability PICOBridge.PicoDerivationNoninterference
  PICOBridge.PicoDerivationCache PICOBridge.PicoDerivationSmallStep.
Require DerivedCache.
Require Core.RelyGuarantee.
Require Import Examples.PicoSemanticCacheAPIExamples.
Require Export Examples.PicoConcreteHashProvider.

Theorem pico_concrete_hash_value_adapter_api : forall receiver,
  PicoHashCacheValueAdapter (pico_hash_cache_adapter receiver).
Proof. intros receiver v. apply pico_concrete_hash_value_adapter. Qed.

Section concrete_hash_api.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : @CacheMemoryModelProgress Hmem}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Sigma}.
  Context `{!genericCacheG hash_cache_protocol Sigma}.

  Theorem pico_heap_hash_callable_api_wfI
      receiver m h0 hash_value C receiver_type method compute
      (Htyping : stmt_typing CT [receiver_type] AbstractState
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hreceiver : sbase receiver_type = TRef C)
      (Hoverride : forall parent_def parent mdef_parent qc,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        bound CT C = Some qc ->
        FindMethodWithName CT parent method mdef_parent ->
        method_override_compatible CT qc
          (pico_hash_method_signature receiver_type method)
          (msignature mdef_parent))
      (Hcache_runtime : PicoHashCacheRuntimeAssignable CT receiver_type) :
    pico_ts_derived_computation_atI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      (pico_hash_cache_receiver (pico_hash_cache_adapter receiver))
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_callable_method_wfI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      C (pico_hash_method_def_with receiver_type method compute)
      (pico_hash_method_contract_at receiver hash_value) ∗
    pico_exported_methodI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      (pico_hash_method_contract_at receiver hash_value)
      (pico_hash_method_def_with receiver_type method compute).
  Proof.
    iIntros "#Hcompute".
    assert (Hfield_at : forall rGamma h loc,
      pico_core_typed_env CT [receiver_type; int_type; int_type] rGamma h ->
      runtime_getVal rGamma cache_receiver = Some (Iot loc) ->
      loc = receiver ->
      pico_core_cache_field hash_cache_protocol
        (pico_hash_cache_adapter receiver) (loc, hash_cache_field) =
        Some HashField).
    { intros rGamma h loc Henv Hentry ->. apply pico_concrete_hash_adapter_at. }
    iPoseProof (@pico_hash_method_callable_for_with_computationI
      Hmem Hprogress CT Sigma ownPGS0 genericCacheG0
      (pico_hash_cache_adapter receiver) hash_value (fun loc => loc = receiver)
      (pico_concrete_hash_semimm CT receiver m h0 hash_value)
      receiver_type method compute Htyping Hfield_at
      (pico_concrete_hash_value_adapter_api receiver) Hcache_runtime
      with "Hcompute") as "#Hcallable".
    iSplit.
    - iSplit; [iPureIntro | iExact "Hcallable"].
      eapply pico_hash_method_def_with_wf; eauto.
    - iApply pico_callable_method_exportI. iExact "Hcallable".
  Qed.

  (** A concrete client call consumes the installed hash API and resumes with
      both its functional contract and PICO's typed caller environment.  The
      closed-dispatch premise states that this singleton environment covers
      every dynamic subtype admitted at this call site. *)
  Theorem pico_heap_hash_api_call_wpI
      receiver m h0 hash_value C receiver_type method compute
      sGamma sGamma' mt caller x y args vals h sigma V K E Phi
      (Hmethod_typing : stmt_typing CT [receiver_type] AbstractState
        (pico_hash_method_stmt_with compute)
        [receiver_type; int_type; int_type])
      (Hoverride : forall parent_def parent mdef_parent qc,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        bound CT C = Some qc ->
        FindMethodWithName CT parent method mdef_parent ->
        method_override_compatible CT qc
          (pico_hash_method_signature receiver_type method)
          (msignature mdef_parent))
      (Hcache_runtime : PicoHashCacheRuntimeAssignable CT receiver_type)
      (Hcall_typing : stmt_typing CT sGamma mt
        (SCall x method y args) sGamma')
      (Hstatic_receiver : static_getType sGamma y = Some receiver_type)
      (Hreceiver_base : sbase receiver_type = TRef C)
      (Hclosed_dispatch : forall D mdef,
        class_subtype CT D C ->
        FindMethodWithName CT D method mdef -> D = C)
      (Henv : pico_core_typed_env CT sGamma caller h)
      (Hreceiver : runtime_getVal caller y = Some (Iot receiver))
      (Hbase : r_basetype h receiver = Some C)
      (Hfind : FindMethodWithName CT C method
        (pico_hash_method_def_with receiver_type method compute))
      (Hargs : runtime_lookup_list caller args = Some vals)
      (Hstate : pico_core_lr_state CT (mkPicoCoreState h sigma)) :
    pico_ts_derived_computation_atI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      (pico_hash_cache_receiver (pico_hash_cache_adapter receiver))
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      compute cache_tmp (Int hash_value) -∗
    pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
      hash_value (pico_hash_cache_adapter receiver)
      (pico_concrete_hash_semimm CT receiver m h0 hash_value)
      (mkPicoCoreState h sigma) -∗
    ownP (mkPicoCoreState h sigma) -∗
    (▷ ∀ callee_done final_state V' returned,
      ⌜pico_core_typed_env CT sGamma'
        (set_vars caller (update x returned (vars caller)))
        (pcs_heap final_state)⌝ -∗
      ⌜pico_core_lr_state CT final_state⌝ -∗
      ⌜pico_core_heap_types_extend h (pcs_heap final_state)⌝ -∗
      ⌜psmc_post (pico_hash_method_contract_at receiver hash_value)
        (mkr_env (Iot receiver :: vals))
        (mkPicoCoreVal OK callee_done V')⌝ -∗
      pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value) final_state -∗
      ownP final_state -∗
      WP CoreRun
        (set_vars caller (update x returned (vars caller)))
        SSkip V' K @ NotStuck; E {{ Phi }}) -∗
    WP CoreRun caller (SCall x method y args) V K
      @ NotStuck; E {{ Phi }}.
  Proof.
    iIntros "#Hcompute HR Hown Hcontinue".
    iPoseProof (pico_heap_hash_callable_api_wfI receiver m h0 hash_value C
      receiver_type method compute Hmethod_typing Hreceiver_base Hoverride
      Hcache_runtime
      with "Hcompute") as "[#Hapi _]".
    set (contract := pico_hash_method_contract_at receiver hash_value).
    set (Psi := pico_singleton_semantic_method_env C method contract).
    iPoseProof (pico_singleton_semantic_method_env_wfI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      C method contract
      (pico_hash_method_def_with receiver_type method compute) Hfind
      with "Hapi") as "#Hsemantic".
    assert (Hsummary : pico_ts_call_summary CT Psi sGamma x y method args).
    {
      exists receiver_type, C, contract. repeat split; try assumption.
      - unfold Psi, pico_singleton_semantic_method_env.
        rewrite !Nat.eqb_refl. reflexivity.
      - intros D mdef Hsub HfindD.
        assert (D = C) by (eapply Hclosed_dispatch; eauto). subst D.
        unfold Psi, pico_singleton_semantic_method_env.
        rewrite !Nat.eqb_refl. reflexivity.
    }
    iApply (pico_semantic_typed_call_wpI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      Psi sGamma sGamma' mt caller x y method args receiver C
      (pico_hash_method_def_with receiver_type method compute) vals
      h sigma V K E Phi Hcall_typing Hsummary Henv Hreceiver Hbase Hfind
      Hargs Hstate with "Hsemantic HR Hown [Hcontinue]").
    - intros advertised Hspec.
      unfold Psi, pico_singleton_semantic_method_env in Hspec.
      rewrite !Nat.eqb_refl in Hspec. inversion Hspec; subst advertised.
      exists receiver. split; [reflexivity | reflexivity].
    - iNext. iIntros (advertised callee_done final_state V' returned)
        "%Hspec %Hcaller_typed %Hstate_final %Hextend %Hpost HR Hown".
      unfold Psi, pico_singleton_semantic_method_env in Hspec.
      rewrite !Nat.eqb_refl in Hspec. inversion Hspec; subst advertised.
      iApply ("Hcontinue" with "[] [] [] [] HR Hown").
      + iPureIntro. exact Hcaller_typed.
      + iPureIntro. exact Hstate_final.
      + iPureIntro. exact Hextend.
      + iPureIntro. unfold contract in Hpost. exact Hpost.
  Qed.

  (** The payload read is a derived computation for the concrete provider:
      from any frame whose receiver is the provider's receiver, it stores the
      provider's hash in [cache_tmp] and leaves the state unchanged. *)
  Lemma pico_hash_read_computationI receiver m h0 hash_value
      (Hfoot : pico_hash_abstract_field CT h0 receiver (receiver, 1))
      (Hpayload : DerivedCache.field_read h0 receiver 1 (Int hash_value)) :
    ⊢ pico_derived_computation_atI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      (pico_hash_cache_receiver (pico_hash_cache_adapter receiver))
      pico_hash_read_compute_stmt cache_tmp (Int hash_value).
  Proof.
    iModIntro.
    iIntros (rGamma loc [h sigma] V K E Phi old)
      "%Hreceiver %Hok %Hold Hworld Hown Hnext".
    destruct (pico_hash_cache_adapter_some receiver (loc, hash_cache_field)
      HashField Hok) as [Haddr _].
    unfold pico_hash_cache_addr in Haddr. injection Haddr as ->.
    iDestruct "Hworld" as (gamma) "[%Hinv Hsem]".
    have Hprovider : pico_hash_provider_inv CT receiver m h0 hash_value
      (mkPicoCoreState h sigma) := Hinv.
    destruct Hprovider as (_ & (_ & _ & _ & Hhist & _) & _).
    destruct (Hhist receiver 1 (Int hash_value) Hfoot Hpayload)
      as [Hnonempty Honly].
    assert (Hhistory : history_of sigma (receiver, 1) <> []).
    { intros Hnil. apply Hnonempty. unfold values_written_to.
      rewrite Hnil. reflexivity. }
    destruct (wm_read_nonempty sigma V (receiver, 1) Hhistory)
      as (v & V1 & Hread).
    assert (Hready : exists next state',
      pico_core_step CT (CoreRun rGamma pico_hash_read_compute_stmt V K)
        (mkPicoCoreState h sigma) next state').
    { eexists _, _. unfold pico_hash_read_compute_stmt.
      eapply PCS_AssignField; [exact Hold | exact Hreceiver | exact Hread]. }
    iApply (pico_core_ownP_wp_from_direct_step_contI CT E Phi _ _ Hready
      with "Hown [Hsem Hnext]").
    iNext. iIntros (next state') "%Hactual Hown".
    destruct (pico_hash_read_compute_step_inv CT rGamma V K h sigma next state'
      receiver hash_value Hreceiver Honly Hactual) as (V2 & -> & ->).
    iApply ("Hnext" $! V2 with "[Hsem] Hown").
    iExists gamma. iFrame "Hsem". iPureIntro. exact Hinv.
  Qed.

  Lemma pico_hash_read_ts_computationI receiver m h0 hash_value
      C receiver_type
      (Hreceiver_base : sbase receiver_type = TRef C)
      (Hpayload_abstract : abstract_field CT C 1)
      (Hfoot : pico_hash_abstract_field CT h0 receiver (receiver, 1))
      (Hpayload : DerivedCache.field_read h0 receiver 1 (Int hash_value)) :
    ⊢ pico_ts_derived_computation_atI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      (pico_hash_cache_receiver (pico_hash_cache_adapter receiver))
      ts_no_calls [receiver_type; int_type; int_type]
      [receiver_type; int_type; int_type]
      pico_hash_read_compute_stmt cache_tmp (Int hash_value).
  Proof.
    iSplit.
    - iPureIntro. constructor.
      eapply TSERO_Field with (T := receiver_type) (C := C);
        [reflexivity | exact Hreceiver_base | exact Hpayload_abstract].
    - iApply pico_hash_read_computationI; assumption.
  Qed.

  (** The cached hash method that reads its payload is installed as a
      callable and exported API method with no separate computation
      premise. *)
  Theorem pico_heap_hash_read_callable_api_wfI
      receiver m h0 hash_value C receiver_type method
      (Htyping : stmt_typing CT [receiver_type] AbstractState
        (pico_hash_method_stmt_with pico_hash_read_compute_stmt)
        [receiver_type; int_type; int_type])
      (Hreceiver : sbase receiver_type = TRef C)
      (Hoverride : forall parent_def parent mdef_parent qc,
        find_class CT C = Some parent_def ->
        super (signature parent_def) = Some parent ->
        bound CT C = Some qc ->
        FindMethodWithName CT parent method mdef_parent ->
        method_override_compatible CT qc
          (pico_hash_method_signature receiver_type method)
          (msignature mdef_parent))
      (Hcache_runtime : PicoHashCacheRuntimeAssignable CT receiver_type)
      (Hpayload_abstract : abstract_field CT C 1)
      (Hfoot : pico_hash_abstract_field CT h0 receiver (receiver, 1))
      (Hpayload : DerivedCache.field_read h0 receiver 1 (Int hash_value)) :
    ⊢ pico_callable_method_wfI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      C (pico_hash_method_def_with receiver_type method
          pico_hash_read_compute_stmt)
      (pico_hash_method_contract_at receiver hash_value) ∗
    pico_exported_methodI CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        hash_value (pico_hash_cache_adapter receiver)
        (pico_concrete_hash_semimm CT receiver m h0 hash_value))
      (pico_hash_method_contract_at receiver hash_value)
      (pico_hash_method_def_with receiver_type method
        pico_hash_read_compute_stmt).
  Proof.
    iApply (pico_heap_hash_callable_api_wfI receiver m h0 hash_value C
      receiver_type method pico_hash_read_compute_stmt Htyping Hreceiver
      Hoverride Hcache_runtime).
    iApply pico_hash_read_ts_computationI; eassumption.
  Qed.
End concrete_hash_api.

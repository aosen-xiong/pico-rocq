From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Require Import Syntax DerivedCache PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.

(** * Pure Iris Staging Layer for PICO Semantic Cache Safety

    This file intentionally mirrors the pure Rocq theorem as pure Iris facts.
    It is a staging point before introducing stronger ghost state or a full
    type-indexed logical relation for PICO typing. *)

Section pico_iris_semantic_cache.
  Context {PROP : bi}.

(** Pure Iris view of the concrete PICO cache-history invariant. *)
  Definition wm_config_cache_history_stateI
      (cfg : wm_config) (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value) : PROP :=
    ⌜wm_config_cache_history_state cfg addr derived abs_vals⌝%I.

(** Pure Iris view of the same invariant after translation to the generic
    [CacheHistOK] predicate. *)
  Definition wm_config_cache_hist_ok_genericI
      (cfg : wm_config) (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value) : PROP :=
    ⌜CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        abs_vals⌝%I.

(** Pure Iris view of config-level cache safety. *)
  Definition cache_safe_configI
      (cfg : wm_config) (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value) : PROP :=
    ⌜cache_safe_config cfg addr derived abs_vals⌝%I.

(** Pure Iris view of semantic cache safety for all reachable executions. *)
  Definition wm_semantic_cache_safe_executionI
      `{CacheMemoryModel} (CT : class_table) (cfg : wm_config)
      (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value) : PROP :=
    ⌜wm_semantic_cache_safe_execution CT cfg addr derived abs_vals⌝%I.

  Definition wm_semantic_cache_safe_underI
      `{CacheMemoryModel} (CT : class_table) (cfg : wm_config)
      (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value)
      (Allowed : wm_config -> Prop) : PROP :=
    ⌜wm_semantic_cache_safe_under CT cfg addr derived abs_vals Allowed⌝%I.

  Lemma wm_config_cache_history_stateI_intro :
    forall cfg addr derived abs_vals
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ wm_config_cache_history_stateI cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hstate.
    iPureIntro.
    exact Hstate.
  Qed.

  Lemma wm_config_cache_history_state_genericI :
    forall cfg addr derived abs_vals
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ wm_config_cache_hist_ok_genericI cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hstate.
    iPureIntro.
    apply wm_cache_history_state_generic.
    exact Hstate.
  Qed.

  Lemma wm_config_cache_hist_ok_generic_stateI :
    forall cfg addr derived abs_vals
      (Hhist : CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        abs_vals),
      ⊢ wm_config_cache_history_stateI cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hhist.
    iPureIntro.
    apply generic_cache_hist_ok_wm_cache_history_state.
    exact Hhist.
  Qed.

  Lemma cache_safe_configI_intro :
    forall cfg addr derived abs_vals
      (Hsafe : cache_safe_config cfg addr derived abs_vals),
      ⊢ cache_safe_configI cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hsafe.
    iPureIntro.
    exact Hsafe.
  Qed.

  Lemma wm_config_cache_history_state_read_validI :
    forall `{CacheMemoryModel} cfg V addr v V' derived abs_vals
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg) V addr v V'),
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem cfg V addr v V' derived abs_vals Hstate Hread.
    iPureIntro.
    eapply wm_config_cache_history_state_read_valid; eauto.
  Qed.

(** A read from a config satisfying the concrete cache-history invariant
    observes a valid generic cache value. *)
  Lemma wm_config_cache_history_state_read_valid_genericI :
    forall `{CacheMemoryModel} cfg V addr v V' derived abs_vals
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg) V addr v V'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem cfg V addr v V' derived abs_vals Hstate Hread.
    iPureIntro.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
    apply wm_cache_history_state_generic.
    exact Hstate.
  Qed.

  Lemma wm_write_allowed_read_valid_genericI :
    forall `{CacheMemoryModel}
           sigma sigma' Vw Vw' Vr addr write_addr val_y v Vr'
           derived abs_vals
           (Hstate : wm_cache_history_state sigma addr derived abs_vals)
           (Hwrite : wm_write sigma sigma' Vw Vw' write_addr val_y)
           (Hallowed :
             wm_write_allowed_for_cache write_addr addr val_y derived abs_vals)
           (Hread : wm_read sigma' Vr addr v Vr'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem sigma sigma' Vw Vw' Vr addr write_addr val_y v Vr'
           derived abs_vals Hstate Hwrite Hallowed Hread.
    iPureIntro.
    eapply wm_write_allowed_read_valid_generic; eauto.
  Qed.

  Lemma wm_config_cache_history_state_read_unknown_or_derivedI :
    forall `{CacheMemoryModel} cfg V addr v V' derived abs_vals
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg) V addr v V'),
      ⊢ (⌜cache_value_unknown v \/
            cache_value_known derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem cfg V addr v V' derived abs_vals Hstate Hread.
    iPureIntro.
    eapply wm_config_cache_history_state_read_unknown_or_derived; eauto.
  Qed.

  Lemma wm_semantic_cache_safe_executionI_intro :
    forall `{CacheMemoryModel} CT cfg addr derived abs_vals
      (Hexec : wm_semantic_cache_safe_execution CT cfg addr derived abs_vals),
      ⊢ wm_semantic_cache_safe_executionI CT cfg addr derived abs_vals.
  Proof.
    intros Hmem CT cfg addr derived abs_vals Hexec.
    iPureIntro.
    exact Hexec.
  Qed.

  Lemma wm_semantic_cache_safe_underI_intro :
    forall `{CacheMemoryModel} CT cfg addr derived abs_vals Allowed
      (Hunder : wm_semantic_cache_safe_under CT cfg addr derived abs_vals Allowed),
      ⊢ wm_semantic_cache_safe_underI CT cfg addr derived abs_vals Allowed.
  Proof.
    intros Hmem CT cfg addr derived abs_vals Allowed Hunder.
    iPureIntro.
    exact Hunder.
  Qed.

  Lemma wm_semantic_cache_safe_execution_read_validI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals V v V'
      (Hexec : wm_semantic_cache_safe_execution CT cfg addr derived abs_vals)
      (Hsteps : wm_steps CT cfg cfg')
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals V v V'
           Hexec Hsteps Hstate Hread.
    iPureIntro.
    pose proof (Hexec cfg' Hsteps Hstate) as Hfinal.
    eapply wm_config_cache_history_state_read_valid; eauto.
  Qed.

(** Semantic cache safety plus a concrete execution gives the generic
    cache-history invariant in the final configuration. *)
  Lemma wm_semantic_cache_safe_execution_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
      (Hexec : wm_semantic_cache_safe_execution CT cfg addr derived abs_vals)
      (Hsteps : wm_steps CT cfg cfg')
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ wm_config_cache_hist_ok_genericI cfg' addr derived abs_vals.
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals Hexec Hsteps Hstate.
    iPureIntro.
    apply wm_cache_history_state_generic.
    exact (Hexec cfg' Hsteps Hstate).
  Qed.

  Lemma wm_semantic_cache_safe_execution_read_valid_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals V v V'
      (Hexec : wm_semantic_cache_safe_execution CT cfg addr derived abs_vals)
      (Hsteps : wm_steps CT cfg cfg')
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals V v V'
           Hexec Hsteps Hstate Hread.
    iPureIntro.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
    apply wm_cache_history_state_generic.
    exact (Hexec cfg' Hsteps Hstate).
  Qed.

  Lemma wm_semantic_cache_safe_execution_read_unknown_or_derivedI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals V v V'
      (Hexec : wm_semantic_cache_safe_execution CT cfg addr derived abs_vals)
      (Hsteps : wm_steps CT cfg cfg')
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_value_unknown v \/
            cache_value_known derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals V v V'
           Hexec Hsteps Hstate Hread.
    iPureIntro.
    pose proof (Hexec cfg' Hsteps Hstate) as Hfinal.
    eapply wm_config_cache_history_state_read_unknown_or_derived; eauto.
  Qed.

  Lemma wm_steps_read_valid_from_allowed_writesI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_transition_writes_allowed_for_cache
          (wc_state c1) (wc_state c2) addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hallowed Hstate Hread.
    iPureIntro.
    eapply wm_steps_read_valid_from_allowed_writes; eauto.
  Qed.

  Lemma wm_steps_read_valid_from_allowed_writes_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_transition_writes_allowed_for_cache
          (wc_state c1) (wc_state c2) addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hallowed Hstate Hread.
    iPureIntro.
    eapply wm_steps_read_valid_from_allowed_writes_generic; eauto.
  Qed.

  Lemma wm_steps_read_valid_from_thread_allowed_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        forall i t,
          nth_error (wc_threads c1) i = Some t ->
          wm_thread_writes_allowed_for_cache t addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hallowed Hstate Hread.
    iPureIntro.
    eapply wm_steps_read_valid_from_thread_allowed_generic; eauto.
  Qed.

  Lemma wm_steps_read_unknown_or_derived_from_allowed_writesI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_transition_writes_allowed_for_cache
          (wc_state c1) (wc_state c2) addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_value_unknown v \/
            cache_value_known derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hallowed Hstate Hread.
    iPureIntro.
    pose proof (wm_steps_preserve_cache_history_from_allowed_writes
      CT cfg cfg' addr derived abs_vals Hsteps Hallowed Hstate) as Hfinal.
    eapply wm_config_cache_history_state_read_unknown_or_derived; eauto.
  Qed.

  Lemma wm_steps_read_valid_from_config_allowedI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_config_threads_allowed_for_cache c1 addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hallowed Hstate Hread.
    iPureIntro.
    eapply wm_steps_read_valid_from_config_allowed; eauto.
    apply wm_steps_allowed_configs_from_global.
    exact Hallowed.
  Qed.

  Lemma wm_steps_read_valid_from_config_allowed_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_config_threads_allowed_for_cache c1 addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hallowed Hstate Hread.
    iPureIntro.
    eapply wm_steps_read_valid_from_config_allowed_generic; eauto.
  Qed.

  Lemma wm_steps_read_valid_from_closed_config_safe_genericI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hsafe_cfg : cache_safe_config cfg addr derived abs_vals)
      (Hclosed : forall c1 c2,
        wm_step CT c1 c2 ->
        cache_safe_config c1 addr derived abs_vals ->
        cache_safe_config c2 addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hsafe_cfg Hclosed Hstate Hread.
    iPureIntro.
    eapply wm_steps_read_valid_from_closed_config_safe_generic; eauto.
  Qed.

  Lemma wm_steps_read_unknown_or_derived_from_config_allowedI :
    forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        wm_config_threads_allowed_for_cache c1 addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
      (Hread : wm_read (wc_state cfg') V addr v V'),
      ⊢ (⌜cache_value_unknown v \/
            cache_value_known derived abs_vals v⌝ : PROP).
  Proof.
    intros Hmem CT cfg cfg' V addr v V' derived abs_vals
           Hsteps Hallowed Hstate Hread.
    iPureIntro.
    pose proof (wm_steps_preserve_cache_history_from_config_allowed
      CT cfg cfg' addr derived abs_vals Hsteps
      (wm_steps_allowed_configs_from_global
        CT cfg cfg'
        (fun c => wm_config_threads_allowed_for_cache c addr derived abs_vals)
        Hallowed)
      Hstate) as Hfinal.
    eapply wm_config_cache_history_state_read_unknown_or_derived; eauto.
  Qed.

  Theorem cache_safe_config_semantic_cache_safe_underI :
    forall `{CacheMemoryModel} CT cfg addr derived abs_vals,
      ⊢ wm_semantic_cache_safe_underI
          CT
          cfg
          addr
          derived
          abs_vals
          (fun c => cache_safe_config c addr derived abs_vals).
  Proof.
    intros Hmem CT cfg addr derived abs_vals.
    iPureIntro.
    apply cache_safe_config_semantic_cache_safe.
  Qed.

  Theorem cache_safe_config_semantic_cache_safeI :
    forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
      (Hsteps : wm_steps CT cfg cfg')
      (Hsafe : forall c1 c2,
        wm_step CT c1 c2 ->
        cache_safe_config c1 addr derived abs_vals)
      (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
      ⊢ wm_config_cache_history_stateI cfg' addr derived abs_vals.
  Proof.
    intros Hmem CT cfg cfg' addr derived abs_vals Hsteps Hsafe Hstate.
    iPureIntro.
    eapply cache_safe_config_semantic_cache_safe; eauto.
  Qed.

  Theorem cache_safe_config_semantic_cache_safe_executionI :
    forall `{CacheMemoryModel} CT cfg addr derived abs_vals
      (Hsafe : forall c1 c2,
        wm_step CT c1 c2 ->
        cache_safe_config c1 addr derived abs_vals),
      ⊢ wm_semantic_cache_safe_executionI CT cfg addr derived abs_vals.
  Proof.
    intros Hmem CT cfg addr derived abs_vals Hsafe.
    iPureIntro.
    intros cfg' Hsteps Hstate.
    eapply cache_safe_config_semantic_cache_safe; eauto.
  Qed.

  Theorem cache_compute_write_safe_semantic_cache_safe_tailI :
    forall `{CacheMemoryModel}
           CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n V sigma cfg'
      (Hsafe : cache_compute_write_safe
        CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals n)
      (Hsteps : wm_steps
        CT
        (mkWMConfig
          sigma
          [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V])
        cfg')
      (Hallowed : forall c1 c2,
        wm_step CT c1 c2 ->
        cache_safe_config c1 (loc, cache_f) derived abs_vals)
      (Hstate : wm_config_cache_history_state
        (mkWMConfig
          sigma
          [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V])
        (loc, cache_f)
        derived
        abs_vals),
      ⊢ wm_config_cache_history_stateI cfg' (loc, cache_f) derived abs_vals.
  Proof.
    intros Hmem CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n V sigma cfg' Hsafe Hsteps Hallowed Hstate.
    iPureIntro.
    eapply cache_safe_config_semantic_cache_safe; eauto.
  Qed.
End pico_iris_semantic_cache.

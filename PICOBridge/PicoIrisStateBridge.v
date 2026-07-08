From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.

Require Import Syntax Helpers DerivedCache PICOBridge.PicoMemoryModel PICOBridge.PicoIrisStateInterp.
Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState Core.GenericDerivedCache.
Require Import Iris.GenericDerivedCacheIris.

(** * Bridge from Iris WP State to PICO Cache State

    The [irisGS] class keeps [state_interp] abstract.  This file does not try
    to construct a new [irisGS] instance yet; instead, it names the contract
    that later state-interpretation work must instantiate: the weak state
    [sigma] exposed by WP is the [wc_state] of the PICO configuration protected
    by [pico_cache_state_interp]. *)

Section pico_iris_state_bridge.
  Context `{Hmem : CacheMemoryModel}.
  Context `{!invGS Σ}.
  Context `{!PicoIrisGhostState.picoCacheG Σ}.

(** Bridge assertion tying Iris's abstract WP state [sigma] to the PICO
    configuration protected by [pico_cache_state_interp]. *)
  Definition pico_wp_state_cfg_bridge
      (sigma : wm_state) (N : namespace) (cfg : wm_config)
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜sigma = wc_state cfg⌝ ∗
    pico_cache_state_interp N cfg addr derived abs_vals.

(** Allocate the bridge for the current weak-memory state of [cfg]. *)
  Lemma pico_wp_state_cfg_bridge_alloc N cfg addr derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    ⊢ |={⊤}=>
      pico_wp_state_cfg_bridge
        (wc_state cfg)
        N
        cfg
        addr
        derived
        abs_vals.
  Proof.
    intros Hstate.
    unfold pico_wp_state_cfg_bridge.
    iMod (pico_cache_state_interp_alloc N cfg addr derived abs_vals Hstate)
      as "Hstate".
    iModIntro.
    iSplit; [done |].
    iExact "Hstate".
  Qed.

  Lemma pico_wp_state_cfg_bridge_state_interp
      E sigma N cfg addr derived abs_vals :
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ⌜sigma = wc_state cfg⌝.
  Proof.
    iIntros "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(%Hsigma & Hstate)".
    iModIntro.
    iSplitL "Hstate".
    - iSplit; [done |].
      iExact "Hstate".
    - done.
  Qed.

  Lemma pico_wp_state_cfg_bridge_target_history_valid
      E sigma N cfg addr derived abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ⌜derived_cache_history_ok
        derived
        abs_vals
        (history_of sigma addr)⌝.
  Proof.
    iIntros (Hsubset) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(%Hsigma & Hstate)".
    iMod (pico_cache_state_interp_target_history_valid
      E N cfg addr derived abs_vals with "Hstate") as "[Hstate %Hvalid]";
      [exact Hsubset |].
    iModIntro.
    iSplitL "Hstate".
    - iSplit; [done |].
      iExact "Hstate".
    - iPureIntro.
      rewrite Hsigma.
      exact Hvalid.
  Qed.

(** Extract generic cache-history validity through the bridge. *)
  Lemma pico_wp_state_cfg_bridge_target_history_valid_generic
      E sigma N cfg addr derived abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ⌜CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        sigma
        abs_vals⌝.
  Proof.
    iIntros (Hsubset) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(%Hsigma & Hstate)".
    iMod (pico_cache_state_interp_target_history_valid_generic
      E N cfg addr derived abs_vals with "Hstate") as "[Hstate %Hvalid]";
      [exact Hsubset |].
    iModIntro.
    iSplitL "Hstate".
    - iSplit; [done |].
      iExact "Hstate".
    - iPureIntro.
      rewrite Hsigma.
      exact Hvalid.
  Qed.

  Lemma pico_wp_state_cfg_bridge_valid_extension_generic
      E sigma0 sigma N cfg addr derived abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        sigma0
        sigma
        abs_vals⌝.
  Proof.
    iIntros (Hsubset) "Hbridge".
    iMod (pico_wp_state_cfg_bridge_target_history_valid_generic
      E sigma N cfg addr derived abs_vals with "Hbridge")
      as "[Hbridge %Hhist]"; [exact Hsubset |].
    iModIntro.
    iFrame.
    iPureIntro.
    intros [] v Hin.
    right.
    eapply Hhist.
    exact Hin.
  Qed.

(** Allocate the generic cache-history ghost interpretation from the bridged
    PICO state. *)
  Lemma pico_wp_state_cfg_bridge_generic_history_interp_alloc
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E sigma N cfg addr abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma).
  Proof.
    iIntros (Hsubset) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(%Hsigma & Hstate)".
    subst sigma.
    iMod (pico_cache_state_interp_generic_history_interp_alloc
      derived E N cfg addr abs_vals with "Hstate")
      as "[Hstate Hgeneric]"; [exact Hsubset |].
    iModIntro.
    iSplitL "Hstate".
    - iSplit; [done |].
      iExact "Hstate".
    - iExact "Hgeneric".
  Qed.

  Lemma pico_wp_state_cfg_bridge_read_valid
      E sigma N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read sigma V addr v V'⌝ ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_target_history_valid
      E sigma N cfg addr derived abs_vals with "Hbridge")
      as "[Hbridge %Hhist]"; [exact Hsubset |].
    iModIntro.
    iFrame.
    iPureIntro.
    eapply cache_history_read_valid; eauto.
  Qed.

  Lemma pico_wp_state_cfg_bridge_read_valid_generic
      E sigma N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read sigma V addr v V'⌝ ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_target_history_valid_generic
      E sigma N cfg addr derived abs_vals with "Hbridge")
      as "[Hbridge %Hhist]"; [exact Hsubset |].
    iModIntro.
    iFrame.
    iPureIntro.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  Qed.

  Lemma pico_wp_state_cfg_bridge_generic_history_read_valid
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E sigma N cfg V addr v V' abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read sigma V addr v V'⌝ ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝.
  Proof.
    iIntros (Hsubset) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_generic_history_interp_alloc
      derived E sigma N cfg addr abs_vals with "Hbridge")
      as "[Hbridge Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iDestruct
      (wm_derived_cache_history_interp_read_valid_preserve
        derived sigma V addr v V' abs_vals γ with "Hgeneric []")
      as "[Hgeneric %Hvalid]".
    {
      iPureIntro.
      exact Hread.
    }
    iModIntro.
    iSplitL "Hbridge".
    - iExact "Hbridge".
    - iExists γ.
      iSplitL "Hgeneric".
      + iExact "Hgeneric".
      + done.
  Qed.

  Theorem pico_wp_state_cfg_bridge_generic_history_refines_pure
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E sigma N cfg addr abs_vals
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        sigma
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset) "Hbridge %Hsafe %Hreads %Hexec".
    iMod (pico_wp_state_cfg_bridge_generic_history_interp_alloc
      derived E sigma N cfg addr abs_vals with "Hbridge")
      as "[Hbridge Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iDestruct
      (wm_derived_cache_history_interp_refines_pure_preserve
        derived
        F
        run_with_cache_trace
        sigma
        addr
        abs_vals
        γ
        args
        tr
        r
        with "Hgeneric [] [] []")
      as "[Hgeneric %Hresult]".
    {
      iPureIntro.
      exact Hsafe.
    }
    {
      iPureIntro.
      exact Hreads.
    }
    {
      iPureIntro.
      exact Hexec.
    }
    iModIntro.
    iSplitL "Hbridge".
    - iExact "Hbridge".
    - iExists γ.
      iSplitL "Hgeneric".
      + iExact "Hgeneric".
      + done.
  Qed.

  Theorem pico_wp_state_cfg_bridge_generic_history_refines_pure_post_extension
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E sigma sigma' N cfg addr abs_vals
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        sigma
        sigma'
        abs_vals⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        sigma'
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset) "Hbridge %Hsafe %Hext %Hreads %Hexec".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(%Hsigma & Hstate)".
    subst sigma.
    iMod
      (pico_cache_state_interp_generic_history_refines_pure_post_extension
        derived E N cfg sigma' addr abs_vals
        F run_with_cache_trace args tr r with "Hstate [] [] [] []")
      as "[Hstate Hresult]"; [exact Hsubset | | | | |].
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hext.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iModIntro.
      iSplitL "Hstate".
      + iSplit; [done |].
        iExact "Hstate".
      + iExact "Hresult".
  Qed.

  Theorem pico_wp_state_cfg_bridge_semantic_immutability_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E sigma sigma' N cfg addr abs_vals
      (Stable : StableAbs wm_state (list Syntax.value))
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    Stable sigma abs_vals ->
    Stable sigma' abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        sigma
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ -∗
    ⌜CacheHistExtendsByTrace
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        sigma
        sigma'
        (run_writes (run_with_cache_trace abs_vals args tr))⌝ ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ'
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    iIntros (Hsubset Hstable Hstable')
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(%Hsigma & Hstate)".
    subst sigma.
    iMod
      (pico_cache_state_interp_semantic_immutability_method_write_extension_post
        derived E N cfg sigma' addr abs_vals Stable
        F run_with_cache_trace args tr r with "Hstate [] [] [] []")
      as "[Hstate Hpost]"; [exact Hsubset | exact Hstable | exact Hstable' | | | | |].
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
    - iModIntro.
      iSplitL "Hstate".
      + iSplit; [done |].
        iExact "Hstate".
      + iExact "Hpost".
  Qed.

  Lemma pico_wp_state_cfg_bridge_read_unknown_or_derived
      E sigma N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read sigma V addr v V'⌝ ={E}=∗
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ∗
    ⌜cache_value_unknown v \/ cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset) "Hbridge Hread".
    iMod (pico_wp_state_cfg_bridge_read_valid
      E sigma N cfg V addr v V' derived abs_vals with "Hbridge Hread")
      as "[Hbridge %Hvalid]"; [exact Hsubset |].
    iModIntro.
    iFrame.
    iPureIntro.
    apply derived_cache_valid_unknown_or_derived.
    apply derived_cache_msg_ok_cache_valid.
    exact Hvalid.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_thread_step
      E N N' CT sigma sigma' e e' addr derived abs_vals :
    ↑N ⊆ E ->
    cache_safe_thread e addr derived abs_vals ->
    wm_thread_step CT sigma e sigma' e' ->
    pico_wp_state_cfg_bridge
      sigma
      N
      (mkWMConfig sigma [e])
      addr
      derived
      abs_vals ={E}=∗
    pico_wp_state_cfg_bridge
      sigma'
      N'
      (mkWMConfig sigma' [e'])
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hsafe Hstep) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod (pico_cache_state_interp_after_thread_step
      E N N' CT sigma sigma' e e' addr derived abs_vals with
      "Hstate") as "Hstate'"; eauto.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_allowed_write_threads
      E N N' sigma sigma' pre_threads post_threads V V'
      write_addr addr val_y derived abs_vals :
    ↑N ⊆ E ->
    wm_write sigma sigma' V V' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_wp_state_cfg_bridge
      sigma
      N
      (mkWMConfig sigma pre_threads)
      addr
      derived
      abs_vals ={E}=∗
    pico_wp_state_cfg_bridge
      sigma'
      N'
      (mkWMConfig sigma' post_threads)
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hwrite Hallowed) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod (pico_cache_state_interp_after_allowed_write_threads
      E N N' sigma sigma' pre_threads post_threads V V'
      write_addr addr val_y derived abs_vals with "Hstate") as "Hstate'";
      eauto.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_allowed_write
      E N N' sigma sigma' threads V V' write_addr addr val_y
      derived abs_vals :
    ↑N ⊆ E ->
    wm_write sigma sigma' V V' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_wp_state_cfg_bridge
      sigma
      N
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals ={E}=∗
    pico_wp_state_cfg_bridge
      sigma'
      N'
      (mkWMConfig sigma' threads)
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hwrite Hallowed) "Hbridge".
    iApply (pico_wp_state_cfg_bridge_after_allowed_write_threads
      E N N' sigma sigma' threads threads V V' write_addr addr val_y
      derived abs_vals with "Hbridge"); eauto.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_allowed_write_threads_read_valid_generic
      E N N' sigma sigma' pre_threads post_threads Vw Vw' Vr
      write_addr addr val_y v Vr' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_write sigma sigma' Vw Vw' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_wp_state_cfg_bridge
      sigma
      N
      (mkWMConfig sigma pre_threads)
      addr
      derived
      abs_vals -∗
    ⌜wm_read sigma' Vr addr v Vr'⌝ ={E}=∗
    pico_wp_state_cfg_bridge
      sigma'
      N'
      (mkWMConfig sigma' post_threads)
      addr
      derived
      abs_vals ∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hwrite Hallowed) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_after_allowed_write_threads
      E N N' sigma sigma' pre_threads post_threads Vw Vw'
      write_addr addr val_y derived abs_vals with "Hbridge")
      as "Hbridge'"; eauto.
    iApply (pico_wp_state_cfg_bridge_read_valid_generic
      E sigma' N' (mkWMConfig sigma' post_threads) Vr addr v Vr'
      derived abs_vals with "Hbridge' []").
    - exact Hsubset'.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_allowed_write_read_valid_generic
      E N N' sigma sigma' threads Vw Vw' Vr
      write_addr addr val_y v Vr' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_write sigma sigma' Vw Vw' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_wp_state_cfg_bridge
      sigma
      N
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals -∗
    ⌜wm_read sigma' Vr addr v Vr'⌝ ={E}=∗
    pico_wp_state_cfg_bridge
      sigma'
      N'
      (mkWMConfig sigma' threads)
      addr
      derived
      abs_vals ∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hwrite Hallowed) "Hbridge Hread".
    iApply (pico_wp_state_cfg_bridge_after_allowed_write_threads_read_valid_generic
      E N N' sigma sigma' threads threads Vw Vw' Vr
      write_addr addr val_y v Vr' derived abs_vals with
      "Hbridge Hread"); eauto.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_fldwrite_step
      E N N' sigma sigma' rΓ V V' x f y loc_x val_y
      addr derived abs_vals :
    ↑N ⊆ E ->
    cache_safe_stmt rΓ addr derived abs_vals (SFldWrite x f y) ->
    runtime_getVal rΓ x = Some (Iot loc_x) ->
    runtime_getVal rΓ y = Some val_y ->
    wm_write sigma sigma' V V' (loc_x, f) val_y ->
    pico_wp_state_cfg_bridge
      sigma
      N
      (mkWMConfig sigma [mkWMThread rΓ (SFldWrite x f y) V])
      addr
      derived
      abs_vals ={E}=∗
    pico_wp_state_cfg_bridge
      sigma'
      N'
      (mkWMConfig sigma' [mkWMThread rΓ SSkip V'])
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hsafe Hx Hy Hwrite) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod (pico_cache_state_interp_after_fldwrite_step
      E N N' sigma sigma' rΓ V V' x f y loc_x val_y
      addr derived abs_vals with "Hstate") as "Hstate'";
      eauto.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hsteps Hsafe) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with "Hstate") as "Hstate'".
    - exact Hsubset.
    - exact Hsteps.
    - exact Hsafe.
    - iModIntro.
      iSplit; [done |].
      iExact "Hstate'".
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_valid_extension_generic
      E N N' CT sigma cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge
      (wc_state cfg')
      N'
      cfg'
      addr
      derived
      abs_vals ∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        sigma
        (wc_state cfg')
        abs_vals⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hbridge".
    iMod (pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'"; eauto.
    iApply (pico_wp_state_cfg_bridge_valid_extension_generic
      E sigma (wc_state cfg') N' cfg' addr derived abs_vals
      with "Hbridge'").
    exact Hsubset'.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_preserved
      E N N' sigma cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hpres) "Hbridge".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod (pico_cache_state_interp_after_steps_preserved
      E N N' cfg cfg' addr derived abs_vals with "Hstate") as "Hstate'".
    - exact Hsubset.
    - exact Hpres.
    - iModIntro.
      iSplit; [done |].
      iExact "Hstate'".
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_preserved_valid_extension_generic
      E N N' sigma cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge
      (wc_state cfg')
      N'
      cfg'
      addr
      derived
      abs_vals ∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        sigma
        (wc_state cfg')
        abs_vals⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hbridge".
    iMod (pico_wp_state_cfg_bridge_after_steps_preserved
      E N N' sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'"; eauto.
    iApply (pico_wp_state_cfg_bridge_valid_extension_generic
      E sigma (wc_state cfg') N' cfg' addr derived abs_vals
      with "Hbridge'").
    exact Hsubset'.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_read_valid
      E N N' CT sigma cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'".
    - exact Hsubset.
    - exact Hsteps.
    - exact Hsafe.
    - iMod (pico_wp_state_cfg_bridge_read_valid
        E (wc_state cfg') N' cfg' V addr v V' derived abs_vals
        with "Hbridge' []") as "[_ %Hok]".
      + exact Hsubset'.
      + iPureIntro.
        exact Hread.
      + iModIntro.
        iPureIntro.
        exact Hok.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_read_valid_generic
      E N N' CT sigma cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'".
    - exact Hsubset.
    - exact Hsteps.
    - exact Hsafe.
    - iMod (pico_wp_state_cfg_bridge_read_valid_generic
        E (wc_state cfg') N' cfg' V addr v V' derived abs_vals
        with "Hbridge' []") as "[_ %Hok]".
      + exact Hsubset'.
      + iPureIntro.
        exact Hread.
      + iModIntro.
        iPureIntro.
        exact Hok.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_generic_history_interp_alloc
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT sigma cfg cfg' addr abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hbridge".
    iMod (pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'"; eauto.
    iApply (pico_wp_state_cfg_bridge_generic_history_interp_alloc
      derived E (wc_state cfg') N' cfg' addr abs_vals with "Hbridge'").
    exact Hsubset'.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_generic_history_read_valid
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT sigma cfg cfg' V addr v V' abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')) ∗
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'"; eauto.
    iApply (pico_wp_state_cfg_bridge_generic_history_read_valid
      derived E (wc_state cfg') N' cfg' V addr v V' abs_vals
      with "Hbridge'"); eauto.
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_generic_history_refines_pure
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT sigma cfg cfg' addr abs_vals
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe)
      "Hbridge %Hmethod %Hreads %Hexec".
    iMod (pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'"; eauto.
    iApply (pico_wp_state_cfg_bridge_generic_history_refines_pure
      derived E (wc_state cfg') N' cfg' addr abs_vals
      F run_with_cache_trace args tr r with "Hbridge'"); eauto.
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_generic_history_refines_pure_post_extension
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT sigma cfg cfg' addr abs_vals
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe)
      "Hbridge %Hmethod %Hreads %Hexec".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(%Hsigma & Hstate)".
    subst sigma.
    iMod
      (pico_cache_state_interp_after_steps_generic_history_refines_pure_post_extension
        derived E N N' CT cfg cfg' addr abs_vals
        F run_with_cache_trace args tr r with "Hstate [] [] []")
      as "[Hstate' Hresult]".
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iModIntro.
      iSplitL "Hstate'".
      + iSplit; [done |].
        iExact "Hstate'".
      + iExact "Hresult".
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT sigma cfg cfg' addr abs_vals
      (Stable : StableAbs wm_state (list Syntax.value))
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    Stable (wc_state cfg) abs_vals ->
    Stable (wc_state cfg') abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ'
        (wc_state cfg')
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe Hstable Hstable')
      "Hbridge %Hmethod %Hreads %Hexec".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod
      (pico_cache_state_interp_after_steps_semantic_immutability_method_post
        derived E N N' CT cfg cfg' addr abs_vals Stable
        F run_with_cache_trace args tr r with "Hstate [] [] []")
      as "[Hstate' Hpost]".
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iModIntro.
      iSplitL "Hstate'".
      + iSplit; [done |].
        iExact "Hstate'".
      + iExact "Hpost".
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT sigma cfg cfg' sigma' addr abs_vals
      (Stable : StableAbs wm_state (list Syntax.value))
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    Stable (wc_state cfg') abs_vals ->
    Stable sigma' abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ -∗
    ⌜CacheHistExtendsByTrace
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg')
        sigma'
        (run_writes (run_with_cache_trace abs_vals args tr))⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ'
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe Hstable Hstable')
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod
      (pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CT cfg cfg' sigma' addr abs_vals Stable
        F run_with_cache_trace args tr r with "Hstate [] [] [] []")
      as "[Hstate' Hpost]".
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
    - iModIntro.
      iSplitL "Hstate'".
      + iSplit; [done |].
        iExact "Hstate'".
      + iExact "Hpost".
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep sigma cfg cfg' sigma' addr abs_vals
      CTabs C loc abs_fields
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CTstep cfg cfg' ->
    (forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_steps_writes_avoid_fields CTstep cfg cfg' loc abs_fields ->
    wm_histories_preserve_fields (wc_state cfg') sigma' loc abs_fields ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ -∗
    ⌜CacheHistExtendsByTrace
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg')
        sigma'
        (run_writes (run_with_cache_trace abs_vals args tr))⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        (pico_wm_stable_abs CTabs C loc abs_fields)
        γ'
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe Havoid Hpres Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    pose proof
      (pico_wm_stable_abs_preserved_by_steps_avoiding_writes
        CTstep CTabs C loc abs_fields cfg cfg' abs_vals
        Hsteps Havoid Hstable) as Hstable'.
    pose proof
      (pico_wm_stable_abs_preserved_by_histories
        CTabs C loc abs_fields (wc_state cfg') sigma' abs_vals
        Hpres Hstable') as Hstable_post.
    iApply
      (pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CTstep sigma cfg cfg' sigma' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hbridge [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Hstable'.
    - exact Hstable_post.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep sigma cfg cfg' sigma' addr abs_vals
      CTabs C loc abs_fields rt_abs
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CTstep cfg cfg' ->
    (forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CTstep C abs_fields ->
    wm_histories_preserve_fields (wc_state cfg') sigma' loc abs_fields ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ -∗
    ⌜CacheHistExtendsByTrace
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg')
        sigma'
        (run_writes (run_with_cache_trace abs_vals args tr))⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        (pico_wm_stable_abs CTabs C loc abs_fields)
        γ'
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    iIntros
      (Hsubset Hsubset' Hsteps Hsafe Htype HC Hfinals Hpres Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    pose proof
      (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
        CTstep CTabs C loc abs_fields cfg cfg' Hsteps
        rt_abs abs_vals Htype HC Hfinals Hstable) as Hstable'.
    pose proof
      (pico_wm_stable_abs_preserved_by_histories
        CTabs C loc abs_fields (wc_state cfg') sigma' abs_vals
        Hpres Hstable') as Hstable_post.
    iApply
      (pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CTstep sigma cfg cfg' sigma' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hbridge [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Hstable'.
    - exact Hstable_post.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_trace_robust_cache_only_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep sigma cfg cfg' sigma' addr abs_vals
      CTabs C loc abs_fields
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CTstep cfg cfg' ->
    (forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_steps_writes_avoid_fields CTstep cfg cfg' loc abs_fields ->
    wm_histories_only_extend_field (wc_state cfg') sigma' addr ->
    wm_write_avoids_fields addr loc abs_fields ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ -∗
    ⌜CacheHistExtendsByTrace
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg')
        sigma'
        (run_writes (run_with_cache_trace abs_vals args tr))⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        (pico_wm_stable_abs CTabs C loc abs_fields)
        γ'
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    iIntros
      (Hsubset Hsubset' Hsteps Hsafe Havoid_steps Honly Havoid_target
       Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod
      (pico_cache_state_interp_after_steps_pico_wm_stable_trace_robust_cache_only_post
        derived E N N' CTstep cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hstate [] [] [] []")
      as "[Hstate' Hpost]".
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Havoid_steps.
    - exact Honly.
    - exact Havoid_target.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
    - iModIntro.
      iSplitL "Hstate'".
      + iSplit; [done |].
        iExact "Hstate'".
      + iExact "Hpost".
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_trace_robust_cache_only_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep sigma cfg cfg' sigma' addr abs_vals
      CTabs C loc abs_fields rt_abs
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CTstep cfg cfg' ->
    (forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CTstep C abs_fields ->
    wm_histories_only_extend_field (wc_state cfg') sigma' addr ->
    wm_write_avoids_fields addr loc abs_fields ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ -∗
    ⌜CacheHistExtendsByTrace
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg')
        sigma'
        (run_writes (run_with_cache_trace abs_vals args tr))⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        (pico_wm_stable_abs CTabs C loc abs_fields)
        γ'
        sigma'
        abs_vals
        (wm_derived_cache_snapshot derived addr sigma').
  Proof.
    iIntros
      (Hsubset Hsubset' Hsteps Hsafe Htype HC Hfinals Honly Havoid_target
       Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    unfold pico_wp_state_cfg_bridge.
    iDestruct "Hbridge" as "(_ & Hstate)".
    iMod
      (pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_trace_robust_cache_only_post
        derived E N N' CTstep cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields rt_abs F run_with_cache_trace args tr r
        with "Hstate [] [] [] []")
      as "[Hstate' Hpost]".
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Htype.
    - exact HC.
    - exact Hfinals.
    - exact Honly.
    - exact Havoid_target.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
    - iModIntro.
      iSplitL "Hstate'".
      + iSplit; [done |].
        iExact "Hstate'".
      + iExact "Hpost".
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep sigma cfg cfg' addr abs_vals
      CTabs C loc abs_fields
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CTstep cfg cfg' ->
    (forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg') abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        (pico_wm_stable_abs CTabs C loc abs_fields)
        γ'
        (wc_state cfg')
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe Hstable Hstable')
      "Hbridge %Hmethod %Hreads %Hexec".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_post
        derived E N N' CTstep sigma cfg cfg' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep sigma cfg cfg' addr abs_vals
      CTabs C loc abs_fields
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CTstep cfg cfg' ->
    (forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_steps_writes_avoid_fields CTstep cfg cfg' loc abs_fields ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        (pico_wm_stable_abs CTabs C loc abs_fields)
        γ'
        (wc_state cfg')
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe Havoid Hstable)
      "Hbridge %Hmethod %Hreads %Hexec".
    pose proof
      (pico_wm_stable_abs_preserved_by_steps_avoiding_writes
        CTstep CTabs C loc abs_fields cfg cfg' abs_vals
        Hsteps Havoid Hstable) as Hstable'.
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_method_post
        derived E N N' CTstep sigma cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep sigma cfg cfg' addr abs_vals
      CTabs C loc abs_fields rt_abs
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CTstep cfg cfg' ->
    (forall c1 c2,
      wm_step CTstep c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CTstep C abs_fields ->
    pico_wm_stable_abs CTabs C loc abs_fields (wc_state cfg) abs_vals ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg')
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ',
      ⌜r = F abs_vals args⌝ ∗
      generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        (pico_wm_stable_abs CTabs C loc abs_fields)
        γ'
        (wc_state cfg')
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros
      (Hsubset Hsubset' Hsteps Hsafe Htype HC Hfinals Hstable)
      "Hbridge %Hmethod %Hreads %Hexec".
    pose proof
      (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
        CTstep CTabs C loc abs_fields cfg cfg' Hsteps
        rt_abs abs_vals Htype HC Hfinals Hstable) as Hstable'.
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_method_post
        derived E N N' CTstep sigma cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsafe.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_read_unknown_or_derived
      E N N' CT sigma cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/ cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hbridge Hread".
    iMod (pico_wp_state_cfg_bridge_after_steps
      E N N' CT sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'".
    - exact Hsubset.
    - exact Hsteps.
    - exact Hsafe.
    - iMod (pico_wp_state_cfg_bridge_read_unknown_or_derived
        E (wc_state cfg') N' cfg' V addr v V' derived abs_vals
        with "Hbridge' Hread") as "[_ %Hok]".
      + exact Hsubset'.
      + iModIntro.
        iPureIntro.
        exact Hok.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_preserved_read_valid
      E N N' sigma cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_after_steps_preserved
      E N N' sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'".
    - exact Hsubset.
    - exact Hpres.
    - iMod (pico_wp_state_cfg_bridge_read_valid
        E (wc_state cfg') N' cfg' V addr v V' derived abs_vals
        with "Hbridge' []") as "[_ %Hok]".
      + exact Hsubset'.
      + iPureIntro.
        exact Hread.
      + iModIntro.
        iPureIntro.
        exact Hok.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_preserved_read_valid_generic
      E N N' sigma cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hbridge %Hread".
    iMod (pico_wp_state_cfg_bridge_after_steps_preserved
      E N N' sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'".
    - exact Hsubset.
    - exact Hpres.
    - iMod (pico_wp_state_cfg_bridge_read_valid_generic
        E (wc_state cfg') N' cfg' V addr v V' derived abs_vals
        with "Hbridge' []") as "[_ %Hok]".
      + exact Hsubset'.
      + iPureIntro.
        exact Hread.
      + iModIntro.
        iPureIntro.
        exact Hok.
  Qed.

  Lemma pico_wp_state_cfg_bridge_after_steps_preserved_read_unknown_or_derived
      E N N' sigma cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/ cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hbridge Hread".
    iMod (pico_wp_state_cfg_bridge_after_steps_preserved
      E N N' sigma cfg cfg' addr derived abs_vals with "Hbridge")
      as "Hbridge'".
    - exact Hsubset.
    - exact Hpres.
    - iMod (pico_wp_state_cfg_bridge_read_unknown_or_derived
        E (wc_state cfg') N' cfg' V addr v V' derived abs_vals
        with "Hbridge' Hread") as "[_ %Hok]".
      + exact Hsubset'.
      + iModIntro.
        iPureIntro.
        exact Hok.
  Qed.

  Lemma pico_wp_state_cfg_bridge_alloc_after_steps_read_valid
      (N N' : namespace) CT cfg cfg' V addr v V' derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_read (wc_state cfg') V addr v V' ->
    ⊢ (|={⊤}=>
      ⌜derived_cache_msg_ok derived abs_vals v⌝ : iProp Σ).
  Proof.
    iIntros (Hinit Hsteps Hsafe Hread).
    iMod (pico_wp_state_cfg_bridge_alloc
      N cfg addr derived abs_vals Hinit) as "Hbridge".
    iApply (pico_wp_state_cfg_bridge_after_steps_read_valid
      ⊤ N N' CT (wc_state cfg) cfg cfg' V addr v V'
      derived abs_vals with "Hbridge").
    - set_solver.
    - set_solver.
    - exact Hsteps.
    - exact Hsafe.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_wp_state_cfg_bridge_alloc_after_steps_read_valid_generic
      (N N' : namespace) CT cfg cfg' V addr v V' derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_read (wc_state cfg') V addr v V' ->
    ⊢ (|={⊤}=>
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝ : iProp Σ).
  Proof.
    iIntros (Hinit Hsteps Hsafe Hread).
    iMod (pico_wp_state_cfg_bridge_alloc
      N cfg addr derived abs_vals Hinit) as "Hbridge".
    iApply (pico_wp_state_cfg_bridge_after_steps_read_valid_generic
      ⊤ N N' CT (wc_state cfg) cfg cfg' V addr v V'
      derived abs_vals with "Hbridge").
    - set_solver.
    - set_solver.
    - exact Hsteps.
    - exact Hsafe.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_wp_state_cfg_bridge_alloc_after_steps_read_unknown_or_derived
      (N N' : namespace) CT cfg cfg' V addr v V' derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    wm_read (wc_state cfg') V addr v V' ->
    ⊢ (|={⊤}=>
      ⌜cache_value_unknown v \/
        cache_value_known derived abs_vals v⌝ : iProp Σ).
  Proof.
    iIntros (Hinit Hsteps Hsafe Hread).
    iMod (pico_wp_state_cfg_bridge_alloc
      N cfg addr derived abs_vals Hinit) as "Hbridge".
    iApply (pico_wp_state_cfg_bridge_after_steps_read_unknown_or_derived
      ⊤ N N' CT (wc_state cfg) cfg cfg' V addr v V'
      derived abs_vals with "Hbridge").
    - set_solver.
    - set_solver.
    - exact Hsteps.
    - exact Hsafe.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_wp_state_cfg_bridge_alloc_after_steps_preserved_read_valid_generic
      (N N' : namespace) cfg cfg' V addr v V' derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    wm_read (wc_state cfg') V addr v V' ->
    ⊢ (|={⊤}=>
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝ : iProp Σ).
  Proof.
    iIntros (Hinit Hpres Hread).
    iMod (pico_wp_state_cfg_bridge_alloc
      N cfg addr derived abs_vals Hinit) as "Hbridge".
    iApply (pico_wp_state_cfg_bridge_after_steps_preserved_read_valid_generic
      ⊤ N N' (wc_state cfg) cfg cfg' V addr v V'
      derived abs_vals with "Hbridge").
    - set_solver.
    - set_solver.
    - exact Hpres.
    - iPureIntro.
      exact Hread.
  Qed.
End pico_iris_state_bridge.

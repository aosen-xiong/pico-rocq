From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.

Require Import Syntax PICOBridge.PicoMemoryModel PICOBridge.PicoIrisLanguage.
Require Import PICOBridge.PicoIrisWP PICOBridge.PicoIrisThreadSafety PICOBridge.PicoIrisStateBridge.

(** * WP State-Bridge Contracts for PICO

    [pico_wp_state_cfg_bridge] records the field-addressed cache-state facade
    for a concrete weak-memory configuration.  Generic Iris WP exposes only the
    abstract [state_interp].  This file names the exact bridge-aware obligation
    that a later concrete [irisGS] instance should satisfy, while keeping the
    current WP lifting theorem parametric in the ordinary Iris state update. *)

Section pico_iris_wp_state_bridge.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!irisGS_gen hlc (pico_language CT) Σ}.
  Context `{!invGS Σ}.
  Context `{!PicoIrisGhostState.picoCacheG Σ}.

(** Plain WP lifting premise for the PICO language, stated without the cache
    state bridge. *)
  Definition pico_wp_state_bridge_lift_premise
      (s : stuckness) (E : coPset) (Φ : val (pico_language CT) -> iProp Σ)
      (e : wm_thread) : iProp Σ :=
    ∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck
        then exists e' sigma', wm_thread_step CT sigma e sigma' e'
        else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }}.

(** Bridge-aware step contract: the abstract WP state is exposed together with
    the PICO cache-state bridge for the singleton thread configuration. *)
  Definition pico_wp_state_bridge_step_contract
      (s : stuckness) (E : coPset) (Φ : val (pico_language CT) -> iProp Σ)
      (e : wm_thread) (N : namespace) (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value)
      : iProp Σ :=
    ∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      state_interp sigma ns (k ++ ks) nt ∗
      pico_wp_state_cfg_bridge
        sigma
        N
        (mkWMConfig sigma [e])
        addr
        derived
        abs_vals ∗
      ⌜if s is NotStuck
        then exists e' sigma', wm_thread_step CT sigma e sigma' e'
        else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        state_interp sigma ns (k ++ ks) nt -∗
        pico_wp_state_cfg_bridge
          sigma
          N
          (mkWMConfig sigma [e])
          addr
          derived
          abs_vals -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }}.

(** Cache-safe lifting premise that additionally passes one-step cache-history
    preservation to the continuation. *)
  Definition pico_wp_state_bridge_cache_safe_lift_premise
      (s : stuckness) (E : coPset) (Φ : val (pico_language CT) -> iProp Σ)
      (e : wm_thread) (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value)
      : iProp Σ :=
    ∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck
        then exists e' sigma', wm_thread_step CT sigma e sigma' e'
        else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        ⌜wm_cache_history_state sigma addr derived abs_vals ->
          wm_cache_history_state sigma' addr derived abs_vals⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }}.

(** Bridge-aware cache-safe step contract.  This is the obligation a future
    concrete state interpretation should discharge. *)
  Definition pico_wp_state_bridge_cache_safe_step_contract
      (s : stuckness) (E : coPset) (Φ : val (pico_language CT) -> iProp Σ)
      (e : wm_thread) (N : namespace) (addr : FieldAddr)
      (derived : list Syntax.value -> nat) (abs_vals : list Syntax.value)
      : iProp Σ :=
    ∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      state_interp sigma ns (k ++ ks) nt ∗
      pico_wp_state_cfg_bridge
        sigma
        N
        (mkWMConfig sigma [e])
        addr
        derived
        abs_vals ∗
      ⌜if s is NotStuck
        then exists e' sigma', wm_thread_step CT sigma e sigma' e'
        else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        ⌜wm_cache_history_state sigma addr derived abs_vals ->
          wm_cache_history_state sigma' addr derived abs_vals⌝ -∗
        state_interp sigma ns (k ++ ks) nt -∗
        pico_wp_state_cfg_bridge
          sigma
          N
          (mkWMConfig sigma [e])
          addr
          derived
          abs_vals -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }}.

  Lemma pico_wp_state_bridge_step_contract_lift_premise
      s E Φ e N addr derived abs_vals :
    pico_wp_state_bridge_step_contract s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_lift_premise s E Φ e.
  Proof.
    unfold pico_wp_state_bridge_step_contract,
      pico_wp_state_bridge_lift_premise.
    iIntros "Hcontract" (sigma ns k ks nt) "Hstate".
    iMod ("Hcontract" with "Hstate")
      as "(Hstate & Hbridge & %Hred & Hstep)".
    iModIntro.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "Hthread Hcred".
    iApply ("Hstep" with "Hthread Hstate Hbridge Hcred").
  Qed.

  Lemma pico_wp_state_bridge_cache_safe_step_contract_lift_premise
      s E Φ e N addr derived abs_vals :
    pico_wp_state_bridge_cache_safe_step_contract
      s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_lift_premise
      s E Φ e addr derived abs_vals.
  Proof.
    unfold pico_wp_state_bridge_cache_safe_step_contract,
      pico_wp_state_bridge_cache_safe_lift_premise.
    iIntros "Hcontract" (sigma ns k ks nt) "Hstate".
    iMod ("Hcontract" with "Hstate")
      as "(Hstate & Hbridge & %Hred & Hstep)".
    iModIntro.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "Hthread Hpres Hcred".
    iApply ("Hstep" with "Hthread Hpres Hstate Hbridge Hcred").
  Qed.

  Lemma pico_wp_state_bridge_step_contract_cache_safe_contract
      s E Φ e N addr derived abs_vals :
    pico_wp_state_bridge_step_contract s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_step_contract
      s E Φ e N addr derived abs_vals.
  Proof.
    unfold pico_wp_state_bridge_step_contract,
      pico_wp_state_bridge_cache_safe_step_contract.
    iIntros "Hcontract" (sigma ns k ks nt) "Hstate".
    iMod ("Hcontract" with "Hstate")
      as "(Hstate & Hbridge & %Hred & Hstep)".
    iModIntro.
    iFrame.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "Hthread _ Hstate Hbridge Hcred".
    iApply ("Hstep" with "Hthread Hstate Hbridge Hcred").
  Qed.

  Lemma pico_wp_state_bridge_step_contract_cache_safe_lift_premise
      s E Φ e N addr derived abs_vals :
    pico_wp_state_bridge_step_contract s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_lift_premise
      s E Φ e addr derived abs_vals.
  Proof.
    iIntros "Hcontract".
    iPoseProof
      (pico_wp_state_bridge_step_contract_cache_safe_contract
        with "Hcontract") as "Hcache_contract".
    iApply (pico_wp_state_bridge_cache_safe_step_contract_lift_premise
      with "Hcache_contract").
  Qed.

  Lemma pico_wp_state_bridge_cache_safe_lift_premise_lift_premise
      s E Φ e addr derived abs_vals :
    pico_thread_cache_safeI e addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_lift_premise
      s E Φ e addr derived abs_vals -∗
    pico_wp_state_bridge_lift_premise s E Φ e.
  Proof.
    unfold pico_wp_state_bridge_cache_safe_lift_premise,
      pico_wp_state_bridge_lift_premise.
    iIntros "Hsafe Hlift" (sigma ns k ks nt) "Hstate".
    iPoseProof (pico_thread_cache_safeI_step_preserves_cacheI with "Hsafe")
      as "Hpres_all".
    iDestruct "Hpres_all" as %Hpres_all.
    iMod ("Hlift" with "Hstate") as "[%Hred Hstep]".
    iModIntro.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "Hthread Hcred".
    iDestruct "Hthread" as %Hthread.
    iApply ("Hstep" with "[//] [] Hcred").
    iPureIntro.
    intros Hhistory.
    eapply Hpres_all; eauto.
  Qed.

  Lemma pico_wp_state_bridge_cache_safe_contract_step_contract
      s E Φ e N addr derived abs_vals :
    pico_thread_cache_safeI e addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_step_contract
      s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract s E Φ e N addr derived abs_vals.
  Proof.
    unfold pico_wp_state_bridge_cache_safe_step_contract,
      pico_wp_state_bridge_step_contract.
    iIntros "Hsafe Hcontract" (sigma ns k ks nt) "Hstate".
    iPoseProof (pico_thread_cache_safeI_step_preserves_cacheI with "Hsafe")
      as "Hpres_all".
    iDestruct "Hpres_all" as %Hpres_all.
    iMod ("Hcontract" with "Hstate")
      as "(Hstate & Hbridge & %Hred & Hstep)".
    iModIntro.
    iFrame.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "Hthread Hstate Hbridge Hcred".
    iDestruct "Hthread" as %Hthread.
    iApply ("Hstep" with "[//] [] Hstate Hbridge Hcred").
    iPureIntro.
    intros Hhistory.
    eapply Hpres_all; eauto.
  Qed.

  Lemma pico_wp_state_bridge_cache_safe_contract_from_step_contract
      s E Φ e N addr derived abs_vals :
    pico_thread_cache_safeI e addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_step_contract
      s E Φ e N addr derived abs_vals.
  Proof.
    unfold pico_wp_state_bridge_step_contract,
      pico_wp_state_bridge_cache_safe_step_contract.
    iIntros "Hsafe Hcontract" (sigma ns k ks nt) "Hstate".
    iMod ("Hcontract" with "Hstate")
      as "(Hstate & Hbridge & %Hred & Hstep)".
    iModIntro.
    iFrame.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "Hthread _ Hstate Hbridge Hcred".
    iApply ("Hstep" with "Hthread Hstate Hbridge Hcred").
  Qed.

End pico_iris_wp_state_bridge.

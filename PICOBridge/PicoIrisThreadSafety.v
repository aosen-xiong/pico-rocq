From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.

Require Import Syntax PICOBridge.PicoMemoryModel PICOBridge.PicoIrisLanguage PICOBridge.PicoIrisWP.

(** * WP-Facing Cache-Safety Facts for PICO Threads

    This is still deliberately pure: [cache_safe_thread] is exposed as an Iris
    proposition, and the WP lifting rule below supplies the one-step
    cache-history preservation fact to the continuation.  A later logical
    relation can replace these pure facts with a semantic interpretation of
    PICO typing rules. *)

Section pico_iris_thread_safety.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!irisGS_gen hlc (pico_language CT) Σ}.

(** Pure Iris assertion that a thread is cache-safe for the target field. *)
  Definition pico_thread_cache_safeI
      (e : wm_thread) (addr : FieldAddr)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜cache_safe_thread e addr derived abs_vals⌝%I.

(** Pure Iris assertion that any one step of this thread preserves the target
    cache-history invariant. *)
  Definition pico_thread_step_preserves_cacheI
      (e : wm_thread) (addr : FieldAddr)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜forall sigma sigma' e',
      wm_thread_step CT sigma e sigma' e' ->
      wm_cache_history_state sigma addr derived abs_vals ->
      wm_cache_history_state sigma' addr derived abs_vals⌝%I.

  Lemma pico_thread_cache_safeI_intro :
    forall e addr derived abs_vals,
      cache_safe_thread e addr derived abs_vals ->
      ⊢ pico_thread_cache_safeI e addr derived abs_vals.
  Proof.
    intros e addr derived abs_vals Hsafe.
    iPureIntro.
    exact Hsafe.
  Qed.

(** Core one-step preservation theorem for cache-safe threads. *)
  Lemma cache_safe_thread_step_preserves_cache :
    forall e addr derived abs_vals sigma sigma' e',
      cache_safe_thread e addr derived abs_vals ->
      wm_thread_step CT sigma e sigma' e' ->
      wm_cache_history_state sigma addr derived abs_vals ->
      wm_cache_history_state sigma' addr derived abs_vals.
  Proof.
    intros e addr derived abs_vals sigma sigma' e' Hsafe Hstep Hstate.
    eapply wm_cache_safe_transition_preserves_cache_history; eauto.
    eapply wm_thread_step_cache_safe_from_thread; eauto.
    apply cache_safe_thread_implies_wm_thread_writes_allowed.
    exact Hsafe.
  Qed.

  Lemma pico_thread_step_preserves_cacheI_intro :
    forall e addr derived abs_vals,
      cache_safe_thread e addr derived abs_vals ->
      ⊢ pico_thread_step_preserves_cacheI e addr derived abs_vals.
  Proof.
    intros e addr derived abs_vals Hsafe.
    iPureIntro.
    intros sigma sigma' e' Hstep Hstate.
      eapply cache_safe_thread_step_preserves_cache; eauto.
  Qed.

  Lemma pico_thread_cache_safeI_step_preserves_cacheI :
    forall e addr derived abs_vals,
      pico_thread_cache_safeI e addr derived abs_vals -∗
      pico_thread_step_preserves_cacheI e addr derived abs_vals.
  Proof.
    iIntros (e addr derived abs_vals) "%Hsafe".
    iApply pico_thread_step_preserves_cacheI_intro.
    exact Hsafe.
  Qed.

(** WP lifting rule that passes cache-history preservation for the selected
    cache-safe thread step to the continuation. *)
  Lemma wp_pico_lift_cache_safe_thread_step s E Φ e addr derived abs_vals :
    to_val e = None ->
    cache_safe_thread e addr derived abs_vals ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck then reducible e sigma else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        ⌜wm_cache_history_state sigma addr derived abs_vals ->
          wm_cache_history_state sigma' addr derived abs_vals⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val Hsafe) "Hlift".
    iApply wp_pico_lift_thread_step; [exact Hnot_val |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Hlift" with "Hstate") as "[$ Hstep]".
    iModIntro.
    iNext.
    iIntros (e' sigma') "%Hthread Hcred".
    iAssert
      (⌜wm_cache_history_state sigma addr derived abs_vals ->
        wm_cache_history_state sigma' addr derived abs_vals⌝)%I as "%Hpres".
    {
      iPureIntro.
      intro Hhistory.
      eapply cache_safe_thread_step_preserves_cache; eauto.
    }
    iMod ("Hstep" $! e' sigma' with "[//] [//] Hcred") as "[$ Hwp]".
    iModIntro.
    iFrame.
  Qed.

  Lemma wp_pico_lift_cache_safe_thread_stepI s E Φ e addr derived abs_vals :
    to_val e = None ->
    pico_thread_cache_safeI e addr derived abs_vals -∗
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck then reducible e sigma else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        ⌜wm_cache_history_state sigma addr derived abs_vals ->
          wm_cache_history_state sigma' addr derived abs_vals⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val) "Hsafe Hlift".
    iDestruct "Hsafe" as %Hsafe.
    iApply wp_pico_lift_cache_safe_thread_step; [exact Hnot_val | exact Hsafe |].
    iExact "Hlift".
  Qed.

  Lemma wp_pico_lift_cache_safe_thread_step_exists s E Φ e addr derived abs_vals :
    to_val e = None ->
    cache_safe_thread e addr derived abs_vals ->
    (∀ sigma ns k ks nt,
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
        WP e' @ s; E {{ Φ }})
    ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val Hsafe) "Hlift".
    iApply wp_pico_lift_thread_step_exists; [exact Hnot_val |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Hlift" with "Hstate") as "[$ Hstep]".
    iModIntro.
    iNext.
    iIntros (e' sigma') "%Hthread Hcred".
    iAssert
      (⌜wm_cache_history_state sigma addr derived abs_vals ->
        wm_cache_history_state sigma' addr derived abs_vals⌝)%I as "%Hpres".
    {
      iPureIntro.
      intro Hhistory.
      eapply cache_safe_thread_step_preserves_cache; eauto.
    }
    iMod ("Hstep" $! e' sigma' with "[//] [//] Hcred") as "[$ Hwp]".
    iModIntro.
    iFrame.
  Qed.

  Lemma wp_pico_lift_cache_safe_thread_step_existsI s E Φ e addr derived abs_vals :
    to_val e = None ->
    pico_thread_cache_safeI e addr derived abs_vals -∗
    (∀ sigma ns k ks nt,
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
        WP e' @ s; E {{ Φ }})
    -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val) "Hsafe Hlift".
    iDestruct "Hsafe" as %Hsafe.
    iApply wp_pico_lift_cache_safe_thread_step_exists; [exact Hnot_val | exact Hsafe |].
    iExact "Hlift".
  Qed.
End pico_iris_thread_safety.

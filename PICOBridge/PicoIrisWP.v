From iris.program_logic Require Import weakestpre lifting.
From iris.proofmode Require Import proofmode.

Require Import Syntax PICOBridge.PicoMemoryModel PICOBridge.PicoIrisLanguage.

(** * WP Lifting for the PICO Iris Language

    This file deliberately keeps Iris's [state_interp] abstract via [irisGS].
    It specializes the generic Iris lifting rule to [wm_thread_step],
    discharging the PICO-specific facts that primitive steps have no
    observations and fork no child expressions. *)

Section pico_wp.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!irisGS_gen hlc (pico_language CT) Σ}.

(** Low-level lifting lemma: proving a WP for a non-value PICO expression is
    reduced to handling every possible [wm_thread_step]. *)
  Lemma wp_pico_lift_thread_step s E Φ e :
    to_val e = None ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck then reducible e sigma else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val) "Hlift".
    iApply wp_lift_step; [exact Hnot_val |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Hlift" with "Hstate") as "[$ Hstep]".
    iModIntro.
    iNext.
    iIntros (e' sigma' efs Hprim) "Hcred".
    destruct (pico_prim_step_inv CT e sigma k e' sigma' efs Hprim)
      as [-> [-> Hthread]].
    iMod ("Hstep" $! e' sigma' with "[//] Hcred") as "[$ Hwp]".
    iModIntro.
    simpl.
    iFrame.
  Qed.

(** Convenience lifting lemma where reducibility is provided by existence of a
    [wm_thread_step]. *)
  Lemma wp_pico_lift_thread_step_exists s E Φ e :
    to_val e = None ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck
        then exists e' sigma', wm_thread_step CT sigma e sigma' e'
        else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma e sigma' e'⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val) "Hlift".
    iApply wp_pico_lift_thread_step; [exact Hnot_val |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Hlift" with "Hstate") as "[%Hred Hstep]".
    iModIntro.
    iSplit.
    - destruct s; simpl in *; auto.
      iPureIntro.
      apply pico_reducible_iff_thread_step.
      exact Hred.
    - iNext.
      iIntros (e' sigma') "Hthread Hcred".
      iApply ("Hstep" with "Hthread Hcred").
  Qed.
End pico_wp.

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.

Require Import Syntax DerivedCache PICOBridge.PicoMemoryModel PICOBridge.PicoIrisSemanticCache.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache.

(** * Invariant-Backed PICO Cache-History Interpretation

    The earlier semantic-cache wrappers are generic pure Iris facts.  This file
    introduces the first PICO-specific invariant boundary: a namespace protects
    the pure cache-history validity fact for a particular weak-memory
    configuration.  Later ghost-state work can refine this definition while
    preserving the lemmas below as the public API. *)

Section pico_iris_cache_invariant.
  Context `{Hmem : CacheMemoryModel}.
  Context `{!invGS Σ}.

(** Public invariant for the concrete cache-history predicate of one
    weak-memory configuration and target field. *)
  Definition pico_cache_history_inv
      (N : namespace) (cfg : wm_config) (addr : FieldAddr)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    inv N (wm_config_cache_history_stateI cfg addr derived abs_vals : iProp Σ).

  Global Instance pico_cache_history_inv_persistent
      N cfg addr derived abs_vals :
    Persistent (pico_cache_history_inv N cfg addr derived abs_vals).
  Proof. apply _. Qed.

(** Allocate the invariant from the concrete cache-history fact. *)
  Lemma pico_cache_history_inv_alloc N cfg addr derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    ⊢ |={⊤}=> pico_cache_history_inv N cfg addr derived abs_vals.
  Proof.
    intros Hstate.
    iMod (inv_alloc N _
      (wm_config_cache_history_stateI cfg addr derived abs_vals : iProp Σ)
      with "[]") as "#Hinv".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iExact "Hinv".
  Qed.

(** Opening the invariant around a read exposes the specialized
    [derived_cache_msg_ok] read-validity fact. *)
  Lemma pico_cache_history_inv_read_valid E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset) "#Hinv %Hread".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    eapply wm_config_cache_history_state_read_valid; eauto.
  Qed.

  Lemma pico_cache_history_inv_cache_hist_ok_generic
      E N cfg addr derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_history_inv N cfg addr derived abs_vals ={E}=∗
    ⌜CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        abs_vals⌝.
  Proof.
    iIntros (Hsubset) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    apply wm_cache_history_state_generic.
    exact Hstate.
  Qed.

  Lemma pico_cache_history_inv_valid_extension_generic
      E N cfg sigma addr derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_history_inv N cfg addr derived abs_vals ={E}=∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        sigma
        (wc_state cfg)
        abs_vals⌝.
  Proof.
    iIntros (Hsubset) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    eapply wm_cache_history_state_valid_extension_generic.
    exact Hstate.
  Qed.

(** Generic-protocol version of invariant-backed read validity. *)
  Lemma pico_cache_history_inv_read_valid_generic
      E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset) "#Hinv %Hread".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
    apply wm_cache_history_state_generic.
    exact Hstate.
  Qed.

  Lemma pico_cache_history_inv_read_unknown_or_derived
      E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/
      cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset) "#Hinv %Hread".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    eapply wm_config_cache_history_state_read_unknown_or_derived; eauto.
  Qed.

(** Semantic cache safety lets us allocate a fresh invariant for the final
    configuration after a weak-memory execution. *)
  Lemma pico_cache_history_inv_after_execution_alloc
      E N N' CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_semantic_cache_safe_execution CT cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    |={E}=> pico_cache_history_inv N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hexec Hsteps) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    pose proof (Hexec cfg' Hsteps Hstate) as Hfinal.
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI cfg' addr derived abs_vals : iProp Σ)
      with "[]") as "#Hfinal".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExact "Hfinal".
  Qed.

  Lemma pico_cache_history_inv_after_execution_read_valid
      E N CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    wm_semantic_cache_safe_execution CT cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hexec Hsteps) "#Hinv %Hread".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    pose proof (Hexec cfg' Hsteps Hstate) as Hfinal.
    eapply wm_config_cache_history_state_read_valid; eauto.
  Qed.

  Lemma pico_cache_history_inv_after_execution_cache_hist_ok_generic
      E N CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_semantic_cache_safe_execution CT cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    pico_cache_history_inv N cfg addr derived abs_vals ={E}=∗
    ⌜CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wc_state cfg')
        abs_vals⌝.
  Proof.
    iIntros (Hsubset Hexec Hsteps) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    apply wm_cache_history_state_generic.
    exact (Hexec cfg' Hsteps Hstate).
  Qed.

  Lemma pico_cache_history_inv_after_execution_valid_extension_generic
      E N CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_semantic_cache_safe_execution CT cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    pico_cache_history_inv N cfg addr derived abs_vals ={E}=∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        (wc_state cfg')
        abs_vals⌝.
  Proof.
    iIntros (Hsubset Hexec Hsteps) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    eapply wm_cache_history_state_valid_extension_generic.
    exact (Hexec cfg' Hsteps Hstate).
  Qed.

  Lemma pico_cache_history_inv_after_execution_read_valid_generic
      E N CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    wm_semantic_cache_safe_execution CT cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hexec Hsteps) "#Hinv %Hread".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
    apply wm_cache_history_state_generic.
    exact (Hexec cfg' Hsteps Hstate).
  Qed.

  Lemma pico_cache_history_inv_after_execution_read_unknown_or_derived
      E N CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    wm_semantic_cache_safe_execution CT cfg addr derived abs_vals ->
    wm_steps CT cfg cfg' ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/
      cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hexec Hsteps) "#Hinv %Hread".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iPureIntro.
    pose proof (Hexec cfg' Hsteps Hstate) as Hfinal.
    eapply wm_config_cache_history_state_read_unknown_or_derived; eauto.
  Qed.

  Lemma pico_cache_history_inv_after_thread_step_alloc
      E N N' CT sigma sigma' e e' addr derived abs_vals :
    ↑N ⊆ E ->
    cache_safe_thread e addr derived abs_vals ->
    wm_thread_step CT sigma e sigma' e' ->
    pico_cache_history_inv N (mkWMConfig sigma [e]) addr derived abs_vals -∗
    |={E}=> pico_cache_history_inv N' (mkWMConfig sigma' [e']) addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hsafe Hstep) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    assert (Hfinal :
      wm_config_cache_history_state
        (mkWMConfig sigma' [e'])
        addr
        derived
        abs_vals).
    {
      unfold wm_config_cache_history_state in *.
      eapply wm_cache_safe_transition_preserves_cache_history; eauto.
      eapply wm_thread_step_cache_safe_from_thread; eauto.
      apply cache_safe_thread_implies_wm_thread_writes_allowed.
      exact Hsafe.
    }
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI
        (mkWMConfig sigma' [e'])
        addr
        derived
        abs_vals : iProp Σ)
      with "[]") as "#Hfinal".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExact "Hfinal".
  Qed.

  Lemma pico_cache_history_inv_after_config_step_alloc
      E N N' CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    cache_safe_config cfg addr derived abs_vals ->
    wm_step CT cfg cfg' ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    |={E}=> pico_cache_history_inv N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hsafe Hstep) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    assert (Hfinal :
      wm_config_cache_history_state cfg' addr derived abs_vals).
    {
      eapply wm_step_preserves_cache_history; eauto.
      eapply wm_step_cache_safe_from_config_allowed; eauto.
      apply cache_safe_config_implies_wm_config_threads_allowed.
      exact Hsafe.
    }
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI cfg' addr derived abs_vals : iProp Σ)
      with "[]") as "#Hfinal".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExact "Hfinal".
  Qed.

  Lemma pico_cache_history_inv_after_steps_alloc
      E N N' CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    |={E}=> pico_cache_history_inv N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hsteps Hsafe) "#Hinv".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    assert (Hfinal :
      wm_config_cache_history_state cfg' addr derived abs_vals).
    {
      eapply cache_safe_config_semantic_cache_safe; eauto.
    }
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI cfg' addr derived abs_vals : iProp Σ)
      with "[]") as "#Hfinal".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExact "Hfinal".
  Qed.

  Lemma pico_cache_history_inv_after_steps_valid_extension_generic
      E N N' CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_history_inv N cfg addr derived abs_vals ={E}=∗
    pico_cache_history_inv N' cfg' addr derived abs_vals ∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        (wc_state cfg')
        abs_vals⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinv".
    iMod (pico_cache_history_inv_after_steps_alloc
      E N N' CT cfg cfg' addr derived abs_vals with "Hinv")
      as "#Hfinal"; eauto.
    iMod (pico_cache_history_inv_valid_extension_generic
      E N' cfg' (wc_state cfg) addr derived abs_vals with "Hfinal")
      as %Hext; [exact Hsubset' |].
    iModIntro.
    iSplit; [iExact "Hfinal" |].
    iPureIntro.
    exact Hext.
  Qed.

  Lemma pico_cache_history_inv_after_steps_read_valid
      E N N' CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinv %Hread".
    iMod (pico_cache_history_inv_after_steps_alloc
      E N N' CT cfg cfg' addr derived abs_vals
      with "Hinv") as "#Hfinal"; eauto.
    iApply (pico_cache_history_inv_read_valid
      E N' cfg' V addr v V' derived abs_vals with "Hfinal");
      [exact Hsubset' |].
    iPureIntro.
    exact Hread.
  Qed.

  Lemma pico_cache_history_inv_after_steps_read_valid_generic
      E N N' CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinv %Hread".
    iMod (pico_cache_history_inv_after_steps_alloc
      E N N' CT cfg cfg' addr derived abs_vals
      with "Hinv") as "#Hfinal"; eauto.
    iApply (pico_cache_history_inv_read_valid_generic
      E N' cfg' V addr v V' derived abs_vals with "Hfinal");
      [exact Hsubset' |].
    iPureIntro.
    exact Hread.
  Qed.

  Lemma pico_cache_history_inv_after_steps_read_unknown_or_derived
      E N N' CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/
      cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinv %Hread".
    iMod (pico_cache_history_inv_after_steps_alloc
      E N N' CT cfg cfg' addr derived abs_vals
      with "Hinv") as "#Hfinal"; eauto.
    iApply (pico_cache_history_inv_read_unknown_or_derived
      E N' cfg' V addr v V' derived abs_vals with "Hfinal");
      [exact Hsubset' |].
    iPureIntro.
    exact Hread.
  Qed.
End pico_iris_cache_invariant.

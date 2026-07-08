From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.

Require Import Syntax Helpers DerivedCache PICOBridge.PicoMemoryModel PICOBridge.PicoIrisSemanticCache.
Require Import PICOBridge.PicoIrisCacheInvariant PICOBridge.PicoIrisGhostState.
Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState Core.GenericDerivedCache.
Require Import Iris.GenericDerivedCacheIris.

(** * Ghost-Backed PICO State Interpretation Facade

    This layer keeps the invariant-backed cache-history interpretation from
    [PicoIrisCacheInvariant], but pairs it with hidden authoritative ownership
    of the weak-memory state and the concrete target field history.  Later work
    can refine that payload into per-field ownership while preserving the API
    below. *)

Section pico_iris_state_interp.
  Context `{Hmem : CacheMemoryModel}.
  Context `{!invGS Σ}.
  Context `{!picoCacheG Σ}.

(** Public state interpretation for one PICO weak-memory configuration and one
    target cache field.  The ghost names are existentially hidden so clients do
    not depend on the current ownership representation. *)
  Definition pico_cache_state_interp
      (N : namespace) (cfg : wm_config) (addr : FieldAddr)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ∃ γσ γf γh,
      pico_cache_weak_state_auth γσ (wc_state cfg) ∗
      pico_cache_weak_state_own γσ (wc_state cfg) ∗
      pico_cache_config_field_history_auth γf cfg addr ∗
      pico_cache_config_field_history_own γf cfg addr ∗
      pico_cache_config_history_auth γh cfg addr ∗
      pico_cache_config_history_own γh cfg addr ∗
      pico_cache_history_inv N cfg addr derived abs_vals.

(** Allocate the state interpretation from a concrete cache-history invariant. *)
  Lemma pico_cache_state_interp_alloc N cfg addr derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    ⊢ |={⊤}=> pico_cache_state_interp N cfg addr derived abs_vals.
  Proof.
    intros Hstate.
    unfold pico_cache_state_interp.
    iMod (pico_cache_weak_state_own_alloc (wc_state cfg))
      as (γσ) "[Hstate_auth #Hstate_own]".
    iMod (pico_cache_field_history_own_alloc cfg addr derived abs_vals Hstate)
      as (γf) "[Hfield_auth #Hfield_own]".
    iMod (pico_cache_history_own_alloc cfg addr derived abs_vals Hstate)
      as (γh) "[Hhist_auth #Hhist_own]".
    iMod (pico_cache_history_inv_alloc N cfg addr derived abs_vals Hstate)
      as "#Hinv".
    iModIntro.
    iExists γσ, γf, γh.
    iFrame.
    iFrame "#".
  Qed.

(** Read-validity theorem exposed by the state interpretation. *)
  Lemma pico_cache_state_interp_read_valid
      E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset) "Hinterp Hread".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
    iApply (pico_cache_history_inv_read_valid with "Hinv Hread").
    exact Hsubset.
  Qed.

(** Generic-protocol read-validity theorem exposed by the state interpretation. *)
  Lemma pico_cache_state_interp_read_valid_generic
      E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset) "Hinterp Hread".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
    iApply (pico_cache_history_inv_read_valid_generic with "Hinv Hread").
    exact Hsubset.
  Qed.

  Lemma pico_cache_state_interp_read_unknown_or_derived
      E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/ cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset) "Hinterp Hread".
    iMod (pico_cache_state_interp_read_valid
      E N cfg V addr v V' derived abs_vals with "Hinterp Hread")
      as %Hvalid; [exact Hsubset |].
    iModIntro.
    iPureIntro.
    apply derived_cache_valid_unknown_or_derived.
    apply derived_cache_msg_ok_cache_valid.
    exact Hvalid.
  Qed.

  Lemma pico_cache_state_interp_weak_state_snapshot
      E N cfg addr derived abs_vals :
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ∃ γσ, pico_cache_weak_state_own γσ (wc_state cfg).
  Proof.
    iIntros "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
    iModIntro.
    iSplitL "Hstate_auth Hfield_auth Hhist_auth".
    - iExists γσ, γf, γh.
      iFrame.
      iFrame "#".
    - iExists γσ.
      iExact "Hstate_own".
  Qed.

  Lemma pico_cache_state_interp_field_history_snapshot
      E N cfg addr derived abs_vals :
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ∃ γf, pico_cache_config_field_history_own γf cfg addr.
  Proof.
    iIntros "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
    iModIntro.
    iSplitL "Hstate_auth Hfield_auth Hhist_auth".
    - iExists γσ, γf, γh.
      iFrame.
      iFrame "#".
    - iExists γf.
      iExact "Hfield_own".
  Qed.

(** Extract the concrete validity fact for the target field history while
    preserving the state interpretation. *)
  Lemma pico_cache_state_interp_target_history_valid
      E N cfg addr derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ⌜derived_cache_history_ok
        derived
        abs_vals
        (history_of (wc_state cfg) addr)⌝.
  Proof.
    iIntros (Hsubset) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iSplitL "Hstate_auth Hfield_auth Hhist_auth".
    - iExists γσ, γf, γh.
      iFrame.
      iFrame "#".
    - iPureIntro.
      exact Hstate.
  Qed.

  Lemma pico_cache_state_interp_target_history_valid_generic
      E N cfg addr derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ⌜CacheHistOK
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        abs_vals⌝.
  Proof.
    iIntros (Hsubset) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    iModIntro.
    iSplitL "Hstate_auth Hfield_auth Hhist_auth".
    - iExists γσ, γf, γh.
      iFrame.
      iFrame "#".
    - iPureIntro.
      apply wm_cache_history_state_generic.
      exact Hstate.
  Qed.

  Lemma pico_cache_state_interp_valid_extension_generic
      E N cfg sigma addr derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        sigma
        (wc_state cfg)
        abs_vals⌝.
  Proof.
    iIntros (Hsubset) "Hinterp".
    iMod (pico_cache_state_interp_target_history_valid_generic
      E N cfg addr derived abs_vals with "Hinterp")
      as "[Hinterp %Hhist]"; [exact Hsubset |].
    iModIntro.
    iFrame.
    iPureIntro.
    intros [] v Hin.
    right.
    eapply Hhist.
    exact Hin.
  Qed.

  Lemma pico_cache_state_interp_generic_history_interp_alloc
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N cfg addr abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg)).
  Proof.
    iIntros (Hsubset) "Hinterp".
    iMod (pico_cache_state_interp_target_history_valid_generic
      E N cfg addr derived abs_vals with "Hinterp")
      as "[Hinterp %Hhist]"; [exact Hsubset |].
    iMod (wm_derived_cache_history_interp_alloc
      derived (wc_state cfg) addr abs_vals Hhist) as (γ) "Hgeneric".
    iModIntro.
    iSplitL "Hinterp".
    - iExact "Hinterp".
    - iExists γ.
      iExact "Hgeneric".
  Qed.

  Lemma pico_cache_state_interp_generic_history_read_valid
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N cfg V addr v V' abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg)) ∗
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝.
  Proof.
    iIntros (Hsubset) "Hinterp %Hread".
    iMod (pico_cache_state_interp_generic_history_interp_alloc
      derived E N cfg addr abs_vals with "Hinterp")
      as "[Hinterp Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iDestruct
      (wm_derived_cache_history_interp_read_valid_preserve
        derived (wc_state cfg) V addr v V' abs_vals γ
        with "Hgeneric []")
      as "[Hgeneric %Hvalid]".
    {
      iPureIntro.
      exact Hread.
    }
    iModIntro.
    iSplitL "Hinterp".
    - iExact "Hinterp".
    - iExists γ.
      iSplitL "Hgeneric".
      + iExact "Hgeneric".
      + done.
  Qed.

  Theorem pico_cache_state_interp_generic_history_refines_pure
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N cfg addr abs_vals
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg)
        tr⌝ -∗
    ⌜weak_exec_matches_trace
        (derived_cache_protocol derived)
        run_with_cache_trace
        abs_vals
        args
        tr
        r⌝ ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg)) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset) "Hinterp %Hsafe %Hreads %Hexec".
    iMod (pico_cache_state_interp_generic_history_interp_alloc
      derived E N cfg addr abs_vals with "Hinterp")
      as "[Hinterp Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iDestruct
      (wm_derived_cache_history_interp_refines_pure_preserve
        derived
        F
        run_with_cache_trace
        (wc_state cfg)
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
    iSplitL "Hinterp".
    - iExact "Hinterp".
    - iExists γ.
      iSplitL "Hgeneric".
      + iExact "Hgeneric".
      + done.
  Qed.

  Theorem pico_cache_state_interp_generic_history_refines_pure_post_extension
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N cfg sigma' addr abs_vals
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
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
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg)) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset) "Hinterp %Hsafe %Hext %Hreads %Hexec".
    iMod (pico_cache_state_interp_generic_history_interp_alloc
      derived E N cfg addr abs_vals with "Hinterp")
      as "[Hinterp Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iDestruct
      (wm_derived_cache_history_interp_refines_pure_post_extension_preserve
        derived
        F
        run_with_cache_trace
        (wc_state cfg)
        sigma'
        addr
        abs_vals
        γ
        args
        tr
        r
        with "Hgeneric [] [] [] []")
      as "[Hgeneric %Hresult]".
    {
      iPureIntro.
      exact Hsafe.
    }
    {
      iPureIntro.
      exact Hext.
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
    iSplitL "Hinterp".
    - iExact "Hinterp".
    - iExists γ.
      iSplitL "Hgeneric".
      + iExact "Hgeneric".
      + done.
  Qed.

  Theorem pico_cache_state_interp_semantic_immutability_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N cfg sigma' addr abs_vals
      (Stable : StableAbs wm_state (list Syntax.value))
      {Args Result : Type}
      (F : list Syntax.value -> Args -> Result)
      (run_with_cache_trace :
        list Syntax.value -> Args ->
        CacheTrace (derived_cache_protocol derived) ->
        CacheRun (derived_cache_protocol derived) Result)
      args tr r :
    ↑N ⊆ E ->
    Stable (wc_state cfg) abs_vals ->
    Stable sigma' abs_vals ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜CacheSafeMethod (derived_cache_protocol derived) F run_with_cache_trace⌝ -∗
    ⌜TraceReadsFromHistory
        (derived_cache_protocol derived)
        (wm_derived_cache_read derived addr)
        (wc_state cfg)
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
        (wc_state cfg)
        sigma'
        (run_writes (run_with_cache_trace abs_vals args tr))⌝ ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec %Hext_by_writes".
    iMod (pico_cache_state_interp_generic_history_interp_alloc
      derived E N cfg addr abs_vals with "Hinterp")
      as "[Hinterp Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iAssert
      (generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ
        (wc_state cfg)
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg)))
      with "[Hgeneric]" as "Hsem".
    {
      unfold generic_semantic_immutability_interp.
      iSplit.
      - iPureIntro.
        exact Hstable.
      - iExact "Hgeneric".
    }
    iMod
      (wm_derived_cache_trace_robust_semantic_immutability_alloc_post
        derived
        Stable
        F
        run_with_cache_trace
        (wc_state cfg)
        sigma'
        addr
        abs_vals
        γ
        args
        tr
        r
        with "Hsem [] [] [] [] []")
      as (γ') "[%Hresult Hsem']".
    - iPureIntro.
      exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
    - iModIntro.
      iSplitL "Hinterp".
      + iExact "Hinterp".
      + iExists γ'.
        iSplit.
        * iPureIntro.
          exact Hresult.
        * iExact "Hsem'".
  Qed.

  Lemma pico_cache_state_interp_field_history_snapshot_valid
      E N cfg addr derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ∃ γf,
      pico_cache_config_field_history_own γf cfg addr ∗
      ⌜derived_cache_history_ok
          derived
          abs_vals
          (history_of (wc_state cfg) addr)⌝.
  Proof.
    iIntros (Hsubset) "Hinterp".
    iMod (pico_cache_state_interp_field_history_snapshot
      E N cfg addr derived abs_vals with "Hinterp") as "[Hinterp Hfield]".
    iMod (pico_cache_state_interp_target_history_valid
      E N cfg addr derived abs_vals with "Hinterp") as "[Hinterp %Hvalid]";
      [exact Hsubset |].
    iModIntro.
    iFrame.
    iDestruct "Hfield" as (γf) "#Hfield".
    iExists γf.
    iFrame "#".
    done.
  Qed.

  Lemma pico_cache_state_interp_field_history_read_valid
      E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset) "Hinterp %Hread".
    iMod (pico_cache_state_interp_field_history_snapshot_valid
      E N cfg addr derived abs_vals with "Hinterp")
      as "[Hinterp Hfield_valid]"; [exact Hsubset |].
    iDestruct "Hfield_valid" as (γf) "[#Hfield %Hvalid]".
    iModIntro.
    iFrame.
    iPureIntro.
    eapply cache_history_read_valid; eauto.
  Qed.

  Lemma pico_cache_state_interp_field_history_read_valid_generic
      E N cfg V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg) V addr v V'⌝ ={E}=∗
    pico_cache_state_interp N cfg addr derived abs_vals ∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset) "Hinterp %Hread".
    iMod (pico_cache_state_interp_target_history_valid_generic
      E N cfg addr derived abs_vals with "Hinterp")
      as "[Hinterp %Hhist]"; [exact Hsubset |].
    iModIntro.
    iFrame.
    iPureIntro.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
  Qed.

  Lemma pico_cache_state_interp_after_target_write
      E N N' sigma sigma' threads V V' addr n derived abs_vals :
    ↑N ⊆ E ->
    n = derived abs_vals ->
    n <> 0 ->
    wm_write sigma sigma' V V' addr (Int n) ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals ={E}=∗
    pico_cache_state_interp
      N'
      (mkWMConfig sigma' threads)
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hderived Hnz Hwrite) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
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
        (mkWMConfig sigma' threads)
        addr
        derived
        abs_vals).
    {
      unfold wm_config_cache_history_state in *.
      eapply wm_write_known_preserves_cache_history; eauto.
    }
    iMod (pico_cache_weak_state_own_alloc sigma')
      as (γσ') "[Hstate_auth' #Hstate_own']".
    iMod (pico_cache_field_history_own_alloc
      (mkWMConfig sigma' threads) addr derived abs_vals Hfinal)
      as (γf') "[Hfield_auth' #Hfield_own']".
    iMod (pico_cache_history_own_alloc
      (mkWMConfig sigma' threads) addr derived abs_vals Hfinal)
      as (γh') "[Hhist_auth' #Hhist_own']".
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI
        (mkWMConfig sigma' threads)
        addr
        derived
        abs_vals : iProp Σ)
      with "[]") as "#Hinv'".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExists γσ', γf', γh'.
    iFrame.
    iFrame "#".
  Qed.

  Lemma pico_cache_state_interp_after_other_write
      E N N' sigma sigma' threads V V' write_addr addr val_y
      derived abs_vals :
    ↑N ⊆ E ->
    write_addr <> addr ->
    wm_write sigma sigma' V V' write_addr val_y ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals ={E}=∗
    pico_cache_state_interp
      N'
      (mkWMConfig sigma' threads)
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hneq Hwrite) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
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
        (mkWMConfig sigma' threads)
        addr
        derived
        abs_vals).
    {
      unfold wm_config_cache_history_state in *.
      eapply wm_cache_safe_transition_preserves_cache_history; eauto.
      eapply wm_write_other_cache_safe_transition; eauto.
    }
    iMod (pico_cache_weak_state_own_alloc sigma')
      as (γσ') "[Hstate_auth' #Hstate_own']".
    iMod (pico_cache_field_history_own_alloc
      (mkWMConfig sigma' threads) addr derived abs_vals Hfinal)
      as (γf') "[Hfield_auth' #Hfield_own']".
    iMod (pico_cache_history_own_alloc
      (mkWMConfig sigma' threads) addr derived abs_vals Hfinal)
      as (γh') "[Hhist_auth' #Hhist_own']".
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI
        (mkWMConfig sigma' threads)
        addr
        derived
        abs_vals : iProp Σ)
      with "[]") as "#Hinv'".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExists γσ', γf', γh'.
    iFrame.
    iFrame "#".
  Qed.

  Lemma pico_cache_state_interp_after_allowed_write_threads
      E N N' sigma sigma' pre_threads post_threads V V'
      write_addr addr val_y derived abs_vals :
    ↑N ⊆ E ->
    wm_write sigma sigma' V V' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma pre_threads)
      addr
      derived
      abs_vals ={E}=∗
    pico_cache_state_interp
      N'
      (mkWMConfig sigma' post_threads)
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hwrite Hallowed) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
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
        (mkWMConfig sigma' post_threads)
        addr
        derived
        abs_vals).
    {
      unfold wm_config_cache_history_state in *.
      eapply wm_cache_safe_transition_preserves_cache_history; eauto.
      eapply wm_write_allowed_cache_safe_transition; eauto.
    }
    iMod (pico_cache_weak_state_own_alloc sigma')
      as (γσ') "[Hstate_auth' #Hstate_own']".
    iMod (pico_cache_field_history_own_alloc
      (mkWMConfig sigma' post_threads) addr derived abs_vals Hfinal)
      as (γf') "[Hfield_auth' #Hfield_own']".
    iMod (pico_cache_history_own_alloc
      (mkWMConfig sigma' post_threads) addr derived abs_vals Hfinal)
      as (γh') "[Hhist_auth' #Hhist_own']".
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI
        (mkWMConfig sigma' post_threads)
        addr
        derived
        abs_vals : iProp Σ)
      with "[]") as "#Hinv'".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExists γσ', γf', γh'.
    iFrame.
    iFrame "#".
  Qed.

  Lemma pico_cache_state_interp_after_allowed_write
      E N N' sigma sigma' threads V V' write_addr addr val_y
      derived abs_vals :
    ↑N ⊆ E ->
    wm_write sigma sigma' V V' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals ={E}=∗
    pico_cache_state_interp
      N'
      (mkWMConfig sigma' threads)
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hwrite Hallowed) "Hinterp".
    iApply (pico_cache_state_interp_after_allowed_write_threads
      E N N' sigma sigma' threads threads V V' write_addr addr val_y
      derived abs_vals with "Hinterp"); eauto.
  Qed.

  Lemma pico_cache_state_interp_after_allowed_write_threads_read_valid_generic
      E N N' sigma sigma' pre_threads post_threads Vw Vw' Vr
      write_addr addr val_y v Vr' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_write sigma sigma' Vw Vw' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma pre_threads)
      addr
      derived
      abs_vals -∗
    ⌜wm_read sigma' Vr addr v Vr'⌝ ={E}=∗
    pico_cache_state_interp
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
    iIntros (Hsubset Hsubset' Hwrite Hallowed) "Hinterp %Hread".
    iMod (pico_cache_state_interp_after_allowed_write_threads
      E N N' sigma sigma' pre_threads post_threads Vw Vw'
      write_addr addr val_y derived abs_vals with "Hinterp")
      as "Hinterp'"; eauto.
    iApply (pico_cache_state_interp_field_history_read_valid_generic
      E N' (mkWMConfig sigma' post_threads) Vr addr v Vr'
      derived abs_vals with "Hinterp' []").
    - exact Hsubset'.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_cache_state_interp_after_allowed_write_read_valid_generic
      E N N' sigma sigma' threads Vw Vw' Vr
      write_addr addr val_y v Vr' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_write sigma sigma' Vw Vw' write_addr val_y ->
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma threads)
      addr
      derived
      abs_vals -∗
    ⌜wm_read sigma' Vr addr v Vr'⌝ ={E}=∗
    pico_cache_state_interp
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
    iIntros (Hsubset Hsubset' Hwrite Hallowed) "Hinterp Hread".
    iApply (pico_cache_state_interp_after_allowed_write_threads_read_valid_generic
      E N N' sigma sigma' threads threads Vw Vw' Vr
      write_addr addr val_y v Vr' derived abs_vals with
      "Hinterp Hread"); eauto.
  Qed.

  Lemma pico_cache_state_interp_after_fldwrite_step
      E N N' sigma sigma' rΓ V V' x f y loc_x val_y
      addr derived abs_vals :
    ↑N ⊆ E ->
    cache_safe_stmt rΓ addr derived abs_vals (SFldWrite x f y) ->
    runtime_getVal rΓ x = Some (Iot loc_x) ->
    runtime_getVal rΓ y = Some val_y ->
    wm_write sigma sigma' V V' (loc_x, f) val_y ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma [mkWMThread rΓ (SFldWrite x f y) V])
      addr
      derived
      abs_vals ={E}=∗
    pico_cache_state_interp
      N'
      (mkWMConfig sigma' [mkWMThread rΓ SSkip V'])
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hsafe Hx Hy Hwrite) "Hinterp".
    assert (Hallowed :
      wm_write_allowed_for_cache (loc_x, f) addr val_y derived abs_vals).
    {
      pose proof (cache_safe_stmt_implies_wm_stmt_writes_allowed
        rΓ (SFldWrite x f y) addr derived abs_vals Hsafe) as Hwrites.
      simpl in Hwrites.
      eapply Hwrites; eauto.
    }
    iApply (pico_cache_state_interp_after_allowed_write_threads
      E N N' sigma sigma'
      [mkWMThread rΓ (SFldWrite x f y) V]
      [mkWMThread rΓ SSkip V']
      V V' (loc_x, f) addr val_y derived abs_vals with "Hinterp");
      eauto.
  Qed.

  Lemma pico_cache_state_interp_after_thread_step
      E N N' CT sigma sigma' e e' addr derived abs_vals :
    ↑N ⊆ E ->
    cache_safe_thread e addr derived abs_vals ->
    wm_thread_step CT sigma e sigma' e' ->
    pico_cache_state_interp
      N
      (mkWMConfig sigma [e])
      addr
      derived
      abs_vals ={E}=∗
    pico_cache_state_interp
      N'
      (mkWMConfig sigma' [e'])
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hsafe Hstep) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
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
    iMod (pico_cache_weak_state_own_alloc sigma')
      as (γσ') "[Hstate_auth' #Hstate_own']".
    iMod (pico_cache_field_history_own_alloc
      (mkWMConfig sigma' [e']) addr derived abs_vals Hfinal)
      as (γf') "[Hfield_auth' #Hfield_own']".
    iMod (pico_cache_history_own_alloc
      (mkWMConfig sigma' [e']) addr derived abs_vals Hfinal)
      as (γh') "[Hhist_auth' #Hhist_own']".
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI
        (mkWMConfig sigma' [e'])
        addr
        derived
        abs_vals : iProp Σ)
      with "[]") as "#Hinv'".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExists γσ', γf', γh'.
    iFrame.
    iFrame "#".
  Qed.

  Lemma pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    |={E}=>
    pico_cache_state_interp N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hsteps Hsafe) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
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
    iMod (pico_cache_weak_state_own_alloc (wc_state cfg'))
      as (γσ') "[Hstate_auth' #Hstate_own']".
    iMod (pico_cache_field_history_own_alloc cfg' addr derived abs_vals Hfinal)
      as (γf') "[Hfield_auth' #Hfield_own']".
    iMod (pico_cache_history_own_alloc cfg' addr derived abs_vals Hfinal)
      as (γh') "[Hhist_auth' #Hhist_own']".
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI cfg' addr derived abs_vals : iProp Σ)
      with "[]") as "#Hinv'".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExists γσ', γf', γh'.
    iFrame.
    iFrame "#".
  Qed.

  Lemma pico_cache_state_interp_after_steps_valid_extension_generic
      E N N' CT cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        (wc_state cfg')
        abs_vals⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinterp".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with "Hinterp")
      as "Hinterp'"; eauto.
    iApply (pico_cache_state_interp_valid_extension_generic
      E N' cfg' (wc_state cfg) addr derived abs_vals with "Hinterp'").
    exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_after_steps_preserved
      E N N' cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    |={E}=>
    pico_cache_state_interp N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hpres) "Hinterp".
    unfold pico_cache_state_interp.
    iDestruct "Hinterp" as
      (γσ γf γh)
      "(Hstate_auth & #Hstate_own & Hfield_auth & #Hfield_own & Hhist_auth & #Hhist_own & #Hinv)".
    iInv N as ">Hstate" "Hclose".
    iDestruct "Hstate" as "%Hstate".
    iMod ("Hclose" with "[]") as "_".
    {
      iNext.
      iPureIntro.
      exact Hstate.
    }
    pose proof (Hpres Hstate) as Hfinal.
    iMod (pico_cache_weak_state_own_alloc (wc_state cfg'))
      as (γσ') "[Hstate_auth' #Hstate_own']".
    iMod (pico_cache_field_history_own_alloc cfg' addr derived abs_vals Hfinal)
      as (γf') "[Hfield_auth' #Hfield_own']".
    iMod (pico_cache_history_own_alloc cfg' addr derived abs_vals Hfinal)
      as (γh') "[Hhist_auth' #Hhist_own']".
    iMod (inv_alloc N' _
      (wm_config_cache_history_stateI cfg' addr derived abs_vals : iProp Σ)
      with "[]") as "#Hinv'".
    {
      iNext.
      iPureIntro.
      exact Hfinal.
    }
    iModIntro.
    iExists γσ', γf', γh'.
    iFrame.
    iFrame "#".
  Qed.

  Lemma pico_cache_state_interp_after_steps_preserved_valid_extension_generic
      E N N' cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
    ⌜CacheHistValidExtension
        (derived_cache_protocol derived)
        (wm_derived_cache_history derived addr)
        (wm_derived_cache_history derived addr)
        (wc_state cfg)
        (wc_state cfg')
        abs_vals⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hinterp".
    iMod (pico_cache_state_interp_after_steps_preserved
      E N N' cfg cfg' addr derived abs_vals with "Hinterp")
      as "Hinterp'"; eauto.
    iApply (pico_cache_state_interp_valid_extension_generic
      E N' cfg' (wc_state cfg) addr derived abs_vals with "Hinterp'").
    exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_after_steps_read_valid
      E N N' CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinterp Hread".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with
      "Hinterp") as "Hfinal"; eauto.
    iApply (pico_cache_state_interp_read_valid
      E N' cfg' V addr v V' derived abs_vals with
      "Hfinal Hread").
    exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_after_steps_read_valid_generic
      E N N' CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinterp Hread".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with
      "Hinterp") as "Hfinal"; eauto.
    iApply (pico_cache_state_interp_read_valid_generic
      E N' cfg' V addr v V' derived abs_vals with
      "Hfinal Hread").
    exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_after_steps_generic_history_interp_alloc
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT cfg cfg' addr abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    |={E}=>
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinterp".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with "Hinterp")
      as "Hfinal"; eauto.
    iApply (pico_cache_state_interp_generic_history_interp_alloc
      derived E N' cfg' addr abs_vals with "Hfinal").
    exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_after_steps_generic_history_read_valid
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT cfg cfg' V addr v V' abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinterp %Hread".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with "Hinterp")
      as "Hfinal"; eauto.
    iApply (pico_cache_state_interp_generic_history_read_valid
      derived E N' cfg' V addr v V' abs_vals with "Hfinal");
      eauto.
  Qed.

  Theorem pico_cache_state_interp_after_steps_generic_history_refines_pure
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT cfg cfg' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe)
      "Hinterp %Hmethod %Hreads %Hexec".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with "Hinterp")
      as "Hfinal"; eauto.
    iApply (pico_cache_state_interp_generic_history_refines_pure
      derived E N' cfg' addr abs_vals F run_with_cache_trace args tr r
      with "Hfinal"); eauto.
  Qed.

  Theorem pico_cache_state_interp_after_steps_generic_history_refines_pure_post_extension
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT cfg cfg' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg)) ∗
      ⌜PureRecomputeResult F abs_vals args r⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe)
      "Hinterp %Hmethod %Hreads %Hexec".
    iMod (pico_cache_state_interp_generic_history_interp_alloc
      derived E N cfg addr abs_vals with "Hinterp")
      as "[Hinterp Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iMod (pico_cache_state_interp_after_steps_valid_extension_generic
      E N N' CT cfg cfg' addr derived abs_vals with "Hinterp")
      as "[Hinterp' %Hext]"; eauto.
    iDestruct
      (wm_derived_cache_history_interp_refines_pure_post_extension_preserve
        derived
        F
        run_with_cache_trace
        (wc_state cfg)
        (wc_state cfg')
        addr
        abs_vals
        γ
        args
        tr
        r
        with "Hgeneric [] [] [] []")
      as "[Hgeneric %Hresult]".
    {
      iPureIntro.
      exact Hmethod.
    }
    {
      iPureIntro.
      exact Hext.
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
    iSplitL "Hinterp'".
    - iExact "Hinterp'".
    - iExists γ.
      iSplitL "Hgeneric".
      + iExact "Hgeneric".
      + done.
  Qed.

  Theorem pico_cache_state_interp_after_steps_semantic_immutability_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT cfg cfg' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec".
    iMod (pico_cache_state_interp_generic_history_interp_alloc
      derived E N cfg addr abs_vals with "Hinterp")
      as "[Hinterp Hgeneric]"; [exact Hsubset |].
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iAssert
      (generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ
        (wc_state cfg)
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg)))
      with "[Hgeneric]" as "Hsem".
    {
      unfold generic_semantic_immutability_interp.
      iSplit.
      - iPureIntro.
        exact Hstable.
      - iExact "Hgeneric".
    }
    iMod (pico_cache_state_interp_after_steps_valid_extension_generic
      E N N' CT cfg cfg' addr derived abs_vals with "Hinterp")
      as "[Hinterp' %Hext]"; eauto.
    iMod
      (wm_derived_cache_semantic_immutability_method_post_valid_extension_alloc_post_trace
        derived
        Stable
        F
        run_with_cache_trace
        (wc_state cfg)
        (wc_state cfg')
        addr
        abs_vals
        γ
        args
        tr
        r
        with "Hsem [] [] [] [] []")
      as (γ') "[%Hresult Hsem']".
    - iPureIntro.
      exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext.
    - iModIntro.
      iSplitL "Hinterp'".
      + iExact "Hinterp'".
      + iExists γ'.
        iSplit.
        * iPureIntro.
          exact Hresult.
        * iExact "Hsem'".
  Qed.

  Theorem pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CT cfg cfg' sigma' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec %Hext_by_writes".
    iMod (pico_cache_state_interp_after_steps_generic_history_interp_alloc
      derived E N N' CT cfg cfg' addr abs_vals with "Hinterp")
      as "[Hinterp' Hgeneric]"; eauto.
    iDestruct "Hgeneric" as (γ) "Hgeneric".
    iAssert
      (generic_semantic_immutability_interp
        (derived_cache_protocol derived)
        Stable
        γ
        (wc_state cfg')
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')))
      with "[Hgeneric]" as "Hsem".
    {
      unfold generic_semantic_immutability_interp.
      iSplit.
      - iPureIntro.
        exact Hstable.
      - iExact "Hgeneric".
    }
    iMod
      (wm_derived_cache_trace_robust_semantic_immutability_alloc_post
        derived
        Stable
        F
        run_with_cache_trace
        (wc_state cfg')
        sigma'
        addr
        abs_vals
        γ
        args
        tr
        r
        with "Hsem [] [] [] [] []")
      as (γ') "[%Hresult Hsem']".
    - iPureIntro.
      exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
    - iModIntro.
      iSplitL "Hinterp'".
      + iExact "Hinterp'".
      + iExists γ'.
        iSplit.
        * iPureIntro.
          exact Hresult.
        * iExact "Hsem'".
  Qed.

  Theorem pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep cfg cfg' sigma' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec %Hext_by_writes".
    pose proof
      (pico_wm_stable_abs_preserved_by_steps_avoiding_writes
        CTstep CTabs C loc abs_fields cfg cfg' abs_vals
        Hsteps Havoid Hstable) as Hstable'.
    pose proof
      (pico_wm_stable_abs_preserved_by_histories
        CTabs C loc abs_fields (wc_state cfg') sigma' abs_vals
        Hpres Hstable') as Hstable_post.
    iApply
      (pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CTstep cfg cfg' sigma' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hinterp [] [] [] []").
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

  Theorem pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_write_extension_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep cfg cfg' sigma' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec %Hext_by_writes".
    pose proof
      (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
        CTstep CTabs C loc abs_fields cfg cfg' Hsteps
        rt_abs abs_vals Htype HC Hfinals Hstable) as Hstable'.
    pose proof
      (pico_wm_stable_abs_preserved_by_histories
        CTabs C loc abs_fields (wc_state cfg') sigma' abs_vals
        Hpres Hstable') as Hstable_post.
    iApply
      (pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CTstep cfg cfg' sigma' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hinterp [] [] [] []").
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

  Theorem pico_cache_state_interp_after_steps_pico_wm_stable_trace_robust_cache_only_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep cfg cfg' sigma' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec %Hext_by_writes".
    pose proof
      (wm_histories_only_extend_field_preserves_fields
        (wc_state cfg') sigma' addr loc abs_fields
        Honly Havoid_target) as Hpres.
    pose proof
      (pico_wm_stable_abs_preserved_by_steps_avoiding_writes
        CTstep CTabs C loc abs_fields cfg cfg' abs_vals
        Hsteps Havoid_steps Hstable) as Hstable'.
    pose proof
      (pico_wm_stable_abs_preserved_by_histories
        CTabs C loc abs_fields (wc_state cfg') sigma' abs_vals
        Hpres Hstable') as Hstable_post.
    iApply
      (pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CTstep cfg cfg' sigma' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hinterp [] [] [] []").
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

  Theorem pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_trace_robust_cache_only_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep cfg cfg' sigma' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec %Hext_by_writes".
    pose proof
      (wm_histories_only_extend_field_preserves_fields
        (wc_state cfg') sigma' addr loc abs_fields
        Honly Havoid_target) as Hpres.
    pose proof
      (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
        CTstep CTabs C loc abs_fields cfg cfg' Hsteps
        rt_abs abs_vals Htype HC Hfinals Hstable) as Hstable'.
    pose proof
      (pico_wm_stable_abs_preserved_by_histories
        CTabs C loc abs_fields (wc_state cfg') sigma' abs_vals
        Hpres Hstable') as Hstable_post.
    iApply
      (pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CTstep cfg cfg' sigma' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hinterp [] [] [] []").
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

  Theorem pico_cache_state_interp_after_steps_pico_wm_stable_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep cfg cfg' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec".
    iApply
      (pico_cache_state_interp_after_steps_semantic_immutability_method_post
        derived E N N' CTstep cfg cfg' addr abs_vals
        (pico_wm_stable_abs CTabs C loc abs_fields)
        F run_with_cache_trace args tr r with "Hinterp [] [] []").
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

  Theorem pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep cfg cfg' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec".
    pose proof
      (pico_wm_stable_abs_preserved_by_steps_avoiding_writes
        CTstep CTabs C loc abs_fields cfg cfg' abs_vals
        Hsteps Havoid Hstable) as Hstable'.
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_method_post
        derived E N N' CTstep cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hinterp [] [] []").
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

  Theorem pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_post
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' CTstep cfg cfg' addr abs_vals
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
    pico_cache_state_interp N cfg addr derived abs_vals -∗
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
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
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
      "Hinterp %Hmethod %Hreads %Hexec".
    pose proof
      (wm_steps_preserve_pico_wm_stable_abs_from_final_fields
        CTstep CTabs C loc abs_fields cfg cfg' Hsteps
        rt_abs abs_vals Htype HC Hfinals Hstable) as Hstable'.
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_method_post
        derived E N N' CTstep cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hinterp [] [] []").
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

  Lemma pico_cache_state_interp_after_steps_read_unknown_or_derived
      E N N' CT cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/ cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsafe) "Hinterp Hread".
    iMod (pico_cache_state_interp_after_steps
      E N N' CT cfg cfg' addr derived abs_vals with
      "Hinterp") as "Hfinal".
    - exact Hsubset.
    - exact Hsteps.
    - exact Hsafe.
    - iApply (pico_cache_state_interp_read_unknown_or_derived
        E N' cfg' V addr v V' derived abs_vals with
        "Hfinal Hread").
      exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_after_steps_preserved_read_valid
      E N N' cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hinterp Hread".
    iMod (pico_cache_state_interp_after_steps_preserved
      E N N' cfg cfg' addr derived abs_vals with "Hinterp") as "Hfinal";
      eauto.
    iApply (pico_cache_state_interp_read_valid
      E N' cfg' V addr v V' derived abs_vals with
      "Hfinal Hread").
    exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_after_steps_preserved_read_valid_generic
      E N N' cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hinterp Hread".
    iMod (pico_cache_state_interp_after_steps_preserved
      E N N' cfg cfg' addr derived abs_vals with "Hinterp") as "Hfinal";
      eauto.
    iApply (pico_cache_state_interp_read_valid_generic
      E N' cfg' V addr v V' derived abs_vals with
      "Hfinal Hread").
    exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_alloc_after_steps_read_valid_generic
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
    iMod (pico_cache_state_interp_alloc N cfg addr derived abs_vals Hinit)
      as "Hstate".
    iApply (pico_cache_state_interp_after_steps_read_valid_generic
      ⊤ N N' CT cfg cfg' V addr v V' derived abs_vals
      with "Hstate").
    - set_solver.
    - set_solver.
    - exact Hsteps.
    - exact Hsafe.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_cache_state_interp_alloc_after_steps_preserved_read_valid_generic
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
    iMod (pico_cache_state_interp_alloc N cfg addr derived abs_vals Hinit)
      as "Hstate".
    iApply
      (pico_cache_state_interp_after_steps_preserved_read_valid_generic
        ⊤ N N' cfg cfg' V addr v V' derived abs_vals
        with "Hstate").
    - set_solver.
    - set_solver.
    - exact Hpres.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_cache_state_interp_after_steps_preserved_read_unknown_or_derived
      E N N' cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    pico_cache_state_interp N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_value_unknown v \/ cache_value_known derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hpres) "Hinterp Hread".
    iMod (pico_cache_state_interp_after_steps_preserved
      E N N' cfg cfg' addr derived abs_vals with "Hinterp") as "Hfinal".
    - exact Hsubset.
    - exact Hpres.
    - iApply (pico_cache_state_interp_read_unknown_or_derived
        E N' cfg' V addr v V' derived abs_vals with
        "Hfinal Hread").
      exact Hsubset'.
  Qed.

  Lemma pico_cache_state_interp_alloc_after_steps_read_unknown_or_derived
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
    iMod (pico_cache_state_interp_alloc N cfg addr derived abs_vals Hinit)
      as "Hstate".
    iApply (pico_cache_state_interp_after_steps_read_unknown_or_derived
      ⊤ N N' CT cfg cfg' V addr v V' derived abs_vals
      with "Hstate").
    - set_solver.
    - set_solver.
    - exact Hsteps.
    - exact Hsafe.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_cache_state_interp_alloc_after_steps_preserved_read_unknown_or_derived
      (N N' : namespace) cfg cfg' V addr v V' derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    (wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals) ->
    wm_read (wc_state cfg') V addr v V' ->
    ⊢ (|={⊤}=>
      ⌜cache_value_unknown v \/
        cache_value_known derived abs_vals v⌝ : iProp Σ).
  Proof.
    iIntros (Hinit Hpres Hread).
    iMod (pico_cache_state_interp_alloc N cfg addr derived abs_vals Hinit)
      as "Hstate".
    iApply
      (pico_cache_state_interp_after_steps_preserved_read_unknown_or_derived
        ⊤ N N' cfg cfg' V addr v V' derived abs_vals
        with "Hstate").
    - set_solver.
    - set_solver.
    - exact Hpres.
    - iPureIntro.
      exact Hread.
  Qed.
End pico_iris_state_interp.

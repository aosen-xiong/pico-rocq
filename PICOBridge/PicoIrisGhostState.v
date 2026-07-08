From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth agree gmap.
From iris.base_logic Require Import own.

Require Import Syntax PICOBridge.PicoMemoryModel.

(** * Low-Level PICO Cache Ghost State

    This is intentionally small: the first authoritative payloads record the
    whole weak-memory state and the concrete target field history in
    auth/agreement resources.  The public state-interpretation layer hides the
    ghost names, so later work can refine this into more precise ownership of
    field-addressed memory cells. *)

(** Resource class for weak-memory state ownership, field-history ownership,
    and target-history ownership. *)
Class picoCacheG Σ := PicoCacheG {
  pico_cache_state_inG :
    inG Σ (authR (optionUR (agreeR (leibnizO wm_state))));
  pico_cache_field_mem_inG :
    inG Σ (authR (gmapUR FieldAddr (agreeR (leibnizO history))));
  pico_cache_history_inG :
    inG Σ (authR (optionUR (agreeR (leibnizO history))));
}.

Section pico_iris_ghost_state.
  Context `{Hmem : CacheMemoryModel}.
  Context `{!picoCacheG Σ}.

(** Agreement element for a whole weak-memory state. *)
  Definition pico_cache_state_elem (sigma : wm_state) :
      optionUR (agreeR (leibnizO wm_state)) :=
    Some (to_agree (A := leibnizO wm_state) sigma).

(** Authoritative ownership of the current weak-memory state. *)
  Definition pico_cache_weak_state_auth
      (γ : gname) (sigma : wm_state) : iProp Σ :=
    @own
      Σ
      (authR (optionUR (agreeR (leibnizO wm_state))))
      pico_cache_state_inG
      γ
      (● pico_cache_state_elem sigma).

(** Persistent fragment witnessing the same weak-memory state. *)
  Definition pico_cache_weak_state_own
      (γ : gname) (sigma : wm_state) : iProp Σ :=
    @own
      Σ
      (authR (optionUR (agreeR (leibnizO wm_state))))
      pico_cache_state_inG
      γ
      (◯ pico_cache_state_elem sigma).

  Definition pico_cache_history_elem (hist : history) :
      optionUR (agreeR (leibnizO history)) :=
    Some (to_agree (A := leibnizO history) hist).

  Definition pico_cache_field_history_elem
      (addr : FieldAddr) (hist : history) :
      gmapUR FieldAddr (agreeR (leibnizO history)) :=
    {[ addr := to_agree (A := leibnizO history) hist ]}.

  Definition pico_cache_field_history_auth
      (γ : gname) (addr : FieldAddr) (hist : history) : iProp Σ :=
    @own
      Σ
      (authR (gmapUR FieldAddr (agreeR (leibnizO history))))
      pico_cache_field_mem_inG
      γ
      (● pico_cache_field_history_elem addr hist).

  Definition pico_cache_field_history_own
      (γ : gname) (addr : FieldAddr) (hist : history) : iProp Σ :=
    @own
      Σ
      (authR (gmapUR FieldAddr (agreeR (leibnizO history))))
      pico_cache_field_mem_inG
      γ
      (◯ pico_cache_field_history_elem addr hist).

(** Authoritative ownership of one target field history. *)
  Definition pico_cache_history_auth
      (γ : gname) (hist : history) : iProp Σ :=
    @own
      Σ
      (authR (optionUR (agreeR (leibnizO history))))
      pico_cache_history_inG
      γ
      (● pico_cache_history_elem hist).

(** Persistent fragment for one target field history. *)
  Definition pico_cache_history_own
      (γ : gname) (hist : history) : iProp Σ :=
    @own
      Σ
      (authR (optionUR (agreeR (leibnizO history))))
      pico_cache_history_inG
      γ
      (◯ pico_cache_history_elem hist).

  Definition pico_cache_config_history_auth
      (γ : gname) (cfg : wm_config) (addr : FieldAddr) : iProp Σ :=
    pico_cache_history_auth γ (history_of (wc_state cfg) addr).

  Definition pico_cache_config_history_own
      (γ : gname) (cfg : wm_config) (addr : FieldAddr) : iProp Σ :=
    pico_cache_history_own γ (history_of (wc_state cfg) addr).

  Definition pico_cache_config_field_history_auth
      (γ : gname) (cfg : wm_config) (addr : FieldAddr) : iProp Σ :=
    pico_cache_field_history_auth
      γ
      addr
      (history_of (wc_state cfg) addr).

  Definition pico_cache_config_field_history_own
      (γ : gname) (cfg : wm_config) (addr : FieldAddr) : iProp Σ :=
    pico_cache_field_history_own
      γ
      addr
      (history_of (wc_state cfg) addr).

  Global Instance pico_cache_history_own_persistent
      γ hist :
    Persistent (pico_cache_history_own γ hist).
  Proof. apply _. Qed.

  Global Instance pico_cache_weak_state_own_persistent
      γ sigma :
    Persistent (pico_cache_weak_state_own γ sigma).
  Proof. apply _. Qed.

  Global Instance pico_cache_field_history_own_persistent
      γ addr hist :
    Persistent (pico_cache_field_history_own γ addr hist).
  Proof. apply _. Qed.

(** Allocate whole-state authoritative and fragment ownership. *)
  Lemma pico_cache_weak_state_own_alloc sigma :
    ⊢ |==> ∃ γ,
      pico_cache_weak_state_auth γ sigma ∗
      pico_cache_weak_state_own γ sigma.
  Proof.
    iMod (@own_alloc
      Σ
      (authR (optionUR (agreeR (leibnizO wm_state))))
      pico_cache_state_inG
      (● pico_cache_state_elem sigma ⋅ ◯ pico_cache_state_elem sigma))
      as (γ) "[Hauth #Hown]".
    {
      apply auth_both_valid.
      split; done.
    }
    iModIntro.
    iExists γ.
    iSplitL "Hauth".
    - unfold pico_cache_weak_state_auth.
      iExact "Hauth".
    - unfold pico_cache_weak_state_own.
      iExact "Hown".
  Qed.

(** Allocate target-history ownership from a concrete cache-history invariant. *)
  Lemma pico_cache_history_own_alloc cfg addr derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    ⊢ |==> ∃ γ,
      pico_cache_config_history_auth γ cfg addr ∗
      pico_cache_config_history_own γ cfg addr.
  Proof.
    intros Hstate.
    iMod (@own_alloc
      Σ
      (authR (optionUR (agreeR (leibnizO history))))
      pico_cache_history_inG
      (● pico_cache_history_elem (history_of (wc_state cfg) addr) ⋅
       ◯ pico_cache_history_elem (history_of (wc_state cfg) addr)))
      as (γ) "[Hauth #Hown]".
    {
      apply auth_both_valid.
      split; done.
    }
    iModIntro.
    iExists γ.
    iSplitL "Hauth".
    - unfold pico_cache_config_history_auth, pico_cache_history_auth.
      iExact "Hauth".
    - unfold pico_cache_config_history_own, pico_cache_history_own.
      iExact "Hown".
  Qed.

(** Allocate map-based field-history ownership for the target address. *)
  Lemma pico_cache_field_history_own_alloc cfg addr derived abs_vals :
    wm_config_cache_history_state cfg addr derived abs_vals ->
    ⊢ |==> ∃ γ,
      pico_cache_config_field_history_auth γ cfg addr ∗
      pico_cache_config_field_history_own γ cfg addr.
  Proof.
    intros Hstate.
    iMod (@own_alloc
      Σ
      (authR (gmapUR FieldAddr (agreeR (leibnizO history))))
      pico_cache_field_mem_inG
      (● pico_cache_field_history_elem
          addr
          (history_of (wc_state cfg) addr) ⋅
       ◯ pico_cache_field_history_elem
          addr
          (history_of (wc_state cfg) addr)))
      as (γ) "[Hauth #Hown]".
    {
      apply auth_both_valid_2.
      - unfold pico_cache_field_history_elem.
        rewrite singleton_valid.
        done.
      - reflexivity.
    }
    iModIntro.
    iExists γ.
    iSplitL "Hauth".
    - unfold pico_cache_config_field_history_auth.
      unfold pico_cache_field_history_auth.
      iExact "Hauth".
    - unfold pico_cache_config_field_history_own.
      unfold pico_cache_field_history_own.
      iExact "Hown".
  Qed.
End pico_iris_ghost_state.

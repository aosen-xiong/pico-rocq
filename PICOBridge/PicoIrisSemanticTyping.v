From iris.program_logic Require Import weakestpre.
From iris.proofmode Require Import proofmode.

From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers Typing DerivedCache PICOBridge.PicoMemoryModel PICOBridge.PicoCacheTyping.
Require Bigstep.
Require Import PICOBridge.PicoIrisLanguage PICOBridge.PicoIrisSemanticCache PICOBridge.PicoIrisCacheInvariant.
Require Import PICOBridge.PicoIrisStateInterp PICOBridge.PicoIrisStateBridge.
Require Import PICOBridge.PicoIrisWP PICOBridge.PicoIrisThreadSafety PICOBridge.PicoIrisWPStateBridge.
Require Import Core.GenericCacheProtocol Iris.GenericCacheIris Iris.GenericCacheGhostState.
Require Import Core.GenericDerivedCache Iris.GenericDerivedCacheIris.

(** * Semantic Typing Facade for the PICO Iris Pipeline

    This file gives names to the Iris propositions that currently stand in for
    the future logical relation: a statement or thread is semantically
    acceptable for the cache proof when it is both PICO-typed and cache-safe.
    The facts are still pure, but WP rules can now consume the semantic
    interpretation rather than raw proof-engineering premises. *)

Section pico_iris_semantic_typing.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!irisGS_gen hlc (pico_language CT) Σ}.

(** Current semantic statement interpretation: ordinary PICO typing plus
    cache-safety of the statement's field writes. *)
  Definition pico_sem_typed_stmt_cacheI
      (sΓ sΓ' : s_env) (mt : method_type) (rΓ : r_env) (s : stmt)
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜stmt_typing CT sΓ mt s sΓ' /\
      cache_safe_stmt rΓ addr derived abs_vals s⌝%I.

  Definition pico_sem_typed_thread_cacheI
      (sΓ sΓ' : s_env) (mt : method_type) (e : wm_thread)
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    pico_sem_typed_stmt_cacheI
      sΓ sΓ' mt (wt_env e) (wt_stmt e) addr derived abs_vals.

  Definition sem_typed_thread_entry
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) (e : wm_thread) : Prop :=
    exists sΓ sΓ' mt,
      stmt_typing CT sΓ mt (wt_stmt e) sΓ' /\
      cache_safe_thread e addr derived abs_vals.

(** Config-level semantic interpretation for a thread pool. *)
  Definition pico_sem_typed_config_cacheI
      (cfg : wm_config) (addr : FieldAddr)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜Forall
      (sem_typed_thread_entry addr derived abs_vals)
      (wc_threads cfg)⌝%I.

(** Iris-facing proposition for the concrete cache-update sequence rule. *)
  Definition pico_sem_cache_update_sequenceI
      (sΓ : s_env) (mt : method_type) (rΓ : r_env)
      (loc : Loc) (cache_f receiver tmp : var)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) (n : nat) : iProp Σ :=
    ⌜cache_update_sequence_safe
      CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n⌝%I.

(** Iris-facing proposition for generic pure-recompute refinement of the cache
    compute phase. *)
  Definition pico_sem_cache_compute_refines_pureI
      (derived : list Syntax.value -> nat) : iProp Σ :=
    CacheRefinesPureI
      (derived_cache_protocol derived)
      (pico_cache_compute_pure_result derived)
      (pico_cache_compute_run derived).

  Lemma pico_sem_cache_update_sequence_intro :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      ⊢ pico_sem_cache_update_sequenceI
          sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe.
    iPureIntro.
    exact Hsafe.
  Qed.

  Lemma pico_sem_cache_compute_refines_pure_introI :
    forall derived,
      ⊢ pico_sem_cache_compute_refines_pureI derived.
  Proof.
    intros derived.
    unfold pico_sem_cache_compute_refines_pureI.
    iPureIntro.
    apply pico_cache_compute_refines_pure.
  Qed.

  Lemma verified_cache_compute_refines_pure_via_genericI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n
           (tr : CacheTrace (derived_cache_protocol derived)),
      verified_cache_compute
        CT sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n ->
      ValidTrace (derived_cache_protocol derived) abs_vals tr ->
      ⊢ (PureRecomputeResultI
          (pico_cache_compute_pure_result derived)
          abs_vals
          tt
          (Int n) : iProp Σ).
  Proof.
    intros sΓ sΓ_mid mt rΓ rΓ_mid compute tmp derived abs_vals n tr
           Hcompute Htrace.
    iPureIntro.
    eapply verified_cache_compute_refines_pure_via_generic; eauto.
  Qed.

  Lemma cache_compute_write_safe_refines_pure_via_genericI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n
           (tr : CacheTrace (derived_cache_protocol derived)),
      cache_compute_write_safe
        CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals n ->
      ValidTrace (derived_cache_protocol derived) abs_vals tr ->
      ⊢ (PureRecomputeResultI
          (pico_cache_compute_pure_result derived)
          abs_vals
          tt
          (Int n) : iProp Σ).
  Proof.
    intros sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n tr Hsafe Htrace.
    iPureIntro.
    eapply cache_compute_write_safe_refines_pure_via_generic; eauto.
  Qed.

  Lemma cache_update_sequence_safe_refines_pure_via_genericI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n
           (tr : CacheTrace (derived_cache_protocol derived)),
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      ValidTrace (derived_cache_protocol derived) abs_vals tr ->
      ⊢ (PureRecomputeResultI
          (pico_cache_compute_pure_result derived)
          abs_vals
          tt
          (Int n) : iProp Σ).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n tr
           Hsafe Htrace.
    iPureIntro.
    eapply cache_update_sequence_safe_refines_pure_via_generic; eauto.
  Qed.

  Lemma sem_typed_thread_entry_assign_int_post :
    forall addr derived abs_vals rΓ V x n old_v,
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ (SVarAss x (EInt n)) V) ->
      runtime_getVal rΓ x = Some old_v ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread
          (set_vars rΓ (update x (Int n) (vars rΓ)))
          SSkip
          V).
  Proof.
    intros addr derived abs_vals rΓ V x n old_v Hentry _.
    destruct Hentry as [sΓ [sΓ' [mt [Htyping _]]]].
    exists sΓ, sΓ, mt.
    split.
    - inversion Htyping; subst.
      apply ST_Skip.
      exact Hwf.
    - constructor.
  Qed.

  Lemma sem_typed_thread_entry_field_read_post :
    forall addr derived abs_vals sigma rΓ V V' x y f loc_y v,
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ (SVarAss x (EField y f)) V) ->
      runtime_getVal rΓ y = Some (Iot loc_y) ->
      wm_read sigma V (loc_y, f) v V' ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread
          (set_vars rΓ (update x v (vars rΓ)))
          SSkip
          V').
  Proof.
    intros addr derived abs_vals sigma rΓ V V' x y f loc_y v
           Hentry _ _.
    destruct Hentry as [sΓ [sΓ' [mt [Htyping _]]]].
    exists sΓ, sΓ, mt.
    split.
    - inversion Htyping; subst.
      apply ST_Skip.
      exact Hwf.
    - constructor.
  Qed.

  Lemma sem_typed_thread_entry_fldwrite_post :
    forall addr derived abs_vals rΓ V V' x f y,
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ (SFldWrite x f y) V) ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ SSkip V').
  Proof.
    intros addr derived abs_vals rΓ V V' x f y Hentry.
    destruct Hentry as [sΓ [sΓ' [mt [Htyping _]]]].
    exists sΓ, sΓ, mt.
    split.
    - inversion Htyping; subst; apply ST_Skip; assumption.
    - constructor.
  Qed.

  Lemma sem_typed_thread_entry_seqskip_post :
    forall addr derived abs_vals rΓ V s2,
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ (SSeq SSkip s2) V) ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ s2 V).
  Proof.
    intros addr derived abs_vals rΓ V s2 Hentry.
    destruct Hentry as [sΓ [sΓ'' [mt [Htyping Hsafe]]]].
    inversion Htyping; subst.
    inversion Htype1; subst.
    inversion Hsafe; subst.
    exists sΓ', sΓ'', mt.
    split; assumption.
  Qed.

  Lemma sem_typed_thread_entry_seqstep_residual_post :
    forall addr derived abs_vals sΓ sΓ_mid sΓ'' mt
      rΓ' V' s1' s2,
      stmt_typing CT sΓ mt s1' sΓ_mid ->
      stmt_typing CT sΓ_mid mt s2 sΓ'' ->
      cache_safe_thread
        (mkWMThread rΓ' s1' V') addr derived abs_vals ->
      cache_safe_thread
        (mkWMThread rΓ' s2 V') addr derived abs_vals ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ' (residual_seq_wm s1' s2) V').
  Proof.
    intros addr derived abs_vals sΓ sΓ_mid sΓ'' mt
           rΓ' V' s1' s2 Htype1 Htype2 Hsafe1 Hsafe2.
    destruct s1'; simpl.
    - exists sΓ_mid, sΓ'', mt.
      split; [exact Htype2 | exact Hsafe2].
    - exists sΓ, sΓ'', mt.
      split.
      + eapply ST_Seq; eauto.
        eapply stmt_typing_wf_env; eauto.
      + apply cache_safe_seq; assumption.
    - exists sΓ, sΓ'', mt.
      split.
      + eapply ST_Seq; eauto.
        eapply stmt_typing_wf_env; eauto.
      + apply cache_safe_seq; assumption.
    - exists sΓ, sΓ'', mt.
      split.
      + eapply ST_Seq; eauto.
        eapply stmt_typing_wf_env; eauto.
      + apply cache_safe_seq; assumption.
    - exists sΓ, sΓ'', mt.
      split.
      + eapply ST_Seq; eauto.
        eapply stmt_typing_wf_env; eauto.
      + apply cache_safe_seq; assumption.
    - exists sΓ, sΓ'', mt.
      split.
      + eapply ST_Seq; eauto.
        eapply stmt_typing_wf_env; eauto.
      + apply cache_safe_seq; assumption.
    - exists sΓ, sΓ'', mt.
      split.
      + eapply ST_Seq; eauto.
        eapply stmt_typing_wf_env; eauto.
      + apply cache_safe_seq; assumption.
  Qed.

  Lemma sem_typed_thread_entry_seqstep_assign_int_post :
    forall addr derived abs_vals rΓ V x n old_v s2,
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ (SSeq (SVarAss x (EInt n)) s2) V) ->
      runtime_getVal rΓ x = Some old_v ->
      cache_safe_thread
        (mkWMThread
          (set_vars rΓ (update x (Int n) (vars rΓ)))
          s2
          V)
        addr
        derived
        abs_vals ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread
          (set_vars rΓ (update x (Int n) (vars rΓ)))
          s2
          V).
  Proof.
    intros addr derived abs_vals rΓ V x n old_v s2
           Hentry _ Hsafe2.
    destruct Hentry as [sΓ [sΓ'' [mt [Htyping _]]]].
    inversion Htyping; subst.
    inversion Htype1; subst.
    eexists _, _, mt.
    split; [exact Htype2 | exact Hsafe2].
  Qed.

  Lemma sem_typed_thread_entry_seqstep_field_read_post :
    forall addr derived abs_vals sigma rΓ V V' x y f loc_y v s2,
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ (SSeq (SVarAss x (EField y f)) s2) V) ->
      runtime_getVal rΓ y = Some (Iot loc_y) ->
      wm_read sigma V (loc_y, f) v V' ->
      cache_safe_thread
        (mkWMThread
          (set_vars rΓ (update x v (vars rΓ)))
          s2
          V')
        addr
        derived
        abs_vals ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread
          (set_vars rΓ (update x v (vars rΓ)))
          s2
          V').
  Proof.
    intros addr derived abs_vals sigma rΓ V V' x y f loc_y v s2
           Hentry _ _ Hsafe2.
    destruct Hentry as [sΓ [sΓ'' [mt [Htyping _]]]].
    inversion Htyping; subst.
    inversion Htype1; subst.
    eexists _, _, mt.
    split; [exact Htype2 | exact Hsafe2].
  Qed.

  Lemma sem_typed_thread_entry_seqstep_fldwrite_post :
    forall addr derived abs_vals rΓ V V' x f y s2,
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ (SSeq (SFldWrite x f y) s2) V) ->
      cache_safe_thread
        (mkWMThread rΓ s2 V')
        addr
        derived
        abs_vals ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ s2 V').
  Proof.
    intros addr derived abs_vals rΓ V V' x f y s2 Hentry Hsafe2.
    destruct Hentry as [sΓ [sΓ'' [mt [Htyping _]]]].
    inversion Htyping; subst.
    inversion Htype1; subst.
    all: eexists _, _, _; split; [eassumption | exact Hsafe2].
  Qed.

  Lemma pico_sem_typed_stmt_cacheI_intro :
    forall sΓ sΓ' mt rΓ s addr derived abs_vals,
      stmt_typing CT sΓ mt s sΓ' ->
      cache_safe_stmt rΓ addr derived abs_vals s ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ' mt rΓ s addr derived abs_vals.
  Proof.
    intros sΓ sΓ' mt rΓ s addr derived abs_vals Htyping Hsafe.
    iPureIntro.
    split; assumption.
  Qed.

  Lemma sem_cache_skipI :
    forall sΓ mt rΓ addr derived abs_vals,
      stmt_typing CT sΓ mt SSkip sΓ ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ mt rΓ SSkip addr derived abs_vals.
  Proof.
    intros sΓ mt rΓ addr derived abs_vals Htyping.
    iApply pico_sem_typed_stmt_cacheI_intro.
    - exact Htyping.
    - constructor.
  Qed.

  Lemma sem_cache_localI :
    forall sΓ sΓ' mt rΓ T x addr derived abs_vals,
      stmt_typing CT sΓ mt (SLocal T x) sΓ' ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ' mt rΓ (SLocal T x) addr derived abs_vals.
  Proof.
    intros sΓ sΓ' mt rΓ T x addr derived abs_vals Htyping.
    iApply pico_sem_typed_stmt_cacheI_intro.
    - exact Htyping.
    - constructor.
  Qed.

  Lemma sem_cache_varassI :
    forall sΓ mt rΓ x e addr derived abs_vals,
      stmt_typing CT sΓ mt (SVarAss x e) sΓ ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ mt rΓ (SVarAss x e) addr derived abs_vals.
  Proof.
    intros sΓ mt rΓ x e addr derived abs_vals Htyping.
    iApply pico_sem_typed_stmt_cacheI_intro.
    - exact Htyping.
    - constructor.
  Qed.

  Lemma sem_cache_fldwrite_otherI :
    forall sΓ mt rΓ x f y addr derived abs_vals,
      stmt_typing CT sΓ mt (SFldWrite x f y) sΓ ->
      (forall loc_x,
        runtime_getVal rΓ x = Some (Iot loc_x) ->
        (loc_x, f) <> addr) ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ mt rΓ (SFldWrite x f y) addr derived abs_vals.
  Proof.
    intros sΓ mt rΓ x f y addr derived abs_vals Htyping Hother.
    iApply pico_sem_typed_stmt_cacheI_intro.
    - exact Htyping.
    - apply cache_safe_fldwrite_other.
      exact Hother.
  Qed.

  Lemma sem_cache_fldwrite_target_knownI :
    forall sΓ mt rΓ loc cache_f x y derived abs_vals n,
      stmt_typing CT sΓ mt (SFldWrite x cache_f y) sΓ ->
      runtime_getVal rΓ x = Some (Iot loc) ->
      runtime_getVal rΓ y = Some (Int n) ->
      n = derived abs_vals ->
      n <> 0 ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ
          sΓ
          mt
          rΓ
          (SFldWrite x cache_f y)
          (loc, cache_f)
          derived
          abs_vals.
  Proof.
    intros sΓ mt rΓ loc cache_f x y derived abs_vals n
           Htyping Hx Hy Hderived Hnz.
    iApply pico_sem_typed_stmt_cacheI_intro.
    - exact Htyping.
    - eapply cache_safe_fldwrite_target_known; eauto.
  Qed.

  Lemma sem_cache_newI :
    forall sΓ mt rΓ x qc C args addr derived abs_vals,
      stmt_typing CT sΓ mt (SNew x qc C args) sΓ ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ mt rΓ (SNew x qc C args) addr derived abs_vals.
  Proof.
    intros sΓ mt rΓ x qc C args addr derived abs_vals Htyping.
    iApply pico_sem_typed_stmt_cacheI_intro.
    - exact Htyping.
    - constructor.
  Qed.

  Lemma sem_cache_callI :
    forall sΓ mt rΓ x y m args addr derived abs_vals,
      stmt_typing CT sΓ mt (SCall x y m args) sΓ ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ mt rΓ (SCall x y m args) addr derived abs_vals.
  Proof.
    intros sΓ mt rΓ x y m args addr derived abs_vals Htyping.
    iApply pico_sem_typed_stmt_cacheI_intro.
    - exact Htyping.
    - constructor.
  Qed.

  Lemma sem_cache_seqI :
    forall sΓ sΓ' sΓ'' mt rΓ s1 s2 addr derived abs_vals,
      stmt_typing CT sΓ mt s1 sΓ' ->
      stmt_typing CT sΓ' mt s2 sΓ'' ->
      pico_sem_typed_stmt_cacheI sΓ sΓ' mt rΓ s1 addr derived abs_vals -∗
      pico_sem_typed_stmt_cacheI sΓ' sΓ'' mt rΓ s2 addr derived abs_vals -∗
      pico_sem_typed_stmt_cacheI
        sΓ sΓ'' mt rΓ (SSeq s1 s2) addr derived abs_vals.
  Proof.
    iIntros (sΓ sΓ' sΓ'' mt rΓ s1 s2 addr derived abs_vals
             Htype1 Htype2) "Hsem1 Hsem2".
    iDestruct "Hsem1" as %[Htype1' Hsafe1].
    iDestruct "Hsem2" as %[Htype2' Hsafe2].
    iPureIntro.
    split.
    - eapply ST_Seq; eauto.
      eapply stmt_typing_wf_env; eauto.
    - apply cache_safe_seq; assumption.
  Qed.

  Lemma pico_sem_typed_thread_cacheI_intro :
    forall sΓ sΓ' mt e addr derived abs_vals,
      stmt_typing CT sΓ mt (wt_stmt e) sΓ' ->
      cache_safe_thread e addr derived abs_vals ->
      ⊢ pico_sem_typed_thread_cacheI
          sΓ sΓ' mt e addr derived abs_vals.
  Proof.
    intros sΓ sΓ' mt e addr derived abs_vals Htyping Hsafe.
    unfold pico_sem_typed_thread_cacheI, cache_safe_thread in *.
    iApply pico_sem_typed_stmt_cacheI_intro; eauto.
  Qed.

  Lemma pico_sem_typed_thread_cacheI_cache_safe :
    forall sΓ sΓ' mt e addr derived abs_vals,
      pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals
      ⊢ pico_thread_cache_safeI e addr derived abs_vals.
  Proof.
    intros sΓ sΓ' mt e addr derived abs_vals.
    iIntros "Hsem".
    iDestruct "Hsem" as %[_ Hsafe].
    iPureIntro.
    exact Hsafe.
  Qed.

  Lemma pico_sem_typed_thread_cacheI_bridge_cache_safe_contract
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ sΓ sΓ' mt e N addr derived abs_vals :
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_step_contract
      CT s E Φ e N addr derived abs_vals.
  Proof.
    iIntros "Hsem Hcontract".
    iPoseProof (pico_sem_typed_thread_cacheI_cache_safe with "Hsem")
      as "Hsafe".
    iApply (pico_wp_state_bridge_cache_safe_contract_from_step_contract
      with "Hsafe Hcontract").
  Qed.

  Lemma pico_sem_typed_thread_cacheI_bridge_cache_safe_lift_premise
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ sΓ sΓ' mt e N addr derived abs_vals :
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_lift_premise
      CT s E Φ e addr derived abs_vals.
  Proof.
    iIntros "Hsem Hcontract".
    iPoseProof
      (pico_sem_typed_thread_cacheI_bridge_cache_safe_contract
        with "Hsem Hcontract") as "Hcache_contract".
    iApply (pico_wp_state_bridge_cache_safe_step_contract_lift_premise
      with "Hcache_contract").
  Qed.

  Lemma pico_sem_typed_thread_cacheI_bridge_lift_premise
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ sΓ sΓ' mt e N addr derived abs_vals :
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_lift_premise CT s E Φ e.
  Proof.
    iIntros "_ Hcontract".
    iApply (pico_wp_state_bridge_step_contract_lift_premise
      with "Hcontract").
  Qed.

  Lemma pico_sem_typed_thread_cacheI_bridge_lift_premise_from_cache_safe
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ sΓ sΓ' mt e addr derived abs_vals :
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_lift_premise
      CT s E Φ e addr derived abs_vals -∗
    pico_wp_state_bridge_lift_premise CT s E Φ e.
  Proof.
    iIntros "Hsem Hlift".
    iPoseProof (pico_sem_typed_thread_cacheI_cache_safe with "Hsem")
      as "Hsafe".
    iApply (pico_wp_state_bridge_cache_safe_lift_premise_lift_premise
      with "Hsafe Hlift").
  Qed.

  Lemma pico_sem_typed_thread_cacheI_bridge_contract_from_cache_safe
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ sΓ sΓ' mt e N addr derived abs_vals :
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals.
  Proof.
    iIntros "Hsem Hcontract".
    iPoseProof (pico_sem_typed_thread_cacheI_cache_safe with "Hsem")
      as "Hsafe".
    iApply (pico_wp_state_bridge_cache_safe_contract_step_contract
      with "Hsafe Hcontract").
  Qed.

  Lemma pico_sem_typed_thread_cacheI_entry :
    forall sΓ sΓ' mt e addr derived abs_vals,
      pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
      ⌜sem_typed_thread_entry addr derived abs_vals e⌝.
  Proof.
    iIntros (sΓ sΓ' mt e addr derived abs_vals) "Hsem".
    iDestruct "Hsem" as %[Htyping Hsafe].
    iPureIntro.
    exists sΓ, sΓ', mt.
    split; assumption.
  Qed.

  Lemma pico_sem_typed_config_cacheI_intro :
    forall cfg addr derived abs_vals,
      Forall
        (sem_typed_thread_entry addr derived abs_vals)
        (wc_threads cfg) ->
      ⊢ pico_sem_typed_config_cacheI cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hcfg.
    iPureIntro.
    exact Hcfg.
  Qed.

  Lemma pico_sem_typed_config_cacheI_cache_safe_config :
    forall cfg addr derived abs_vals,
      pico_sem_typed_config_cacheI cfg addr derived abs_vals
      ⊢ cache_safe_configI cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals.
    iIntros "Hsem".
    iDestruct "Hsem" as "%Hsem".
    iPureIntro.
    unfold cache_safe_config.
    induction Hsem as [|e es Hthread Hthreads IH].
    - constructor.
    - destruct Hthread as [sΓ [sΓ' [mt [_ Hsafe]]]].
      constructor; assumption.
  Qed.

  Lemma sem_typed_config_entries_cache_safe_config :
    forall cfg addr derived abs_vals,
      Forall
        (sem_typed_thread_entry addr derived abs_vals)
        (wc_threads cfg) ->
      cache_safe_config cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hentries.
    unfold cache_safe_config.
    induction Hentries as [|e es Hentry Hentries IH].
    - constructor.
    - destruct Hentry as [sΓ [sΓ' [mt [_ Hsafe]]]].
      constructor; assumption.
  Qed.

  Lemma sem_typed_config_entries_nth_thread_entry :
    forall threads i e addr derived abs_vals,
      Forall
        (sem_typed_thread_entry addr derived abs_vals)
        threads ->
      nth_error threads i = Some e ->
      sem_typed_thread_entry addr derived abs_vals e.
  Proof.
    intros threads i e addr derived abs_vals Hentries.
    revert i e.
    induction Hentries as [|t ts Hentry Hentries IH]; intros i e Hnth.
    - destruct i; inversion Hnth.
    - destruct i as [|i].
      + simpl in Hnth. inversion Hnth; subst. exact Hentry.
      + simpl in Hnth. eapply IH; eauto.
  Qed.

  Definition sem_typed_config_entry_interpretation
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) (cfg : wm_config) : Prop :=
    Forall
      (sem_typed_thread_entry addr derived abs_vals)
      (wc_threads cfg).

  Lemma sem_typed_config_entry_interpretation_nth_thread_entry :
    forall cfg i e addr derived abs_vals,
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      nth_error (wc_threads cfg) i = Some e ->
      sem_typed_thread_entry addr derived abs_vals e.
  Proof.
    intros cfg i e addr derived abs_vals Hinterp Hnth.
    unfold sem_typed_config_entry_interpretation in Hinterp.
    eapply sem_typed_config_entries_nth_thread_entry; eauto.
  Qed.

  Lemma sem_typed_config_entry_interpretation_nth_cache_safe_thread :
    forall cfg i e addr derived abs_vals,
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      nth_error (wc_threads cfg) i = Some e ->
      cache_safe_thread e addr derived abs_vals.
  Proof.
    intros cfg i e addr derived abs_vals Hinterp Hnth.
    destruct (sem_typed_config_entry_interpretation_nth_thread_entry
      cfg i e addr derived abs_vals Hinterp Hnth)
      as [sΓ [sΓ' [mt [_ Hsafe]]]].
    exact Hsafe.
  Qed.

  Lemma pico_sem_typed_config_cacheI_interp :
    forall cfg addr derived abs_vals,
      pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
      ⌜sem_typed_config_entry_interpretation addr derived abs_vals cfg⌝.
  Proof.
    iIntros (cfg addr derived abs_vals) "Hcfg".
    iExact "Hcfg".
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_thread_entryI :
    forall cfg i e addr derived abs_vals,
      nth_error (wc_threads cfg) i = Some e ->
      pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
      ⌜sem_typed_thread_entry addr derived abs_vals e⌝.
  Proof.
    iIntros (cfg i e addr derived abs_vals Hnth) "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as %Hinterp.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_nth_thread_entry;
      eauto.
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_threadI :
    forall cfg i e addr derived abs_vals,
      nth_error (wc_threads cfg) i = Some e ->
      pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
      ∃ sΓ sΓ' mt,
        pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals.
  Proof.
    iIntros (cfg i e addr derived abs_vals Hnth) "Hcfg".
    iDestruct
      (pico_sem_typed_config_cacheI_nth_thread_entryI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as %Hentry.
    destruct Hentry as [sΓ [sΓ' [mt [Htyping Hsafe]]]].
    iExists sΓ, sΓ', mt.
    iPureIntro.
    split; [exact Htyping |].
    exact Hsafe.
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_threadI_elim :
    forall cfg i e addr derived abs_vals (P : iProp Σ),
      nth_error (wc_threads cfg) i = Some e ->
      pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
      (∀ sΓ sΓ' mt,
        pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
        P) -∗
      P.
  Proof.
    iIntros (cfg i e addr derived abs_vals P Hnth) "Hcfg Hk".
    iDestruct
      (pico_sem_typed_config_cacheI_nth_threadI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as (sΓ sΓ' mt) "Hthread".
    iApply ("Hk" with "Hthread").
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_thread_cache_safeI :
    forall cfg i e addr derived abs_vals,
      nth_error (wc_threads cfg) i = Some e ->
      pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
      pico_thread_cache_safeI e addr derived abs_vals.
  Proof.
    iIntros (cfg i e addr derived abs_vals Hnth) "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as %Hinterp.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_nth_cache_safe_thread;
      eauto.
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_bridge_cache_safe_contract
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e N addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_step_contract
      CT s E Φ e N addr derived abs_vals.
  Proof.
    iIntros (Hnth) "Hcfg Hcontract".
    iPoseProof
      (pico_sem_typed_config_cacheI_nth_thread_cache_safeI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as "Hsafe".
    iApply (pico_wp_state_bridge_cache_safe_contract_from_step_contract
      with "Hsafe Hcontract").
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_bridge_cache_safe_lift_premise
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e N addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_lift_premise
      CT s E Φ e addr derived abs_vals.
  Proof.
    iIntros (Hnth) "Hcfg Hcontract".
    iPoseProof
      (pico_sem_typed_config_cacheI_nth_bridge_cache_safe_contract
        s E Φ cfg i e N addr derived abs_vals Hnth with
        "Hcfg Hcontract") as "Hcache_contract".
    iApply (pico_wp_state_bridge_cache_safe_step_contract_lift_premise
      with "Hcache_contract").
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_bridge_lift_premise
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e N addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_lift_premise CT s E Φ e.
  Proof.
    iIntros (Hnth) "Hcfg Hcontract".
    iDestruct
      (pico_sem_typed_config_cacheI_nth_thread_cache_safeI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as %Hsafe.
    iPoseProof
      (pico_wp_state_bridge_step_contract_cache_safe_lift_premise
        with "Hcontract") as "Hcache_lift".
    iApply (pico_wp_state_bridge_cache_safe_lift_premise_lift_premise
      with "[] Hcache_lift").
    iPureIntro.
    exact Hsafe.
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_thread_bridge_lift_premise
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e N addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    ∃ sΓ sΓ' mt,
      pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals ∗
      pico_wp_state_bridge_lift_premise CT s E Φ e.
  Proof.
    iIntros (Hnth) "Hcfg Hcontract".
    iDestruct
      (pico_sem_typed_config_cacheI_nth_thread_entryI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as %Hentry.
    destruct Hentry as [sΓ [sΓ' [mt [Htyping Hsafe]]]].
    iExists sΓ, sΓ', mt.
    iSplit.
    - iPureIntro.
      split; [exact Htyping | exact Hsafe].
    - iApply (pico_sem_typed_thread_cacheI_bridge_lift_premise
        with "[] Hcontract").
      iPureIntro.
      split; [exact Htyping | exact Hsafe].
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_thread_bridge_cache_safe_lift_premise
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e N addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    ∃ sΓ sΓ' mt,
      pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals ∗
      pico_wp_state_bridge_cache_safe_lift_premise
        CT s E Φ e addr derived abs_vals.
  Proof.
    iIntros (Hnth) "Hcfg Hcontract".
    iDestruct
      (pico_sem_typed_config_cacheI_nth_thread_entryI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as %Hentry.
    destruct Hentry as [sΓ [sΓ' [mt [Htyping Hsafe]]]].
    iExists sΓ, sΓ', mt.
    iSplit.
    - iPureIntro.
      split; [exact Htyping | exact Hsafe].
    - iApply (pico_sem_typed_thread_cacheI_bridge_cache_safe_lift_premise
        with "[] Hcontract").
      iPureIntro.
      split; [exact Htyping | exact Hsafe].
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_thread_bridge_cache_safe_contract
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e N addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    ∃ sΓ sΓ' mt,
      pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals ∗
      pico_wp_state_bridge_cache_safe_step_contract
        CT s E Φ e N addr derived abs_vals.
  Proof.
    iIntros (Hnth) "Hcfg Hcontract".
    iDestruct
      (pico_sem_typed_config_cacheI_nth_thread_entryI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as %Hentry.
    destruct Hentry as [sΓ [sΓ' [mt [Htyping Hsafe]]]].
    iExists sΓ, sΓ', mt.
    iSplit.
    - iPureIntro.
      split; [exact Htyping | exact Hsafe].
    - iApply (pico_sem_typed_thread_cacheI_bridge_cache_safe_contract
        with "[] Hcontract").
      iPureIntro.
      split; [exact Htyping | exact Hsafe].
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_bridge_lift_premise_from_cache_safe
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_lift_premise
      CT s E Φ e addr derived abs_vals -∗
    pico_wp_state_bridge_lift_premise CT s E Φ e.
  Proof.
    iIntros (Hnth) "Hcfg Hlift".
    iPoseProof
      (pico_sem_typed_config_cacheI_nth_thread_cache_safeI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as "Hsafe".
    iApply (pico_wp_state_bridge_cache_safe_lift_premise_lift_premise
      with "Hsafe Hlift").
  Qed.

  Lemma pico_sem_typed_config_cacheI_nth_bridge_contract_from_cache_safe
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      s E Φ cfg i e N addr derived abs_vals :
    nth_error (wc_threads cfg) i = Some e ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_wp_state_bridge_cache_safe_step_contract
      CT s E Φ e N addr derived abs_vals -∗
    pico_wp_state_bridge_step_contract
      CT s E Φ e N addr derived abs_vals.
  Proof.
    iIntros (Hnth) "Hcfg Hcontract".
    iPoseProof
      (pico_sem_typed_config_cacheI_nth_thread_cache_safeI
        cfg i e addr derived abs_vals Hnth with "Hcfg")
      as "Hsafe".
    iApply (pico_wp_state_bridge_cache_safe_contract_step_contract
      with "Hsafe Hcontract").
  Qed.

  Definition sem_typed_config_step_closureI
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c2⌝%I.

  Definition sem_typed_thread_post_stepsI
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜forall c1 c2,
      wm_step CT c1 c2 ->
      forall sigma sigma' threads i t t',
        c1 = mkWMConfig sigma threads ->
        nth_error threads i = Some t ->
        wm_thread_step CT sigma t sigma' t' ->
        sem_typed_thread_entry addr derived abs_vals t'⌝%I.

  Definition sem_typed_covered_stepsI
      (addr : FieldAddr) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    ⌜forall c1 c2,
      wm_step CT c1 c2 ->
      forall sigma sigma' threads i t t',
        c1 = mkWMConfig sigma threads ->
        nth_error threads i = Some t ->
        wm_thread_step CT sigma t sigma' t' ->
        sem_typed_thread_entry addr derived abs_vals t ->
        sem_typed_thread_entry addr derived abs_vals t'⌝%I.

  Lemma sem_typed_config_step_closureI_intro :
    forall addr derived abs_vals,
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      ⊢ sem_typed_config_step_closureI addr derived abs_vals.
  Proof.
    intros addr derived abs_vals Hclosed.
    iPureIntro.
    exact Hclosed.
  Qed.

  Lemma sem_typed_config_step_closureI_elim :
    forall addr derived abs_vals,
      sem_typed_config_step_closureI addr derived abs_vals -∗
      ⌜forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2⌝.
  Proof.
    iIntros (addr derived abs_vals) "Hclosed".
    iExact "Hclosed".
  Qed.

  Lemma sem_typed_thread_post_stepsI_intro :
    forall addr derived abs_vals,
      (forall c1 c2,
        wm_step CT c1 c2 ->
        forall sigma sigma' threads i t t',
          c1 = mkWMConfig sigma threads ->
          nth_error threads i = Some t ->
          wm_thread_step CT sigma t sigma' t' ->
          sem_typed_thread_entry addr derived abs_vals t') ->
      ⊢ sem_typed_thread_post_stepsI addr derived abs_vals.
  Proof.
    intros addr derived abs_vals Hpost.
    iPureIntro.
    exact Hpost.
  Qed.

  Lemma sem_typed_thread_post_stepsI_elim :
    forall addr derived abs_vals,
      sem_typed_thread_post_stepsI addr derived abs_vals -∗
      ⌜forall c1 c2,
        wm_step CT c1 c2 ->
        forall sigma sigma' threads i t t',
          c1 = mkWMConfig sigma threads ->
          nth_error threads i = Some t ->
          wm_thread_step CT sigma t sigma' t' ->
          sem_typed_thread_entry addr derived abs_vals t'⌝.
  Proof.
    iIntros (addr derived abs_vals) "Hpost".
    iExact "Hpost".
  Qed.

  Lemma sem_typed_covered_stepsI_intro :
    forall addr derived abs_vals,
      (forall c1 c2,
        wm_step CT c1 c2 ->
        forall sigma sigma' threads i t t',
          c1 = mkWMConfig sigma threads ->
          nth_error threads i = Some t ->
          wm_thread_step CT sigma t sigma' t' ->
          sem_typed_thread_entry addr derived abs_vals t ->
          sem_typed_thread_entry addr derived abs_vals t') ->
      ⊢ sem_typed_covered_stepsI addr derived abs_vals.
  Proof.
    intros addr derived abs_vals Hcovered.
    iPureIntro.
    exact Hcovered.
  Qed.

  Lemma sem_typed_covered_stepsI_elim :
    forall addr derived abs_vals,
      sem_typed_covered_stepsI addr derived abs_vals -∗
      ⌜forall c1 c2,
        wm_step CT c1 c2 ->
        forall sigma sigma' threads i t t',
          c1 = mkWMConfig sigma threads ->
          nth_error threads i = Some t ->
          wm_thread_step CT sigma t sigma' t' ->
          sem_typed_thread_entry addr derived abs_vals t ->
          sem_typed_thread_entry addr derived abs_vals t'⌝.
  Proof.
    iIntros (addr derived abs_vals) "Hcovered".
    iExact "Hcovered".
  Qed.

  Lemma sem_typed_config_entry_interpretation_cache_safe_config :
    forall cfg addr derived abs_vals,
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      cache_safe_config cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hsem.
    apply sem_typed_config_entries_cache_safe_config.
    exact Hsem.
  Qed.

  Lemma sem_typed_config_entry_interpretation_step_update :
    forall cfg cfg' addr derived abs_vals,
      wm_step CT cfg cfg' ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall sigma sigma' threads i t t',
        cfg = mkWMConfig sigma threads ->
        nth_error threads i = Some t ->
        wm_thread_step CT sigma t sigma' t' ->
        sem_typed_thread_entry addr derived abs_vals t') ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg'.
  Proof.
    intros cfg cfg' addr derived abs_vals Hstep Hsem Hpost.
    inversion Hstep as
      [sigma sigma' threads threads' i t t' Hnth Hthread Hthreads'];
      subst.
    simpl in *.
    apply Forall_update.
    - exact Hsem.
    - eapply Hpost; eauto.
    - apply nth_error_Some.
      rewrite Hnth.
      discriminate.
  Qed.

  Lemma sem_typed_config_step_closureI_from_thread_postI :
    forall addr derived abs_vals,
      sem_typed_thread_post_stepsI addr derived abs_vals -∗
      sem_typed_config_step_closureI addr derived abs_vals.
  Proof.
    iIntros (addr derived abs_vals) "Hpost".
    iDestruct (sem_typed_thread_post_stepsI_elim with "Hpost") as %Hpost.
    iApply sem_typed_config_step_closureI_intro.
    intros c1 c2 Hstep Hinterp.
    eapply sem_typed_config_entry_interpretation_step_update; eauto.
  Qed.

  Lemma sem_typed_config_step_closureI_from_coveredI :
    forall addr derived abs_vals,
      sem_typed_covered_stepsI addr derived abs_vals -∗
      sem_typed_config_step_closureI addr derived abs_vals.
  Proof.
    iIntros (addr derived abs_vals) "Hcovered".
    iDestruct (sem_typed_covered_stepsI_elim with "Hcovered")
      as %Hcovered.
    iApply sem_typed_config_step_closureI_intro.
    intros c1 c2 Hstep Hinterp.
    eapply sem_typed_config_entry_interpretation_step_update; eauto.
    intros sigma sigma' threads i t t' Hcfg Hnth Hthread.
    eapply Hcovered; eauto.
    subst c1.
    unfold sem_typed_config_entry_interpretation in Hinterp.
    eapply Forall_nth_error; eauto.
  Qed.

  Lemma sem_typed_config_entry_interpretation_seqstep_update :
    forall sigma sigma' threads i rΓ rΓ' V V' s1 s1' s2
      addr derived abs_vals,
      nth_error threads i = Some (mkWMThread rΓ (SSeq s1 s2) V) ->
      wm_thread_step CT
        sigma
        (mkWMThread rΓ s1 V)
        sigma'
        (mkWMThread rΓ' s1' V') ->
      sem_typed_thread_entry
        addr derived abs_vals
        (mkWMThread rΓ' (residual_seq_wm s1' s2) V') ->
      sem_typed_config_entry_interpretation
        addr derived abs_vals
        (mkWMConfig sigma threads) ->
      sem_typed_config_entry_interpretation
        addr derived abs_vals
        (mkWMConfig
          sigma'
          (update
            i
            (mkWMThread rΓ' (residual_seq_wm s1' s2) V')
            threads)).
  Proof.
    intros sigma sigma' threads i rΓ rΓ' V V' s1 s1' s2
           addr derived abs_vals Hnth _ Hresidual Hinterp.
    simpl in *.
    apply Forall_update.
    - exact Hinterp.
    - exact Hresidual.
    - apply nth_error_Some.
      rewrite Hnth.
      discriminate.
  Qed.

  Theorem sem_typed_config_entry_interpretation_semantic_cache_safe :
    forall cfg addr derived abs_vals,
      wm_semantic_cache_safe_under
        CT
        cfg
        addr
        derived
        abs_vals
        (sem_typed_config_entry_interpretation addr derived abs_vals).
  Proof.
    intros cfg addr derived abs_vals cfg' Hsteps Hsem Hstate.
    eapply cache_safe_config_semantic_cache_safe; eauto.
    intros c1 c2 Hpre Hstep Hpost.
    apply sem_typed_config_entry_interpretation_cache_safe_config.
    eapply Hsem; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_semantic_cache_safeI :
    forall cfg cfg' addr derived abs_vals,
      wm_steps CT cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      ⊢ (⌜wm_config_cache_history_state cfg' addr derived abs_vals⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals Hsteps Hsem Hstate.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_semantic_cache_safe; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_final_read_valid :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      derived_cache_msg_ok derived abs_vals v.
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hstate Hread.
    pose proof
      (sem_typed_config_entry_interpretation_semantic_cache_safe
        cfg addr derived abs_vals cfg' Hsteps
        (wm_steps_allowed_configs_from_global
          CT cfg cfg'
          (sem_typed_config_entry_interpretation addr derived abs_vals)
          Hsem)
        Hstate) as Hfinal.
    eapply wm_config_cache_history_state_read_valid; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_final_read_validI :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hstate Hread.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_final_read_valid; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_final_read_valid_generic :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v.
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hstate Hread.
    pose proof
      (sem_typed_config_entry_interpretation_semantic_cache_safe
        cfg addr derived abs_vals cfg' Hsteps
        (wm_steps_allowed_configs_from_global
          CT cfg cfg'
          (sem_typed_config_entry_interpretation addr derived abs_vals)
          Hsem)
        Hstate) as Hfinal.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
    apply wm_cache_history_state_generic.
    exact Hfinal.
  Qed.

  Theorem sem_typed_config_entry_interpretation_final_read_valid_genericI :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hstate Hread.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_final_read_valid_generic;
      eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_closed_final_read_valid :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      derived_cache_msg_ok derived abs_vals v.
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hclosed Hstate Hread.
    revert Hsem Hstate.
    induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH];
      intros Hsem Hstate.
    - eapply wm_config_cache_history_state_read_valid; eauto.
    - apply (IH Hread).
      + eapply Hclosed; eauto.
      + eapply wm_step_preserves_cache_history; eauto.
        eapply wm_step_cache_safe_from_config_allowed; eauto.
        apply cache_safe_config_implies_wm_config_threads_allowed.
        apply sem_typed_config_entry_interpretation_cache_safe_config.
        exact Hsem.
  Qed.

  Theorem sem_typed_config_entry_interpretation_closed_cache_history_preserved :
    forall cfg cfg' addr derived abs_vals,
      wm_steps CT cfg cfg' ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_config_cache_history_state cfg' addr derived abs_vals.
  Proof.
    intros cfg cfg' addr derived abs_vals Hsteps Hsem Hclosed Hstate.
    revert Hsem Hstate.
    induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH];
      intros Hsem Hstate.
    - exact Hstate.
    - apply IH.
      + eapply Hclosed; eauto.
      + eapply wm_step_preserves_cache_history; eauto.
        eapply wm_step_cache_safe_from_config_allowed; eauto.
        apply cache_safe_config_implies_wm_config_threads_allowed.
        apply sem_typed_config_entry_interpretation_cache_safe_config.
        exact Hsem.
  Qed.

  Theorem sem_typed_config_entry_interpretation_closed_cache_history_preservedI :
    forall cfg cfg' addr derived abs_vals,
      wm_steps CT cfg cfg' ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      ⊢ (⌜wm_config_cache_history_state cfg' addr derived abs_vals⌝
          : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals Hsteps Hsem Hclosed Hstate.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_closed_cache_history_preserved;
      eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_closed_semantic_executionI :
    forall cfg addr derived abs_vals,
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      ⊢ (wm_semantic_cache_safe_executionI CT cfg addr derived abs_vals
          : iProp Σ).
  Proof.
    intros cfg addr derived abs_vals Hsem Hclosed.
    iPureIntro.
    intros cfg' Hsteps Hstate.
    eapply sem_typed_config_entry_interpretation_closed_cache_history_preserved;
      eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_closed_final_read_validI :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hclosed Hstate Hread.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_closed_final_read_valid;
      eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_closed_final_read_valid_generic :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v.
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hclosed Hstate Hread.
    pose proof
      (sem_typed_config_entry_interpretation_closed_cache_history_preserved
        cfg cfg' addr derived abs_vals Hsteps Hsem Hclosed Hstate) as Hfinal.
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
    apply wm_cache_history_state_generic.
    exact Hfinal.
  Qed.

  Theorem sem_typed_config_entry_interpretation_closed_final_read_valid_genericI :
    forall cfg cfg' addr derived abs_vals V v V',
      wm_steps CT cfg cfg' ->
      sem_typed_config_entry_interpretation addr derived abs_vals cfg ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c2) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsteps Hsem Hclosed Hstate Hread.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_closed_final_read_valid_generic;
      eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_cache_safe_execution :
    forall cfg addr derived abs_vals,
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_semantic_cache_safe_execution CT cfg addr derived abs_vals.
  Proof.
    intros cfg addr derived abs_vals Hsem cfg' Hsteps Hstate.
    eapply sem_typed_config_entry_interpretation_semantic_cache_safe; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_cache_safe_executionI :
    forall cfg addr derived abs_vals,
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      ⊢ (⌜wm_semantic_cache_safe_execution CT cfg addr derived abs_vals⌝
          : iProp Σ).
  Proof.
    intros cfg addr derived abs_vals Hsem _.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_cache_safe_execution; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_semantic_executionI :
    forall cfg addr derived abs_vals,
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      ⊢ (wm_semantic_cache_safe_executionI CT cfg addr derived abs_vals
          : iProp Σ).
  Proof.
    intros cfg addr derived abs_vals Hsem.
    iPureIntro.
    eapply sem_typed_config_entry_interpretation_cache_safe_execution; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_semantic_execution_read_validI :
    forall cfg cfg' addr derived abs_vals V v V',
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_steps CT cfg cfg' ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsem Hsteps Hstate Hread.
    iApply wm_semantic_cache_safe_execution_read_validI; eauto.
    eapply sem_typed_config_entry_interpretation_cache_safe_execution; eauto.
  Qed.

  Theorem sem_typed_config_entry_interpretation_semantic_execution_read_valid_genericI :
    forall cfg cfg' addr derived abs_vals V v V',
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
      wm_steps CT cfg cfg' ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      wm_read (wc_state cfg') V addr v V' ->
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals V v V'
           Hsem Hsteps Hstate Hread.
    iApply wm_semantic_cache_safe_execution_read_valid_genericI; eauto.
    eapply sem_typed_config_entry_interpretation_cache_safe_execution; eauto.
  Qed.

  Lemma pico_sem_typed_config_cacheI_semantic_cache_safe :
    forall cfg cfg' addr derived abs_vals,
      wm_steps CT cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry addr derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state cfg addr derived abs_vals ->
      ⊢ (⌜wm_config_cache_history_state cfg' addr derived abs_vals⌝ : iProp Σ).
  Proof.
    intros cfg cfg' addr derived abs_vals Hsteps Hsem Hstate.
    iPureIntro.
    eapply cache_safe_config_semantic_cache_safe; eauto.
    intros c1 c2 Hpre Hstep Hpost.
    apply sem_typed_config_entries_cache_safe_config.
    eapply Hsem; eauto.
  Qed.

  Lemma pico_sem_typed_config_cacheI_inv_step_update
      `{!invGS Σ}
      E N N' cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_step CT cfg cfg' ->
    pico_sem_typed_config_cacheI cfg addr derived abs_vals -∗
    pico_cache_history_inv N cfg addr derived abs_vals ={E}=∗
    pico_cache_history_inv N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hstep) "Hsem Hinv".
    iDestruct "Hsem" as "%Hsem".
    iApply pico_cache_history_inv_after_config_step_alloc; eauto.
    apply sem_typed_config_entries_cache_safe_config.
    exact Hsem.
  Qed.

  Lemma sem_typed_config_entry_interpretation_inv_steps_update
      `{!invGS Σ}
      E N N' cfg cfg' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    |={E}=>
    pico_cache_history_inv N' cfg' addr derived abs_vals.
  Proof.
    iIntros (Hsubset Hsteps Hsem) "Hinv".
    iApply pico_cache_history_inv_after_steps_alloc; eauto.
    intros c1 c2 Hstep.
    apply sem_typed_config_entry_interpretation_cache_safe_config.
    eapply Hsem; eauto.
  Qed.

  Lemma sem_typed_config_entry_interpretation_inv_steps_read_valid
      `{!invGS Σ}
      E N N' cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsem) "Hinv %Hread".
    iApply (pico_cache_history_inv_after_steps_read_valid
      E N N' CT cfg cfg' V addr v V' derived abs_vals with "Hinv");
      eauto.
    intros c1 c2 Hstep.
    apply sem_typed_config_entry_interpretation_cache_safe_config.
    eapply Hsem; eauto.
  Qed.

  Lemma sem_typed_config_entry_interpretation_inv_steps_read_valid_generic
      `{!invGS Σ}
      E N N' cfg cfg' V addr v V' derived abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    pico_cache_history_inv N cfg addr derived abs_vals -∗
    ⌜wm_read (wc_state cfg') V addr v V'⌝ ={E}=∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsem) "Hinv %Hread".
    iApply (pico_cache_history_inv_after_steps_read_valid_generic
      E N N' CT cfg cfg' V addr v V' derived abs_vals with "Hinv");
      eauto.
    intros c1 c2 Hstep.
    apply sem_typed_config_entry_interpretation_cache_safe_config.
    eapply Hsem; eauto.
  Qed.

  Lemma sem_typed_state_generic_history_interp_allocI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iIntros (Hsubset) "Hstate".
    iApply (pico_cache_state_interp_generic_history_interp_alloc
      with "Hstate").
    exact Hsubset.
  Qed.

  Lemma sem_typed_state_generic_history_read_validI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iIntros (Hsubset) "Hstate %Hread".
    iApply (pico_cache_state_interp_generic_history_read_valid
      with "Hstate"); eauto.
  Qed.

  Theorem sem_typed_state_generic_history_refines_pureI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iIntros (Hsubset) "Hstate %Hsafe %Hreads %Hexec".
    iApply (pico_cache_state_interp_generic_history_refines_pure
      with "Hstate"); eauto.
  Qed.

  Theorem sem_typed_state_generic_history_refines_pure_post_extensionI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iIntros (Hsubset) "Hstate %Hsafe %Hext %Hreads %Hexec".
    iApply (pico_cache_state_interp_generic_history_refines_pure_post_extension
      derived E N cfg sigma' addr abs_vals F run_with_cache_trace args tr r
      with "Hstate [] [] [] []").
    - exact Hsubset.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hext.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Lemma sem_typed_wp_bridge_generic_history_interp_allocI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iApply (pico_wp_state_cfg_bridge_generic_history_interp_alloc
      with "Hbridge").
    exact Hsubset.
  Qed.

  Lemma sem_typed_wp_bridge_generic_history_read_validI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iApply (pico_wp_state_cfg_bridge_generic_history_read_valid
      with "Hbridge"); eauto.
  Qed.

  Theorem sem_typed_wp_bridge_generic_history_refines_pureI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iApply (pico_wp_state_cfg_bridge_generic_history_refines_pure
      with "Hbridge"); eauto.
  Qed.

  Theorem sem_typed_wp_bridge_generic_history_refines_pure_post_extensionI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
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
    iApply (pico_wp_state_cfg_bridge_generic_history_refines_pure_post_extension
      derived E sigma sigma' N cfg addr abs_vals
      F run_with_cache_trace args tr r with "Hbridge [] [] [] []").
    - exact Hsubset.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hext.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Lemma sem_typed_state_after_steps_generic_history_interp_allocI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' addr abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    pico_cache_state_interp N cfg addr derived abs_vals ={E}=∗
    pico_cache_state_interp N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsem) "Hstate".
    iApply (pico_cache_state_interp_after_steps_generic_history_interp_alloc
      derived E N N' CT cfg cfg' addr abs_vals with "Hstate").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
  Qed.

  Lemma sem_typed_state_after_steps_generic_history_read_validI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' V addr v V' abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem) "Hstate %Hread".
    iApply (pico_cache_state_interp_after_steps_generic_history_read_valid
      derived E N N' CT cfg cfg' V addr v V' abs_vals with "Hstate []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - iPureIntro.
      exact Hread.
  Qed.

  Theorem sem_typed_state_after_steps_generic_history_refines_pureI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem)
      "Hstate %Hsafe %Hreads %Hexec".
    iApply (pico_cache_state_interp_after_steps_generic_history_refines_pure
      derived E N N' CT cfg cfg' addr abs_vals
      F run_with_cache_trace args tr r with "Hstate [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_state_after_steps_generic_history_refines_pure_post_extensionI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem)
      "Hstate %Hsafe %Hreads %Hexec".
    iApply (pico_cache_state_interp_after_steps_generic_history_refines_pure_post_extension
      derived E N N' CT cfg cfg' addr abs_vals
      F run_with_cache_trace args tr r with "Hstate [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Lemma sem_typed_wp_bridge_after_steps_generic_history_interp_allocI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' addr abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    pico_wp_state_cfg_bridge sigma N cfg addr derived abs_vals ={E}=∗
    pico_wp_state_cfg_bridge (wc_state cfg') N' cfg' addr derived abs_vals ∗
    ∃ γ,
      generic_cache_history_interp
        (derived_cache_protocol derived)
        γ
        abs_vals
        (wm_derived_cache_snapshot derived addr (wc_state cfg')).
  Proof.
    iIntros (Hsubset Hsubset' Hsteps Hsem) "Hbridge".
    iApply (pico_wp_state_cfg_bridge_after_steps_generic_history_interp_alloc
      derived E N N' CT sigma cfg cfg' addr abs_vals with "Hbridge").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
  Qed.

  Lemma sem_typed_wp_bridge_after_steps_generic_history_read_validI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' V addr v V' abs_vals :
    ↑N ⊆ E ->
    ↑N' ⊆ E ->
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem) "Hbridge %Hread".
    iApply (pico_wp_state_cfg_bridge_after_steps_generic_history_read_valid
      derived E N N' CT sigma cfg cfg' V addr v V' abs_vals
      with "Hbridge []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - iPureIntro.
      exact Hread.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_generic_history_refines_pureI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem)
      "Hbridge %Hsafe %Hreads %Hexec".
    iApply (pico_wp_state_cfg_bridge_after_steps_generic_history_refines_pure
      derived E N N' CT sigma cfg cfg' addr abs_vals
      F run_with_cache_trace args tr r with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_generic_history_refines_pure_post_extensionI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem)
      "Hbridge %Hsafe %Hreads %Hexec".
    iApply (pico_wp_state_cfg_bridge_after_steps_generic_history_refines_pure_post_extension
      derived E N N' CT sigma cfg cfg' addr abs_vals
      F run_with_cache_trace args tr r with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - iPureIntro.
      exact Hsafe.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_state_after_steps_semantic_immutability_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Hstable Hstable')
      "Hstate %Hmethod %Hreads %Hexec".
    iApply
      (pico_cache_state_interp_after_steps_semantic_immutability_method_post
        derived E N N' CT cfg cfg' addr abs_vals Stable
        F run_with_cache_trace args tr r with "Hstate [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_semantic_immutability_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Hstable Hstable')
      "Hbridge %Hmethod %Hreads %Hexec".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_post
        derived E N N' CT sigma cfg cfg' addr abs_vals Stable
        F run_with_cache_trace args tr r with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_state_after_steps_semantic_immutability_method_write_extension_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' sigma' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Hstable Hstable')
      "Hstate %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_cache_state_interp_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CT cfg cfg' sigma' addr abs_vals Stable
        F run_with_cache_trace args tr r with "Hstate [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
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
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_semantic_immutability_method_write_extension_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' sigma' addr abs_vals
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
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Hstable Hstable')
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_semantic_immutability_method_write_extension_post
        derived E N N' CT sigma cfg cfg' sigma' addr abs_vals Stable
        F run_with_cache_trace args tr r with "Hbridge [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
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
  Qed.

  Theorem sem_typed_state_after_steps_pico_wm_stable_preserved_method_write_extension_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_steps_writes_avoid_fields CT cfg cfg' loc abs_fields ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Havoid Hpres Hstable)
      "Hstate %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_preserved_method_write_extension_post
        derived E N N' CT cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hstate [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Havoid.
    - exact Hpres.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_steps_writes_avoid_fields CT cfg cfg' loc abs_fields ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Havoid Hpres Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_preserved_method_write_extension_post
        derived E N N' CT sigma cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hbridge [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Havoid.
    - exact Hpres.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
  Qed.

  Theorem sem_typed_state_after_steps_pico_wm_stable_final_fields_method_write_extension_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CT C abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Htype HC Hfinals Hpres Hstable)
      "Hstate %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_write_extension_post
        derived E N N' CT cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields rt_abs F run_with_cache_trace args tr r
        with "Hstate [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Htype.
    - exact HC.
    - exact Hfinals.
    - exact Hpres.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CT C abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Htype HC Hfinals Hpres Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_write_extension_post
        derived E N N' CT sigma cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields rt_abs F run_with_cache_trace args tr r
        with "Hbridge [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Htype.
    - exact HC.
    - exact Hfinals.
    - exact Hpres.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
    - iPureIntro.
      exact Hext_by_writes.
  Qed.

  Theorem sem_typed_state_after_steps_pico_wm_stable_trace_robust_cache_only_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_steps_writes_avoid_fields CT cfg cfg' loc abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Havoid_steps Honly Havoid_target
       Hstable)
      "Hstate %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_trace_robust_cache_only_post
        derived E N N' CT cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hstate [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
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
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_pico_wm_stable_trace_robust_cache_only_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_steps_writes_avoid_fields CT cfg cfg' loc abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Havoid_steps Honly Havoid_target
       Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_trace_robust_cache_only_post
        derived E N N' CT sigma cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hbridge [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
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
  Qed.

  Theorem sem_typed_state_after_steps_pico_wm_stable_final_fields_trace_robust_cache_only_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CT C abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Htype HC Hfinals Honly Havoid_target
       Hstable)
      "Hstate %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_trace_robust_cache_only_post
        derived E N N' CT cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields rt_abs F run_with_cache_trace args tr r
        with "Hstate [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
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
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_trace_robust_cache_only_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' sigma' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CT C abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Htype HC Hfinals Honly Havoid_target
       Hstable)
      "Hbridge %Hmethod %Hreads %Hexec %Hext_by_writes".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_trace_robust_cache_only_post
        derived E N N' CT sigma cfg cfg' sigma' addr abs_vals
        CTabs C loc abs_fields rt_abs F run_with_cache_trace args tr r
        with "Hbridge [] [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
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
  Qed.

  Theorem sem_typed_state_after_steps_pico_wm_stable_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Hstable Hstable')
      "Hstate %Hmethod %Hreads %Hexec".
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_method_post
        derived E N N' CT cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hstate [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_pico_wm_stable_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Hstable Hstable')
      "Hbridge %Hmethod %Hreads %Hexec".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_method_post
        derived E N N' CT sigma cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_state_after_steps_pico_wm_stable_preserved_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_steps_writes_avoid_fields CT cfg cfg' loc abs_fields ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Havoid Hstable)
      "Hstate %Hmethod %Hreads %Hexec".
    pose proof
      (pico_wm_stable_abs_preserved_by_steps_avoiding_writes
        CT CTabs C loc abs_fields cfg cfg' abs_vals
        Hsteps Havoid Hstable) as Hstable'.
    iApply
      (sem_typed_state_after_steps_pico_wm_stable_method_postI
        derived E N N' cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hstate [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsem.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_pico_wm_stable_preserved_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_steps_writes_avoid_fields CT cfg cfg' loc abs_fields ->
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
    iIntros (Hsubset Hsubset' Hsteps Hsem Havoid Hstable)
      "Hbridge %Hmethod %Hreads %Hexec".
    pose proof
      (pico_wm_stable_abs_preserved_by_steps_avoiding_writes
        CT CTabs C loc abs_fields cfg cfg' abs_vals
        Hsteps Havoid Hstable) as Hstable'.
    iApply
      (sem_typed_wp_bridge_after_steps_pico_wm_stable_method_postI
        derived E N N' sigma cfg cfg' addr abs_vals
        CTabs C loc abs_fields F run_with_cache_trace args tr r
        with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - exact Hsem.
    - exact Hstable.
    - exact Hstable'.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_state_after_steps_pico_wm_stable_final_fields_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' cfg cfg' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CT C abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Htype HC Hfinals Hstable)
      "Hstate %Hmethod %Hreads %Hexec".
    iApply
      (pico_cache_state_interp_after_steps_pico_wm_stable_final_fields_method_post
        derived E N N' CT cfg cfg' addr abs_vals
        CTabs C loc abs_fields rt_abs F run_with_cache_trace args tr r
        with "Hstate [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Htype.
    - exact HC.
    - exact Hfinals.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Theorem sem_typed_wp_bridge_after_steps_pico_wm_stable_final_fields_method_postI
      `{!invGS Σ} `{!PicoIrisGhostState.picoCacheG Σ}
      derived `{!genericCacheG (derived_cache_protocol derived) Σ}
      E N N' sigma cfg cfg' addr abs_vals
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
    wm_steps CT cfg cfg' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation addr derived abs_vals c1) ->
    wm_get_type (wc_state cfg) loc = Some rt_abs ->
    rctype rt_abs = C ->
    final_fields CT C abs_fields ->
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
      (Hsubset Hsubset' Hsteps Hsem Htype HC Hfinals Hstable)
      "Hbridge %Hmethod %Hreads %Hexec".
    iApply
      (pico_wp_state_cfg_bridge_after_steps_pico_wm_stable_final_fields_method_post
        derived E N N' CT sigma cfg cfg' addr abs_vals
        CTabs C loc abs_fields rt_abs F run_with_cache_trace args tr r
        with "Hbridge [] [] []").
    - exact Hsubset.
    - exact Hsubset'.
    - exact Hsteps.
    - intros c1 c2 Hstep.
      apply sem_typed_config_entry_interpretation_cache_safe_config.
      eapply Hsem; eauto.
    - exact Htype.
    - exact HC.
    - exact Hfinals.
    - exact Hstable.
    - iPureIntro.
      exact Hmethod.
    - iPureIntro.
      exact Hreads.
    - iPureIntro.
      exact Hexec.
  Qed.

  Lemma cache_compute_write_safe_tail_sem_typed_threadI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n V,
      cache_compute_write_safe
        CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals n ->
      ⊢ pico_sem_typed_thread_cacheI
          sΓ_mid
          sΓ_mid
          mt
          (mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V)
          (loc, cache_f)
          derived
          abs_vals.
  Proof.
    intros sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n V Hsafe.
    iPureIntro.
    split.
    - destruct Hsafe as [_ Htype_write _].
      exact Htype_write.
    - eapply cache_compute_write_safe_implies_cache_safe_tail.
      exact Hsafe.
  Qed.

  Lemma cache_compute_write_safe_tail_sem_typed_stmtI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n,
      cache_compute_write_safe
        CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals n ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ_mid
          sΓ_mid
          mt
          rΓ_mid
          (SFldWrite receiver cache_f tmp)
          (loc, cache_f)
          derived
          abs_vals.
  Proof.
    intros sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n Hsafe.
    iPureIntro.
    split.
    - destruct Hsafe as [_ Htype_write _].
      exact Htype_write.
    - eapply cache_compute_write_safe_implies_cache_safe_tail.
      exact Hsafe.
  Qed.

  Lemma cache_compute_then_write_safe_sem_typed_phasesI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n,
      cache_compute_then_write_safe
        CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals n ->
      ⊢ pico_sem_typed_stmt_cacheI
          sΓ sΓ_mid mt rΓ compute (loc, cache_f) derived abs_vals ∗
        pico_sem_typed_stmt_cacheI
          sΓ_mid
          sΓ_mid
          mt
          rΓ_mid
          (SFldWrite receiver cache_f tmp)
          (loc, cache_f)
          derived
          abs_vals.
  Proof.
    intros sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n Hsafe.
    destruct Hsafe as [Hcompute_write Hcompute_safe Hwrite_safe].
    destruct Hcompute_write as [Hcompute Htype_write Hreceiver].
    destruct Hcompute as [Htype_compute Htmp Hderived Hnz].
    iSplit.
    - iPureIntro.
      split; assumption.
    - iPureIntro.
      split; assumption.
  Qed.

  Definition pico_sem_cache_compute_then_write_phasesI
      (sΓ sΓ_mid : s_env) (mt : method_type)
      (rΓ rΓ_mid : r_env) (loc : Loc) (cache_f receiver tmp : var)
      (compute : stmt) (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) : iProp Σ :=
    pico_sem_typed_stmt_cacheI
      sΓ sΓ_mid mt rΓ compute (loc, cache_f) derived abs_vals ∗
    pico_sem_typed_stmt_cacheI
      sΓ_mid
      sΓ_mid
      mt
      rΓ_mid
      (SFldWrite receiver cache_f tmp)
      (loc, cache_f)
      derived
      abs_vals.

  Lemma cache_compute_then_write_safe_sem_typed_phases_namedI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n,
      cache_compute_then_write_safe
        CT sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals n ->
      ⊢ pico_sem_cache_compute_then_write_phasesI
          sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
          derived abs_vals.
  Proof.
    intros sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals n Hsafe.
    unfold pico_sem_cache_compute_then_write_phasesI.
    iApply cache_compute_then_write_safe_sem_typed_phasesI.
    exact Hsafe.
  Qed.

  Lemma cache_update_sequence_safe_sem_typed_phasesI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      ⊢ pico_sem_cache_compute_then_write_phasesI
          sΓ
          sΓ
          mt
          rΓ
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          loc
          cache_f
          receiver
          tmp
          (SVarAss tmp (EInt n))
          derived
          abs_vals.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe.
    iApply cache_compute_then_write_safe_sem_typed_phases_namedI.
    apply cache_update_sequence_safe_implies_compute_then_write_safe.
    exact Hsafe.
  Qed.

  Lemma pico_sem_cache_update_sequence_phasesI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n,
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      pico_sem_cache_compute_then_write_phasesI
        sΓ
        sΓ
        mt
        rΓ
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        loc
        cache_f
        receiver
        tmp
        (SVarAss tmp (EInt n))
        derived
        abs_vals.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n) "%Hsafe".
    iApply cache_update_sequence_safe_sem_typed_phasesI.
    exact Hsafe.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_threadI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals V,
      pico_sem_cache_compute_then_write_phasesI
        sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals -∗
      pico_sem_typed_thread_cacheI
        sΓ_mid
        sΓ_mid
        mt
        (mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V)
        (loc, cache_f)
        derived
        abs_vals.
  Proof.
    iIntros (sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
             derived abs_vals V) "Hphases".
    unfold pico_sem_cache_compute_then_write_phasesI,
      pico_sem_typed_thread_cacheI.
    iDestruct "Hphases" as "[_ Hwrite]".
    iExact "Hwrite".
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_configI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals V sigma,
      pico_sem_cache_compute_then_write_phasesI
        sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals -∗
      pico_sem_typed_config_cacheI
        (mkWMConfig
          sigma
          [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V])
        (loc, cache_f)
        derived
        abs_vals.
  Proof.
    iIntros (sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
             derived abs_vals V sigma) "Hphases".
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_threadI with "Hphases")
        as "Htail".
    iDestruct
      (pico_sem_typed_thread_cacheI_entry with "Htail")
        as "%Hentry".
    iPureIntro.
    constructor; [exact Hentry | constructor].
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_closed_final_read_validI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals V sigma cfg' Vread v Vread',
      let tail_cfg :=
        mkWMConfig
          sigma
          [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
      wm_steps CT tail_cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2) ->
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
      pico_sem_cache_compute_then_write_phasesI
        sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals -∗
      ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
             derived abs_vals V sigma cfg' Vread v Vread'
             tail_cfg Hsteps Hclosed Hstate Hread) "Hphases".
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_configI
        with "Hphases") as "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as "%Hinterp".
    iApply sem_typed_config_entry_interpretation_closed_final_read_validI;
      eauto.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_closed_final_read_valid_genericI :
    forall sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
           derived abs_vals V sigma cfg' Vread v Vread',
      let tail_cfg :=
        mkWMConfig
          sigma
          [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
      wm_steps CT tail_cfg cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2) ->
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
      pico_sem_cache_compute_then_write_phasesI
        sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals -∗
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝.
  Proof.
    iIntros (sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
             derived abs_vals V sigma cfg' Vread v Vread'
             tail_cfg Hsteps Hclosed Hstate Hread) "Hphases".
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_configI
        with "Hphases") as "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as "%Hinterp".
    iApply sem_typed_config_entry_interpretation_closed_final_read_valid_genericI;
      eauto.
  Qed.

  Definition pico_sem_cache_compute_then_write_phases_tail_execution_specI
      (sΓ sΓ_mid : s_env) (mt : method_type)
      (rΓ rΓ_mid : r_env) (loc : Loc)
      (cache_f receiver tmp : var) (compute : stmt)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) (V : nat)
      (sigma : wm_state) (cfg' : wm_config) : iProp Σ :=
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    ⌜wm_steps CT tail_cfg cfg' /\
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals /\
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2)⌝ ∗
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals.

  Lemma pico_sem_cache_compute_then_write_phases_tail_execution_specI_intro
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' :
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c1 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c2) ->
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals -∗
    pico_sem_cache_compute_then_write_phases_tail_execution_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg'.
  Proof.
    iIntros (tail_cfg Hsteps Hstate Hclosed) "Hphases".
    unfold pico_sem_cache_compute_then_write_phases_tail_execution_specI.
    iFrame.
    iPureIntro.
    repeat split; assumption.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_execution_specI_from_closureI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' :
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals -∗
    sem_typed_config_step_closureI (loc, cache_f) derived abs_vals -∗
    pico_sem_cache_compute_then_write_phases_tail_execution_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg'.
  Proof.
    iIntros (tail_cfg Hsteps Hstate) "Hphases Hclosed".
    iDestruct (sem_typed_config_step_closureI_elim with "Hclosed")
      as %Hclosed.
    iApply (pico_sem_cache_compute_then_write_phases_tail_execution_specI_intro
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' with "Hphases"); eauto.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_execution_specI_elim
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' :
    pico_sem_cache_compute_then_write_phases_tail_execution_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' -∗
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    ⌜wm_steps CT tail_cfg cfg' /\
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals /\
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2)⌝ ∗
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals.
  Proof.
    iIntros "Hspec".
    unfold pico_sem_cache_compute_then_write_phases_tail_execution_specI.
    iExact "Hspec".
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_execution_specI_final_historyI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' :
    pico_sem_cache_compute_then_write_phases_tail_execution_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' -∗
    ⌜wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals⌝.
  Proof.
    iIntros "Hspec".
    iDestruct (pico_sem_cache_compute_then_write_phases_tail_execution_specI_elim
      with "Hspec") as "[%Hfacts Hphases]".
    destruct Hfacts as [Hsteps [Hstate Hclosed]].
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_configI
        with "Hphases") as "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as "%Hinterp".
    iApply
      (sem_typed_config_entry_interpretation_closed_cache_history_preservedI
        (mkWMConfig
          sigma
          [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V])
        cfg'
        (loc, cache_f)
        derived
        abs_vals); eauto.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_execution_specI_semantic_executionI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' :
    pico_sem_cache_compute_then_write_phases_tail_execution_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' -∗
    wm_semantic_cache_safe_executionI
      CT
      (mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V])
      (loc, cache_f)
      derived
      abs_vals.
  Proof.
    iIntros "Hspec".
    iDestruct (pico_sem_cache_compute_then_write_phases_tail_execution_specI_elim
      with "Hspec") as "[%Hfacts Hphases]".
    destruct Hfacts as [Hsteps [Hstate Hclosed]].
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_configI
        with "Hphases") as "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as "%Hinterp".
    iApply
      (sem_typed_config_entry_interpretation_closed_semantic_executionI
        (mkWMConfig
          sigma
          [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V])
        (loc, cache_f)
        derived
        abs_vals); eauto.
  Qed.

  Definition pico_sem_cache_compute_then_write_phases_tail_read_specI
      (sΓ sΓ_mid : s_env) (mt : method_type)
      (rΓ rΓ_mid : r_env) (loc : Loc)
      (cache_f receiver tmp : var) (compute : stmt)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) (V : nat)
      (sigma : wm_state) (cfg' : wm_config)
      (Vread : view) (v : Syntax.value) (Vread' : view) : iProp Σ :=
    pico_sem_cache_compute_then_write_phases_tail_execution_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' ∗
    ⌜wm_read (wc_state cfg') Vread (loc, cache_f) v Vread'⌝.

  Lemma pico_sem_cache_compute_then_write_phases_tail_read_specI_intro
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' :
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c1 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c2) ->
    wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals -∗
    pico_sem_cache_compute_then_write_phases_tail_read_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread'.
  Proof.
    iIntros (tail_cfg Hsteps Hstate Hclosed Hread) "Hphases".
    unfold pico_sem_cache_compute_then_write_phases_tail_read_specI.
    iSplitL "Hphases".
    - iApply (pico_sem_cache_compute_then_write_phases_tail_execution_specI_intro
        sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals V sigma cfg' with "Hphases"); eauto.
    - iPureIntro. exact Hread.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_read_specI_elim
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' :
    pico_sem_cache_compute_then_write_phases_tail_read_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' -∗
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    ⌜wm_steps CT tail_cfg cfg' /\
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals /\
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' /\
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2)⌝ ∗
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals.
  Proof.
    iIntros "Hspec".
    unfold pico_sem_cache_compute_then_write_phases_tail_read_specI.
    iDestruct "Hspec" as "[Hexec %Hread]".
    iDestruct (pico_sem_cache_compute_then_write_phases_tail_execution_specI_elim
      with "Hexec") as "[%Hfacts Hphases]".
    destruct Hfacts as [Hsteps [Hstate Hclosed]].
    iFrame.
    iPureIntro.
    repeat split; assumption.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_read_specI_final_read_validI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' :
    pico_sem_cache_compute_then_write_phases_tail_read_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' -∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros "Hspec".
    iDestruct (pico_sem_cache_compute_then_write_phases_tail_read_specI_elim
      with "Hspec") as "[%Hfacts Hphases]".
    destruct Hfacts as [Hsteps [Hstate [Hread Hclosed]]].
    iApply (pico_sem_cache_compute_then_write_phases_tail_closed_final_read_validI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' with "Hphases");
      eauto.
  Qed.

  Lemma pico_sem_cache_compute_then_write_phases_tail_read_specI_final_read_valid_genericI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' :
    pico_sem_cache_compute_then_write_phases_tail_read_specI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V sigma cfg' Vread v Vread' -∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros "Hspec".
    iDestruct (pico_sem_cache_compute_then_write_phases_tail_read_specI_elim
      with "Hspec") as "[%Hfacts Hphases]".
    destruct Hfacts as [Hsteps [Hstate [Hread Hclosed]]].
    iApply
      (pico_sem_cache_compute_then_write_phases_tail_closed_final_read_valid_genericI
        sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
        derived abs_vals V sigma cfg' Vread v Vread' with "Hphases");
      eauto.
  Qed.

  Definition pico_sem_cache_update_sequence_tail_execution_specI
      (sΓ : s_env) (mt : method_type) (rΓ : r_env)
      (loc : Loc) (cache_f receiver tmp : var)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) (n V : nat)
      (sigma : wm_state) (cfg' : wm_config) : iProp Σ :=
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    ⌜wm_steps CT tail_cfg cfg' /\
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals /\
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2)⌝ ∗
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_intro
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c1 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c2) ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate Hclosed) "Hseq".
    unfold pico_sem_cache_update_sequence_tail_execution_specI.
    iFrame.
    iPureIntro.
    repeat split; assumption.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_from_closureI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    sem_typed_config_step_closureI (loc, cache_f) derived abs_vals -∗
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate) "Hseq Hclosed".
    iDestruct (sem_typed_config_step_closureI_elim with "Hclosed")
      as %Hclosed.
    iApply (pico_sem_cache_update_sequence_tail_execution_specI_intro
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      with "Hseq"); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_from_thread_postI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    sem_typed_thread_post_stepsI (loc, cache_f) derived abs_vals -∗
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate) "Hseq Hpost".
    iPoseProof (sem_typed_config_step_closureI_from_thread_postI with "Hpost")
      as "Hclosed".
    iApply (pico_sem_cache_update_sequence_tail_execution_specI_from_closureI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      with "Hseq Hclosed"); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_from_coveredI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    sem_typed_covered_stepsI (loc, cache_f) derived abs_vals -∗
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate) "Hseq Hcovered".
    iPoseProof (sem_typed_config_step_closureI_from_coveredI with "Hcovered")
      as "Hclosed".
    iApply (pico_sem_cache_update_sequence_tail_execution_specI_from_closureI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      with "Hseq Hclosed"); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_elim
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' -∗
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    ⌜wm_steps CT tail_cfg cfg' /\
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals /\
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2)⌝ ∗
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n.
  Proof.
    iIntros "Hspec".
    unfold pico_sem_cache_update_sequence_tail_execution_specI.
    iExact "Hspec".
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_phaseI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' -∗
    pico_sem_cache_compute_then_write_phases_tail_execution_specI
      sΓ
      sΓ
      mt
      rΓ
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      loc
      cache_f
      receiver
      tmp
      (SVarAss tmp (EInt n))
      derived
      abs_vals
      V
      sigma
      cfg'.
  Proof.
    iIntros "Hspec".
    iDestruct (pico_sem_cache_update_sequence_tail_execution_specI_elim
      with "Hspec") as "[%Hfacts Hseq]".
    destruct Hfacts as [Hsteps [Hstate Hclosed]].
    iPoseProof (pico_sem_cache_update_sequence_phasesI with "Hseq")
      as "Hphases".
    iApply (pico_sem_cache_compute_then_write_phases_tail_execution_specI_intro
      sΓ sΓ mt rΓ (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      loc cache_f receiver tmp (SVarAss tmp (EInt n))
      derived abs_vals V sigma cfg' with "Hphases"); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_final_historyI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' -∗
    ⌜wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals⌝.
  Proof.
    iIntros "Hspec".
    iPoseProof
      (pico_sem_cache_update_sequence_tail_execution_specI_phaseI
        with "Hspec") as "Hphase".
    iApply
      (pico_sem_cache_compute_then_write_phases_tail_execution_specI_final_historyI
        with "Hphase").
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_execution_specI_semantic_executionI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' :
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' -∗
    wm_semantic_cache_safe_executionI
      CT
      (mkWMConfig
        sigma
        [mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V])
      (loc, cache_f)
      derived
      abs_vals.
  Proof.
    iIntros "Hspec".
    iPoseProof
      (pico_sem_cache_update_sequence_tail_execution_specI_phaseI
        with "Hspec") as "Hphase".
    iApply
      (pico_sem_cache_compute_then_write_phases_tail_execution_specI_semantic_executionI
        with "Hphase").
  Qed.

  Definition pico_sem_cache_update_sequence_tail_read_specI
      (sΓ : s_env) (mt : method_type) (rΓ : r_env)
      (loc : Loc) (cache_f receiver tmp : var)
      (derived : list Syntax.value -> nat)
      (abs_vals : list Syntax.value) (n V : nat)
      (sigma : wm_state) (cfg' : wm_config)
      (Vread : view) (v : Syntax.value) (Vread' : view) : iProp Σ :=
    pico_sem_cache_update_sequence_tail_execution_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg' ∗
    ⌜wm_read (wc_state cfg') Vread (loc, cache_f) v Vread'⌝.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_intro
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
    (forall c1 c2,
      wm_step CT c1 c2 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c1 ->
      sem_typed_config_entry_interpretation
        (loc, cache_f) derived abs_vals c2) ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate Hread Hclosed) "Hseq".
    unfold pico_sem_cache_update_sequence_tail_read_specI.
    iSplitL "Hseq".
    - iApply (pico_sem_cache_update_sequence_tail_execution_specI_intro
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
        with "Hseq"); eauto.
    - iPureIntro.
      exact Hread.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_from_closureI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    sem_typed_config_step_closureI (loc, cache_f) derived abs_vals -∗
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate Hread) "Hseq Hclosed".
    iDestruct (sem_typed_config_step_closureI_elim with "Hclosed")
      as %Hclosed.
    iApply (pico_sem_cache_update_sequence_tail_read_specI_intro
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' with "Hseq"); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_from_thread_postI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    sem_typed_thread_post_stepsI (loc, cache_f) derived abs_vals -∗
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate Hread) "Hseq Hpost".
    iPoseProof (sem_typed_config_step_closureI_from_thread_postI with "Hpost")
      as "Hclosed".
    iApply (pico_sem_cache_update_sequence_tail_read_specI_from_closureI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' with "Hseq Hclosed"); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_from_coveredI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    wm_steps CT tail_cfg cfg' ->
    wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals ->
    wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    sem_typed_covered_stepsI (loc, cache_f) derived abs_vals -∗
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread'.
  Proof.
    iIntros (rΓ_mid tail_cfg Hsteps Hstate Hread) "Hseq Hcovered".
    iPoseProof (sem_typed_config_step_closureI_from_coveredI with "Hcovered")
      as "Hclosed".
    iApply (pico_sem_cache_update_sequence_tail_read_specI_from_closureI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' with "Hseq Hclosed"); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_elim
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' -∗
    let rΓ_mid := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail_cfg :=
      mkWMConfig
        sigma
        [mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V] in
    ⌜wm_steps CT tail_cfg cfg' /\
      wm_config_cache_history_state tail_cfg (loc, cache_f) derived abs_vals /\
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' /\
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c1 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f) derived abs_vals c2)⌝ ∗
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n.
  Proof.
    iIntros "Hspec".
    unfold pico_sem_cache_update_sequence_tail_read_specI.
    iDestruct "Hspec" as "[Hexec %Hread]".
    iDestruct (pico_sem_cache_update_sequence_tail_execution_specI_elim
      with "Hexec") as "[%Hfacts Hseq]".
    destruct Hfacts as [Hsteps [Hstate Hclosed]].
    iSplitL "".
    - iPureIntro.
      repeat split; assumption.
    - iExact "Hseq".
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_phaseI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' -∗
    pico_sem_cache_compute_then_write_phases_tail_read_specI
      sΓ
      sΓ
      mt
      rΓ
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      loc
      cache_f
      receiver
      tmp
      (SVarAss tmp (EInt n))
      derived
      abs_vals
      V
      sigma
      cfg'
      Vread
      v
      Vread'.
  Proof.
    iIntros "Hspec".
    unfold pico_sem_cache_update_sequence_tail_read_specI.
    iDestruct "Hspec" as "[Hexec %Hread]".
    unfold pico_sem_cache_compute_then_write_phases_tail_read_specI.
    iSplitL "Hexec".
    - iApply (pico_sem_cache_update_sequence_tail_execution_specI_phaseI
        with "Hexec").
    - iPureIntro. exact Hread.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_final_read_validI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' -∗
    ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros "Hspec".
    iPoseProof (pico_sem_cache_update_sequence_tail_read_specI_phaseI
      with "Hspec") as "Hphase".
    iApply
      (pico_sem_cache_compute_then_write_phases_tail_read_specI_final_read_validI
        with "Hphase").
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_final_read_valid_genericI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' -∗
    ⌜cache_valid
        (derived_cache_protocol derived)
        abs_vals
        DerivedCacheField
        v⌝.
  Proof.
    iIntros "Hspec".
    iPoseProof (pico_sem_cache_update_sequence_tail_read_specI_phaseI
      with "Hspec") as "Hphase".
    iApply
      (pico_sem_cache_compute_then_write_phases_tail_read_specI_final_read_valid_genericI
        with "Hphase").
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_final_historyI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' -∗
    ⌜wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals⌝.
  Proof.
    iIntros "Hspec".
    iDestruct (pico_sem_cache_update_sequence_tail_read_specI_elim
      with "Hspec") as "[%Hfacts Hseq]".
    destruct Hfacts as [Hsteps [Hstate [Hread Hclosed]]].
    iPoseProof (pico_sem_cache_update_sequence_phasesI with "Hseq")
      as "Hphases".
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_configI
        with "Hphases") as "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as "%Hinterp".
    iApply
      (sem_typed_config_entry_interpretation_closed_cache_history_preservedI
        (mkWMConfig
          sigma
          [mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V])
        cfg'
        (loc, cache_f)
        derived
        abs_vals); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_read_specI_semantic_executionI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' :
    pico_sem_cache_update_sequence_tail_read_specI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma cfg'
      Vread v Vread' -∗
    wm_semantic_cache_safe_executionI
      CT
      (mkWMConfig
        sigma
        [mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V])
      (loc, cache_f)
      derived
      abs_vals.
  Proof.
    iIntros "Hspec".
    iDestruct (pico_sem_cache_update_sequence_tail_read_specI_elim
      with "Hspec") as "[%Hfacts Hseq]".
    destruct Hfacts as [Hsteps [Hstate [Hread Hclosed]]].
    iPoseProof (pico_sem_cache_update_sequence_phasesI with "Hseq")
      as "Hphases".
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_configI
        with "Hphases") as "Hcfg".
    iDestruct (pico_sem_typed_config_cacheI_interp with "Hcfg")
      as "%Hinterp".
    iApply
      (sem_typed_config_entry_interpretation_closed_semantic_executionI
        (mkWMConfig
          sigma
          [mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V])
        (loc, cache_f)
        derived
        abs_vals); eauto.
  Qed.

  Lemma cache_update_sequence_safe_tail_sem_typed_threadI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      ⊢ pico_sem_typed_thread_cacheI
          sΓ
          sΓ
          mt
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          (loc, cache_f)
          derived
          abs_vals.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V Hsafe.
    destruct Hsafe as
      [Htype_compute Htype_write Hneq Hreceiver Htmp_dom Hderived Hnz].
    iPureIntro.
    split.
    - exact Htype_write.
    - eapply cache_safe_fldwrite_target_after_assign_int; eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_threadI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V,
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      pico_sem_typed_thread_cacheI
        sΓ
        sΓ
        mt
        (mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V)
        (loc, cache_f)
        derived
        abs_vals.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V)
      "%Hsafe".
    iApply cache_update_sequence_safe_tail_sem_typed_threadI.
    exact Hsafe.
  Qed.

  Lemma cache_update_sequence_safe_first_step_tail :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      wm_thread_step
        CT
        sigma
        (mkWMThread
          rΓ
          (cache_update_sequence_stmt tmp receiver cache_f n)
          V)
        sigma
        (mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma Hsafe.
    destruct Hsafe as
      [_ _ _ _ Htmp_dom _ _].
    unfold cache_update_sequence_stmt.
    destruct (nth_error_Some_exists (vars rΓ) tmp Htmp_dom) as
      [old_v Hold].
    change (SFldWrite receiver cache_f tmp) with
      (residual_seq_wm SSkip (SFldWrite receiver cache_f tmp)).
    eapply WMTS_SeqStep.
    eapply WMTS_AssignInt with (old_v := old_v).
    exact Hold.
  Qed.

  Lemma cache_update_sequence_safe_first_step_inv :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma sigma' e',
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      wm_thread_step
        CT
        sigma
        (mkWMThread
          rΓ
          (cache_update_sequence_stmt tmp receiver cache_f n)
          V)
        sigma'
        e' ->
      sigma' = sigma /\
      e' =
        mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma sigma' e' _ Hstep.
    unfold cache_update_sequence_stmt in Hstep.
    inversion Hstep; subst; try discriminate.
    inversion H6; subst; try discriminate.
    split; reflexivity.
  Qed.

  Lemma cache_update_sequence_safe_first_step_exists :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      exists e' sigma',
        wm_thread_step
          CT
          sigma
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V)
          sigma'
          e'.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma Hsafe.
    exists
      (mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V),
      sigma.
    eapply cache_update_sequence_safe_first_step_tail; eauto.
  Qed.

  Lemma cache_update_sequence_safe_first_step_not_stuck :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      @not_stuck (pico_language CT)
        (mkWMThread
          rΓ
          (cache_update_sequence_stmt tmp receiver cache_f n)
          V)
        sigma.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma Hsafe.
    apply pico_not_stuck_intro.
    right.
    eapply cache_update_sequence_safe_first_step_exists; eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_first_step_existsI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      ⌜exists e' sigma',
        wm_thread_step
          CT
          sigma
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V)
          sigma'
          e'⌝.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma)
      "%Hsafe".
    iPureIntro.
    eapply cache_update_sequence_safe_first_step_exists; eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_not_stuckI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      ⌜@not_stuck (pico_language CT)
        (mkWMThread
          rΓ
          (cache_update_sequence_stmt tmp receiver cache_f n)
          V)
        sigma⌝.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma)
      "%Hsafe".
    iPureIntro.
    eapply cache_update_sequence_safe_first_step_not_stuck; eauto.
  Qed.

  Lemma cache_update_sequence_safe_step_to_sem_typed_tailI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      ⊢ ∃ e',
        ⌜wm_thread_step
          CT
          sigma
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V)
          sigma
          e'⌝ ∗
        pico_sem_typed_thread_cacheI
          sΓ
          sΓ
          mt
          e'
          (loc, cache_f)
          derived
          abs_vals.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma Hsafe.
    iExists
      (mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V).
    iSplit.
    - iPureIntro.
      eapply cache_update_sequence_safe_first_step_tail; eauto.
    - iApply cache_update_sequence_safe_tail_sem_typed_threadI.
      exact Hsafe.
  Qed.

  Lemma cache_update_sequence_safe_config_first_step_tail :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      wm_step
        CT
        (mkWMConfig
          sigma
          [mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V])
        (mkWMConfig
          sigma
          [mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V]).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma Hsafe.
    eapply WMS_Thread with
      (i := 0)
      (t :=
        mkWMThread
          rΓ
          (cache_update_sequence_stmt tmp receiver cache_f n)
          V)
      (t' :=
        mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V).
    - reflexivity.
    - eapply cache_update_sequence_safe_first_step_tail; eauto.
    - reflexivity.
  Qed.

  Lemma cache_update_sequence_safe_config_step_to_sem_typed_tailI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      ⊢ ∃ cfg',
        ⌜wm_step
          CT
          (mkWMConfig
            sigma
            [mkWMThread
              rΓ
              (cache_update_sequence_stmt tmp receiver cache_f n)
              V])
          cfg'⌝ ∗
        ⌜wm_config_cache_history_state
          (mkWMConfig
            sigma
            [mkWMThread
              rΓ
              (cache_update_sequence_stmt tmp receiver cache_f n)
              V])
          (loc, cache_f)
          derived
          abs_vals ->
          wm_config_cache_history_state
            cfg'
            (loc, cache_f)
            derived
            abs_vals⌝ ∗
        pico_sem_typed_config_cacheI cfg' (loc, cache_f) derived abs_vals.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V sigma Hsafe.
    iExists
      (mkWMConfig
        sigma
        [mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V]).
    iSplit.
    - iPureIntro.
      eapply cache_update_sequence_safe_config_first_step_tail; eauto.
    - iSplit.
      + iPureIntro.
        intro Hstate.
        exact Hstate.
      + iPureIntro.
        constructor.
        * exists sΓ, sΓ, mt.
          split.
          -- destruct Hsafe as [_ Htype_write _ _ _ _ _].
             exact Htype_write.
          -- unfold cache_safe_thread.
             eapply cache_update_sequence_safe_implies_cache_safe_tail.
             exact Hsafe.
        * constructor.
  Qed.

  Lemma cache_update_sequence_safe_tail_sem_typed_entry :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      sem_typed_thread_entry
        (loc, cache_f)
        derived
        abs_vals
        (mkWMThread
          (set_vars rΓ (update tmp (Int n) (vars rΓ)))
          (SFldWrite receiver cache_f tmp)
          V).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V Hsafe.
    exists sΓ, sΓ, mt.
    split.
    - destruct Hsafe as [_ Htype_write _ _ _ _ _].
      exact Htype_write.
    - unfold cache_safe_thread.
      eapply cache_update_sequence_safe_implies_cache_safe_tail.
      exact Hsafe.
  Qed.

  Lemma cache_update_sequence_safe_update_threads_sem_typed :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           threads i,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      i < length threads ->
      Forall
        (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
        threads ->
      Forall
        (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
        (update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           threads i Hsafe Hlen Hthreads.
    apply Forall_update; auto.
    eapply cache_update_sequence_safe_tail_sem_typed_entry; eauto.
  Qed.

  Lemma cache_update_sequence_safe_embedded_config_step_to_sem_typed_tailI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V) ->
      Forall
        (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
        (update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads) ->
      ⊢ ∃ cfg',
        ⌜wm_step CT (mkWMConfig sigma threads) cfg'⌝ ∗
        ⌜wm_config_cache_history_state
          (mkWMConfig sigma threads)
          (loc, cache_f)
          derived
          abs_vals ->
          wm_config_cache_history_state
            cfg'
            (loc, cache_f)
            derived
            abs_vals⌝ ∗
        pico_sem_typed_config_cacheI cfg' (loc, cache_f) derived abs_vals.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i Hsafe Hnth Htail_threads.
    set (tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V).
    iExists (mkWMConfig sigma (update i tail threads)).
    iSplit.
    - iPureIntro.
      eapply WMS_Thread with
        (i := i)
        (t :=
          mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V)
        (t' := tail).
      + exact Hnth.
      + unfold tail.
        eapply cache_update_sequence_safe_first_step_tail; eauto.
      + reflexivity.
    - iSplit.
      + iPureIntro.
        intro Hstate.
        exact Hstate.
      + iPureIntro.
        unfold tail.
        exact Htail_threads.
  Qed.

  Lemma cache_update_sequence_safe_embedded_config_tail_execution_safeI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i cfg',
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V) ->
      let tail_threads :=
        update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads in
      wm_steps CT (mkWMConfig sigma tail_threads) cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      ⊢ (⌜wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals⌝
          : iProp Σ).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i cfg' Hsafe Hnth tail_threads Hsteps Hallowed Hstate.
    iPureIntro.
    eapply cache_safe_config_semantic_cache_safe; eauto.
    intros c1 c2 Hpre Hstep Hpost.
    apply sem_typed_config_entries_cache_safe_config.
    eapply Hallowed; eauto.
  Qed.

  Lemma cache_update_sequence_safe_tail_pool_cache_safe_execution :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      let tail_threads :=
        update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads in
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f)
          derived
          abs_vals
          c1) ->
      wm_semantic_cache_safe_execution
        CT
        (mkWMConfig sigma tail_threads)
        (loc, cache_f)
        derived
        abs_vals.
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i _ tail_threads Hsem.
    eapply sem_typed_config_entry_interpretation_cache_safe_execution; eauto.
  Qed.

  Lemma cache_update_sequence_safe_tail_pool_cache_safe_executionI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i,
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      let tail_threads :=
        update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads in
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f)
          derived
          abs_vals
          c1) ->
      wm_config_cache_history_state
        (mkWMConfig sigma tail_threads)
        (loc, cache_f)
        derived
        abs_vals ->
      ⊢ (⌜wm_semantic_cache_safe_execution
            CT
            (mkWMConfig sigma tail_threads)
            (loc, cache_f)
            derived
            abs_vals⌝ : iProp Σ).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i Hsafe tail_threads Hsem Hstate.
    iPureIntro.
    eapply cache_update_sequence_safe_tail_pool_cache_safe_execution; eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_tail_pool_cache_safe_executionI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i,
      let tail_threads :=
        update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads in
      (forall c1 c2,
        wm_step CT c1 c2 ->
        sem_typed_config_entry_interpretation
          (loc, cache_f)
          derived
          abs_vals
          c1) ->
      wm_config_cache_history_state
        (mkWMConfig sigma tail_threads)
        (loc, cache_f)
        derived
        abs_vals ->
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      ⌜wm_semantic_cache_safe_execution
        CT
        (mkWMConfig sigma tail_threads)
        (loc, cache_f)
        derived
        abs_vals⌝.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
             sigma threads i tail_threads Hsem Hstate) "Hseq".
    iDestruct "Hseq" as %Hsafe.
    iApply (cache_update_sequence_safe_tail_pool_cache_safe_executionI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
      sigma threads i); eauto.
  Qed.

  Definition cache_update_sequence_selected_first_execution
      (rΓ : r_env) (receiver tmp cache_f : var) (n V : nat)
      (sigma : wm_state) (threads : list wm_thread) (i : nat)
      (cfg' : wm_config) : Prop :=
    wm_steps
      CT
      (mkWMConfig
        sigma
        (update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads))
      cfg'.

  Lemma cache_update_sequence_safe_embedded_config_execution_safeI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i cfg',
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V) ->
      let tail_threads :=
        update
          i
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            (SFldWrite receiver cache_f tmp)
            V)
          threads in
      wm_steps CT (mkWMConfig sigma tail_threads) cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      ⊢ (⌜wm_steps CT (mkWMConfig sigma threads) cfg' /\
          wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals⌝
          : iProp Σ).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i cfg' Hsafe Hnth tail_threads Hsteps Hallowed Hstate.
    iPureIntro.
    split.
    - eapply WMS_Step.
      + eapply WMS_Thread with
          (i := i)
          (t :=
            mkWMThread
              rΓ
              (cache_update_sequence_stmt tmp receiver cache_f n)
              V)
          (t' :=
            mkWMThread
              (set_vars rΓ (update tmp (Int n) (vars rΓ)))
              (SFldWrite receiver cache_f tmp)
              V).
        * exact Hnth.
        * eapply cache_update_sequence_safe_first_step_tail; eauto.
        * reflexivity.
      + exact Hsteps.
    - eapply cache_safe_config_semantic_cache_safe; eauto.
      intros c1 c2 Hpre Hstep Hpost.
      apply sem_typed_config_entries_cache_safe_config.
      eapply Hallowed; eauto.
  Qed.

  Lemma cache_update_sequence_safe_selected_first_execution_safeI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i cfg',
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V) ->
      cache_update_sequence_selected_first_execution
        rΓ receiver tmp cache_f n V sigma threads i cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      ⊢ (⌜wm_steps CT (mkWMConfig sigma threads) cfg' /\
          wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals⌝
          : iProp Σ).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i cfg' Hsafe Hnth Hselected Hallowed Hstate.
    unfold cache_update_sequence_selected_first_execution in Hselected.
    eapply cache_update_sequence_safe_embedded_config_execution_safeI; eauto.
  Qed.

  Lemma cache_update_sequence_safe_selected_first_final_read_validI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
           sigma threads i cfg' Vread v Vread',
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            Vthread) ->
      cache_update_sequence_selected_first_execution
        rΓ receiver tmp cache_f n Vthread sigma threads i cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
      ⊢ (⌜derived_cache_msg_ok derived abs_vals v⌝ : iProp Σ).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
           sigma threads i cfg' Vread v Vread'
           Hsafe Hnth Hselected Hallowed Hstate Hread.
    iPureIntro.
    unfold cache_update_sequence_selected_first_execution in Hselected.
    assert (Hfinal :
      wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals).
    {
      eapply cache_safe_config_semantic_cache_safe; eauto.
      intros c1 c2 Hpre Hstep Hpost.
      apply sem_typed_config_entries_cache_safe_config.
      eapply Hallowed; eauto.
    }
    eapply wm_config_cache_history_state_read_valid; eauto.
  Qed.

  Lemma cache_update_sequence_safe_selected_first_final_read_valid_genericI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
           sigma threads i cfg' Vread v Vread',
      cache_update_sequence_safe
        CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            Vthread) ->
      cache_update_sequence_selected_first_execution
        rΓ receiver tmp cache_f n Vthread sigma threads i cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
      ⊢ (⌜cache_valid
            (derived_cache_protocol derived)
            abs_vals
            DerivedCacheField
            v⌝ : iProp Σ).
  Proof.
    intros sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
           sigma threads i cfg' Vread v Vread'
           Hsafe Hnth Hselected Hallowed Hstate Hread.
    iPureIntro.
    unfold cache_update_sequence_selected_first_execution in Hselected.
    assert (Hfinal :
      wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals).
    {
      eapply cache_safe_config_semantic_cache_safe; eauto.
      intros c1 c2 Hpre Hstep Hpost.
      apply sem_typed_config_entries_cache_safe_config.
      eapply Hallowed; eauto.
    }
    eapply wm_read_valid_via_generic_cache_hist_ok; eauto.
    apply wm_cache_history_state_generic.
    exact Hfinal.
  Qed.

  Lemma pico_sem_cache_update_sequence_selected_first_execution_safeI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
           sigma threads i cfg',
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            V) ->
      cache_update_sequence_selected_first_execution
        rΓ receiver tmp cache_f n V sigma threads i cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      ⌜wm_steps CT (mkWMConfig sigma threads) cfg' /\
        wm_config_cache_history_state cfg' (loc, cache_f) derived abs_vals⌝.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
             sigma threads i cfg' Hnth Hselected Hallowed Hstate) "Hseq".
    iDestruct "Hseq" as %Hsafe.
    iApply (cache_update_sequence_safe_selected_first_execution_safeI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
      sigma threads i cfg'); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_selected_first_final_read_validI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
           sigma threads i cfg' Vread v Vread',
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            Vthread) ->
      cache_update_sequence_selected_first_execution
        rΓ receiver tmp cache_f n Vthread sigma threads i cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      ⌜derived_cache_msg_ok derived abs_vals v⌝.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
             sigma threads i cfg' Vread v Vread'
             Hnth Hselected Hallowed Hstate Hread) "Hseq".
    iDestruct "Hseq" as %Hsafe.
    iApply (cache_update_sequence_safe_selected_first_final_read_validI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
      sigma threads i cfg' Vread v Vread'); eauto.
  Qed.

  Lemma pico_sem_cache_update_sequence_selected_first_final_read_valid_genericI :
    forall sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
           sigma threads i cfg' Vread v Vread',
      nth_error
        threads
        i =
        Some
          (mkWMThread
            rΓ
            (cache_update_sequence_stmt tmp receiver cache_f n)
            Vthread) ->
      cache_update_sequence_selected_first_execution
        rΓ receiver tmp cache_f n Vthread sigma threads i cfg' ->
      (forall c1 c2,
        wm_step CT c1 c2 ->
        Forall
          (sem_typed_thread_entry (loc, cache_f) derived abs_vals)
          (wc_threads c1)) ->
      wm_config_cache_history_state
        (mkWMConfig sigma threads)
        (loc, cache_f)
        derived
        abs_vals ->
      wm_read (wc_state cfg') Vread (loc, cache_f) v Vread' ->
      pico_sem_cache_update_sequenceI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
      ⌜cache_valid
          (derived_cache_protocol derived)
          abs_vals
          DerivedCacheField
          v⌝.
  Proof.
    iIntros (sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
             sigma threads i cfg' Vread v Vread'
             Hnth Hselected Hallowed Hstate Hread) "Hseq".
    iDestruct "Hseq" as %Hsafe.
    iApply (cache_update_sequence_safe_selected_first_final_read_valid_genericI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Vthread
      sigma threads i cfg' Vread v Vread'); eauto.
  Qed.

  Lemma wp_pico_lift_cache_update_sequence_to_sem_typed_tail
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    cache_update_sequence_safe
      CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
    let tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V in
    let full :=
      mkWMThread
        rΓ
        (cache_update_sequence_stmt tmp receiver cache_f n)
        V in
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP tail @ s; E {{ Φ }}))
    ⊢ WP full @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros (Hsafe) "Htail".
    iApply wp_pico_lift_thread_step.
    - unfold cache_update_sequence_stmt.
      apply pico_language_to_val_seq.
    - iIntros (sigma ns k ks nt) "Hstate".
      iMod ("Htail" with "Hstate") as "Htail_step".
      iModIntro.
      iSplit.
      + destruct s; simpl; auto.
        iPureIntro.
        eapply pico_reducible_from_thread_step.
        eapply cache_update_sequence_safe_first_step_tail; eauto.
      + iNext.
        iIntros (e' sigma') "%Hstep Hcred".
        destruct (cache_update_sequence_safe_first_step_inv
          sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
          sigma sigma' e' Hsafe Hstep) as [-> ->].
        iMod ("Htail_step" with "Hcred") as "[$ Hwp]".
        iModIntro.
        iFrame.
  Qed.

  Lemma wp_pico_lift_cache_update_sequence_to_sem_typed_tail_exists
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    cache_update_sequence_safe
      CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
    let tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V in
    let full :=
      mkWMThread
        rΓ
        (cache_update_sequence_stmt tmp receiver cache_f n)
        V in
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP tail @ s; E {{ Φ }}))
    ⊢ WP full @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros (Hsafe) "Htail".
    iApply wp_pico_lift_thread_step_exists.
    - unfold cache_update_sequence_stmt.
      apply pico_language_to_val_seq.
    - iIntros (sigma ns k ks nt) "Hstate".
      iMod ("Htail" with "Hstate") as "Htail_step".
      iModIntro.
      iSplit.
      + destruct s; simpl; auto.
        iPureIntro.
        eexists _, _.
        eapply cache_update_sequence_safe_first_step_tail; eauto.
      + iNext.
        iIntros (e' sigma') "%Hstep Hcred".
        destruct (cache_update_sequence_safe_first_step_inv
          sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V
          sigma sigma' e' Hsafe Hstep) as [-> ->].
        iMod ("Htail_step" with "Hcred") as "[$ Hwp]".
        iModIntro.
        iFrame.
  Qed.

  Lemma wp_pico_lift_cache_update_sequence_with_sem_typed_tail
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    cache_update_sequence_safe
      CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
    let tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V in
    let full :=
      mkWMThread
        rΓ
        (cache_update_sequence_stmt tmp receiver cache_f n)
        V in
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        (pico_sem_typed_thread_cacheI
          sΓ sΓ mt tail (loc, cache_f) derived abs_vals -∗
          WP tail @ s; E {{ Φ }})))
    ⊢ WP full @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros (Hsafe) "Htail".
    iApply wp_pico_lift_cache_update_sequence_to_sem_typed_tail; [exact Hsafe |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Htail" with "Hstate") as "Htail_step".
    iModIntro.
    iNext.
    iIntros "Hcred".
    iMod ("Htail_step" with "Hcred") as "[$ Hwp_from_sem]".
    iModIntro.
    iApply "Hwp_from_sem".
    iApply cache_update_sequence_safe_tail_sem_typed_threadI.
    exact Hsafe.
  Qed.

  Lemma wp_pico_lift_cache_update_sequence_with_sem_typed_tail_exists
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    cache_update_sequence_safe
      CT sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n ->
    let tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V in
    let full :=
      mkWMThread
        rΓ
        (cache_update_sequence_stmt tmp receiver cache_f n)
        V in
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        (pico_sem_typed_thread_cacheI
          sΓ sΓ mt tail (loc, cache_f) derived abs_vals -∗
          WP tail @ s; E {{ Φ }})))
    ⊢ WP full @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros (Hsafe) "Htail".
    iApply wp_pico_lift_cache_update_sequence_to_sem_typed_tail_exists; [exact Hsafe |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Htail" with "Hstate") as "Htail_step".
    iModIntro.
    iNext.
    iIntros "Hcred".
    iMod ("Htail_step" with "Hcred") as "[$ Hwp_from_sem]".
    iModIntro.
    iApply "Hwp_from_sem".
    iApply cache_update_sequence_safe_tail_sem_typed_threadI.
    exact Hsafe.
  Qed.

  Lemma wp_pico_lift_sem_cache_update_sequence_with_tail
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    let tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V in
    let full :=
      mkWMThread
        rΓ
        (cache_update_sequence_stmt tmp receiver cache_f n)
        V in
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        (pico_sem_typed_thread_cacheI
          sΓ sΓ mt tail (loc, cache_f) derived abs_vals -∗
          WP tail @ s; E {{ Φ }})))
    -∗ WP full @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros "Hseq Htail".
    iDestruct "Hseq" as %Hsafe.
    iApply wp_pico_lift_cache_update_sequence_with_sem_typed_tail.
    - exact Hsafe.
    - iExact "Htail".
  Qed.

  Lemma wp_pico_lift_sem_cache_update_sequence_with_tail_exists
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    let tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V in
    let full :=
      mkWMThread
        rΓ
        (cache_update_sequence_stmt tmp receiver cache_f n)
        V in
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        (pico_sem_typed_thread_cacheI
          sΓ sΓ mt tail (loc, cache_f) derived abs_vals -∗
          WP tail @ s; E {{ Φ }})))
    -∗ WP full @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros "Hseq Htail".
    iDestruct "Hseq" as %Hsafe.
    iApply wp_pico_lift_cache_update_sequence_with_sem_typed_tail_exists.
    - exact Hsafe.
    - iExact "Htail".
  Qed.

  Lemma wp_pico_lift_sem_typed_thread_step
      s E Φ sΓ sΓ' mt e addr derived abs_vals :
    to_val e = None ->
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
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
    iIntros (Hnot_val) "Hsem Hlift".
    iPoseProof (pico_sem_typed_thread_cacheI_cache_safe with "Hsem")
      as "Hsafe".
    iApply (wp_pico_lift_cache_safe_thread_stepI with "Hsafe Hlift").
    exact Hnot_val.
  Qed.

  Lemma wp_pico_lift_sem_typed_thread_step_exists
      s E Φ sΓ sΓ' mt e addr derived abs_vals :
    to_val e = None ->
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
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
    iIntros (Hnot_val) "Hsem Hlift".
    iPoseProof (pico_sem_typed_thread_cacheI_cache_safe with "Hsem")
      as "Hsafe".
    iApply (wp_pico_lift_cache_safe_thread_step_existsI with "Hsafe Hlift").
    exact Hnot_val.
  Qed.

  Lemma wp_pico_sem_cache_update_tail_fldwrite_step_progress
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    let tail_env := set_vars rΓ (update tmp (Int n) (vars rΓ)) in
    let tail := mkWMThread tail_env (SFldWrite receiver cache_f tmp) V in
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜exists sigma' V' rt a,
        wm_get_type sigma loc = Some rt /\
        sf_assignability_rel CT (rctype rt) cache_f a /\
        Bigstep.runtime_vpa_assignability (rqtype rt) a = Assignable /\
        wm_write sigma sigma' V V' (loc, cache_f) (Int n)⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma tail sigma' e'⌝ -∗
        ⌜wm_cache_history_state sigma (loc, cache_f) derived abs_vals ->
          wm_cache_history_state sigma' (loc, cache_f) derived abs_vals⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    -∗ WP tail @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros "Hseq Hwp".
    iDestruct "Hseq" as %Hsafe.
    iPoseProof
      (cache_update_sequence_safe_tail_sem_typed_threadI
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V Hsafe)
      as "Htail".
    destruct Hsafe as
      [_ _ Hneq Hreceiver Htmp_dom _ _].
    assert (Hreceiver_tail :
      runtime_getVal
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        receiver = Some (Iot loc)).
    {
      rewrite runtime_getVal_set_vars_update_diff; eauto.
    }
    assert (Htmp_tail :
      runtime_getVal
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        tmp = Some (Int n)).
    {
      apply runtime_getVal_set_vars_update_same.
      exact Htmp_dom.
    }
    iApply (wp_pico_lift_sem_typed_thread_step_exists with "Htail").
    - apply pico_language_to_val_fld_write.
    - iIntros (sigma ns k ks nt) "Hstate".
      iMod ("Hwp" with "Hstate") as "[%Hwrite Hstep]".
      iModIntro.
      iSplit.
      + destruct s; simpl; auto.
        destruct Hwrite as
          [sigma' [V' [rt [a [Htype [Hfield [Hassign Hwrite]]]]]]].
        iPureIntro.
        eexists
          (mkWMThread
            (set_vars rΓ (update tmp (Int n) (vars rΓ)))
            SSkip
            V'),
          sigma'.
        eapply WMTS_FldWrite; eauto.
      + iExact "Hstep".
  Qed.

  Lemma wp_pico_lift_sem_cache_update_sequence_full_progress
      s E Φ sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n V :
    let tail :=
      mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V in
    let full :=
      mkWMThread
        rΓ
        (cache_update_sequence_stmt tmp receiver cache_f n)
        V in
    pico_sem_cache_update_sequenceI
      sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n -∗
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        (∀ sigma_tail ns_tail k_tail ks_tail nt_tail,
          state_interp
            sigma_tail
            ns_tail
            (k_tail ++ ks_tail)
            nt_tail ={E,∅}=∗
          ⌜exists sigma' V' rt a,
            wm_get_type sigma_tail loc = Some rt /\
            sf_assignability_rel CT (rctype rt) cache_f a /\
            Bigstep.runtime_vpa_assignability (rqtype rt) a = Assignable /\
            wm_write sigma_tail sigma' V V' (loc, cache_f) (Int n)⌝ ∗
          ▷ ∀ e' sigma',
            ⌜wm_thread_step CT sigma_tail tail sigma' e'⌝ -∗
            ⌜wm_cache_history_state
                sigma_tail
                (loc, cache_f)
                derived
                abs_vals ->
              wm_cache_history_state
                sigma'
                (loc, cache_f)
                derived
                abs_vals⌝ -∗
            £ 1 ={∅,E}=∗
            state_interp sigma' (S ns_tail) ks_tail nt_tail ∗
            WP e' @ s; E {{ Φ }})))
    -∗ WP full @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros "Hseq Hprogress".
    iDestruct "Hseq" as %Hsafe.
    iPoseProof
      (pico_sem_cache_update_sequence_intro
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe)
      as "Hseq_first".
    iApply (wp_pico_lift_sem_cache_update_sequence_with_tail_exists
      with "Hseq_first").
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Hprogress" with "Hstate") as "Hafter_first".
    iModIntro.
    iNext.
    iIntros "Hcred".
    iMod ("Hafter_first" with "Hcred") as "[$ Htail_progress]".
    iModIntro.
    iIntros "_".
    iPoseProof
      (pico_sem_cache_update_sequence_intro
        sΓ mt rΓ loc cache_f receiver tmp derived abs_vals n Hsafe)
      as "Hseq_tail".
    iApply (wp_pico_sem_cache_update_tail_fldwrite_step_progress
      with "Hseq_tail Htail_progress").
  Qed.

  Lemma wp_pico_lift_sem_cache_compute_then_write_tail_step
      s E Φ sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V :
    let tail :=
      mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V in
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals -∗
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck then reducible tail sigma else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma tail sigma' e'⌝ -∗
        ⌜wm_cache_history_state sigma (loc, cache_f) derived abs_vals ->
          wm_cache_history_state sigma' (loc, cache_f) derived abs_vals⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    -∗ WP tail @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros "Hphases Hwp".
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_threadI
        with "Hphases") as "Htail".
    iApply (wp_pico_lift_sem_typed_thread_step with "Htail Hwp").
    apply pico_language_to_val_fld_write.
  Qed.

  Lemma wp_pico_lift_sem_cache_compute_then_write_tail_step_exists
      s E Φ sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals V :
    let tail :=
      mkWMThread rΓ_mid (SFldWrite receiver cache_f tmp) V in
    pico_sem_cache_compute_then_write_phasesI
      sΓ sΓ_mid mt rΓ rΓ_mid loc cache_f receiver tmp compute
      derived abs_vals -∗
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck
        then exists e' sigma', wm_thread_step CT sigma tail sigma' e'
        else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜wm_thread_step CT sigma tail sigma' e'⌝ -∗
        ⌜wm_cache_history_state sigma (loc, cache_f) derived abs_vals ->
          wm_cache_history_state sigma' (loc, cache_f) derived abs_vals⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    -∗ WP tail @ s; E {{ Φ }}.
  Proof.
    simpl.
    iIntros "Hphases Hwp".
    iPoseProof
      (pico_sem_cache_compute_then_write_phases_tail_threadI
        with "Hphases") as "Htail".
    iApply (wp_pico_lift_sem_typed_thread_step_exists with "Htail Hwp").
    apply pico_language_to_val_fld_write.
  Qed.

  Lemma pico_sem_typed_thread_cacheI_inv_step_update
      `{!invGS Σ}
      E N N' sΓ sΓ' mt e sigma sigma' e' addr derived abs_vals :
    ↑N ⊆ E ->
    wm_thread_step CT sigma e sigma' e' ->
    pico_sem_typed_thread_cacheI sΓ sΓ' mt e addr derived abs_vals -∗
    pico_cache_history_inv
      N
      (mkWMConfig sigma [e])
      addr
      derived
      abs_vals ={E}=∗
    pico_cache_history_inv
      N'
      (mkWMConfig sigma' [e'])
      addr
      derived
      abs_vals.
  Proof.
    iIntros (Hsubset Hstep) "Hsem Hinv".
    iPoseProof (pico_sem_typed_thread_cacheI_cache_safe with "Hsem")
      as "HsafeI".
    iDestruct "HsafeI" as %Hsafe.
    iApply pico_cache_history_inv_after_thread_step_alloc; eauto.
  Qed.
End pico_iris_semantic_typing.

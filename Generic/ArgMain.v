From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases GhostOverride ArgClean ArgOverride GhostCall ArgCall.

(** The main step of readonly-state and transitive-state preservation over
    payload views.  There is no condition on the allocations a protected
    method performs. *)

Lemma pg_step : forall P CT,
  clean_bounds_ct CT ->
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ sΓ' G L next wf mode qthis lc lm,
      readonly_state_method_scope (tv_mode Δ) ->
      nomut_bounds Δ ->
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ (tv_mode Δ) s sΓ' ->
      heapP P CT h G L next ->
      frameP CT sΓ rΓ h G L next wf mode qthis lc lm ->
      ffit CT L Δ (act_frame qthis wf mode lc lm) ->
      (forall l, P l -> l < dom h) ->
      exists G' next',
        heapP P CT h' G' L next' /\
        frameP CT sΓ' rΓ' h' G' L next' wf mode qthis lc lm /\
        gext h G G' /\ next <= next' /\
        prot_preserved P CT (tv_mode Δ) h h'.
Proof.
  intros P CT Hcl rΓ h s res rΓ' h' Heval.
  induction Heval;
    intros Hres Δ sΓ sΓ' G L next wf mode qthis lc lm Hrs Hcb Hwf Htype HG HF
      Hfl HPdom;
    try discriminate;
    destruct (frame_ctx_p _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf HF)
      as (ιt & ot & Hthis0 & Hobj0 & Hq & Hlc & Hlm & Hfb); subst qthis.
  - (* skip *)
    inversion Htype; subst. exists G, next.
    refine (conj HG (conj HF (conj (gext_refl _ _) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
  - (* local *)
    inversion Htype; subst. exists G, next.
    refine (conj HG (conj _ (conj (gext_refl _ _) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    apply frameP_local; auto.
    destruct Hwf as (_ & _ & _ & _ & _ & Hlen & _). exact Hlen.
  - (* assign *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    exists G, next.
    refine (conj HG (conj _ (conj (gext_refl _ _) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    eapply (plcase_assign P CT Δ sΓ rΓ h G L next wf mode lc lm ιt ot
              Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hfl); eauto.
  - (* field write *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst. exists G, next.
    destruct (plcase_fldwrite P CT Δ sΓ rΓ h G L next wf mode lc lm ιt ot
                Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hlc Hlm Hfl _ _ _ _ _ _ _ _
                Htype Hval_x Hobj Hfield Hassign Hval_y) as [HG' Hp].
    refine (conj HG' (conj _ (conj (gext_refl _ _) (conj (le_n _) Hp)))).
    eapply frameP_ext; eauto using update_field_heap_ext, gext_refl.
  - (* new *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst.
    destruct (plcase_new P CT Δ sΓ rΓ h G L next wf mode lc lm ιt ot
                Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hlc Hlm Hfl
                (fun o0 n0 B0 Hb0 => proj1 (Hcb o0 n0 B0 Hb0))
                _ _ _ _ _ _ _ _ Htype Hthis Hargs Hmut HPdom)
      as (HG' & HF' & Hgx).
    eexists _, next.
    refine (conj HG' (conj HF' (conj Hgx (conj (le_n _) _)))).
    intros l qr C0 Rs vals0 f HP Hl _.
    exists vals0. split; [|reflexivity].
    rewrite runtime_getObj_last2; [eapply runtime_getObj_dom; eauto | exact Hl].
  - (* call *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst.
    eapply (plcase_call P CT Δ sΓ rΓ h G L next wf mode lc lm ιt ot
              Hcl Hrs Hcb Hwf HG HF Hfl Hthis0 Hobj0 HPdom
              _ _ _ _ _ _ _ _ _ _ _ _ _ _
              Htype Hval_y Hbase Hfind Hargs Hframe Heval Hretval).
    intros Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0.
    exact (IHHeval Hcl eq_refl Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0).
  - (* cast *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    exists G, next.
    refine (conj HG (conj _ (conj (gext_refl _ _) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    eapply (plcase_cast P CT Δ sΓ rΓ h G L next wf mode lc lm ιt ot
              Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hfl); eauto.
  - (* sequence *)
    inversion Htype; subst.
    destruct (IHHeval1 Hcl eq_refl _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf Htype1 HG HF
                Hfl HPdom)
      as (G1 & next1 & HG1 & HF1 & Hgx1 & Hle1 & HP1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval1) as [Hd1 _].
    assert (HPdom1 : forall l, P l -> l < dom h').
    { intros l HP. specialize (HPdom l HP). lia. }
    destruct (IHHeval2 Hcl eq_refl _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf1 Htype2 HG1 HF1
                Hfl HPdom1)
      as (G2 & next2 & HG2 & HF2 & Hgx2 & Hle2 & HP2).
    exists G2, next2.
    refine (conj HG2 (conj HF2 (conj _ (conj _ _)))).
    + eapply gext_trans; eauto.
    + lia.
    + intros l qr C Rs vals f HP Hl Hprot.
      destruct (HP1 l qr C Rs vals f HP Hl Hprot) as (vals1 & Hl1 & He1).
      destruct (HP2 l qr C Rs vals1 f HP Hl1 Hprot) as (vals2 & Hl2 & He2).
      exists vals2. split; auto. congruence.
Qed.

Print Assumptions pg_step.

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

(** Composition of protected-field preservation along a run. *)
Lemma prot_preserved_seq : forall P CT mt h h1 h2,
  prot_preserved P CT mt h h1 -> prot_preserved P CT mt h1 h2 ->
  prot_preserved P CT mt h h2.
Proof.
  intros P CT mt h h1 h2 H1 H2 l qr C Rs vals f HP Hl Hprot.
  destruct (H1 l qr C Rs vals f HP Hl Hprot) as (vals1 & Hl1 & He1).
  destruct (H2 l qr C Rs vals1 f HP Hl1 Hprot) as (vals2 & Hl2 & He2).
  exists vals2. split; auto. congruence.
Qed.

Lemma pg_step_any : forall P CT,
  clean_bounds_ct CT ->
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    forall Δ sΓ sΓ' G L next wf mode qthis lc lm lk,
      readonly_state_method_scope (tv_mode Δ) ->
      nomut_bounds Δ ->
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ (tv_mode Δ) s sΓ' ->
      heapP P CT h G L next ->
      frameP CT sΓ rΓ h G L next wf mode qthis lc lm lk ->
      ffit CT L Δ (act_frame qthis wf mode lc lm lk) ->
      (forall l, P l -> l < dom h) ->
      prot_preserved P CT (tv_mode Δ) h h' /\
      (res = OK ->
       exists G' next',
         heapP P CT h' G' L next' /\
         frameP CT sΓ' rΓ' h' G' L next' wf mode qthis lc lm lk /\
         gext h G G' /\ next <= next').
Proof.
  intros P CT Hcl rΓ h s res rΓ' h' Heval.
  induction Heval;
    intros Δ sΓ sΓ' G L next wf mode qthis lc lm lk Hrs Hcb Hwf Htype HG HF
      Hfl HPdom;
    try (split; [apply prot_preserved_refl | discriminate]);
    destruct (frame_ctx_p _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf HF)
      as (ιt & ot & Hthis0 & Hobj0 & Hq & Hlc & Hlm & Hfb); subst qthis.
  - (* skip *)
    inversion Htype; subst. split; [apply prot_preserved_refl|]. intros _.
    exists G, next.
    refine (conj HG (conj HF (conj (gext_refl _ _) (le_n _)))).
  - (* local *)
    inversion Htype; subst. split; [apply prot_preserved_refl|]. intros _.
    exists G, next.
    refine (conj HG (conj _ (conj (gext_refl _ _) (le_n _)))).
    apply frameP_local; auto.
    destruct Hwf as (_ & _ & _ & _ & _ & Hlen & _). exact Hlen.
  - (* assign *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    split; [apply prot_preserved_refl|]. intros _.
    exists G, next.
    refine (conj HG (conj _ (conj (gext_refl _ _) (le_n _)))).
    eapply (plcase_assign P CT Δ sΓ rΓ h G L next wf mode lc lm lk ιt ot
              Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hfl); eauto.
  - (* field write *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst.
    destruct (plcase_fldwrite P CT Δ sΓ rΓ h G L next wf mode lc lm lk ιt ot
                Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hlc Hlm Hfl _ _ _ _ _ _ _ _
                Htype Hval_x Hobj Hfield Hassign Hval_y) as [HG' Hp].
    split; [exact Hp|]. intros _. exists G, next.
    refine (conj HG' (conj _ (conj (gext_refl _ _) (le_n _)))).
    eapply frameP_ext; eauto using update_field_heap_ext, gext_refl.
  - (* new *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst.
    destruct (plcase_new P CT Δ sΓ rΓ h G L next wf mode lc lm lk ιt ot
                Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hlc Hlm Hfl
                (fun o0 n0 B0 Hb0 => proj1 (Hcb o0 n0 B0 Hb0))
                _ _ _ _ _ _ _ _ Htype Hthis Hargs Hmut HPdom)
      as (HG' & HF' & Hgx).
    split.
    { intros l qr C0 Rs vals0 f HP Hl _.
      exists vals0. split; [|reflexivity].
      rewrite runtime_getObj_last2; [eapply runtime_getObj_dom; eauto | exact Hl]. }
    intros _. eexists _, next.
    refine (conj HG' (conj HF' (conj Hgx (le_n _)))).
  - (* call *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst.
    destruct (plcase_call P CT Δ sΓ rΓ h G L next wf mode lc lm lk ιt ot
              Hcl Hrs Hcb Hwf HG HF Hfl Hthis0 Hobj0 HPdom
              _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ Htype Hval_y Hbase Hfind Hargs Hframe Heval
              (fun Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0 lk0 =>
                 IHHeval Hcl Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0 lk0))
      as [Hp Hok].
    split; [exact Hp|]. intros _. exact (Hok eq_refl _ Hretval).
  - (* call, the body ends in a null dereference *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst.
    destruct (plcase_call P CT Δ sΓ rΓ h G L next wf mode lc lm lk ιt ot
              Hcl Hrs Hcb Hwf HG HF Hfl Hthis0 Hobj0 HPdom
              _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ Htype Hval_y Hbase Hfind Hargs Hframe Heval
              (fun Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0 lk0 =>
                 IHHeval Hcl Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0 lk0))
      as [Hp _].
    split; [exact Hp | discriminate].
  - (* call, the body ends in a rejected write *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    subst.
    destruct (plcase_call P CT Δ sΓ rΓ h G L next wf mode lc lm lk ιt ot
              Hcl Hrs Hcb Hwf HG HF Hfl Hthis0 Hobj0 HPdom
              _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ Htype Hval_y Hbase Hfind Hargs Hframe Heval
              (fun Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0 lk0 =>
                 IHHeval Hcl Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0 lk0))
      as [Hp _].
    split; [exact Hp | discriminate].
  - (* cast *)
    assert (HsΓ : sΓ' = sΓ) by (inversion Htype; reflexivity). subst sΓ'.
    split; [apply prot_preserved_refl|]. intros _.
    exists G, next.
    refine (conj HG (conj _ (conj (gext_refl _ _) (le_n _)))).
    eapply (plcase_cast P CT Δ sΓ rΓ h G L next wf mode lc lm lk ιt ot
              Hrs Hcb Hwf HG HF Hthis0 Hobj0 Hfb Hfl); eauto.
  - (* sequence *)
    inversion Htype; subst.
    destruct (IHHeval1 Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf Htype1 HG HF
                Hfl HPdom) as [HP1 Hok1].
    destruct (Hok1 eq_refl) as (G1 & next1 & HG1 & HF1 & Hgx1 & Hle1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval1) as [Hd1 _].
    assert (HPdom1 : forall l, P l -> l < dom h').
    { intros l HP. specialize (HPdom l HP). lia. }
    destruct (IHHeval2 Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf1 Htype2 HG1 HF1
                Hfl HPdom1) as [HP2 Hok2].
    split.
    { exact (prot_preserved_seq _ _ _ _ _ _ HP1 HP2). }
    intros _. destruct (Hok2 eq_refl) as (G2 & next2 & HG2 & HF2 & Hgx2 & Hle2).
    exists G2, next2.
    refine (conj HG2 (conj HF2 (conj _ _))).
    + eapply gext_trans; eauto.
    + lia.
  - (* sequence, the first part ends in a null dereference *)
    inversion Htype; subst.
    destruct (IHHeval Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf Htype1 HG HF
                Hfl HPdom) as [HP1 _].
    split; [exact HP1 | discriminate].
  - (* sequence, the second part ends in a null dereference *)
    inversion Htype; subst.
    destruct (IHHeval1 Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf Htype1 HG HF
                Hfl HPdom) as [HP1 Hok1].
    destruct (Hok1 eq_refl) as (G1 & next1 & HG1 & HF1 & Hgx1 & Hle1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval1) as [Hd1 _].
    assert (HPdom1 : forall l, P l -> l < dom h').
    { intros l HP. specialize (HPdom l HP). lia. }
    split; [|discriminate].
    destruct (IHHeval2 Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf1 Htype2 HG1 HF1
                Hfl HPdom1) as [HP2 _].
    exact (prot_preserved_seq _ _ _ _ _ _ HP1 HP2).
  - (* sequence, the first part ends in a rejected write *)
    inversion Htype; subst.
    destruct (IHHeval Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf Htype1 HG HF
                Hfl HPdom) as [HP1 _].
    split; [exact HP1 | discriminate].
  - (* sequence, the second part ends in a rejected write *)
    inversion Htype; subst.
    destruct (IHHeval1 Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf Htype1 HG HF
                Hfl HPdom) as [HP1 Hok1].
    destruct (Hok1 eq_refl) as (G1 & next1 & HG1 & HF1 & Hgx1 & Hle1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval1) as [Hd1 _].
    assert (HPdom1 : forall l, P l -> l < dom h').
    { intros l HP. specialize (HPdom l HP). lia. }
    split; [|discriminate].
    destruct (IHHeval2 Hcl _ _ _ _ _ _ _ _ _ _ _ _ Hrs Hcb Hwf1 Htype2 HG1 HF1
                Hfl HPdom1) as [HP2 _].
    exact (prot_preserved_seq _ _ _ _ _ _ HP1 HP2).
Qed.

(** The form for a run that finishes normally. *)
Lemma pg_step : forall P CT,
  clean_bounds_ct CT ->
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ sΓ' G L next wf mode qthis lc lm lk,
      readonly_state_method_scope (tv_mode Δ) ->
      nomut_bounds Δ ->
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ (tv_mode Δ) s sΓ' ->
      heapP P CT h G L next ->
      frameP CT sΓ rΓ h G L next wf mode qthis lc lm lk ->
      ffit CT L Δ (act_frame qthis wf mode lc lm lk) ->
      (forall l, P l -> l < dom h) ->
      exists G' next',
        heapP P CT h' G' L next' /\
        frameP CT sΓ' rΓ' h' G' L next' wf mode qthis lc lm lk /\
        gext h G G' /\ next <= next' /\
        prot_preserved P CT (tv_mode Δ) h h'.
Proof.
  intros P CT Hcl rΓ h s res rΓ' h' Heval Hres Δ sΓ sΓ' G L next wf mode qthis
    lc lm lk Hrs Hcb Hwf Htype HG HF Hfl HPdom.
  destruct (pg_step_any P CT Hcl _ _ _ _ _ _ Heval _ _ _ _ _ _ _ _ _ _ _ _
              Hrs Hcb Hwf Htype HG HF Hfl HPdom) as [Hp Hok].
  destruct (Hok Hres) as (G' & next' & HG' & HF' & Hgx & Hle).
  exists G', next'. auto 6.
Qed.

Print Assumptions pg_step_any.
Print Assumptions pg_step.

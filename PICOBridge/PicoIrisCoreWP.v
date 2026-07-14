From iris.program_logic Require Import weakestpre lifting.
From iris.proofmode Require Import proofmode.
From Stdlib Require Import Program.Equality.

Require Import Syntax Helpers Typing Bigstep ViewpointAdaptation
  PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage.

(** * WP Lifting for the PICO Core Language *)

Section pico_core_wp.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!irisGS_gen hlc (pico_core_language CT) Σ}.

  Lemma wp_pico_core_lift_step s E Φ e :
    to_val e = None ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck then reducible e sigma else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜pico_core_step CT e sigma e' sigma'⌝ -∗
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
    pose proof
      (pico_core_prim_step_no_forks CT e sigma k e' sigma' efs Hprim)
      as ->.
    pose proof
      (pico_core_prim_step_is_core_step CT e sigma k e' sigma' [] Hprim)
      as Hcore.
    iMod ("Hstep" $! e' sigma' with "[//] Hcred") as "[$ Hwp]".
    iModIntro.
    simpl.
    iFrame.
  Qed.

  Lemma wp_pico_core_lift_step_exists s E Φ e :
    to_val e = None ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ⌜if s is NotStuck
        then exists e' sigma', pico_core_step CT e sigma e' sigma'
        else True⌝ ∗
      ▷ ∀ e' sigma',
        ⌜pico_core_step CT e sigma e' sigma'⌝ -∗
        £ 1 ={∅,E}=∗
        state_interp sigma' (S ns) ks nt ∗
        WP e' @ s; E {{ Φ }})
    ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val) "Hlift".
    iApply wp_pico_core_lift_step; [exact Hnot_val |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Hlift" with "Hstate") as "[%Hred Hstep]".
    iModIntro.
    iSplit.
    - destruct s; simpl in *; auto.
      iPureIntro.
      apply pico_core_reducible_iff_step.
      exact Hred.
    - iNext.
      iIntros (e' sigma') "Hcore Hcred".
      iApply ("Hstep" with "Hcore Hcred").
  Qed.

  Lemma wp_pico_core_lift_det_step
      s E Φ e
      (next_e : pico_core_state -> pico_core_expr)
      (next_sigma : pico_core_state -> pico_core_state) :
    to_val e = None ->
    (forall sigma,
      pico_core_step CT e sigma (next_e sigma) (next_sigma sigma)) ->
    (forall sigma e' sigma',
      pico_core_step CT e sigma e' sigma' ->
      e' = next_e sigma /\ sigma' = next_sigma sigma) ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp (next_sigma sigma) (S ns) ks nt ∗
        WP next_e sigma @ s; E {{ Φ }}))
    ⊢ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnot_val Hstep Hdet) "Hnext".
    iApply wp_pico_core_lift_step_exists; [exact Hnot_val |].
    iIntros (sigma ns k ks nt) "Hstate".
    iMod ("Hnext" with "Hstate") as "Hnext".
    iModIntro.
    iSplit.
    - destruct s; simpl; auto.
      iPureIntro.
      exists (next_e sigma), (next_sigma sigma).
      apply Hstep.
    - iNext.
      iIntros (e' sigma') "%Hcore Hcred".
      destruct (Hdet sigma e' sigma' Hcore) as [-> ->].
      iApply ("Hnext" with "Hcred").
  Qed.

  Lemma wp_pico_core_skip_done s E Φ rΓ V :
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreDone OK rΓ V @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ SSkip V [] @ s; E {{ Φ }}.
  Proof.
    iIntros "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ SSkip V [])
      (fun _ => CoreDone OK rΓ V)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      apply PCS_SkipDone.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; split; reflexivity.
  Qed.

  Lemma wp_pico_core_skip_seq s E Φ rΓ s2 V K :
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreRun rΓ s2 V K @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ SSkip V (KSeq s2 :: K) @ s; E {{ Φ }}.
  Proof.
    iIntros "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ SSkip V (KSeq s2 :: K))
      (fun _ => CoreRun rΓ s2 V K)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      apply PCS_SkipSeq.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; split; reflexivity.
  Qed.

  Lemma wp_pico_core_skip_call s E Φ callee caller x ret V K retval :
    runtime_getVal callee ret = Some retval ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreRun
          (set_vars caller (update x retval (vars caller)))
          SSkip V K @ s; E {{ Φ }}))
    ⊢ WP CoreRun callee SSkip V (KCall caller x ret :: K) @ s; E {{ Φ }}.
  Proof.
    iIntros (Hret) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun callee SSkip V (KCall caller x ret :: K))
      (fun _ =>
        CoreRun
          (set_vars caller (update x retval (vars caller)))
          SSkip V K)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_SkipCall.
      exact Hret.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; try congruence.
      replace retval0 with retval by congruence.
      split; reflexivity.
  Qed.

  Lemma wp_pico_core_local s E Φ rΓ T x V K :
    runtime_getVal rΓ x = None ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreRun
          (set_vars rΓ (vars rΓ ++ [default_value T]))
          SSkip V K @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SLocal T x) V K @ s; E {{ Φ }}.
  Proof.
    iIntros (Hnone) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SLocal T x) V K)
      (fun _ =>
        CoreRun (set_vars rΓ (vars rΓ ++ [default_value T])) SSkip V K)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_Local.
      exact Hnone.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; split; reflexivity.
  Qed.

  Lemma wp_pico_core_assign_null s E Φ rΓ x old_v V K :
    runtime_getVal rΓ x = Some old_v ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreRun
          (set_vars rΓ (update x Null_a (vars rΓ)))
          SSkip V K @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SVarAss x ENull) V K @ s; E {{ Φ }}.
  Proof.
    iIntros (Hold) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SVarAss x ENull) V K)
      (fun _ =>
        CoreRun (set_vars rΓ (update x Null_a (vars rΓ))) SSkip V K)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_AssignNull.
      exact Hold.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; try discriminate; split; reflexivity.
  Qed.

  Lemma wp_pico_core_assign_var s E Φ rΓ x y old_v val_y V K :
    runtime_getVal rΓ x = Some old_v ->
    runtime_getVal rΓ y = Some val_y ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreRun
          (set_vars rΓ (update x val_y (vars rΓ)))
          SSkip V K @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SVarAss x (EVar y)) V K @ s; E {{ Φ }}.
  Proof.
    iIntros (Hold Hy) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SVarAss x (EVar y)) V K)
      (fun _ =>
        CoreRun (set_vars rΓ (update x val_y (vars rΓ))) SSkip V K)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_AssignVar; eauto.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; try discriminate; try congruence.
      replace val_y0 with val_y by congruence.
      split; reflexivity.
  Qed.

  Lemma wp_pico_core_assign_int s E Φ rΓ x n old_v V K :
    runtime_getVal rΓ x = Some old_v ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreRun
          (set_vars rΓ (update x (Int n) (vars rΓ)))
          SSkip V K @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SVarAss x (EInt n)) V K @ s; E {{ Φ }}.
  Proof.
    iIntros (Hold) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SVarAss x (EInt n)) V K)
      (fun _ =>
        CoreRun (set_vars rΓ (update x (Int n) (vars rΓ))) SSkip V K)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_AssignInt.
      exact Hold.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; try discriminate; split; reflexivity.
  Qed.

  Lemma wp_pico_core_assign_field E Φ rΓ x y f old_v loc_y V K :
    runtime_getVal rΓ x = Some old_v ->
    runtime_getVal rΓ y = Some (Iot loc_y) ->
    (∀ h weak ns k ks nt,
      state_interp (mkPicoCoreState h weak) ns (k ++ ks) nt ={E,∅}=∗
      ▷ ∀ v V',
        ⌜wm_read weak V (loc_y, f) v V'⌝ -∗
        £ 1 ={∅,E}=∗
          state_interp (mkPicoCoreState h weak) (S ns) ks nt ∗
          WP CoreRun
            (set_vars rΓ (update x v (vars rΓ)))
            SSkip V' K @ MaybeStuck; E {{ Φ }})
    ⊢ WP CoreRun rΓ (SVarAss x (EField y f)) V K
        @ MaybeStuck; E {{ Φ }}.
  Proof.
    iIntros (Hx Hy) "Hnext".
    iApply wp_pico_core_lift_step_exists; [reflexivity |].
    iIntros ([h weak] ns k ks nt) "Hstate".
    iMod ("Hnext" $! h weak ns k ks nt with "Hstate") as "Hnext".
    iModIntro.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "%Hcore Hcred".
    assert (Hread_inv :
      exists v V',
        wm_read weak V (loc_y, f) v V' /\
        e' =
          CoreRun
            (set_vars rΓ (update x v (vars rΓ)))
            SSkip V' K /\
        sigma' = mkPicoCoreState h weak).
    {
      inversion Hcore; subst; try discriminate; try congruence.
      replace loc_y0 with loc_y by congruence.
      eexists _, _.
      repeat split; eauto.
    }
    destruct Hread_inv as (v & V' & Hread & -> & ->).
    iApply ("Hnext" $! v V' with "[] Hcred").
    iPureIntro; exact Hread.
  Qed.

  Lemma wp_pico_core_assign_field_npe s E Φ rΓ x y f old_v V K :
    runtime_getVal rΓ x = Some old_v ->
    runtime_getVal rΓ y = Some Null_a ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreDone NPE rΓ V @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SVarAss x (EField y f)) V K @ s; E {{ Φ }}.
  Proof.
    iIntros (Hx Hy) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SVarAss x (EField y f)) V K)
      (fun _ => CoreDone NPE rΓ V)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_AssignFieldNPE; eauto.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; try discriminate; try congruence.
      split; reflexivity.
  Qed.

  Lemma wp_pico_core_seq s E Φ rΓ s1 s2 V K :
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreRun rΓ s1 V (KSeq s2 :: K) @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SSeq s1 s2) V K @ s; E {{ Φ }}.
  Proof.
    iIntros "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SSeq s1 s2) V K)
      (fun _ => CoreRun rΓ s1 V (KSeq s2 :: K))
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      apply PCS_Seq.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; split; reflexivity.
  Qed.

  Lemma wp_pico_core_new E Φ rΓ x qc C args loc_this vals V K :
    runtime_getVal rΓ 0 = Some (Iot loc_this) ->
    runtime_lookup_list rΓ args = Some vals ->
    (∀ h weak ns k ks nt,
      state_interp (mkPicoCoreState h weak) ns (k ++ ks) nt ={E,∅}=∗
      ▷ ∀ qthisr qadapted o,
        ⌜r_muttype h loc_this = Some qthisr⌝ -∗
        ⌜vpa_mutability_object_creation qthisr qc = qadapted⌝ -∗
        ⌜o = mkObj (mkruntime_type qadapted C) vals⌝ -∗
        £ 1 ={∅,E}=∗
          state_interp
            (mkPicoCoreState
              (h ++ [o])
              (pico_core_alloc_weak weak o V))
            (S ns) ks nt ∗
          WP CoreRun
            (set_vars rΓ (update x (Iot (dom h)) (vars rΓ)))
            SSkip V K @ MaybeStuck; E {{ Φ }})
    ⊢ WP CoreRun rΓ (SNew x qc C args) V K @ MaybeStuck; E {{ Φ }}.
  Proof.
    iIntros (Hthis Hargs) "Hnext".
    iApply wp_pico_core_lift_step_exists; [reflexivity |].
    iIntros ([h weak] ns k ks nt) "Hstate".
    iMod ("Hnext" $! h weak ns k ks nt with "Hstate") as "Hnext".
    iModIntro.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "%Hcore Hcred".
    assert (Hnew_inv :
      exists qthisr qadapted o,
        r_muttype h loc_this = Some qthisr /\
        vpa_mutability_object_creation qthisr qc = qadapted /\
        o = mkObj (mkruntime_type qadapted C) vals /\
        e' =
          CoreRun
            (set_vars rΓ (update x (Iot (dom h)) (vars rΓ)))
            SSkip V K /\
        sigma' =
          mkPicoCoreState
            (h ++ [o])
            (pico_core_alloc_weak weak o V)).
    {
      inversion Hcore; subst; try discriminate; try congruence.
      replace vals0 with vals by congruence.
      eexists _, _, _.
      repeat split; eauto.
    }
    destruct Hnew_inv as
      (qthisr & qadapted & o & Hmut & Hadapt & Ho & -> & ->).
    iApply ("Hnext" $! qthisr qadapted o with "[] [] [] Hcred").
    - iPureIntro; exact Hmut.
    - iPureIntro; exact Hadapt.
    - iPureIntro; exact Ho.
  Qed.

  Lemma wp_pico_core_fldwrite_cases E Φ rΓ x f y loc_x val_y V K :
    runtime_getVal rΓ x = Some (Iot loc_x) ->
    runtime_getVal rΓ y = Some val_y ->
    (∀ h weak ns k ks nt,
      state_interp (mkPicoCoreState h weak) ns (k ++ ks) nt ={E,∅}=∗
      ▷
        ((∀ o a h' weak' V',
          ⌜runtime_getObj h loc_x = Some o⌝ -∗
          ⌜sf_assignability_rel CT (rctype (rt_type o)) f a⌝ -∗
          ⌜runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable⌝ -∗
          ⌜h' = update_field h loc_x f val_y⌝ -∗
          ⌜wm_write weak weak' V V' (loc_x, f) val_y⌝ -∗
          £ 1 ={∅,E}=∗
            state_interp (mkPicoCoreState h' weak') (S ns) ks nt ∗
            WP CoreRun rΓ SSkip V' K @ MaybeStuck; E {{ Φ }}) ∗
        (∀ o a,
          ⌜runtime_getObj h loc_x = Some o⌝ -∗
          ⌜sf_assignability_rel CT (rctype (rt_type o)) f a⌝ -∗
          ⌜runtime_vpa_assignability (rqtype (rt_type o)) a = Final⌝ -∗
          £ 1 ={∅,E}=∗
            state_interp (mkPicoCoreState h weak) (S ns) ks nt ∗
            WP CoreDone MUTATIONEXP rΓ V @ MaybeStuck; E {{ Φ }})))
    ⊢ WP CoreRun rΓ (SFldWrite x f y) V K
        @ MaybeStuck; E {{ Φ }}.
  Proof.
    iIntros (Hx Hy) "Hnext".
    iApply wp_pico_core_lift_step_exists; [reflexivity |].
    iIntros ([h weak] ns k ks nt) "Hstate".
    iMod ("Hnext" $! h weak ns k ks nt with "Hstate") as "Hnext".
    iModIntro.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "%Hcore Hcred".
    assert (Hwrite_cases :
      (exists o a h' weak' V',
        runtime_getObj h loc_x = Some o /\
        sf_assignability_rel CT (rctype (rt_type o)) f a /\
        runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable /\
        h' = update_field h loc_x f val_y /\
        wm_write weak weak' V V' (loc_x, f) val_y /\
        e' = CoreRun rΓ SSkip V' K /\
        sigma' = mkPicoCoreState h' weak') \/
      (exists o a,
        runtime_getObj h loc_x = Some o /\
        sf_assignability_rel CT (rctype (rt_type o)) f a /\
        runtime_vpa_assignability (rqtype (rt_type o)) a = Final /\
        e' = CoreDone MUTATIONEXP rΓ V /\
        sigma' = mkPicoCoreState h weak)).
    {
      inversion Hcore; subst; try discriminate; try congruence.
      - assert (loc_x0 = loc_x) by congruence.
        assert (val_y0 = val_y) by congruence.
        subst loc_x0 val_y0.
        left.
        eexists o, a, (update_field h loc_x f val_y), sigma'0, V'.
        split; [exact H10 |].
        split; [exact H11 |].
        split; [exact H13 |].
        split; [reflexivity |].
        split; [exact H15 |].
        split; reflexivity.
      - assert (loc_x0 = loc_x) by congruence.
        assert (val_y0 = val_y) by congruence.
        subst loc_x0 val_y0.
        right.
        eexists o, a.
        split; [exact H10 |].
        split; [exact H11 |].
        split; [exact H13 |].
        split; reflexivity.
    }
    destruct Hwrite_cases as [Hsuccess | Hmutation].
    - destruct Hsuccess as
        (o & a & h' & weak' & V' &
          Hobj & Hassign & Hvp & Hheap & Hwrite & -> & ->).
      iDestruct "Hnext" as "[Hwrite_step _]".
      iApply ("Hwrite_step" $! o a h' weak' V'
        with "[] [] [] [] [] Hcred").
      + iPureIntro; exact Hobj.
      + iPureIntro; exact Hassign.
      + iPureIntro; exact Hvp.
      + iPureIntro; exact Hheap.
      + iPureIntro; exact Hwrite.
    - destruct Hmutation as
        (o & a & Hobj & Hassign & Hvp & -> & ->).
      iDestruct "Hnext" as "[_ Hmutation_step]".
      iApply ("Hmutation_step" $! o a with "[] [] [] Hcred").
      + iPureIntro; exact Hobj.
      + iPureIntro; exact Hassign.
      + iPureIntro; exact Hvp.
  Qed.

  Lemma wp_pico_core_fldwrite_npe s E Φ rΓ x f y V K :
    runtime_getVal rΓ x = Some Null_a ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreDone NPE rΓ V @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SFldWrite x f y) V K @ s; E {{ Φ }}.
  Proof.
    iIntros (Hx) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SFldWrite x f y) V K)
      (fun _ => CoreDone NPE rΓ V)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_FldWriteNPE; eauto.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; try discriminate; try congruence.
      split; reflexivity.
  Qed.

  Lemma wp_pico_core_call E Φ rΓ x y m args loc_y vals V K :
    runtime_getVal rΓ y = Some (Iot loc_y) ->
    runtime_lookup_list rΓ args = Some vals ->
    (∀ h weak ns k ks nt,
      state_interp (mkPicoCoreState h weak) ns (k ++ ks) nt ={E,∅}=∗
      ▷ ∀ C mdef body mstmt ret,
        ⌜r_basetype h loc_y = Some C⌝ -∗
        ⌜FindMethodWithName CT C m mdef⌝ -∗
        ⌜body = mbody mdef⌝ -∗
        ⌜mstmt = mbody_stmt body⌝ -∗
        ⌜ret = mreturn body⌝ -∗
        £ 1 ={∅,E}=∗
          state_interp (mkPicoCoreState h weak) (S ns) ks nt ∗
          WP CoreRun
            (mkr_env (Iot loc_y :: vals))
            mstmt V (KCall rΓ x ret :: K)
            @ MaybeStuck; E {{ Φ }})
    ⊢ WP CoreRun rΓ (SCall x y m args) V K
        @ MaybeStuck; E {{ Φ }}.
  Proof.
    iIntros (Hy Hargs) "Hnext".
    iApply wp_pico_core_lift_step_exists; [reflexivity |].
    iIntros ([h weak] ns k ks nt) "Hstate".
    iMod ("Hnext" $! h weak ns k ks nt with "Hstate") as "Hnext".
    iModIntro.
    iSplit; [done |].
    iNext.
    iIntros (e' sigma') "%Hcore Hcred".
    assert (Hcall_inv :
      exists C mdef body mstmt ret,
        r_basetype h loc_y = Some C /\
        FindMethodWithName CT C m mdef /\
        body = mbody mdef /\
        mstmt = mbody_stmt body /\
        ret = mreturn body /\
        e' =
          CoreRun
            (mkr_env (Iot loc_y :: vals))
            mstmt V (KCall rΓ x ret :: K) /\
        sigma' = mkPicoCoreState h weak).
    {
      inversion Hcore; subst; try discriminate; try congruence.
      assert (loc_y0 = loc_y) by congruence.
      assert (vals0 = vals) by congruence.
      subst loc_y0 vals0.
      eexists C, mdef, (mbody mdef),
        (mbody_stmt (mbody mdef)), (mreturn (mbody mdef)).
      repeat split; eauto; reflexivity.
    }
    destruct Hcall_inv as
      (C & mdef & body & mstmt & ret &
        Hbase & Hfind & Hbody & Hstmt & Hret & -> & ->).
    iApply ("Hnext" $! C mdef body mstmt ret
      with "[] [] [] [] [] Hcred").
    - iPureIntro; exact Hbase.
    - iPureIntro; exact Hfind.
    - iPureIntro; exact Hbody.
    - iPureIntro; exact Hstmt.
    - iPureIntro; exact Hret.
  Qed.

  Lemma wp_pico_core_call_npe s E Φ rΓ x y m args V K :
    runtime_getVal rΓ y = Some Null_a ->
    (∀ sigma ns k ks nt,
      state_interp sigma ns (k ++ ks) nt ={E,∅}=∗
      ▷ (£ 1 ={∅,E}=∗
        state_interp sigma (S ns) ks nt ∗
        WP CoreDone NPE rΓ V @ s; E {{ Φ }}))
    ⊢ WP CoreRun rΓ (SCall x y m args) V K @ s; E {{ Φ }}.
  Proof.
    iIntros (Hy) "Hnext".
    iApply (wp_pico_core_lift_det_step
      s E Φ
      (CoreRun rΓ (SCall x y m args) V K)
      (fun _ => CoreDone NPE rΓ V)
      (fun sigma => sigma)
      with "Hnext").
    - reflexivity.
    - intros sigma.
      eapply PCS_CallNPE; eauto.
    - intros sigma e' sigma' Hstep.
      inversion Hstep; subst; try discriminate; try congruence.
      split; reflexivity.
  Qed.

End pico_core_wp.

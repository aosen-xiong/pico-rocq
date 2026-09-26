From iris.program_logic Require Import weakestpre ownp.
From iris.proofmode Require Import proofmode.

Require Import Syntax Helpers Typing Bigstep ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisTypingSupport.
Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState
  Iris.IrisSemanticBridge.

(** * PICO Iris Logical Relation: SemImm Field Operations

    This file contains the PICO-field-address adapters and operation-specific
    WP rules that thread the ghost-backed [SemImmI] predicate through weak
    cache reads and writes.  It is split from the core LR to keep proof-edit
    cycles smaller. *)

Section pico_core_semimm_operations.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!ownPGS (pico_core_language CT) Σ}.
  Context {AbsVal Obj : Type}.
  Context (P : CacheProtocol AbsVal).
  Context `{!genericCacheG P Σ}.

  (** Lift one non-value CESK control state under [MaybeStuck].  Weak reads do
      not provide a global progress witness: the memory interface supplies the
      possible read observations to the continuation instead. *)
  Lemma pico_core_ownP_wp_from_step_contI :
    forall E Phi e state,
      to_val e = None ->
      ownP state -∗
      (▷ ∀ e' state',
        ⌜pico_core_step CT e state e' state'⌝ -∗
        ownP state' ={∅, E}=∗
        WP e' @ MaybeStuck; E {{ Phi }}) -∗
      WP e @ MaybeStuck; E {{ Phi }}.
  Proof.
    intros E Phi e state Hnotval.
    iIntros "Hown Hcont".
    iApply ownP_lift_step.
    iMod (fupd_mask_subseteq ∅) as "Hclose"; [set_solver |].
    iModIntro.
    iExists state.
    iSplit.
    - iPureIntro.
      simpl.
      exact Hnotval.
    - iSplitL "Hown".
      + iNext.
        iExact "Hown".
      + iNext.
        iIntros (k e' state' efs Hprim) "Hown".
        pose proof
          (pico_core_prim_step_no_forks CT e state k e' state' efs Hprim)
          as ->.
        pose proof
          (pico_core_prim_step_is_core_step
            CT e state k e' state' [] Hprim)
          as Hstep.
        iMod ("Hcont" $! e' state' with "[] Hown") as "Hwp".
        { iPureIntro. exact Hstep. }
        iClear "Hclose".
        iModIntro.
        simpl.
        iFrame.
  Qed.

(** Adapter from concrete PICO field addresses and values to a generic cache
    protocol.  The LR keeps this explicit because the generic cache theorem is
    intentionally independent of PICO's concrete field identifiers and value
    syntax. *)
  Record PicoCoreCacheAdapter : Type := {
    pico_core_cache_field :
      FieldAddr -> option (cache_field P);
    pico_core_cache_value :
      forall k : cache_field P, Syntax.value -> option (cache_val P k)
  }.

  Definition PicoCoreCacheReadStep
      (A : PicoCoreCacheAdapter)
      (snap : CacheHistorySnapshot P)
      (addr : FieldAddr) (v : Syntax.value) : Prop :=
    exists k (cv : cache_val P k),
      pico_core_cache_field A addr = Some k /\
      pico_core_cache_value A k v = Some cv /\
      CacheReadStep P snap k cv.

  Definition PicoCoreCacheWriteStep
      (A : PicoCoreCacheAdapter)
      (a : AbsVal)
      (snap snap' : CacheHistorySnapshot P)
      (addr : FieldAddr) (v : Syntax.value) : Prop :=
    exists k (cv : cache_val P k),
      pico_core_cache_field A addr = Some k /\
      pico_core_cache_value A k v = Some cv /\
      CacheWriteStep P a snap snap' k cv.

  Lemma pico_core_cache_read_semimmI
      (A : PicoCoreCacheAdapter)
      (Stable : StableAbs Obj AbsVal)
      γ o a snap addr v :
    SemImmI P Stable γ o a snap -∗
    ⌜PicoCoreCacheReadStep A snap addr v⌝ -∗
    SemImmI P Stable γ o a snap ∗
    ∃ k (cv : cache_val P k),
      ⌜pico_core_cache_field A addr = Some k /\
        pico_core_cache_value A k v = Some cv /\
        cache_valid P a k cv /\ cache_published P k cv⌝.
  Proof.
    iIntros "Hsem %Hread".
    destruct Hread as (k & cv & Hfield & Hvalue & Hsnap).
    iPoseProof
      (cache_read_valid_wp P Stable γ o a snap k cv
        with "Hsem []") as "[Hsem %Hvalid]".
    {
      iPureIntro.
      exact Hsnap.
    }
    destruct Hvalid as [Hvalid Hpublished].
    iSplitL "Hsem".
    - iExact "Hsem".
    - iExists k, cv.
      iPureIntro.
      repeat split; assumption.
  Qed.

  Lemma pico_core_cache_write_semimmI
      (A : PicoCoreCacheAdapter)
      (Stable : StableAbs Obj AbsVal)
      γ o o' a snap snap' addr v
      (Hstable' : Stable o' a) :
    SemImmI P Stable γ o a snap -∗
    ⌜PicoCoreCacheWriteStep A a snap snap' addr v⌝ ==∗
    SemImmI P Stable γ o' a snap'.
  Proof.
    iIntros "Hsem %Hwrite".
    destruct Hwrite as (k & cv & _Hfield & _Hvalue & Hcache_write).
    iApply
      (cache_write_valid_wp P Stable γ o o' a snap snap' k cv
        Hstable' with "Hsem").
    iPureIntro.
    exact Hcache_write.
  Qed.

  Theorem wp_pico_core_assign_field_semimm_ownP
      (A : PicoCoreCacheAdapter)
      (Stable : StableAbs Obj AbsVal)
      γ o a snap
      rΓ x y f old_v loc_y h weak V K
      (E : coPset) (Φ : val (pico_core_language CT) -> iProp Σ)
      (Hx : runtime_getVal rΓ x = Some old_v)
      (Hy : runtime_getVal rΓ y = Some (Iot loc_y))
      (Hread_bridge :
        forall v V',
          wm_read weak V (loc_y, f) v V' ->
          PicoCoreCacheReadStep A snap (loc_y, f) v) :
      ownP (mkPicoCoreState h weak) -∗
      SemImmI P Stable γ o a snap -∗
      ▷ (∀ v V' k (cv : cache_val P k),
        ⌜wm_read weak V (loc_y, f) v V'⌝ -∗
        ⌜pico_core_cache_field A (loc_y, f) = Some k⌝ -∗
        ⌜pico_core_cache_value A k v = Some cv⌝ -∗
        ⌜cache_valid P a k cv⌝ -∗
        SemImmI P Stable γ o a snap -∗
        ownP (mkPicoCoreState h weak) ={∅,E}=∗
        WP CoreRun
          (set_vars rΓ (update x v (vars rΓ)))
          SSkip V' K @ MaybeStuck; E {{ Φ }}) -∗
      WP CoreRun rΓ (SVarAss x (EField y f)) V K
        @ MaybeStuck; E {{ Φ }}.
  Proof.
    iIntros "Hown Hsem Hnext".
    iApply (pico_core_ownP_wp_from_step_contI
      E
      Φ
      (CoreRun rΓ (SVarAss x (EField y f)) V K)
      (mkPicoCoreState h weak)
      with "Hown [Hsem Hnext]").
    - reflexivity.
    - iNext.
      iIntros (e' sigma') "%Hcore Hown".
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
      pose proof (Hread_bridge v V' Hread) as Hcache_read.
      iPoseProof
        (pico_core_cache_read_semimmI A Stable γ o a snap (loc_y, f) v
          with "Hsem []") as "[Hsem Hvalid]".
      {
        iPureIntro.
        exact Hcache_read.
      }
      iDestruct "Hvalid" as (k cv) "%Hvalid".
      destruct Hvalid as (Hfield & Hvalue & Hcache_valid & Hpublished).
      iApply ("Hnext" $! v V' k cv with "[] [] [] [] Hsem Hown").
      + iPureIntro.
        exact Hread.
      + iPureIntro.
        exact Hfield.
      + iPureIntro.
        exact Hvalue.
      + iPureIntro.
        exact Hcache_valid.
  Qed.

  Theorem wp_pico_core_assign_field_semimm_ownP_specI
      (A : PicoCoreCacheAdapter)
      (Stable : StableAbs Obj AbsVal)
      γ o a snap
      rΓ x y f old_v loc_y h weak V
      (Hx : runtime_getVal rΓ x = Some old_v)
      (Hy : runtime_getVal rΓ y = Some (Iot loc_y))
      (Hread_bridge :
        forall v V',
          wm_read weak V (loc_y, f) v V' ->
          PicoCoreCacheReadStep A snap (loc_y, f) v) :
    ⊢ □ ∀ (E : coPset)
          (Φ : val (pico_core_language CT) -> iProp Σ)
          (K : pico_core_cont),
      ownP (mkPicoCoreState h weak) -∗
      SemImmI P Stable γ o a snap -∗
      ▷ (∀ v V' k (cv : cache_val P k),
        ⌜wm_read weak V (loc_y, f) v V'⌝ -∗
        ⌜pico_core_cache_field A (loc_y, f) = Some k⌝ -∗
        ⌜pico_core_cache_value A k v = Some cv⌝ -∗
        ⌜cache_valid P a k cv⌝ -∗
        SemImmI P Stable γ o a snap -∗
        ownP (mkPicoCoreState h weak) ={∅,E}=∗
        WP CoreRun
          (set_vars rΓ (update x v (vars rΓ)))
          SSkip V' K @ MaybeStuck; E {{ Φ }}) -∗
      WP CoreRun rΓ (SVarAss x (EField y f)) V K
        @ MaybeStuck; E {{ Φ }}.
  Proof.
    iModIntro.
    iIntros (E Φ K) "Hown Hsem Hnext".
    iApply
      (wp_pico_core_assign_field_semimm_ownP
        A Stable γ o a snap rΓ x y f old_v loc_y h weak V K
        E Φ Hx Hy Hread_bridge
        with "Hown Hsem Hnext").
  Qed.

  Theorem wp_pico_core_fldwrite_semimm_ownP
      (A : PicoCoreCacheAdapter)
      (Stable : StableAbs Obj AbsVal)
      γ obj_sem obj_sem' a snap snap'
      rΓ x f y loc_x val_y h weak V K
      (E : coPset) (Φ : val (pico_core_language CT) -> iProp Σ)
      (Hx : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hy : runtime_getVal rΓ y = Some val_y)
      (Hstable' : Stable obj_sem' a)
      (Hwrite_bridge :
        forall weak' V',
          wm_write weak weak' V V' (loc_x, f) val_y ->
          PicoCoreCacheWriteStep A a snap snap' (loc_x, f) val_y) :
      ownP (mkPicoCoreState h weak) -∗
      SemImmI P Stable γ obj_sem a snap -∗
      ▷
        ((∀ robj assign h' weak' V',
          ⌜runtime_getObj h loc_x = Some robj⌝ -∗
          ⌜sf_assignability_rel CT (rctype (rt_type robj)) f assign⌝ -∗
          ⌜runtime_vpa_assignability
              (rqtype (rt_type robj)) assign = Assignable⌝ -∗
          ⌜h' = update_field h loc_x f val_y⌝ -∗
          ⌜wm_write weak weak' V V' (loc_x, f) val_y⌝ -∗
          SemImmI P Stable γ obj_sem' a snap' -∗
          ownP (mkPicoCoreState h' weak') ={∅,E}=∗
          WP CoreRun rΓ SSkip V' K @ MaybeStuck; E {{ Φ }}) ∗
        (∀ robj assign,
          ⌜runtime_getObj h loc_x = Some robj⌝ -∗
          ⌜sf_assignability_rel CT (rctype (rt_type robj)) f assign⌝ -∗
          ⌜runtime_vpa_assignability
              (rqtype (rt_type robj)) assign = Final⌝ -∗
          SemImmI P Stable γ obj_sem a snap -∗
          ownP (mkPicoCoreState h weak) ={∅,E}=∗
          WP CoreDone MUTATIONEXP rΓ V @ MaybeStuck; E {{ Φ }})) -∗
      WP CoreRun rΓ (SFldWrite x f y) V K
        @ MaybeStuck; E {{ Φ }}.
  Proof.
    iIntros "Hown Hsem Hnext".
    iApply (pico_core_ownP_wp_from_step_contI
      E
      Φ
      (CoreRun rΓ (SFldWrite x f y) V K)
      (mkPicoCoreState h weak)
      with "Hown [Hsem Hnext]").
    - reflexivity.
    - iNext.
      iIntros (e' sigma') "%Hcore Hown".
      assert (Hwrite_cases :
        (exists robj assign h' weak' V',
          runtime_getObj h loc_x = Some robj /\
          sf_assignability_rel CT (rctype (rt_type robj)) f assign /\
          runtime_vpa_assignability
            (rqtype (rt_type robj)) assign = Assignable /\
          h' = update_field h loc_x f val_y /\
          wm_write weak weak' V V' (loc_x, f) val_y /\
          e' = CoreRun rΓ SSkip V' K /\
          sigma' = mkPicoCoreState h' weak') \/
        (exists robj assign,
          runtime_getObj h loc_x = Some robj /\
          sf_assignability_rel CT (rctype (rt_type robj)) f assign /\
          runtime_vpa_assignability
            (rqtype (rt_type robj)) assign = Final /\
          e' = CoreDone MUTATIONEXP rΓ V /\
          sigma' = mkPicoCoreState h weak)).
      {
        inversion Hcore; subst; try discriminate; try congruence.
        - assert (loc_x0 = loc_x) by congruence.
          assert (val_y0 = val_y) by congruence.
          subst loc_x0 val_y0.
          left.
          eexists o, a0, (update_field h loc_x f val_y), sigma'0, V'.
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
          eexists o, a0.
          split; [exact H10 |].
          split; [exact H11 |].
          split; [exact H13 |].
          split; reflexivity.
      }
      destruct Hwrite_cases as [Hsuccess | Hmutation].
      + destruct Hsuccess as
          (robj & assign & h' & weak' & V' &
            Hobj & Hassign & Hvp & Hheap & Hwrite & -> & ->).
        pose proof (Hwrite_bridge weak' V' Hwrite) as Hcache_write.
        iMod
          (pico_core_cache_write_semimmI
            A Stable γ obj_sem obj_sem' a snap snap'
            (loc_x, f) val_y Hstable'
            with "Hsem []") as "Hsem".
        {
          iPureIntro.
          exact Hcache_write.
        }
        iDestruct "Hnext" as "[Hwrite_step _]".
        iApply ("Hwrite_step" $! robj assign h' weak' V'
          with "[] [] [] [] [] Hsem Hown").
        * iPureIntro.
          exact Hobj.
        * iPureIntro.
          exact Hassign.
        * iPureIntro.
          exact Hvp.
        * iPureIntro.
          exact Hheap.
        * iPureIntro.
          exact Hwrite.
      + destruct Hmutation as
          (robj & assign & Hobj & Hassign & Hvp & -> & ->).
        iDestruct "Hnext" as "[_ Hmutation_step]".
        iApply ("Hmutation_step" $! robj assign
          with "[] [] [] Hsem Hown").
        * iPureIntro.
          exact Hobj.
        * iPureIntro.
          exact Hassign.
        * iPureIntro.
          exact Hvp.
  Qed.

  Theorem wp_pico_core_fldwrite_semimm_ownP_specI
      (A : PicoCoreCacheAdapter)
      (Stable : StableAbs Obj AbsVal)
      γ obj_sem obj_sem' a snap snap'
      rΓ x f y loc_x val_y h weak V
      (Hx : runtime_getVal rΓ x = Some (Iot loc_x))
      (Hy : runtime_getVal rΓ y = Some val_y)
      (Hstable' : Stable obj_sem' a)
      (Hwrite_bridge :
        forall weak' V',
          wm_write weak weak' V V' (loc_x, f) val_y ->
          PicoCoreCacheWriteStep A a snap snap' (loc_x, f) val_y) :
    ⊢ □ ∀ (E : coPset)
          (Φ : val (pico_core_language CT) -> iProp Σ)
          (K : pico_core_cont),
      ownP (mkPicoCoreState h weak) -∗
      SemImmI P Stable γ obj_sem a snap -∗
      ▷
        ((∀ robj assign h' weak' V',
          ⌜runtime_getObj h loc_x = Some robj⌝ -∗
          ⌜sf_assignability_rel CT (rctype (rt_type robj)) f assign⌝ -∗
          ⌜runtime_vpa_assignability
              (rqtype (rt_type robj)) assign = Assignable⌝ -∗
          ⌜h' = update_field h loc_x f val_y⌝ -∗
          ⌜wm_write weak weak' V V' (loc_x, f) val_y⌝ -∗
          SemImmI P Stable γ obj_sem' a snap' -∗
          ownP (mkPicoCoreState h' weak') ={∅,E}=∗
          WP CoreRun rΓ SSkip V' K @ MaybeStuck; E {{ Φ }}) ∗
        (∀ robj assign,
          ⌜runtime_getObj h loc_x = Some robj⌝ -∗
          ⌜sf_assignability_rel CT (rctype (rt_type robj)) f assign⌝ -∗
          ⌜runtime_vpa_assignability
              (rqtype (rt_type robj)) assign = Final⌝ -∗
          SemImmI P Stable γ obj_sem a snap -∗
          ownP (mkPicoCoreState h weak) ={∅,E}=∗
          WP CoreDone MUTATIONEXP rΓ V @ MaybeStuck; E {{ Φ }})) -∗
      WP CoreRun rΓ (SFldWrite x f y) V K
        @ MaybeStuck; E {{ Φ }}.
  Proof.
    iModIntro.
    iIntros (E Φ K) "Hown Hsem Hnext".
    iApply
      (wp_pico_core_fldwrite_semimm_ownP
        A Stable γ obj_sem obj_sem' a snap snap'
        rΓ x f y loc_x val_y h weak V K
        E Φ Hx Hy Hstable' Hwrite_bridge
        with "Hown Hsem Hnext").
  Qed.
End pico_core_semimm_operations.

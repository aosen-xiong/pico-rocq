From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases GhostOverride ArgClean ArgOverride GhostCall.

(** Method calls for the label invariant over payload views.  No condition
    on allocations in the callee is needed. *)

Lemma frameP_next : forall CT sΓ rΓ h G L next next' wf mode qthis lc lm,
  frameP CT sΓ rΓ h G L next wf mode qthis lc lm -> next <= next' ->
  frameP CT sΓ rΓ h G L next' wf mode qthis lc lm.
Proof.
  intros CT sΓ rΓ h G L next next' wf mode qthis lc lm HF Hle. constructor.
  - exact (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_this _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fp_bound _ _ _ _ _ _ _ _ _ _ _ _ HF) as [H1 H2].
    split; eapply Forall_lbound_mono; eauto.
  - exact (fp_vars _ _ _ _ _ _ _ _ _ _ _ _ HF).
Qed.

Lemma lbound_lbot : forall n A, lbound n A -> lbound n (lbot A).
Proof.
  intros n [q0 l C As] H. apply lbound_node in H. destruct H as [_ HAs].
  change (lbound n (LT Bot LOut C As)).
  apply (proj2 (lbound_node _ _ _ _ _)). split; [exact I | exact HAs].
Qed.

Lemma fit3p_push : forall CT L n A B,
  fit3p CT L A B -> lbound n A -> lbound n B -> fit3p CT (n :: L) A B.
Proof.
  intros CT L n A B [H | [H | [Hi H]]] HA HB.
  - left. apply lsubtp_push; auto.
  - right. left. exact H.
  - right. right. split; auto. apply lsubtp_push; auto using lbound_lbot.
Qed.

(** Reading a class type that carries the qualifier of another type: its
    head, qualifier and label, is the head of that type's reading. *)
Lemma ldyn_headby : forall F U C args,
  ldyn F (headby U C args) = lheadby (ldyn F U) C (map (ldyn F) args).
Proof.
  intros F [q1 C1 a1 | [|qv] o n | o n C1 a1] C args; cbn [headby ldyn lheadby];
    try reflexivity;
    destruct (match tv_lookup o (lf_cargs F) (lf_margs F) n with
              | Some A => A | None => ldefault end) as [qa la Ca Aa];
    reflexivity.
Qed.

Lemma plcase_call : forall P CT Δ sΓ rΓ h G L next wf mode lc lm ι o,
  clean_bounds_ct CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  nomut_bounds Δ ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapP P CT h G L next ->
  frameP CT sΓ rΓ h G L next wf mode (rqtype (rt_type o)) lc lm ->
  ffit CT L Δ (act_frame (rqtype (rt_type o)) wf mode lc lm) ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  (forall l, P l -> l < dom h) ->
  forall x m y Us zs ly cy Dr mdr vals rΓ' rΓ'' h' retval,
    stmt_typing CT Δ sΓ (tv_mode Δ) (SCall x m y Us zs) sΓ ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m Dr mdr ->
    runtime_lookup_list rΓ zs = Some vals ->
    callee_env CT rΓ h ly Dr Us vals rΓ' ->
    eval_stmt CT rΓ' h (mbody_stmt (mbody mdr)) OK rΓ'' h' ->
    runtime_getVal rΓ'' (mreturn (mbody mdr)) = Some retval ->
    (forall Δ' sΓ0 sΓ1 G0 L0 next0 wf0 mode0 qthis0 lc0 lm0,
       readonly_state_method_scope (tv_mode Δ') ->
       nomut_bounds Δ' ->
       wf_r_config CT Δ' sΓ0 rΓ' h ->
       stmt_typing CT Δ' sΓ0 (tv_mode Δ') (mbody_stmt (mbody mdr)) sΓ1 ->
       heapP P CT h G0 L0 next0 ->
       frameP CT sΓ0 rΓ' h G0 L0 next0 wf0 mode0 qthis0 lc0 lm0 ->
       ffit CT L0 Δ' (act_frame qthis0 wf0 mode0 lc0 lm0) ->
       (forall l, P l -> l < dom h) ->
       exists G' next',
         heapP P CT h' G' L0 next' /\
         frameP CT sΓ1 rΓ'' h' G' L0 next' wf0 mode0 qthis0 lc0 lm0 /\
         gext h G0 G' /\ next0 <= next' /\
         prot_preserved P CT (tv_mode Δ') h h') ->
    exists G' next',
      heapP P CT h' G' L next' /\
      frameP CT sΓ (set_vars rΓ (update x retval (vars rΓ))) h' G' L next' wf mode
        (rqtype (rt_type o)) lc lm /\
      gext h G G' /\ next <= next' /\
      prot_preserved P CT (tv_mode Δ) h h'.
Proof.
  intros P CT Δ sΓ rΓ h G L next wf mode lc lm ι o Hcl Hrs Hcb Hwf HG HF Hfl
    Hthis Hobj HPdom x m y Us zs ly cy Dr mdr vals rΓ' rΓ'' h' retval
    Htype Hval_y Hbase Hfind Hargs Hframe Heval Hretval IH.
  set (qthis := rqtype (rt_type o)) in *.
  set (Fc := act_frame qthis wf mode lc lm).
  pose proof Hwf as (Hct & Hheap & Hrenv & _).
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι0 & o0 & Hthis0 & Hobj0 & _ & Hlc & Hlm & Hfb).
  assert (ι0 = ι) by congruence. subst ι0.
  rewrite Hobj in Hobj0. inversion Hobj0; subst o0. clear Hobj0.
  fold qthis in Hfb.
  destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
    as (ι1 & o1 & oy1 & Tx1 & _ & _ & _ & _ & _ & _ &
        _ & Hwm' & Hcfg & Hthis' & _ & Hscope').
  inversion Htype; subst.
  pose proof (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF) as HwfL.
  pose proof (hp_live _ _ _ _ _ _ HG _ HwfL) as Hwn.
  destruct (fp_bound _ _ _ _ _ _ _ _ _ _ _ _ HF) as [Hblc Hblm].
  pose proof (act_frame_bound next qthis wf mode lc lm Hwn Hblc Hblm) as HFb.
  fold Fc in HFb.
  pose proof (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hec.
  pose proof (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hem.
  (* the receiver *)
  destruct (pvar_typed CT Δ sΓ rΓ h G L next wf mode lc lm ι o Hwf HF Hthis Hobj
              _ _ _ Hget_y Hval_y) as [Hyty Hyl].
  fold qthis in Hyty. fold qthis in Hyl. fold Fc in Hyl.
  assert (Hyty' : wf_r_typable CT h ly (TClass qy C Ts) qthis (cargs rΓ) (margs rΓ))
    by (eapply wf_r_typable_ubound; eauto).
  assert (Hyl' : lhasp CT h G L ly (ldyn Fc (TClass qy C Ts))).
  { destruct (ubound_subtype CT _ _ _ Hub) as [Heq | Hsub].
    - rewrite <- Heq. exact Hyl.
    - exact (plsub P CT Δ sΓ rΓ h G L next wf mode lc lm o Hrs Hcb Hwf HG HF Hfb
               Hfl _ _ _ Hsub Hyty Hyl). }
  assert (HylD : lhasp CT h G L ly (ldyn Fc (TClass qy D Vs))).
  { exact (plsub P CT Δ sΓ rΓ h G L next wf mode lc lm o Hrs Hcb Hwf HG HF Hfb
             Hfl _ _ _ (qtype_hier CT Δ qy C Ts D Vs Hsuper) Hyty' Hyl'). }
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hyty')
    as (oy & Rs1 & Hoy & Hhead & Hsup1 & Hle1).
  pose proof HylD as (oy' & Hoy' & _ & lcD & HlD & HleD).
  rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'.
  cbn [ldyn] in HleD.
  pose proof (recv_label_cond_p P CT h G L next (tv_mode Δ) ly oy qy C Ts qthis wf
                mode lc lm _ _ HG HwfL Hrs Hoy Hyty' Hyl') as Hcond.
  fold Fc in Hcond.
  pose proof (Hheap ly (runtime_getObj_dom _ _ _ Hoy)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hoy in Hwfo. destruct Hwfo as (Hrt_oy & _).
  unfold r_basetype in Hbase. rewrite Hoy in Hbase. inversion Hbase; subst cy.
  clear Hbase.
  pose proof (hp_erase _ _ _ _ _ _ HG _ _ Hoy) as HeA.
  pose proof (hp_bound _ _ _ _ _ _ HG ly) as HbAo.
  assert (Hbc : forall w, g_col G ly = Some w -> w < next).
  { intros w Hc. destruct (hp_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & H4).
    exact H4. }
  assert (Hbcl0 : lab_bound next (olab (g_col G ly))).
  { destruct (g_col G ly) as [w0|] eqn:Hc0; simpl; auto. }
  destruct oy as [[qr Co Ro] fso].
  cbn [rt_type rqtype rctype rtargs] in *.
  destruct Hframe as (lt & qt & oy' & ca' & Hlt & Hqt & Hoy' & Hsupc & ->).
  rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'.
  cbn [rt_type rqtype rctype rtargs] in Hsupc.
  apply get_this_runtime_getVal in Hlt.
  assert (lt = ι) by congruence. subst lt.
  unfold r_muttype in Hqt. rewrite Hobj in Hqt. inversion Hqt; subst qt. clear Hqt.
  fold qthis in Hcfg, Heval, IH, Hthis'. fold qthis.
  set (margs' := map (dyn (qr2q qthis) (cargs rΓ) (margs rΓ)) Us) in *.
  set (lm' := map (ldyn Fc) Us).
  assert (Hem' : map erase lm' = margs').
  { unfold lm', margs'. rewrite map_erase_ldyn. simpl. rewrite Hec. rewrite Hem.
    reflexivity. }
  (* the receiver's class arguments at the static and the selected class *)
  destruct (super_inst_dyn _ _ _ _ _ _ _ Hsuper (qr2q qr) (qr2q qthis)
              (cargs rΓ) (margs rΓ) Rs1) as (caD & HsupX & HleX); auto.
  { intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete. }
  pose proof (rsuper_inst_trans _ _ _ _ _ _ Hsup1 _ _ HsupX) as HsupD.
  assert (HecD : map erase lcD = caD).
  { pose proof (oview_erase _ _ _ _ _ _ _ HlD) as He.
    rewrite HeA in He.
    eapply rsuper_inst_deterministic; [exact Hct | exact He | exact HsupD]. }
  destruct (oview_exists _ _ _ _ _ _ Hsupc qr (olab (g_col G ly))
              (g_args G ly) eq_refl HeA) as (lc' & Hl' & He').
  pose proof (lookup_refines _ _ _ _ _ _ Hct Hsup1 Hrt_oy _ _ _ _ _ _ _
                Hfind Hfind_m Hsupc HsupD) as (Hsc & Hhd & Hma).
  pose proof (rsuper_wf _ _ _ _ _ _ Hct Hsupc Hrt_oy) as Hview.
  unfold wf_rtypeuse in Hview. simpl in Hview.
  destruct (find_class CT Dr) as [defD|] eqn:HfD; [|contradiction].
  destruct Hview as (_ & Hlf_ca & Hb_ca).
  pose proof (rsuper_wf _ _ _ _ _ _ Hct HsupD Hrt_oy) as HviewD.
  unfold wf_rtypeuse in HviewD. simpl in HviewD.
  destruct (find_class CT D) as [defDs|] eqn:HfDs; [|contradiction].
  destruct HviewD as (_ & Hlf_caD & _).
  pose proof (find_method_wf _ _ _ _ _ Hct Hfind_m) as Hwm.
  assert (Hlm' : Forall rlost_free margs').
  { apply map_dyn_lost_free; auto using qr2q_concrete. }
  assert (Hmrefl : Forall2 rarg_sub margs' margs') by apply Forall2_rarg_sub_refl.
  assert (HbD : rbounds_ok CT (qr2q qr) caD margs' margs'
                  (mtparams (msignature mdef))).
  { unfold rbounds_ok. unfold margs' at 2.
    eapply Forall2_map_left; [exact Htargs_bnd|].
    intros U B [HlfB Hsub]. apply bound_sub_self in Hsub. simpl in HlfB, Hsub.
    pose proof (subtype_dyn _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub) as Hrs0.
    unfold member_type in Hrs0. rewrite dyn_subst in Hrs0.
    rewrite (dyn_adapt_exact (tv_mode Δ) qr qthis qy caD
               (map (dyn (qr2q qthis) (cargs rΓ) (margs rΓ)) Vs)
               margs' margs' B); auto.
    unfold margs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete. }
  destruct (Hma margs' HbD) as (Hb' & Hpar_ref & Hret_ref).
  assert (Hrs' : readonly_state_method_scope (mscope (msignature mdr))).
  { eapply readonly_state_submethod; eauto. }
  destruct (find_method_In _ _ _ _ _ Hfind) as (defD0 & HfD0 & HinD).
  pose proof (Hcl _ _ _ HfD0 HinD Hrs') as Hcb'.
  pose proof Hwm' as
    (Hrecv' & _ & _ & (sΓb & Tb & Hbody & Hnthb & Hsubb) & _ & Hroots').
  destruct (Hroots' Hrs') as [Hnm_recv Hnm_par].
  assert (Hrs_s : readonly_state_method_scope (mscope (msignature mdef))).
  { rewrite <- Hsc. exact Hrs'. }
  pose proof Hwm as (_ & _ & _ & _ & _ & Hroots).
  destruct (Hroots Hrs_s) as [_ Hnm_par_s].
  assert (HbD' : rbounds_ok CT (qr2q qr) caD (map erase lm') (map erase lm')
                   (mtparams (msignature mdef))).
  { rewrite Hem'. exact HbD. }
  assert (Hblc' : Forall (lbound next) lc').
  { unfold oview in *. eapply view_lbound; eauto. }
  assert (HblcD : Forall (lbound next) lcD).
  { unfold oview in *. eapply view_lbound; eauto. }
  assert (Hblm' : Forall (lbound next) lm').
  { apply map_ldyn_lbound. exact HFb. }
  pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) as Hext.
  (* the label side of the bounds *)
  destruct (find_method_In _ _ _ _ _ Hfind_m) as (defDs0 & HfDs0 & HinDs).
  pose proof (Hcl _ _ _ HfDs0 HinDs Hrs_s) as Hcb_s.
  assert (Hconc : lf_q Fc = Mut \/ lf_q Fc = Imm).
  { unfold Fc. simpl. destruct qthis; auto. }
  (* each method type argument fits its bound, in the caller's reading *)
  assert (HlcE : Forall rlost_free (map erase lc)) by (rewrite Hec; exact Hlc).
  assert (HlmE : Forall rlost_free (map erase lm)) by (rewrite Hem; exact Hlm).
  assert (HMVc : forall n B,
            nth_error (mtparams (msignature mdef)) n = Some B ->
            exists U, nth_error Us n = Some U /\
              lost_free (member_type (tv_mode Δ) qy Vs Us B) /\
              lsubt CT L (ldyn Fc U)
                (ldyn Fc (member_type (tv_mode Δ) qy Vs Us B)) /\
              fit3p CT L (ldyn Fc U)
                (ldyn Fc (member_type (tv_mode Δ) qy Vs Us B))).
  { intros n B HnB.
    pose proof (Forall2_nth_error_rel _ _ _ n Htargs_bnd) as Hrel.
    rewrite HnB in Hrel.
    destruct (nth_error Us n) as [U|] eqn:HU; [|contradiction].
    destruct Hrel as [HlfB HsubB].
    exists U. refine (conj eq_refl (conj HlfB (conj _ _))).
    - exact (sub_lsubt CT Δ L Fc Hrs Hconc (proj1 Hfl) _ _
               (bound_sub_self _ _ _ _ HsubB)).
    - assert (HwU : wf_stypeuse CT Δ U).
      { rewrite Forall_forall in Htargs_wf. apply Htargs_wf.
        eapply nth_error_In; eauto. }
      assert (HlU : lost_free U).
      { rewrite Forall_forall in Htargs_lf. apply Htargs_lf.
        eapply nth_error_In; eauto. }
      exact (proj1 (fit3 CT L Δ Fc Hct Hrs Hconc
                      (fun o0 n0 B0 Hb0 => proj1 (Hcb o0 n0 B0 Hb0))
                      (proj1 Hfl) (proj2 Hfl)
                      (pfcoh CT Δ L wf mode lc lm o Hcb) HlcE HlmE U _
                      (sbnd_of_wf _ _ _ _ HwU) HlU
                      (bound_sub_self _ _ _ _ HsubB))). }
  assert (HrtA : wf_rtypeuse CT (mkruntime_type qr Co (map erase (g_args G ly)))).
  { rewrite HeA. exact Hrt_oy. }
  (* everything that does not depend on which world the callee works in *)
  assert (Hgen : forall wf' m0 Lc nextc,
    List.In wf' Lc ->
    heapP P CT h G Lc nextc ->
    (m0 = true -> g_col G ly = Some wf') ->
    (qr = Mut_r ->
     norm Lc (olab (g_col G ly)) = norm Lc (if m0 then LIn wf' else LOut)) ->
    (forall l, lab_bound next l -> norm Lc l = norm L l) ->
    (forall v A, lhasp CT h G L v A -> lbound next A -> lhasp CT h G Lc v A) ->
    (forall A B, lagree L A B -> lbound next A -> lbound next B -> lagree Lc A B) ->
    (forall A B, lsubt CT L A B -> lbound next A -> lbound next B -> lsubt CT Lc A B) ->
    (forall A B, fit3p CT L A B -> lbound next A -> lbound next B -> fit3p CT Lc A B) ->
    (forall hE GE nextE, heapP P CT hE GE Lc nextE -> heapP P CT hE GE L nextE) ->
    (forall hE GE v A, lhasp CT hE GE Lc v A -> lhasp CT hE GE L v A) ->
    norm L (olab (g_col G ly)) = norm L (LIn wf') ->
    (qr = Mut_r ->
     norm L (olab (g_col G ly)) = norm L (if m0 then LIn wf' else LOut)) ->
    next <= nextc -> wf' < nextc ->
    (m0 = true -> List.In wf' L) ->
    exists G' next',
      heapP P CT h' G' L next' /\
      frameP CT sΓ (set_vars rΓ (update x retval (vars rΓ))) h' G' L next' wf mode
        qthis lc lm /\
      gext h G G' /\ next <= next' /\
      prot_preserved P CT (tv_mode Δ) h h').
  { intros wf' m0 Lc nextc W1 W2 W3 W4 W13 W5 W5' Wls Wlsp W6 W7 W8 W9 Wle Wlt Wm.
    set (Fa' := act_frame qr wf' m0 lc' lm').
    set (F1 := act_frame qr wf' m0 lcD lm').
    assert (HallC : forall K Vs0 d,
              oview CT qr (olab (g_col G ly)) Co (g_args G ly) K Vs0 ->
              find_class CT K = Some d ->
              ofacts CT Lc qr (olab (g_col G ly)) K Vs0 d).
    { intros K Vs0 d Hv Hd.
      destruct (hp_obj _ _ _ _ _ _ W2 ly _ Hoy) as (Hi0 & _ & Hf0).
      cbn [rt_type rqtype rctype] in Hi0, Hf0.
      split.
      - exact (proj1 (hinv_oview CT Lc qr _ Co _ K Vs0 Hct Hv Hi0)).
      - exact (proj1 (Hf0 K Vs0 d Hv Hd)). }
    (* a bound of the static declaration: the caller's reading of the adapted
       bound agrees into the callee-side reading *)
    assert (Hbagree : forall Lx B,
              label_cond Lx (unm (vpa_q (tv_mode Δ) qy)) F1
                (lf_with_args Fc (map (ldyn Fc) Vs) lm') ->
              Forall2 (lagree Lx) lcD (map (ldyn Fc) Vs) ->
              no_mut (method_tv_env CT D (msignature mdef)) B ->
              lost_free (member_type (tv_mode Δ) qy Vs Us B) ->
              lagree Lx (ldyn Fc (member_type (tv_mode Δ) qy Vs Us B)) (ldyn F1 B)).
    { intros Lx B Hc Hcar HnmB HlfB.
      apply lagree_sym.
      - unfold member_type, adapt. rewrite ldyn_subst. fold lm'.
        rewrite (no_mut_unm _ _ (vpa_q (tv_mode Δ) qy) HnmB).
        apply ldyn_map_qual_agree; [exact Hc | exact Hcar |].
        simpl. apply Forall2_lagree_refl.
      - rewrite erase_ldyn. simpl. rewrite Hec. rewrite Hem.
        apply dyn_lost_free; auto; try apply qr2q_concrete. }
    assert (HlcDc : Forall2 (lagree Lc) lcD (map (ldyn Fc) Vs)).
    { apply (Forall2_lagree_lift L Lc next _ _ W5' HleD HblcD).
      apply map_ldyn_lbound. exact HFb. }
    assert (Hbcl : lab_bound next (olab (g_col G ly))).
    { destruct (g_col G ly) as [w|] eqn:Hc; simpl; auto. }
    assert (HMVpre : forall n B,
              nth_error (mtparams (msignature mdef)) n = Some B ->
              lsubt CT Lc (ldyn F1 (TVar TVSub MethodVar n)) (ldyn F1 B) /\
              fit3p CT Lc (ldyn F1 (TVar TVSub MethodVar n)) (ldyn F1 B)).
    { intros n B HnB.
      destruct (HMVc n B HnB) as (U & HU & HlfB & Hs & Hsp).
      assert (HY : ldyn F1 (TVar TVSub MethodVar n) = ldyn Fc U).
      { cbn [ldyn act_frame lf_cargs lf_margs tv_lookup F1]. unfold lm'.
        rewrite nth_error_map. rewrite HU. reflexivity. }
      rewrite HY.
      assert (Hag0 : lagree Lc (ldyn Fc (member_type (tv_mode Δ) qy Vs Us B))
                       (ldyn F1 B)).
      { apply (Hbagree Lc B); auto.
        + exact (lc_call_pre L Lc next (vpa_q (tv_mode Δ) qy) qr
                   (g_col G ly) (g_col G ly) Fc wf' m0 lcD lm'
                   (map (ldyn Fc) Vs) lm' Hcond W13 Hbcl HFb W4).
        + exact (proj2 (Hcb_s MethodVar n B HnB)). }
      split.
      - eapply lsubt_agree_r; [|exact Hag0].
        apply Wls; [exact Hs | apply ldyn_lbound; exact HFb
                             | apply ldyn_lbound; exact HFb].
      - eapply fit3p_agree; [|exact Hag0].
        apply Wlsp; [exact Hsp | apply ldyn_lbound; exact HFb
                               | apply ldyn_lbound; exact HFb]. }
    assert (HMVpost : forall n B,
              nth_error (mtparams (msignature mdef)) n = Some B ->
              lsubt CT L (ldyn F1 (TVar TVSub MethodVar n)) (ldyn F1 B) /\
              fit3p CT L (ldyn F1 (TVar TVSub MethodVar n)) (ldyn F1 B)).
    { intros n B HnB.
      destruct (HMVc n B HnB) as (U & HU & HlfB & Hs & Hsp).
      assert (HY : ldyn F1 (TVar TVSub MethodVar n) = ldyn Fc U).
      { cbn [ldyn act_frame lf_cargs lf_margs tv_lookup F1]. unfold lm'.
        rewrite nth_error_map. rewrite HU. reflexivity. }
      rewrite HY.
      assert (Hag0 : lagree L (ldyn Fc (member_type (tv_mode Δ) qy Vs Us B))
                       (ldyn F1 B)).
      { apply (Hbagree L B); auto.
        + apply label_cond_unm.
          exact (lc_call_post L (vpa_q (tv_mode Δ) qy) qr (g_col G ly)
                   (g_col G ly) Fc wf' m0 lcD lm' (map (ldyn Fc) Vs) lm'
                   Hcond W8 W9).
        + exact (proj2 (Hcb_s MethodVar n B HnB)). }
      split.
      - eapply lsubt_agree_r; [exact Hs | exact Hag0].
      - eapply fit3p_agree; [exact Hsp | exact Hag0]. }
    assert (HflC : ffit CT Lc (method_tv_env CT Dr (msignature mdr)) Fa').
    { apply (act_ffit CT Lc qr (g_col G ly) wf' m0 Dr defD
               (msignature mdr) lc' lm' Hct HfD Hcb').
      - exact (HallC Dr lc' defD Hl' HfD).
      - exact W4.
      - intros n B HnB.
        pose proof (lookup_lref_boundsp CT qr (g_col G ly) wf' m0
                      Co Ro C Rs1 Hct Hcl Hsup1 Hrt_oy (g_args G ly) HeA
                      m Dr mdr D mdef ca' caD lc' lcD Hfind Hfind_m Hsupc HsupD
                      Hl' HlD Hrs' lm' Lc W4 HbD') as Hbds.
        pose proof (Forall2_nth_error_rel _ _ _ n Hbds) as Hrel.
        rewrite HnB in Hrel.
        destruct (nth_error (mtparams (msignature mdef)) n) as [Bt|] eqn:HBt;
          [|contradiction].
        destruct (HMVpre n Bt HBt) as [HM1 HM2]. split.
        + eapply lsubt_agree_r; [exact HM1 | exact Hrel].
        + eapply fit3p_agree; [exact HM2 | exact Hrel]. }
    pose proof (lookup_lref_paramsp CT qr (g_col G ly) wf' m0
                  Co Ro C Rs1 Hct Hcl Hsup1 Hrt_oy (g_args G ly) HeA
                  m Dr mdr D mdef ca' caD lc' lcD Hfind Hfind_m Hsupc HsupD
                  Hl' HlD Hrs' lm' P h G Lc nextc W2 W1 W4 HbD'
                  HallC HMVpre) as Hchain.
    rewrite Hem' in Hchain. fold Fa' in Hchain. fold F1 in Hchain.
    assert (Hctp : class_tparams CT Dr = ctparams (signature defD)).
    { unfold class_tparams. rewrite HfD. reflexivity. }
    (* the callee's activation *)
    assert (HFc : frameP CT
                    (mreceiver (msignature mdr) :: mparams (msignature mdr))
                    (mkr_env (Iot ly :: vals) ca' margs') h G Lc nextc wf' m0 qr
                    lc' lm').
    { constructor.
      - exact W1.
      - refine (ex_intro _ ly (ex_intro _ (mkObj (mkruntime_type qr Co Ro) fso)
                 (conj Hthis' (conj Hoy (conj eq_refl W3))))).
      - exact He'.
      - exact Hem'.
      - split; [exact (Forall_lbound_mono _ _ _ Wle Hblc')
               | exact (Forall_lbound_mono _ _ _ Wle Hblm')].
      - intros x0 T v HT Hv.
        unfold static_getType in HT. unfold runtime_getVal in Hv. simpl in Hv.
        destruct x0 as [|i]; simpl in HT, Hv.
        + inversion HT; subst T. inversion Hv; subst v.
          assert (Hargs_recv :
                    Forall2 (lagree Lc) lc'
                      (map (ldyn Fa') (class_var_types (length (class_tparams CT Dr))))).
          { replace (length (class_tparams CT Dr)) with (length (lf_cargs Fa')).
            2:{ rewrite Hctp. rewrite <- (Forall2_length Hb_ca).
                simpl. rewrite <- He'. rewrite length_map. reflexivity. }
            rewrite ldyn_class_var_types. apply Forall2_lagree_refl. }
          destruct Hrecv' as [[q0 Hreq] | [n0 Hreq]].
          { rewrite Hreq. rewrite Hreq in Hnm_recv.
            exists (mkObj (mkruntime_type qr Co Ro) fso). split; [exact Hoy|].
            cbn [ldyn]. split.
            * unfold headL. intros Hmh.
              assert (Hq0 : q0 <> Mut) by (inversion Hnm_recv; auto).
              assert (Hq0r : q0 = RDM /\ qr = Mut_r).
              { change (lf_q Fa') with (qr2q qr) in Hmh.
                destruct q0; simpl in Hmh; try discriminate; try congruence.
                destruct qr; simpl in Hmh; try discriminate; auto. }
              destruct Hq0r as [-> ->].
              change (lab_of Fa' RDM) with (if m0 then LIn wf' else LOut).
              apply headL_of_norm. exact (W4 eq_refl).
            * exists lc'. split; [exact Hl' | exact Hargs_recv]. }
          (* the receiver takes its qualifier from a method type variable:
             its head is the head of what the caller supplied, and the caller
             checked the receiver against it *)
          assert (Hs : recv_slot MethodVar n0 (mreceiver (msignature mdef))).
          { apply (proj2 Hhd). rewrite Hreq. left. eauto. }
          assert (HhL : match (match nth_error lm' n0 with
                               | Some A => A | None => ldefault end) with
                        | LT qh lh _ _ => headL Lc (g_col G ly) qh lh
                        end).
          { destruct (nth_error lm' n0) as [A|] eqn:HA;
              [|simpl; unfold headL; intros Hx; discriminate].
            unfold lm' in HA. rewrite nth_error_map in HA.
            destruct (nth_error Us n0) as [U|] eqn:HU; [|discriminate].
            simpl in HA. inversion HA; subst A.
            destruct Hrcv_sub as [[Hsub Hok] | (-> & Rargs & Hreqr)].
            - destruct Hs as [(C0 & a0 & E) | (C0 & a0 & E)]; rewrite E in Hsub.
              + pose proof (plsub P CT Δ sΓ rΓ h G L next wf mode lc lm o Hrs Hcb
                              Hwf HG HF Hfb Hfl _ _ _ Hsub Hyty Hyl) as Hm.
                fold qthis in Hm. fold Fc in Hm.
                unfold member_type, adapt in Hm.
                cbn [map_qual subst tv_lookup] in Hm. rewrite HU in Hm.
                apply W5 in Hm; [|apply ldyn_lbound; exact HFb].
                rewrite ldyn_headby in Hm.
                destruct (ldyn Fc U) as [qh lh Ch Ah].
                destruct Hm as (o' & _ & Hh' & _). exact Hh'.
              + exfalso.
                pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ Hfb Hsub Hyty)
                  as Hbt.
                assert (Hvb : vpa_q (tv_mode Δ) qy Bot = Bot)
                  by (destruct (tv_mode Δ), qy; reflexivity).
                unfold member_type, adapt in Hbt. cbn [map_qual subst] in Hbt.
                rewrite Hvb in Hbt.
                exact (typable_head_not_bot _ _ _ _ _ _ _ Hbt eq_refl).
            - destruct Hs as [(C0 & a0 & E) | (C0 & a0 & E)];
                rewrite E in Hreqr; discriminate. }
          rewrite Hreq.
          exists (mkObj (mkruntime_type qr Co Ro) fso). split; [exact Hoy|].
          try unfold Fa'. cbn [ldyn act_frame lf_cargs lf_margs tv_lookup].
          destruct (match nth_error lm' n0 with
                    | Some A => A | None => ldefault end) as [qh lh Ch Ah].
          cbn [lheadby]. split; [exact HhL|].
          exists lc'. split; [exact Hl' | exact Hargs_recv].
        + pose proof (Forall2_nth_error_rel _ _ _ i Hchain) as Hrel.
          rewrite HT in Hrel.
          destruct (nth_error (mparams (msignature mdef)) i) as [Ps|] eqn:HPs;
            [|contradiction].
          destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hargs Hv)
            as (yi & A & HyA & Hyv & HnA).
          pose proof (Forall2_nth_error_rel _ _ _ i Harg_sub) as Hrel2.
          rewrite HnA in Hrel2. rewrite HPs in Hrel2. destruct Hrel2 as [Hsub Hok].
          destruct (pvar_typed CT Δ sΓ rΓ h G L next wf mode lc lm ι o Hwf HF
                      Hthis Hobj _ _ _ HyA Hyv) as [Hty Hlv].
          fold qthis in Hty. fold qthis in Hlv. fold Fc in Hlv.
          pose proof (plsub P CT Δ sΓ rΓ h G L next wf mode lc lm o Hrs Hcb Hwf HG HF
                        Hfb Hfl _ _ _ Hsub Hty Hlv) as Hmv.
          fold qthis in Hmv. fold Fc in Hmv.
          pose proof (assignable_to_member _ _ _ (Iot v) _ _ _ _ _ _ _ _ _
                        qr caD margs' Hfb Hlc Hlm (conj Hsub Hok) Hty Hhead HleX
                        Hmrefl) as Hlt_v.
          assert (HnmT : no_mut (method_tv_env CT Dr (msignature mdr)) T).
          { rewrite Forall_forall in Hnm_par. apply Hnm_par.
            eapply nth_error_In; eauto. }
          assert (HnmPs : no_mut (method_tv_env CT D (msignature mdef)) Ps).
          { rewrite Forall_forall in Hnm_par_s. apply Hnm_par_s.
            eapply nth_error_In; eauto. }
          rewrite <- (no_mut_fT _ _ HnmT).
          apply Hrel; [exact Hlt_v|].
          rewrite (no_mut_fT _ _ HnmPs).
          eapply lhasp_agree;
            [apply W5; [exact Hmv | apply ldyn_lbound; exact HFb]|].
          apply lagree_sym.
          * unfold member_type, adapt. rewrite ldyn_subst. fold lm'.
            assert (Hmq : map_qual (vpa_q (tv_mode Δ) qy) Ps =
                          map_qual (fun q0 => match q0 with
                                              | Mut => Lost
                                              | _ => vpa_q (tv_mode Δ) qy q0
                                              end) Ps).
            { apply (no_mut_map_qual_eq _ _ _ _ HnmPs).
              intros q0 Hq0. destruct q0; congruence. }
            rewrite Hmq.
            apply ldyn_map_qual_agree.
            -- apply (lc_call_pre L Lc next (vpa_q (tv_mode Δ) qy) qr
                        (g_col G ly) (g_col G ly) Fc wf' m0 lcD lm'
                        (map (ldyn Fc) Vs) lm' Hcond W13).
               ++ destruct (g_col G ly) as [w|] eqn:Hc; simpl; auto.
               ++ exact HFb.
               ++ exact W4.
            -- simpl. apply (Forall2_lagree_lift L Lc next _ _ W5' HleD HblcD).
               apply map_ldyn_lbound. exact HFb.
            -- simpl. apply Forall2_lagree_refl.
          * rewrite erase_ldyn. simpl. rewrite Hec. rewrite Hem.
            destruct Hok as [Hlf | (C' & Ts' & ->)].
            -- apply dyn_lost_free; auto; try apply qr2q_concrete.
            -- exfalso. eapply (typable_head_not_bot _ _ _ _ _ _ _ Hty).
               reflexivity. }
    destruct (IH (method_tv_env CT Dr (msignature mdr)) _ sΓb G Lc nextc wf' m0
                qr lc' lm' Hrs' Hcb' Hcfg Hbody W2 HFc HflC HPdom)
      as (GE & nextE & HGE & HFE & HgE & HleE & Hprot).
    pose proof (W6 _ _ _ HGE) as HGL.
    exists GE, nextE.
    refine (conj HGL (conj _ (conj HgE (conj _ _)))).
    - eapply frameP_update; [| exact Hnot_rcv | exact Hget_x |].
      + apply (frameP_next CT sΓ rΓ h' GE L next nextE wf mode qthis lc lm);
          [|lia].
        exact (frameP_ext CT sΓ rΓ h h' G GE L next wf mode qthis lc lm
                 HF Hext HgE).
      + intros rv ->.
        pose proof (preservation_pico _ _ _ _ _ _ _ Heval eq_refl _ _ _ _
                      Hcfg Hbody) as Hcfg''.
        destruct (wf_r_config_this _ _ _ _ _ Hcfg'')
          as (ι2 & o2 & Hth2 & Hobj2 & _ & _ & _ & Hfb2).
        pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hcfg'' Hth2 Hobj2 Hnthb)
          as Hrty.
        rewrite Hretval in Hrty.
        destruct (eval_stmt_frame _ _ _ _ _ _ Heval _ _ _ _ Hbody)
          as (Hth_eq & Hca_eq & Hma_eq).
        destruct (heap_ext_getObj _ _ _ _ Hext Hoy) as (oye & Hoye & Hrte).
        assert (ι2 = ly).
        { rewrite Hth_eq in Hth2. rewrite Hthis' in Hth2. congruence. }
        subst ι2.
        rewrite Hoye in Hobj2. inversion Hobj2; subst o2.
        rewrite Hrte in Hrty. rewrite Hrte in Hfb2.
        rewrite Hca_eq in Hrty. rewrite Hma_eq in Hrty.
        rewrite Hca_eq in Hfb2. rewrite Hma_eq in Hfb2.
        cbn [rt_type rqtype cargs margs] in Hrty, Hfb2.
        pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ Hfb2 Hsubb Hrty)
          as Hrty'.
        pose proof (fp_vars _ _ _ _ _ _ _ _ _ _ _ _ HFE _ _ _ Hnthb Hretval)
          as Hrl.
        fold Fa' in Hrl.
        pose proof (hexp_of_live _ _ _ _ _ _ _ _ _ _ _ W1 Hrl) as Hex0.
        destruct (lhasp_subtype_ex P CT (method_tv_env CT Dr (msignature mdr)) h' GE
                    Lc nextE (mscope (msignature mdr)) qr wf' m0 lc' lm' ca'
                    margs' Hct HGE (fun _ => W1) Hrs' eq_refl
                    (vbp_of_fits CT _ h' GE Lc Fa' _ _ qr Hct
                       (hp_cls _ _ _ _ _ _ HGE)
                       (fun v0 ob d0 Hob0 Hd0 =>
                          proj1 (proj2 (proj2 (proj1
                            (hp_obj _ _ _ _ _ _ HGE v0 ob Hob0))) d0 Hd0))
                       (proj2 HflC)
                       eq_refl He' Hem')
                    (fun o0 n0 B0 Hb0 => nomut_bounds_head _ o0 n0 B0 Hcb' Hb0)
                    Hfb2 He' Hem'
                    _ _ Hsubb rv Hrty Hex0 Hrl) as [Hrl' Hex'].
        fold Fa' in Hrl'.
        pose proof (W7 _ _ _ _ Hrl') as HrlL.
        destruct (heap_ext_getObj _ _ _ _ Hext Hoy) as (oye2 & Hoye2 & Hrte2).
        assert (HallL : forall K Vs0 d,
                  oview CT qr (olab (g_col G ly)) Co (g_args G ly) K Vs0 ->
                  find_class CT K = Some d ->
                  ofacts CT L qr (olab (g_col G ly)) K Vs0 d).
        { intros K Vs0 d Hv Hd.
          destruct (HgE ly (runtime_getObj_dom _ _ _ Hoy)) as (Hc1 & Hc2 & Hc3).
          destruct (hp_obj _ _ _ _ _ _ HGL ly oye2 Hoye2) as (Hi0 & _ & Hf0).
          rewrite Hrte2 in Hi0, Hf0. cbn [rt_type rqtype rctype] in Hi0, Hf0.
          rewrite Hc1 in Hi0, Hf0. rewrite Hc3 in Hi0, Hf0.
          split.
          - exact (proj1 (hinv_oview CT L qr _ Co _ K Vs0 Hct Hv Hi0)).
          - exact (proj1 (Hf0 K Vs0 d Hv Hd)). }
        assert (Hrty2 : loc_has_rtype CT h' rv
                  (dyn (qr2q qr) ca' (map erase lm') (mret (msignature mdr)))).
        { rewrite Hem'. exact Hrty'. }
        destruct (lookup_lref_resultp CT qr (g_col G ly) wf' m0
                    Co Ro C Rs1 Hct Hcl Hsup1 Hrt_oy (g_args G ly) HeA
                    m Dr mdr D mdef ca' caD lc' lcD Hfind Hfind_m Hsupc HsupD
                    Hl' HlD Hrs' lm' P h' GE L nextE HGL Wm W8 W9
                    (fun d Hd Hq => W8)
                    HbD' HallL HMVpost rv Hrty2 Hex' HrlL)
          as [HtopL _].
        fold F1 in HtopL.
        assert (Hmem : lhasp CT h' GE L rv
                  (ldyn Fc (member_type (tv_mode Δ) qy Vs Us
                              (mret (msignature mdef))))).
        { eapply lhasp_agree; [exact HtopL|].
          unfold member_type, adapt. rewrite ldyn_subst. fold lm'.
          apply ldyn_map_qual_agree.
          - exact (lc_call_post L (vpa_q (tv_mode Δ) qy) qr (g_col G ly)
                     (g_col G ly) Fc wf' m0 lcD lm' (map (ldyn Fc) Vs) lm'
                     Hcond W8 W9).
          - simpl. exact HleD.
          - simpl. apply Forall2_lagree_refl. }
        apply (lhasp_subtype P CT Δ h' GE L nextE (tv_mode Δ) qthis wf mode lc lm
                 (cargs rΓ) (margs rΓ) Hct HGL HwfL Hrs eq_refl
                 (vbp_of_fits CT Δ h' GE L Fc _ _ qthis Hct
                    (hp_cls _ _ _ _ _ _ HGL)
                    (fun v0 ob d0 Hob0 Hd0 =>
                       proj1 (proj2 (proj2 (proj1
                         (hp_obj _ _ _ _ _ _ HGL v0 ob Hob0))) d0 Hd0))
                    (proj2 Hfl)
                    eq_refl Hec Hem)
                 (fun o0 n0 B0 Hb0 => nomut_bounds_head Δ o0 n0 B0 Hcb Hb0)
                 Hfb Hec Hem
                 _ _ Hret_sub rv); [|exact Hmem].
        unfold wf_r_typable in *. apply Hret_ref in Hrty'.
        unfold member_type. rewrite dyn_subst.
        eapply loc_has_rtype_adapt; eauto.
    - lia.
    - intros l qr0 C0 Rs0 vals0 f HP Hl Hp0. eapply Hprot; eauto.
      destruct Hp0 as [Hp | [Hp | Hstrict]]; [left; auto | right; left; auto |].
      right. right. eapply concrete_assignability_submethod; eauto. }
  (* which world the callee works in *)
  assert (Hnn : ~ List.In next L).
  { intros Hin. pose proof (hp_live _ _ _ _ _ _ HG _ Hin). lia. }
  assert (Hfresh : (forall w, g_col G ly = Some w -> ~ List.In w L) ->
    exists G' next',
      heapP P CT h' G' L next' /\
      frameP CT sΓ (set_vars rΓ (update x retval (vars rΓ))) h' G' L next' wf mode
        qthis lc lm /\
      gext h G G' /\ next <= next' /\
      prot_preserved P CT (tv_mode Δ) h h').
  { intros Hdead.
    assert (Hcd : norm L (olab (g_col G ly)) = None).
    { destruct (g_col G ly) as [w|] eqn:Hc; simpl; auto.
      apply norm_dead. exact (Hdead w eq_refl). }
    apply (Hgen next false (next :: L) (S next)).
    - left. reflexivity.
    - apply heapP_push. exact HG.
    - discriminate.
    - intros _. rewrite (norm_push L next _ Hbcl0). exact Hcd.
    - intros l Hl. apply norm_push. exact Hl.
    - intros v A H Hb. exact (lhasp_push_heap P CT h G L next v A HG H Hb).
    - intros A B H HA HB. exact (lagree_push L next A B H HA HB).
    - intros A B H HA HB. exact (lsubt_push CT L next A B H HA HB).
    - intros A B H HA HB. exact (fit3p_push CT L next A B H HA HB).
    - intros hE GE nextE H. eapply heapP_pop; eauto.
    - intros hE GE v A H. eapply lhasp_pop; eauto.
    - rewrite Hcd. rewrite (norm_dead _ _ Hnn). reflexivity.
    - intros _. exact Hcd.
    - lia.
    - lia.
    - discriminate. }
  destruct (g_col G ly) as [w|] eqn:Hcw.
  - destruct (in_dec Nat.eq_dec w L) as [Hin | Hnin].
    + (* the receiver is in a live world *)
      destruct (hp_col _ _ _ _ _ _ HG _ _ Hcw) as (_ & _ & _ & Hwlt).
      apply (Hgen w true L next); auto.
    + apply Hfresh. intros w0 Hw0. inversion Hw0; subst. exact Hnin.
  - apply Hfresh. intros w0 Hw0. discriminate.
Qed.

Print Assumptions plcase_call.

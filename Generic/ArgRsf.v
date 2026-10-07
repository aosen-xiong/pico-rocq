From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases GhostOverride ArgClean ArgOverride GhostCall ArgCall GhostEntry ArgMain
  ArgEntry.

(** The starting-state hypothesis in the payload reading is kept by every
    well-typed execution. *)

(* ------------------COHERENCE FOLLOWS FROM THE FITS------------------*)

(** What is used of a bound written mutable: its own arguments are fully
    known and satisfy its class's bounds. *)
Definition mbounds (CT : class_table) (Δ : tv_env) : Prop :=
  forall o n K Bs, tv_bound Δ o n = Some (TClass Mut K Bs) ->
    Forall lost_free Bs /\
    exists Δ0,
      readonly_state_method_scope (tv_mode Δ0) /\
      (forall o' n' B', tv_bound Δ0 o' n' = Some B' ->
         tv_bound Δ o' n' = Some B') /\
      forall def, find_class CT K = Some def ->
        Forall2
          (fun T B =>
             lost_free (subst Bs [] (adapt AbstractState Mut B)) ->
             bound_sub CT Δ0 T (subst Bs [] (adapt AbstractState Mut B)))
          Bs (ctparams (signature def)).

(** An argument that fits a bound written mutable is coherent from the
    bound's class up, because the reading of the bound is. *)
Lemma fcoh_of_fits : forall CT L Δ F,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  (lf_q F = Mut \/ lf_q F = Imm) ->
  frame_fits CT L Δ F -> frame_fitsp CT L Δ F ->
  Forall rlost_free (map erase (lf_cargs F)) ->
  Forall rlost_free (map erase (lf_margs F)) ->
  mbounds CT Δ ->
  fcoh CT L Δ F.
Proof.
  intros CT L Δ F Hwf Hrs Hconc Hfits Hfitp Hlc Hlm Hmb o n K Bs Hb Hnd Hsn.
  destruct (Hmb o n K Bs Hb) as [HlfB (Δ0 & Hrs0 & Hsub0 & Hbs)].
  destruct (Hfitp o n _ Hb) as [Hf | [Hd | [Hi _]]]; try contradiction.
  pose proof Hf as Hf0.
  destruct (ldyn F (TVar TVSub o n)) as [qx lx Cx Asx].
  simpl. intros -> Va Hva.
  cbn [ldyn] in Hf.
  destruct Hf as [(Hx & _) | (Hrq & Hl & Vs & Hv & Hle)]; [discriminate|].
  assert (Va = Vs).
  { unfold tview in *. eapply view_deterministic; eauto. }
  subst Va.
  assert (Hl' : norm L lx = norm L (lf_mut F)) by (apply Hl; reflexivity).
  apply (pcoh_lm _ _ _ _ _ _ (lf_mut F)); [symmetry; exact Hl'|].
  destruct (find_class CT K) as [def|] eqn:Hfind.
  - assert (Hni : class_qualifier (signature def) <> Imm_c).
    { intros Hi. apply Hsn. simpl. split; auto.
      exact (view_imm _ _ _ _ _ _ _ _ _ Hwf Hv def Hfind Hi). }
    assert (Hlv : livec CT K).
    { destruct (livec_dec CT K) as [Hx | Hx]; auto. exfalso.
      apply (lsubtp_dead CT L _ _ Hwf Hf0); auto.
      cbn [ldyn]. simpl. intros (Hy & _). contradiction. }
    assert (HlfA : Forall (fun B => lost_free (subst Bs [] (adapt AbstractState Mut B)))
                     (ctparams (signature def))).
    { eapply Forall_impl; [|exact (Hlv def Hfind)]. intros B HB. unfold adapt.
      apply lost_free_inst; auto. intros q1 Hq1. destruct q1; simpl; congruence. }
    destruct (static_mut_pcoh CT L Δ0 F K Bs def Hwf Hrs0 Hconc
                (fun o' n' B' Hb' => Hfits o' n' B' (Hsub0 o' n' B' Hb'))
                Hlc Hlm Hfind
                Hni (Hbs def eq_refl) HlfB HlfA) as (_ & _ & Hp).
    exact (pcoh_agree CT L lx (lf_mut F) K Vs _ (lf_mut F) Hwf Hl' Hle Hp).
  - intros C' As' Hv'. unfold tview in Hv'.
    inversion Hv'; subst.
    + unfold pclassf. rewrite Hfind. exact I.
    + unfold parent_lookup in Hparent. rewrite Hfind in Hparent. discriminate.
Qed.

Print Assumptions fcoh_of_fits.

(* ------------------THE HEAP PART------------------*)

(** Every object's arguments fit its class's bounds in the payload reading,
    with every label outside, and its class can have objects. *)
Definition rsfitp_heap0 (CT : class_table) (h : heap) : Prop :=
  forall l o def,
    runtime_getObj h l = Some o ->
    find_class CT (rctype (rt_type o)) = Some def ->
    (forall L, frame_fitsp CT L (class_env def)
       (hfr CT (rqtype (rt_type o)) LOut (rctype (rt_type o))
          (map lift (rtargs (rt_type o))))) /\
    livec CT (rctype (rt_type o)).

Lemma class_mbounds : forall CT C def,
  wf_class_table CT -> find_class CT C = Some def -> livec CT C ->
  mbounds CT (with_mode (class_env def) ReadonlyState).
Proof.
  intros CT C def Hct Hfind Hlv o n K Bs Hb.
  destruct (tv_bound_class_env def o n _ Hb) as [-> Hnb].
  pose proof (class_bounds_wf _ _ _ Hct Hfind) as Hwfb.
  rewrite Forall_forall in Hwfb.
  pose proof (Hwfb _ (nth_error_In _ _ Hnb)) as HwB.
  pose proof (Hlv def Hfind) as Hlf. rewrite Forall_forall in Hlf.
  pose proof (Hlf _ (nth_error_In _ _ Hnb)) as HlB.
  apply lost_free_class in HlB. destruct HlB as [_ HlBs].
  split; [exact HlBs|].
  exists (with_mode (class_env def) ReadonlyState).
  refine (conj (or_introl eq_refl) (conj (fun _ _ _ H => H) _)).
  intros dK HdK.
  inversion HwB as [? ? ? ? dK' HfK' Hhead Hlen Hargs Hbounds| |]; subst.
  rewrite HdK in HfK'. inversion HfK'; subst dK'.
  eapply Forall2_impl; [|exact Hbounds]. intros a b Hab _. exact Hab.
Qed.

(** The per-object invariant of the starting heap. *)
Lemma obP_ofL : forall CT h,
  wf_class_table CT -> wf_heap CT h ->
  rsfit_heap CT h -> rsfitp_heap0 CT h ->
  forall L l o, runtime_getObj h l = Some o ->
    obP CT L (rqtype (rt_type o)) None (rctype (rt_type o))
      (map lift (rtargs (rt_type o))) /\
    livec CT (rctype (rt_type o)).
Proof.
  intros CT h Hct Hheap Hh Hp L l o Ho.
  pose proof (Hheap l (runtime_getObj_dom _ _ _ Ho)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Ho in Hwfo. destruct Hwfo as (Hrt & _).
  unfold wf_rtypeuse in Hrt.
  destruct (find_class CT (rctype (rt_type o))) as [def|] eqn:Hfind;
    [|contradiction].
  destruct Hrt as (Hag & Hlf & Hb).
  destruct (Hp l o def Ho Hfind) as [Hfp Hlv].
  assert (Hi : hinv CT L (rqtype (rt_type o)) LOut (rctype (rt_type o))
                 (map lift (rtargs (rt_type o)))).
  { refine (conj _ (conj _ _)).
    - intros d Hd. rewrite hfr_lift.
      exact (rsfit_heap_obj CT h l o d Hh Ho Hd L).
    - rewrite map_erase_lift. exact Hlf.
    - intros d Hd. rewrite Hfind in Hd. inversion Hd; subst d.
      split; [exact Hag|]. intros _. rewrite hfr_lift. reflexivity. }
  split; [|exact Hlv].
  refine (conj Hi (conj _ _)).
  - intros w Hc. discriminate.
  - intros D Vs dd Hv Hfd.
    apply (fitsp_oview CT L _ _ _ _ D Vs Hct Hv Hi); [|exact Hfd].
    intros d Hd. rewrite Hfind in Hd. inversion Hd; subst d.
    split; [exact (Hfp L)|].
    apply (fcoh_of_fits CT L (with_mode (class_env def) ReadonlyState)
             (hfr CT (rqtype (rt_type o)) LOut (rctype (rt_type o))
                (map lift (rtargs (rt_type o)))) Hct (or_introl eq_refl)).
    + unfold hfr. simpl. destruct (rqtype (rt_type o)); auto.
    + intros o0 n0 B0 Hb0. exact (proj1 Hi def Hfind o0 n0 B0 Hb0).
    + intros o0 n0 B0 Hb0. exact (Hfp L o0 n0 B0 Hb0).
    + unfold hfr. simpl. rewrite map_erase_lift. exact Hlf.
    + unfold hfr. simpl. constructor.
    + eapply class_mbounds; eauto.
Qed.

Lemma obP_of : forall CT h,
  wf_class_table CT -> wf_heap CT h ->
  rsfit_heap CT h -> rsfitp_heap0 CT h ->
  rsfitp_heap CT h.
Proof. intros CT h Hct Hheap Hh Hp l o Ho. eapply obP_ofL; eauto. Qed.

Print Assumptions obP_of.

(* ------------------ALLOCATION------------------*)

(** What is used of the bounds in scope. *)
Definition sbounds (CT : class_table) (Δ : tv_env) : Prop :=
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) /\
  mbounds CT (with_mode Δ ReadonlyState).

Lemma LF_fcoh : forall CT L Δ q0 ca ma,
  wf_class_table CT ->
  (forall L0, frame_fits CT L0 Δ (LF q0 ca ma)) ->
  (forall L0, frame_fitsp CT L0 Δ (LF q0 ca ma)) ->
  Forall rlost_free ca -> Forall rlost_free ma ->
  sbounds CT Δ ->
  fcoh CT L (with_mode Δ ReadonlyState) (LF q0 ca ma).
Proof.
  intros CT L Δ q0 ca ma Hct Hf Hfp Hlc Hlm [_ Hmb].
  apply (fcoh_of_fits CT L (with_mode Δ ReadonlyState) (LF q0 ca ma) Hct
           (or_introl eq_refl)).
  - simpl. destruct q0; auto.
  - intros o n B Hb. exact (Hf L o n B Hb).
  - intros o n B Hb. exact (Hfp L o n B Hb).
  - simpl. rewrite map_erase_lift. exact Hlc.
  - simpl. rewrite map_erase_lift. exact Hlm.
  - exact Hmb.
Qed.

Lemma dyn_creation_ctx : forall qthis qc Rs T,
  dyn (qr2q qthis) Rs [] (adapt AbstractState (qc2q qc) T) =
  dyn (qr2q (vpa_mutability_object_creation qthis qc)) Rs []
    (adapt AbstractState (qc2q qc) T).
Proof.
  intros qthis qc Rs T. unfold adapt.
  transitivity (dyn (qr2q (vpa_mutability_object_creation qthis qc)) Rs [] T).
  - apply dyn_map_qual_eq. intros q0. destruct qthis, qc, q0; reflexivity.
  - symmetry. apply dyn_map_qual_eq.
    intros q0. destruct qthis, qc, q0; reflexivity.
Qed.

(** Allocation keeps the heap part. *)
Lemma rsfp_new : forall CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals,
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ' ->
  runtime_getVal rΓ 0 = Some (Iot l1) ->
  r_muttype h l1 = Some qthisr ->
  RSF CT Δ rΓ h -> rsfitp_heap0 CT h -> rsfitp_frame CT Δ rΓ h ->
  sbounds CT Δ ->
  rsfitp_heap0 CT
    (h ++ [mkObj
             (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ)) Ts))
             vals]).
Proof.
  intros CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals
    Hwf Htype Hthis0 Hmut [Hh Hfr] Hp Hfrp Hsb.
  inversion Htype; subst.
  pose proof Hwf as (Hct & _).
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & Hmut' & Hlc & Hlm & Hfb).
  apply get_this_runtime_getVal in Hthis0.
  assert (l1 = ι) by congruence. subst l1.
  assert (qthisr = rqtype (rt_type o)) by congruence. subst qthisr.
  set (qthis := rqtype (rt_type o)) in *.
  set (qo := vpa_mutability_object_creation qthis qc) in *.
  set (Rs := map (dyn (qr2q qthis) (cargs rΓ) (margs rΓ)) Ts) in *.
  set (Fc := LF qthis (cargs rΓ) (margs rΓ)).
  intros l o0 def0 Ho Hfc.
  destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
  2:{ assert (Hl : l < dom h).
      { apply runtime_getObj_dom in Ho. rewrite length_app in Ho. simpl in Ho. lia. }
      rewrite runtime_getObj_last2 in Ho; auto.
      exact (Hp l o0 def0 Ho Hfc). }
  rewrite runtime_getObj_last in Ho. inversion Ho; subst o0.
  cbn [rt_type rqtype rctype rtargs] in *.
  rewrite Hfind in Hfc. inversion Hfc; subst def0.
  assert (Hlvc : Forall lost_free (ctparams (signature def))).
  { assert (Hgen : forall Xs Bs,
              Forall2
                (fun T B =>
                   lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
                   bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
                Xs Bs -> Forall lost_free Bs).
    { intros Xs Bs HF2. induction HF2 as [|T B Xs Bs [Hlf _] _ IH];
        constructor; auto.
      apply (lost_free_inst_inv (vpa_q AbstractState (qc2q qc)) Ts [] B);
        [destruct qc; reflexivity | exact Hlf]. }
    exact (Hgen _ _ Hbounds). }
  split.
  2:{ intros d Hd. rewrite Hfind in Hd. inversion Hd; subst d. exact Hlvc. }
  intros L.
  assert (Hconc : lf_q Fc = Mut \/ lf_q Fc = Imm).
  { unfold Fc. simpl. destruct qthis; auto. }
  assert (Hfits : frame_fits CT L (with_mode Δ ReadonlyState) Fc).
  { intros o1 n1 B1 Hb1. exact (Hfr ι o Hthis Hobj L o1 n1 B1 Hb1). }
  assert (Hfitp : frame_fitsp CT L (with_mode Δ ReadonlyState) Fc).
  { intros o1 n1 B1 Hb1. exact (Hfrp ι o Hthis Hobj L o1 n1 B1 Hb1). }
  assert (Hcoh : fcoh CT L (with_mode Δ ReadonlyState) Fc).
  { apply LF_fcoh; auto.
    - intros L0. exact (Hfr ι o Hthis Hobj L0).
    - intros L0. exact (Hfrp ι o Hthis Hobj L0). }
  assert (HlcE : Forall rlost_free (map erase (lf_cargs Fc))).
  { unfold Fc. simpl. rewrite map_erase_lift. exact Hlc. }
  assert (HlmE : Forall rlost_free (map erase (lf_margs Fc))).
  { unfold Fc. simpl. rewrite map_erase_lift. exact Hlm. }
  assert (HsbT : Forall (sbnd CT Δ) Ts).
  { inversion Hwf_new as [? ? ? ? def' Hfind' Hhead' Hlen' Hargs' Hbnd'| |].
    eapply Forall_impl; [|exact Hargs']. intros a Ha.
    exact (sbnd_of_wf _ _ _ _ Ha). }
  assert (HAs : map lift Rs = map (ldyn Fc) Ts).
  { unfold Rs, Fc. rewrite map_map. apply map_ext. intros T.
    symmetry. apply ldyn_lift_LF. }
  assert (Heq : forall B,
            ldyn Fc (member_type AbstractState (qc2q qc) Ts [] B) =
            ldyn (mk_lframe (qr2q qo) LOut LOut (map lift Rs) [])
              (map_qual (vpa_q AbstractState (qc2q qc)) B)).
  { intros B.
    change (mk_lframe (qr2q qo) LOut LOut (map lift Rs) [])
      with (obj_frame qo None None (map lift Rs)).
    rewrite ldyn_lift_obj. unfold Fc. rewrite ldyn_lift_LF. f_equal.
    unfold member_type. rewrite dyn_subst. simpl map. fold Rs.
    apply dyn_creation_ctx. }
  refine (proj1 (pfit_of_fits CT L qo qc LOut LOut C def (map lift Rs) Hct Hfind
                   _ (fun _ => eq_refl) _)).
  { unfold qo. destruct qthis, qc; reflexivity. }
  rewrite HAs.
  assert (Hgen : forall Xs Bs,
            Forall (sbnd CT Δ) Xs -> Forall lost_free Xs ->
            Forall2
              (fun T B =>
                 lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
                 bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
              Xs Bs ->
            Forall2
              (fun A B =>
                 (lsubt CT L A
                    (ldyn (mk_lframe (qr2q qo) LOut LOut (map (ldyn Fc) Ts) [])
                       (map_qual (vpa_q AbstractState (qc2q qc)) B)) /\
                  rlost_free (erase
                    (ldyn (mk_lframe (qr2q qo) LOut LOut (map (ldyn Fc) Ts) [])
                       (map_qual (vpa_q AbstractState (qc2q qc)) B)))) /\
                 fit3p CT L A
                   (ldyn (mk_lframe (qr2q qo) LOut LOut (map (ldyn Fc) Ts) [])
                      (map_qual (vpa_q AbstractState (qc2q qc)) B)) /\
                 (forall q0 K Xs', B = TClass q0 K Xs' -> q0 = Mut ->
                    ~ deadA CT A -> ~ insaneA CT A -> scoh CT L A K))
              (map (ldyn Fc) Xs) Bs).
  { intros Xs Bs HsbX HlfX HF. revert HsbX HlfX.
    induction HF as [|T B Xs Bs [Hlfb Hbs] HF IH]; intros HsbX HlfX; simpl;
      constructor.
    2:{ apply IH; [exact (Forall_inv_tail HsbX) | exact (Forall_inv_tail HlfX)]. }
    pose proof (Forall_inv HsbX) as HsbT0. pose proof (Forall_inv HlfX) as HlfT0.
    rewrite <- HAs. rewrite <- (Heq B).
    pose proof (sub_lsubt CT (with_mode Δ ReadonlyState) L Fc
                  (or_introl eq_refl) Hconc Hfits _ _ (Hbs ReadonlyState)) as Hs.
    destruct (fit3 CT L (with_mode Δ ReadonlyState) Fc Hct (or_introl eq_refl)
                Hconc (fun o1 n1 B1 Hb1 => proj1 Hsb o1 n1 B1 Hb1)
                Hfits Hfitp Hcoh HlcE HlmE T
                (member_type AbstractState (qc2q qc) Ts [] B)
                (sbnd_mode _ _ _ _ HsbT0) HlfT0 (Hbs ReadonlyState))
      as [H3 Hc3].
    refine (conj (conj Hs _) (conj H3 _)).
    - rewrite erase_ldyn. unfold Fc. simpl. rewrite !map_erase_lift.
      apply dyn_lost_free; auto using qr2q_concrete.
    - intros q0 K Xs' -> -> Hnd Hsn.
      eapply Hc3; [| | exact Hnd | exact Hsn].
      + unfold member_type, adapt. cbn [map_qual subst]. reflexivity.
      + destruct qc; reflexivity. }
  exact (Hgen _ _ HsbT Hlost_free Hbounds).
Qed.

Print Assumptions rsfp_new.

(* ------------------THE BOUNDS IN SCOPE OF A CALLEE------------------*)

Lemma lost_free_of_dyn : forall qctx ca ma T,
  rlost_free (dyn qctx ca ma T) -> lost_free T.
Proof.
  intros qctx ca ma T. induction T using qualified_type_ind'; intros Hl.
  - cbn [dyn] in Hl. apply rlost_free_class in Hl. destruct Hl as [Hq Hargs].
    apply (lost_free_class qual C args). split.
    + intros ->. apply Hq. destruct qctx; reflexivity.
    + clear Hq. induction H as [|t r Ht _ IH]; constructor;
        simpl in Hargs; inversion Hargs; subst; auto.
  - destruct u as [|q0]; simpl; auto.
    intros ->. cbn [dyn] in Hl.
    destruct (match tv_lookup o ca ma n with Some R => R | None => default_rtype end)
      as [q1 C1 args1].
    replace (dynq qctx Lost) with Lost in Hl by (destruct qctx; reflexivity).
    simpl in Hl. destruct Hl as [Hx _]. congruence.
  - cbn [dyn] in Hl. apply rlost_free_class in Hl. destruct Hl as [_ Hargs].
    apply lost_free_head.
    induction H as [|t r Ht _ IH]; constructor;
      simpl in Hargs; inversion Hargs; subst; auto.
Qed.

Lemma rsuper_live : forall CT qh C Rs D Vs,
  wf_class_table CT -> rsuper_inst CT qh C Rs D Vs -> livec CT C -> livec CT D.
Proof.
  intros CT qh C Rs D Vs Hct H. induction H; intros Hlv; auto.
  apply IHrsuper_inst. eapply live_parent; eauto.
Qed.

Lemma sbounds_callee : forall CT D' defD mdef',
  wf_class_table CT ->
  find_class CT D' = Some defD ->
  livec CT D' ->
  wf_method CT D' mdef' ->
  Forall lost_free (mtparams (msignature mdef')) ->
  sbounds CT (method_tv_env CT D' (msignature mdef')).
Proof.
  intros CT D' defD mdef' Hct Hfind Hlv Hwm Hlfm.
  pose proof Hwm as (_ & Hmb & _).
  assert (Hcv : forall n B,
            tv_bound (method_tv_env CT D' (msignature mdef')) ClassVar n = Some B ->
            nth_error (ctparams (signature defD)) n = Some B).
  { intros n B Hb. unfold tv_bound, method_tv_env, class_tparams in Hb.
    simpl in Hb. rewrite Hfind in Hb. exact Hb. }
  split.
  - intros o n B Hb. destruct o.
    + pose proof (class_bounds_class _ _ _ Hct Hfind) as Hall.
      rewrite Forall_forall in Hall. apply Hall.
      eapply nth_error_In. exact (Hcv n B Hb).
    + rewrite Forall_forall in Hmb.
      exact (proj1 (Hmb B (nth_error_In _ _ Hb))).
  - intros o n K Bs Hb. destruct o.
    + pose proof (Hcv n _ Hb) as HbC.
      destruct (class_mbounds CT D' defD Hct Hfind Hlv ClassVar n K Bs HbC)
        as [Hl (Δ0 & Hrs0 & Hsub0 & Hbs)].
      split; [exact Hl|]. exists Δ0. refine (conj Hrs0 (conj _ Hbs)).
      intros o' n' B' Hb'. apply Hsub0 in Hb'.
      destruct (tv_bound_class_env defD o' n' B' Hb') as [-> Hnb].
      unfold tv_bound, with_mode, method_tv_env, class_tparams. simpl.
      rewrite Hfind. exact Hnb.
    + assert (HbM : nth_error (mtparams (msignature mdef')) n =
                    Some (TClass Mut K Bs)) by exact Hb.
      rewrite Forall_forall in Hlfm.
      pose proof (Hlfm _ (nth_error_In _ _ HbM)) as HlB.
      apply lost_free_class in HlB. destruct HlB as [_ HlBs].
      split; [exact HlBs|].
      exists (with_mode (method_tv_env CT D' (msignature mdef')) ReadonlyState).
      refine (conj (or_introl eq_refl) (conj (fun _ _ _ H => H) _)).
      intros dK HdK.
      rewrite Forall_forall in Hmb.
      destruct (Hmb _ (nth_error_In _ _ HbM)) as [_ HwB].
      inversion HwB as [? ? ? ? dK' HfK' Hhead Hlen Hargs Hbounds| |]; subst.
      rewrite HdK in HfK'. inversion HfK'; subst dK'.
      eapply Forall2_impl; [|exact Hbounds].
      intros a b Hab Hl m0. exact (Hab m0).
Qed.

(* ------------------CALLS------------------*)

(** At a call, the callee's activation fits its bounds in the payload
    reading. *)
Lemma rsfp_call : forall CT Δ sΓ rΓ h mt x m y Us zs sΓ' ly cy D' mdef' vals rΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCall x m y Us zs) sΓ' ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D' mdef' ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D' Us vals rΓ' ->
  RSF CT Δ rΓ h -> rsfitp_heap0 CT h -> rsfitp_frame CT Δ rΓ h ->
  sbounds CT Δ ->
  rsfitp_frame CT (method_tv_env CT D' (msignature mdef')) rΓ' h.
Proof.
  intros CT Δ sΓ rΓ h mt x m y Us zs sΓ' ly cy D' mdef' vals rΓ'
    Hwf Htype Hvy Hbase Hfind Hvals Henv [Hh Hfr] Hp Hfrp Hsb.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & Hlc & Hlm & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
  rewrite Hvy in Hyty.
  pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ Hfb Hub Hyty) as Hyty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hyty')
    as (oy & Rs1 & Hoy & Hhead & Hsup1 & Hle1).
  pose proof (Hheap ly (runtime_getObj_dom _ _ _ Hoy)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hoy in Hwfo. destruct Hwfo as (Hrt_oy & _).
  unfold r_basetype in Hbase. rewrite Hoy in Hbase. inversion Hbase; subst cy.
  clear Hbase.
  destruct oy as [[qr Co Ro] fso]. simpl in *.
  destruct Henv as (lt & qt & oy' & ca' & Hlt & Hqt & Hoy' & Hsupc & ->).
  rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'. simpl in Hsupc.
  apply get_this_runtime_getVal in Hlt.
  assert (lt = ι) by congruence. subst lt.
  unfold r_muttype in Hqt. rewrite Hobj in Hqt. inversion Hqt; subst qt. clear Hqt.
  set (qctx := rqtype (rt_type o)) in *.
  set (margs' := map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ)) Us) in *.
  destruct (super_inst_dyn _ _ _ _ _ _ _ Hsuper (qr2q qr) (qr2q qctx)
              (cargs rΓ) (margs rΓ) Rs1) as (caD & HsupX & HleX); auto.
  { intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete. }
  pose proof (rsuper_inst_trans _ _ _ _ _ _ Hsup1 _ _ HsupX) as HsupD.
  pose proof (rsuper_wf _ _ _ _ _ _ Hct Hsupc Hrt_oy) as Hview.
  unfold wf_rtypeuse in Hview. simpl in Hview.
  destruct (find_class CT D') as [defD|] eqn:HfD; [|contradiction].
  assert (Hlm' : Forall rlost_free margs').
  { apply map_dyn_lost_free; auto using qr2q_concrete. }
  assert (Hmrefl : Forall2 rarg_sub margs' margs') by apply Forall2_rarg_sub_refl.
  assert (HbD : rbounds_ok CT (qr2q qr) caD margs' margs'
                  (mtparams (msignature mdef))).
  { unfold rbounds_ok. unfold margs' at 2.
    eapply Forall2_map_left; [exact Htargs_bnd|].
    intros U B0 [HlfB Hsub]. apply bound_sub_self in Hsub. simpl in HlfB, Hsub.
    pose proof (subtype_dyn _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub) as Hrs0.
    unfold member_type in Hrs0. rewrite dyn_subst in Hrs0.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ)) Vs)
               margs' margs' B0); auto.
    unfold margs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete. }
  assert (Hconc : lf_q (LF qctx (cargs rΓ) (margs rΓ)) = Mut \/
                  lf_q (LF qctx (cargs rΓ) (margs rΓ)) = Imm).
  { simpl. destruct qctx; auto. }
  intros ι' o' Hth' Ho' L. simpl in Hth'. inversion Hth'; subst ι'.
  rewrite Hoy in Ho'. inversion Ho'; subst o'. simpl.
  intros oo n B Hb.
  rewrite ldyn_lift_LF. rewrite ldyn_lift_LF.
  destruct oo.
  - (* a class type parameter: from the receiver object *)
    assert (HbC : nth_error (ctparams (signature defD)) n = Some B).
    { unfold tv_bound, method_tv_env, class_tparams in Hb. simpl in Hb.
      rewrite HfD in Hb. exact Hb. }
    pose proof (oview_lift CT qr Co Ro D' ca' Hsupc) as Hls.
    destruct (obP_ofL CT h Hct Hheap Hh Hp L ly _ Hoy) as [(_ & _ & Hf3) _].
    cbn [rt_type rqtype rctype rtargs] in Hf3.
    pose proof (proj1 (Hf3 D' (map lift ca') defD Hls HfD) ClassVar n B HbC) as Hs.
    rewrite hfr_lift in Hs.
    rewrite ldyn_lift_obj in Hs. rewrite ldyn_lift_obj in Hs.
    pose proof (class_bounds_wf _ _ _ Hct HfD) as Hwfb.
    rewrite Forall_forall in Hwfb.
    pose proof (Hwfb _ (nth_error_In _ _ HbC)) as HwB.
    rewrite (dyn_no_method_vars _ _ _ _ HwB eq_refl (qr2q qr) ca' margs').
    exact Hs.
  - (* a method type parameter: from the caller's check *)
    assert (HbM : nth_error (mtparams (msignature mdef')) n = Some B) by exact Hb.
    pose proof (lookup_bounds_eq CT qr Co Ro C Rs1 Hct Hsup1 Hrt_oy _ _ _ _ _ _ _
                  margs' Hfind Hfind_m Hsupc HsupD HbD) as Heq.
    pose proof (f_equal (fun l => nth_error l n) Heq) as HnE. simpl in HnE.
    rewrite nth_error_map in HnE. rewrite nth_error_map in HnE.
    rewrite HbM in HnE.
    destruct (nth_error (mtparams (msignature mdef)) n) as [Bs|] eqn:HBs;
      simpl in HnE; [|discriminate].
    inversion HnE as [HdynEq]. rewrite HdynEq.
    pose proof (Forall2_nth_error_rel _ _ _ n Htargs_bnd) as Hrel.
    rewrite HBs in Hrel.
    destruct (nth_error Us n) as [U|] eqn:HU; [|contradiction].
    destruct Hrel as [HlfB HsubB].
    assert (HY : dyn (qr2q qr) ca' margs' (TVar TVSub MethodVar n) =
                 dyn (qr2q qctx) (cargs rΓ) (margs rΓ) U).
    { cbn [dyn tv_lookup]. unfold margs'. rewrite nth_error_map. rewrite HU.
      reflexivity. }
    rewrite HY.
    assert (HwU : wf_stypeuse CT Δ U).
    { rewrite Forall_forall in Htargs_wf. apply Htargs_wf.
      eapply nth_error_In; eauto. }
    assert (HlU : lost_free U).
    { rewrite Forall_forall in Htargs_lf. apply Htargs_lf.
      eapply nth_error_In; eauto. }
    pose proof (proj1 (fit3 CT L (with_mode Δ ReadonlyState)
                  (LF qctx (cargs rΓ) (margs rΓ)) Hct (or_introl eq_refl) Hconc
                  (fun o0 n0 B0 Hb0 => proj1 Hsb o0 n0 B0 Hb0)
                  (fun o0 n0 B0 Hb0 => Hfr ι o Hthis Hobj L o0 n0 B0 Hb0)
                  (fun o0 n0 B0 Hb0 => Hfrp ι o Hthis Hobj L o0 n0 B0 Hb0)
                  (LF_fcoh CT L Δ qctx (cargs rΓ) (margs rΓ) Hct
                     (Hfr ι o Hthis Hobj) (Hfrp ι o Hthis Hobj) Hlc Hlm Hsb)
                  ltac:(simpl; rewrite map_erase_lift; exact Hlc)
                  ltac:(simpl; rewrite map_erase_lift; exact Hlm)
                  U _ (sbnd_mode _ _ _ _ (sbnd_of_wf _ _ _ _ HwU)) HlU
                  (HsubB ReadonlyState))) as Hs.
    rewrite ldyn_lift_LF in Hs. rewrite ldyn_lift_LF in Hs.
    unfold member_type in Hs. rewrite dyn_subst in Hs. fold margs' in Hs.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ)) Vs)
               margs' margs' Bs); auto.
    unfold margs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete.
Qed.

Print Assumptions rsfp_call.

Lemma rsfp_call_sb : forall CT Δ sΓ rΓ h mt x m y Us zs sΓ' ly cy D' mdef' vals rΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCall x m y Us zs) sΓ' ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D' mdef' ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D' Us vals rΓ' ->
  RSF CT Δ rΓ h -> rsfitp_heap0 CT h -> rsfitp_frame CT Δ rΓ h ->
  sbounds CT Δ ->
  sbounds CT (method_tv_env CT D' (msignature mdef')).
Proof.
  intros CT Δ sΓ rΓ h mt x m y Us zs sΓ' ly cy D' mdef' vals rΓ'
    Hwf Htype Hvy Hbase Hfind Hvals Henv [Hh Hfr] Hp Hfrp Hsb.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & Hlc & Hlm & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
  rewrite Hvy in Hyty.
  pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ Hfb Hub Hyty) as Hyty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hyty')
    as (oy & Rs1 & Hoy & Hhead & Hsup1 & Hle1).
  pose proof (Hheap ly (runtime_getObj_dom _ _ _ Hoy)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hoy in Hwfo. destruct Hwfo as (Hrt_oy & _).
  unfold r_basetype in Hbase. rewrite Hoy in Hbase. inversion Hbase; subst cy.
  clear Hbase.
  destruct oy as [[qr Co Ro] fso]. simpl in *.
  destruct Henv as (lt & qt & oy' & ca' & Hlt & Hqt & Hoy' & Hsupc & ->).
  rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'. simpl in Hsupc.
  apply get_this_runtime_getVal in Hlt.
  assert (lt = ι) by congruence. subst lt.
  unfold r_muttype in Hqt. rewrite Hobj in Hqt. inversion Hqt; subst qt. clear Hqt.
  set (qctx := rqtype (rt_type o)) in *.
  set (margs' := map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ)) Us) in *.
  destruct (super_inst_dyn _ _ _ _ _ _ _ Hsuper (qr2q qr) (qr2q qctx)
              (cargs rΓ) (margs rΓ) Rs1) as (caD & HsupX & HleX); auto.
  { intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete. }
  pose proof (rsuper_inst_trans _ _ _ _ _ _ Hsup1 _ _ HsupX) as HsupD.
  pose proof (rsuper_wf _ _ _ _ _ _ Hct Hsupc Hrt_oy) as Hview.
  unfold wf_rtypeuse in Hview. simpl in Hview.
  destruct (find_class CT D') as [defD|] eqn:HfD; [|contradiction].
  assert (Hlm' : Forall rlost_free margs').
  { apply map_dyn_lost_free; auto using qr2q_concrete. }
  assert (Hmrefl : Forall2 rarg_sub margs' margs') by apply Forall2_rarg_sub_refl.
  assert (HbD : rbounds_ok CT (qr2q qr) caD margs' margs'
                  (mtparams (msignature mdef))).
  { unfold rbounds_ok. unfold margs' at 2.
    eapply Forall2_map_left; [exact Htargs_bnd|].
    intros U B0 [HlfB Hsub]. apply bound_sub_self in Hsub. simpl in HlfB, Hsub.
    pose proof (subtype_dyn _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub) as Hrs0.
    unfold member_type in Hrs0. rewrite dyn_subst in Hrs0.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ)) Vs)
               margs' margs' B0); auto.
    unfold margs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete. }
  assert (Hconc : lf_q (LF qctx (cargs rΓ) (margs rΓ)) = Mut \/
                  lf_q (LF qctx (cargs rΓ) (margs rΓ)) = Imm).
  { simpl. destruct qctx; auto. }
  apply (sbounds_callee CT D' defD mdef' Hct HfD).
  - apply (rsuper_live CT _ Co Ro D' ca' Hct Hsupc).
    pose proof Hrt_oy as Hrt0. unfold wf_rtypeuse in Hrt0. simpl in Hrt0.
    destruct (find_class CT Co) as [dCo|] eqn:HfCo; [|contradiction].
    exact (proj2 (Hp ly _ dCo Hoy HfCo)).
  - exact (find_method_wf _ _ _ _ _ Hct Hfind).
  - apply Forall_forall. intros B HB.
    apply In_nth_error in HB. destruct HB as [n HbM].
    pose proof (lookup_bounds_eq CT qr Co Ro C Rs1 Hct Hsup1 Hrt_oy _ _ _ _ _ _ _
                  margs' Hfind Hfind_m Hsupc HsupD HbD) as Heq.
    pose proof (f_equal (fun l => nth_error l n) Heq) as HnE. simpl in HnE.
    rewrite nth_error_map in HnE. rewrite nth_error_map in HnE.
    rewrite HbM in HnE.
    destruct (nth_error (mtparams (msignature mdef)) n) as [Bs|] eqn:HBs;
      simpl in HnE; [|discriminate].
    inversion HnE as [HdynEq].
    pose proof (Forall2_nth_error_rel _ _ _ n Htargs_bnd) as Hrel.
    rewrite HBs in Hrel.
    destruct (nth_error Us n) as [U|] eqn:HU; [|contradiction].
    destruct Hrel as [HlfB HsubB].
    apply (lost_free_of_dyn (qr2q qr) ca' margs'). rewrite HdynEq.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ)) Vs)
               margs' margs' Bs); auto;
      unfold margs'; rewrite <- dyn_subst;
      apply dyn_lost_free; auto using qr2q_concrete.
Qed.

Print Assumptions rsfp_call_sb.

(* ------------------THE INVARIANT------------------*)

(** The starting-state condition: the bounds are satisfied in the protected
    reading, in the earlier form and in the payload form, and the bounds in
    scope are well formed. *)
Definition RSFp (CT : class_table) (Δ : tv_env) (rΓ : r_env) (h : heap) : Prop :=
  RSF CT Δ rΓ h /\ rsfitp_heap0 CT h /\ rsfitp_frame CT Δ rΓ h /\ sbounds CT Δ.

Lemma rsfitp_heap0_update : forall CT h lx ox f0 vy,
  rsfitp_heap0 CT h -> runtime_getObj h lx = Some ox ->
  rsfitp_heap0 CT (update_field h lx f0 vy).
Proof.
  intros CT h lx ox f0 vy Hp Hox l o def Ho Hfc.
  destruct (Nat.eq_dec lx l) as [-> | Hne].
  - rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
    inversion Ho; subst o. simpl in *. exact (Hp l ox def Hox Hfc).
  - rewrite update_field_getObj_diff in Ho; auto. exact (Hp l o def Ho Hfc).
Qed.

Lemma rsfitp_frame_step : forall CT Δ sΓ mt s sΓ' rΓ h rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_stmt CT rΓ h s OK rΓ' h' ->
  rsfitp_frame CT Δ rΓ h -> rsfitp_frame CT Δ rΓ' h'.
Proof.
  intros CT Δ sΓ mt s sΓ' rΓ h rΓ' h' Hwf Htype Heval Hfr ι o' Hth Ho' L.
  destruct (eval_stmt_frame _ _ _ _ _ _ Heval _ _ _ _ Htype) as (Hte & Hce & Hme).
  destruct (wf_r_config_this _ _ _ _ _ Hwf) as (ι0 & o & Hthis & Hobj & _).
  assert (ι = ι0) by congruence. subst ι0.
  destruct (heap_ext_getObj _ _ _ _ (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) Hobj)
    as (o2 & Ho2 & Hrt).
  rewrite Ho' in Ho2. inversion Ho2; subst o2.
  rewrite Hrt. rewrite Hce. rewrite Hme. exact (Hfr ι o Hthis Hobj L).
Qed.

(** Every well-typed statement, in any mode, keeps the heap part. *)
Lemma rsfitp_heap0_preservation : forall CT,
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ',
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      RSFp CT Δ rΓ h ->
      rsfitp_heap0 CT h'.
Proof.
  intros CT rΓ h s res rΓ' h' Heval.
  induction Heval; intros Hres Δ sΓ mt0 sΓ' Hwf Htype HR; try discriminate;
    try exact (proj1 (proj2 HR)).
  - (* field write *)
    subst. exact (rsfitp_heap0_update CT h _ _ _ _ (proj1 (proj2 HR)) Hobj).
  - (* new *)
    subst. destruct HR as (H1 & H2 & H3 & H4). eapply rsfp_new; eauto.
  - (* call *)
    subst.
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ & _ & Hwm & Hcfg & _).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _).
    destruct HR as (H1 & H2 & H3 & H4).
    eapply (IHHeval eq_refl _ _ _ _ Hcfg Hbody).
    refine (conj (conj (proj1 H1) _) (conj H2 (conj _ _))).
    + exact (rsf_call CT Δ sΓ rΓ h mt0 x m y Us zs sΓ' ly cy D mdef vals rΓ'
               Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1).
    + exact (rsfp_call CT Δ sΓ rΓ h mt0 x m y Us zs sΓ' ly cy D mdef vals rΓ'
               Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
    + exact (rsfp_call_sb CT Δ sΓ rΓ h mt0 x m y Us zs sΓ' ly cy D mdef vals rΓ'
               Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
  - (* sequence *)
    inversion Htype; subst.
    pose proof (IHHeval1 eq_refl _ _ _ _ Hwf Htype1 HR) as Hh1.
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    destruct HR as (H1 & H2 & H3 & H4).
    eapply (IHHeval2 eq_refl _ _ _ _ Hwf1 Htype2).
    refine (conj _ (conj Hh1 (conj _ H4))).
    + exact (rsf_preservation CT Δ sΓ mt0 s1 _ rΓ h rΓ' h' Hwf Htype1 Heval1 H1).
    + exact (rsfitp_frame_step CT Δ sΓ mt0 s1 _ rΓ h rΓ' h' Hwf Htype1 Heval1 H3).
Qed.

(** THE STARTING-STATE CONDITION IS KEPT BY EVERY WELL-TYPED EXECUTION. *)
Theorem rsfp_preservation : forall CT Δ sΓ mt s sΓ' rΓ h rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_stmt CT rΓ h s OK rΓ' h' ->
  RSFp CT Δ rΓ h -> RSFp CT Δ rΓ' h'.
Proof.
  intros CT Δ sΓ mt s sΓ' rΓ h rΓ' h' Hwf Htype Heval HR.
  pose proof HR as (H1 & H2 & H3 & H4).
  refine (conj _ (conj _ (conj _ H4))).
  - eapply rsf_preservation; eauto.
  - eapply rsfitp_heap0_preservation; eauto.
  - eapply rsfitp_frame_step; eauto.
Qed.

(** A state with no type variable in scope whose objects are of classes
    without type parameters satisfies the condition as soon as it satisfies
    the earlier form. *)
Lemma RSFp_start : forall CT Δ rΓ h,
  RSF CT Δ rΓ h ->
  class_bounds Δ = [] -> method_bounds Δ = [] ->
  (forall l o def, runtime_getObj h l = Some o ->
     find_class CT (rctype (rt_type o)) = Some def ->
     ctparams (signature def) = []) ->
  RSFp CT Δ rΓ h.
Proof.
  intros CT Δ rΓ h HR Hc Hm Hobj.
  assert (Hnb : forall o n B, tv_bound Δ o n = Some B -> False).
  { intros o n B Hb. unfold tv_bound in Hb.
    destruct o; simpl in Hb; [rewrite Hc in Hb | rewrite Hm in Hb];
      destruct n; discriminate. }
  refine (conj HR (conj _ (conj _ (conj _ _)))).
  - intros l o def Ho Hfc. pose proof (Hobj l o def Ho Hfc) as Hp. split.
    + intros L o' n B Hb. destruct (tv_bound_class_env _ _ _ _ Hb) as [_ Hn].
      rewrite Hp in Hn. destruct n; discriminate.
    + intros d Hd. rewrite Hfc in Hd. inversion Hd; subst d. rewrite Hp.
      constructor.
  - intros ι o _ _ L o' n B Hb. exfalso. exact (Hnb o' n B Hb).
  - intros o n B Hb. exfalso. exact (Hnb o n B Hb).
  - intros o n K Bs Hb. exfalso. exact (Hnb o n _ Hb).
Qed.

(* ------------------THE THEOREMS------------------*)

(** A call that selects a readonly-state or transitive-state method leaves
    the protected fields of every object of the entry heap unchanged.  There
    is no condition on what protected code allocates.  The entry state
    satisfies [RSFp], which every well-typed execution keeps. *)
Theorem rs_ts_call_preservation_final :
  forall CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      prot_cond CT C f (mscope (msignature mdef)) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef
    Hcl Hwf (H1 & H2 & H3 & H4) Htype Heval Hvy Hbase Hfind Hrs.
  pose proof Hwf as (Hct & Hheap & _).
  eapply (rs_ts_call_preservation_payload CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h'
            ly cy D mdef Hcl Hwf H1); eauto.
  - exact (obP_of CT h Hct Hheap (proj1 H1) H2).
  - intros vals0 rΓc Hargs Hframe.
    exact (rsfp_call CT Δ sΓ rΓ h mt x m y Us zs sΓ' ly cy D mdef vals0 rΓc
             Hwf Htype Hvy Hbase Hfind Hargs Hframe H1 H2 H3 H4).
Qed.

Corollary readonly_state_preservation_final :
  forall CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    readonly_state_method_scope (mscope (msignature mdef)) ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros. eapply rs_ts_call_preservation_final; eauto.
  unfold prot_cond. tauto.
Qed.

Corollary transitive_state_preservation_final :
  forall CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us zs) OK rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    mscope (msignature mdef) = TransitiveState ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros until mdef. intros Hcc Hwf HR Htype Heval Hvy Hbase Hfind Hts.
  intros. eapply rs_ts_call_preservation_final; eauto.
  - rewrite Hts. right. reflexivity.
  - rewrite Hts. right. right. right. reflexivity.
Qed.

Print Assumptions rsfp_preservation.
Print Assumptions readonly_state_preservation_final.
Print Assumptions transitive_state_preservation_final.

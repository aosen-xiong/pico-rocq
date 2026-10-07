From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant.

(** The statement cases of the label invariant over payload views. *)

(* ------------------FIELD DECLARATIONS------------------*)

Lemma fdecl_collect : forall CT C f D fd,
  fdecl CT C f D fd ->
  exists fs, CollectFields CT C fs /\ f < length fs.
Proof.
  intros CT C f D fd H. destruct H.
  - exists (map (subst_field Ss) pfs ++ Syntax.fields (body def)). split.
    + eapply CF_Inherit; eauto.
    + rewrite length_app. rewrite length_map.
      assert (f - length pfs < length (Syntax.fields (body def))).
      { apply nth_error_Some. congruence. }
      lia.
  - exists (map (subst_field Ss) pfs ++ Syntax.fields (body def)). split.
    + eapply CF_Inherit; eauto.
    + rewrite length_app. rewrite length_map. lia.
Qed.

Lemma fdecl_deterministic : forall CT C f D fd,
  fdecl CT C f D fd ->
  forall D' fd', fdecl CT C f D' fd' -> D = D' /\ fd = fd'.
Proof.
  intros CT C f D fd H. induction H; intros D' fd' H2.
  - inversion H2; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst.
      rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
      assert (pfs0 = pfs) by eauto using collect_fields_deterministic_rel.
      subst. split; [reflexivity | congruence].
    + rewrite Hfind in Hfind0. inversion Hfind0; subst.
      rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
      assert (pfs0 = pfs) by eauto using collect_fields_deterministic_rel.
      subst. lia.
  - inversion H2; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst.
      rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
      assert (pfs0 = pfs) by eauto using collect_fields_deterministic_rel.
      subst. lia.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst.
      rewrite Hsuper in Hsuper0. inversion Hsuper0; subst.
      apply IHfdecl. exact Hrest.
Qed.

(** A field of a superclass is the same field of the subclass. *)
Lemma fdecl_down : forall CT k hq g d Co As C Vs,
  view CT k hq g d Co As C Vs ->
  forall f D fd, fdecl CT C f D fd -> fdecl CT Co f D fd.
Proof.
  intros CT k hq g d Co As C Vs H. induction H; intros f D0 fd Hd; auto.
  pose proof (IHview f D0 fd Hd) as HdP.
  destruct (fdecl_collect _ _ _ _ _ HdP) as (pfs & Hpcf & Hlt).
  unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  eapply fd_inh; eauto.
Qed.

(* ------------------TRANSPORT------------------*)

Lemma frameP_local : forall CT sΓ rΓ h G L next wf mode qthis lc lm T,
  dom sΓ = dom (vars rΓ) ->
  frameP CT sΓ rΓ h G L next wf mode qthis lc lm ->
  frameP CT (sΓ ++ [T]) (set_vars rΓ (vars rΓ ++ [Null_a])) h G L next wf mode
    qthis lc lm.
Proof.
  intros CT sΓ rΓ h G L next wf mode qthis lc lm T Hlen HF.
  constructor.
  - exact (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fp_this _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι & o & Hth & Hrest).
    exists ι, o. simpl. rewrite get_this_var_mapping_app_null_last. auto.
  - exact (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_bound _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - intros x T0 v HT Hv. unfold static_getType in HT.
    unfold runtime_getVal in Hv. simpl in Hv.
    destruct (Nat.lt_ge_cases x (dom sΓ)) as [Hlt | Hge].
    + rewrite nth_error_app1 in HT; auto.
      rewrite nth_error_app1 in Hv; [lia|].
      eapply (fp_vars _ _ _ _ _ _ _ _ _ _ _ _ HF); eauto.
    + rewrite nth_error_app2 in Hv; [lia|].
      destruct (x - dom (vars rΓ)) as [|k]; simpl in Hv; [discriminate|].
      destruct k; discriminate.
Qed.

(** A field write keeps the heap part, provided the stored value inhabits
    the field's declared type as the receiver object reads it at the class
    that declares the field. *)
Lemma heapP_update : forall P CT h G L next lx ox f0 vy,
  heapP P CT h G L next ->
  runtime_getObj h lx = Some ox ->
  (forall D fd Vs wv,
     fdecl CT (rctype (rt_type ox)) f0 D fd ->
     oview CT (rqtype (rt_type ox)) (olab (g_col G lx)) (rctype (rt_type ox))
       (g_args G lx) D Vs ->
     vy = Iot wv ->
     lhasp CT h G L wv
       (ldyn (hfr CT (rqtype (rt_type ox)) (olab (g_col G lx)) D Vs) (ftype fd))) ->
  heapP P CT (update_field h lx f0 vy) G L next.
Proof.
  intros P CT h G L next lx ox f0 vy HG Hox Hnew.
  pose proof (update_field_heap_ext h lx f0 vy) as Hext.
  constructor.
  - intros l w Hc.
    destruct (hp_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
    rewrite update_field_length. rewrite update_field_r_muttype. auto.
  - intros l o Ho.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
      inversion Ho; subst o. simpl. exact (hp_erase _ _ _ _ _ _ HG _ _ Hox).
    + rewrite update_field_getObj_diff in Ho; auto.
      exact (hp_erase _ _ _ _ _ _ HG _ _ Ho).
  - intros l o f D fd Vs v Ho Hfd Hv Hn.
    eapply lhasp_ext; [exact Hext | apply gext_refl |].
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
      inversion Ho; subst o. simpl in *.
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * apply nth_error_update_same_inv in Hn. subst vy.
        eapply Hnew; eauto.
      * rewrite update_diff in Hn; auto.
        eapply (hp_fields _ _ _ _ _ _ HG); eauto.
    + rewrite update_field_getObj_diff in Ho; auto.
      eapply (hp_fields _ _ _ _ _ _ HG); eauto.
  - exact (hp_live _ _ _ _ _ _ HG).
  - exact (hp_bound _ _ _ _ _ _ HG).
  - intros l o Ho.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
      inversion Ho; subst o. simpl. exact (hp_obj _ _ _ _ _ _ HG _ _ Hox).
    + rewrite update_field_getObj_diff in Ho; auto.
      exact (hp_obj _ _ _ _ _ _ HG _ _ Ho).
  - intros l o Ho.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
      inversion Ho; subst o. simpl. exact (hp_cls _ _ _ _ _ _ HG _ _ Hox).
    + rewrite update_field_getObj_diff in Ho; auto.
      exact (hp_cls _ _ _ _ _ _ HG _ _ Ho).
Qed.

Lemma frame_ctx_p : forall CT Δ sΓ rΓ h G L next wf mode qthis lc lm,
  wf_r_config CT Δ sΓ rΓ h ->
  frameP CT sΓ rΓ h G L next wf mode qthis lc lm ->
  exists ι o,
    get_this_var_mapping (vars rΓ) = Some ι /\
    runtime_getObj h ι = Some o /\
    rqtype (rt_type o) = qthis /\
    Forall rlost_free (cargs rΓ) /\ Forall rlost_free (margs rΓ) /\
    frame_bounds_ok CT Δ (qr2q qthis) (cargs rΓ) (margs rΓ).
Proof.
  intros CT Δ sΓ rΓ h G L next wf mode qthis lc lm Hwf HF.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & Hlc & Hlm & Hfb).
  destruct (fp_this _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι' & o' & Hth' & Ho' & Hq & _).
  assert (ι' = ι) by congruence. subst ι'.
  rewrite Hobj in Ho'. inversion Ho'; subst o'.
  exists ι, o. rewrite <- Hq. auto 10.
Qed.

(** The label side condition for a member access through a receiver, from
    the receiver's ordinary and label typing. *)
Lemma recv_label_cond_p : forall P CT h G L next mt v o qx C Ts qthis wf mode
    lc lm ca ma,
  heapP P CT h G L next ->
  List.In wf L ->
  readonly_state_method_scope mt ->
  runtime_getObj h v = Some o ->
  wf_r_typable CT h v (TClass qx C Ts) qthis ca ma ->
  lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) (TClass qx C Ts)) ->
  label_cond L (vpa_q mt qx)
    (obj_frame (rqtype (rt_type o)) (g_col G v) (g_col G v) [])
    (act_frame qthis wf mode lc lm).
Proof.
  intros P CT h G L next mt v o qx C Ts qthis wf mode lc lm ca ma
    HG HwfL Hrs Ho Hty Hl.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hty)
    as (o' & Vs & Ho' & Hhead & _).
  rewrite Ho in Ho'. inversion Ho'; subst o'. clear Ho'.
  assert (Hnb : qx <> Bot).
  { intros ->. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl). }
  destruct Hl as (o' & Ho' & Hh & _).
  change (headL L (g_col G v) (dynq (qr2q qthis) qx)
            (lab_of (act_frame qthis wf mode lc lm) qx)) in Hh.
  unfold headL in Hh.
  apply rs_label_cond; auto.
  - intros ->. specialize (Hh eq_refl).
    change (lab_of (act_frame qthis wf mode lc lm) Mut) with (LIn wf) in Hh.
    rewrite (norm_live _ _ HwfL) in Hh. split; auto.
  - intros -> Hqo. rewrite Hqo in Hhead.
    assert (qthis = Mut_r).
    { destruct qthis; auto. unfold head_ok in Hhead. simpl in Hhead.
      destruct Hhead as [Hx | [Hx | Hx]]; discriminate. }
    subst qthis. specialize (Hh eq_refl).
    change (lab_of (act_frame Mut_r wf mode lc lm) RDM)
      with (if mode then LIn wf else LOut) in Hh.
    destruct mode.
    + rewrite (norm_live _ _ HwfL) in Hh. exact Hh.
    + exact Hh.
Qed.

(* ------------------STATEMENT CASES------------------*)

Section Cases.
  Variables (P : Loc -> Prop) (CT : class_table) (Δ : tv_env).
  Variables (sΓ : s_env) (rΓ : r_env) (h : heap) (G : ghost).
  Variables (L : list nat) (next wf : nat) (mode : bool).
  Variables (lc lm : list ltype).
  Variables (ι : Loc) (o : Obj).
  Local Notation mt := (tv_mode Δ).
  Local Notation qthis := (rqtype (rt_type o)).
  Hypothesis Hrs : readonly_state_method_scope mt.
  Hypothesis Hnb : nomut_bounds Δ.
  Hypothesis Hwf : wf_r_config CT Δ sΓ rΓ h.
  Hypothesis HG : heapP P CT h G L next.
  Hypothesis HF : frameP CT sΓ rΓ h G L next wf mode qthis lc lm.
  Hypothesis Hthis : get_this_var_mapping (vars rΓ) = Some ι.
  Hypothesis Hobj : runtime_getObj h ι = Some o.
  Hypothesis Hfb : frame_bounds_ok CT Δ (qr2q qthis) (cargs rΓ) (margs rΓ).
  Hypothesis Hlfc : Forall rlost_free (cargs rΓ).
  Hypothesis Hlfm : Forall rlost_free (margs rΓ).
  Hypothesis Hfit : ffit CT L Δ (act_frame qthis wf mode lc lm).
  Hypothesis Hbc : forall o0 n0 B0,
    tv_bound Δ o0 n0 = Some B0 -> is_class_type B0.

  Let Fc := act_frame qthis wf mode lc lm.

  Lemma pvar_typed : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    wf_r_typable CT h v T qthis (cargs rΓ) (margs rΓ) /\
    lhasp CT h G L v (ldyn Fc T).
  Proof.
    intros x T v HT Hv. split.
    - pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HT) as Hty.
      rewrite Hv in Hty. exact Hty.
    - exact (fp_vars _ _ _ _ _ _ _ _ _ _ _ _ HF _ _ _ HT Hv).
  Qed.

  Lemma plsub : forall T U v,
    qualified_type_subtype CT Δ T U ->
    wf_r_typable CT h v T qthis (cargs rΓ) (margs rΓ) ->
    lhasp CT h G L v (ldyn Fc T) ->
    lhasp CT h G L v (ldyn Fc U).
  Proof.
    intros T U v Hsub Hty Hl.
    pose proof Hwf as (Hct & _).
    exact (lhasp_subtype P CT Δ h G L next mt qthis wf mode lc lm _ _
             Hct HG (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF) Hrs eq_refl
             (vbp_of_fits CT Δ h G L (act_frame qthis wf mode lc lm) _ _ qthis
                Hct (hp_cls _ _ _ _ _ _ HG)
                (fun v0 ob def Hob Hdef =>
                   proj1 (proj2 (proj2 (proj1 (hp_obj _ _ _ _ _ _ HG v0 ob Hob)))
                            def Hdef))
                (proj2 Hfit) eq_refl
                (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF) (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF))
             (fun o0 n0 B0 Hb0 => nomut_bounds_head Δ o0 n0 B0 Hnb Hb0) Hfb
             (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF) (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF)
             T U Hsub v Hty Hl).
  Qed.

  (** A receiver seen at the class type through which a member is looked
      up: its object, the object's view at that class, and the per-class
      condition relating the object's reading of a class header to the
      activation's reading of the adapted one. *)
  Lemma precv_view : forall T v qx C Ts,
    ubound Δ T = Some (TClass qx C Ts) ->
    wf_r_typable CT h v T qthis (cargs rΓ) (margs rΓ) ->
    lhasp CT h G L v (ldyn Fc T) ->
    exists ov As,
      runtime_getObj h v = Some ov /\
      wf_r_typable CT h v (TClass qx C Ts) qthis (cargs rΓ) (margs rΓ) /\
      headL L (g_col G v) (dynq (qr2q qthis) qx) (lab_of Fc qx) /\
      oview CT (rqtype (rt_type ov)) (olab (g_col G v))
        (rctype (rt_type ov)) (g_args G v) C As /\
      Forall2 (lagree L) As (map (ldyn Fc) Ts) /\
      (forall C' As',
         oview CT (rqtype (rt_type ov)) (olab (g_col G v)) C As C' As' ->
         forall cs,
           lc2 L (fun q0 => q0) (vpa_q mt qx)
             (hframe (qr2q (rqtype (rt_type ov))) (olab (g_col G v))
                (pclassf CT C' As') As')
             (lf_with_args Fc cs [])).
  Proof.
    intros T v qx C Ts Hub Hty Hl.
    pose proof Hwf as (Hct & _).
    assert (Hty' : wf_r_typable CT h v (TClass qx C Ts) qthis
                     (cargs rΓ) (margs rΓ)).
    { eapply wf_r_typable_ubound; eauto. }
    assert (Hl' : lhasp CT h G L v (ldyn Fc (TClass qx C Ts))).
    { destruct (ubound_subtype CT _ _ _ Hub) as [-> | Hsub]; auto.
      eapply plsub; eauto. }
    pose proof Hl' as (ov & Hov & Hh & As & Hs & Hle).
    pose proof (recv_label_cond_p _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  HG (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF) Hrs Hov Hty' Hl')
      as Hcond.
    exists ov, As. refine (conj Hov (conj Hty' (conj Hh (conj Hs (conj Hle _))))).
    intros C' As' Hv' cs.
    rewrite <- (rd_map_obj (pclassf CT C' As')).
    apply (ostatic_step_cond L mt Fc (qr2q (rqtype (rt_type ov)))
             (olab (g_col G v)) qx (pclassf CT C' As') As' cs [] Hrs).
    - intros As0 q0. exact (Hcond q0).
    - intros ->.
      destruct (pclassf CT C' As') as [[qp lp]|] eqn:Hp; auto.
      destruct qp; auto.
      assert (Hc : g_col G v = Some wf).
      { unfold headL in Hh. specialize (Hh eq_refl).
        change (lab_of Fc Mut) with (LIn wf) in Hh.
        rewrite (norm_live _ _ (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF)) in Hh.
        exact Hh. }
      destruct (hp_obj _ _ _ _ _ _ HG v ov Hov) as (Hi & Hk & _).
      specialize (Hk wf Hc). rewrite Hc in Hi, Hs, Hv', Hp |- *.
      assert (Hop : opcoh CT L (rqtype (rt_type ov)) (LIn wf) C As (LIn wf)).
      { eapply opcoh_view; [|exact Hs]. apply opcoh_of_pown; auto. }
      exact (Hop C' As' Hv' lp Hp).
  Qed.

  Lemma pexpr_lhas : forall e Te w,
    expr_has_type CT Δ sΓ mt e Te ->
    eval_expr CT rΓ h e (Iot w) OK rΓ h ->
    lhasp CT h G L w (ldyn Fc Te).
  Proof.
    intros e Te w Htype Heval.
    inversion Htype; subst; inversion Heval; subst.
    - destruct (pvar_typed _ _ _ Hget Hval) as [_ Hl]. exact Hl.
    - destruct (pvar_typed _ _ _ Hget_x Hval) as [Hty Hl].
      destruct (precv_view _ _ _ _ _ Hub Hty Hl)
        as (ov & As & Hov & _ & _ & Hs & Hle & Hstep).
      rewrite Hobj0 in Hov. inversion Hov; subst ov. clear Hov.
      inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
      destruct (fdecl_of_collect _ _ _ HcfC _ _ HgetC) as (D & fd0 & Hd).
      assert (Hro : vpa_q mt qx RO = RO).
      { destruct Hrs as [-> | ->]; destruct qx; reflexivity. }
      destruct (field_chain _ _ _ _ _ Hd _ _ HcfC HgetC L Fc (vpa_q mt qx)
                  (rqtype (rt_type o0)) (olab (g_col G v)) As
                  (map (ldyn Fc) Ts) Hro Hstep Hle) as (V & Hv & _ & Hag).
      pose proof (hp_fields _ _ _ _ _ _ HG v o0 f D fd0 V w Hobj0
                    (fdecl_down _ _ _ _ _ _ _ _ _ Hs _ _ _ Hd)
                    (oview_trans _ _ _ _ _ _ _ Hs _ _ Hv) Hfield) as Hfv.
      eapply lhasp_agree; [exact Hfv|].
      unfold member_type, adapt. rewrite ldyn_subst. exact Hag.
  Qed.

  Lemma plcase_assign : forall x e v,
    stmt_typing CT Δ sΓ mt (SVarAss x e) sΓ ->
    eval_expr CT rΓ h e v OK rΓ h ->
    frameP CT sΓ (set_vars rΓ (update x v (vars rΓ))) h G L next wf mode
      qthis lc lm.
  Proof.
    intros x e v Htype Heval. inversion Htype; subst.
    eapply frameP_update; eauto.
    intros w ->.
    pose proof (expr_eval_typable _ _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hfb
                  Htype_e Heval) as Hty. simpl in Hty.
    eapply plsub; eauto. eapply pexpr_lhas; eauto.
  Qed.

  Lemma plcase_cast : forall x T y v,
    stmt_typing CT Δ sΓ mt (SCast x T y) sΓ ->
    runtime_getVal rΓ y = Some v ->
    frameP CT sΓ (set_vars rΓ (update x v (vars rΓ))) h G L next wf mode
      qthis lc lm.
  Proof.
    intros x T y v Htype Hval. inversion Htype; subst.
    eapply frameP_update; eauto.
    intros w ->.
    assert (Hsub' : qualified_type_subtype CT Δ Ty Tx).
    { destruct Hsource as [Hs | Hnarrow].
      - eapply qtype_trans; eauto.
      - exfalso. destruct Hrs as [Hr | Hr]; rewrite Hr in Hscope;
          simpl in Hscope; auto. }
    destruct (pvar_typed _ _ _ Hget_y Hval) as [Hty Hl].
    eapply plsub; eauto.
  Qed.

  Lemma plcase_fldwrite : forall x f0 y lx ox a0 vf vy,
    stmt_typing CT Δ sΓ mt (SFldWrite x f0 y) sΓ ->
    runtime_getVal rΓ x = Some (Iot lx) ->
    runtime_getObj h lx = Some ox ->
    getVal (fields_map ox) f0 = Some vf ->
    sf_assignability_rel CT (rctype (rt_type ox)) f0 a0 ->
    runtime_getVal rΓ y = Some vy ->
    heapP P CT (update_field h lx f0 vy) G L next /\
    prot_preserved P CT mt h (update_field h lx f0 vy).
  Proof.
    intros x f0 y lx ox a0 vf vy Htype Hvx Hox Hvf Hassign Hvy.
    inversion Htype; subst.
    destruct (pvar_typed _ _ _ Hget_x Hvx) as [Hxty Hxl].
    destruct (precv_view _ _ _ _ _ Hub Hxty Hxl)
      as (ov & As & Hov & Hxty' & Hhead & Hs & Hle & Hstep).
    rewrite Hox in Hov. inversion Hov; subst ov. clear Hov.
    pose proof Hwf as (Hct & Hheap & _).
    pose proof (Hheap lx (runtime_getObj_dom _ _ _ Hox)) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Hox in Hwfo.
    destruct Hwfo as (_ & fsO & HcfO & _).
    inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
    destruct (field_inherit _ _ _ _ _ _ (oview_erase _ _ _ _ _ _ _ Hs)
                _ _ _ _ HcfC HcfO HgetC) as (fd' & HnO & Hassign_eq & _).
    destruct (fdecl_of_collect _ _ _ HcfC _ _ HgetC) as (D & fd0 & Hd).
    assert (Hro : vpa_q mt qx RO = RO).
    { destruct Hrs as [-> | ->]; destruct qx; reflexivity. }
    destruct (field_chain _ _ _ _ _ Hd _ _ HcfC HgetC L Fc (vpa_q mt qx)
                (rqtype (rt_type ox)) (olab (g_col G lx)) As
                (map (ldyn Fc) Ts) Hro Hstep Hle) as (V & Hv & _ & Hag).
    destruct Hsub as [Hsub Hok].
    split.
    - apply (heapP_update P CT h G L next lx ox f0 vy HG Hox).
      intros D' fdx Vs' wv Hd' Hv' ->.
      destruct (fdecl_deterministic _ _ _ _ _
                  (fdecl_down _ _ _ _ _ _ _ _ _ Hs _ _ _ Hd) _ _ Hd') as [<- <-].
      rewrite (oview_deterministic _ _ _ _ _ _ _ Hct Hv' _
                 (oview_trans _ _ _ _ _ _ _ Hs _ _ Hv)).
      destruct (pvar_typed _ _ _ Hget_y Hvy) as [Hyty Hyl].
      pose proof (plsub _ _ _ Hsub Hyty Hyl) as Hm.
      eapply lhasp_agree; [exact Hm|]. apply lagree_sym.
      + unfold member_type, adapt. rewrite ldyn_subst. exact Hag.
      + rewrite erase_ldyn. simpl.
        rewrite (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF).
        rewrite (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF).
        destruct Hok as [Hlf | (C' & Ts' & ->)].
        * apply dyn_lost_free; auto. apply qr2q_concrete.
        * exfalso. eapply (typable_head_not_bot _ _ _ _ _ _ _ Hyty). reflexivity.
    - intros l qr C0 Rs0 vals f HP Hl Hprot.
      destruct (Nat.eq_dec lx l) as [-> | Hne].
      + rewrite Hl in Hox. inversion Hox; subst ox. simpl in *.
        rewrite (update_field_getObj_same _ _ _ _ _ Hl). simpl.
        eexists. split; [reflexivity|].
        destruct (Nat.eq_dec f0 f) as [-> | Hnf].
        * exfalso.
          assert (Ha0 : a0 = assignability fieldT).
          { destruct Hassign as (fdO & HlookO & Ha).
            inversion HlookO as [? ? fs2 ? ? Hcf2 Hget2]; subst.
            assert (fs2 = fsO) by eauto using collect_fields_deterministic_rel.
            subst fs2. unfold gget in Hget2. congruence. }
          assert (Hqx : qx = Mut).
          { destruct Hprot as [Hp | [Hp | Hstrict]].
            - pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp)
                as Heq.
              rewrite Ha0 in Heq. rewrite Heq in Hassignable.
              destruct (tv_mode Δ), qx; simpl in Hassignable; discriminate.
            - pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp)
                as Heq.
              rewrite Ha0 in Heq. rewrite Heq in Hassignable.
              destruct (tv_mode Δ), qx; simpl in Hassignable;
                try discriminate; reflexivity.
            - destruct Hstrict as [Hst | Hst]; rewrite Hst in Hassignable;
                destruct qx, (assignability fieldT); simpl in Hassignable;
                try discriminate; reflexivity. }
          subst qx.
          unfold headL in Hhead. specialize (Hhead eq_refl).
          change (lab_of Fc Mut) with (LIn wf) in Hhead.
          rewrite (norm_live _ _ (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF)) in Hhead.
          destruct (hp_col _ _ _ _ _ _ HG _ _ Hhead) as (_ & HnP & _). auto.
        * symmetry. apply update_diff; auto.
      + rewrite update_field_getObj_diff; auto. exists vals. split; auto.
  Qed.

  (** With no bound written mutable in scope, the coherence of the
      activation's own type arguments asks nothing. *)
  Lemma pfcoh : fcoh CT L Δ Fc.
  Proof.
    intros o0 n0 K Bs Hb. exfalso.
    exact (nomut_bounds_head Δ o0 n0 _ Hnb Hb eq_refl).
  Qed.

  Lemma plcase_new : forall x qc C Ts ys l1 qthisr vals,
    stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ ->
    runtime_getVal rΓ 0 = Some (Iot l1) ->
    runtime_lookup_list rΓ ys = Some vals ->
    r_muttype h l1 = Some qthisr ->
    (forall l, P l -> l < dom h) ->
    let onew := mkObj
                  (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                     (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ)) Ts)) vals in
    let G' := g_new G (dom h) (new_color qc wf mode) None (map (ldyn Fc) Ts) in
    heapP P CT (h ++ [onew]) G' L next /\
    frameP CT sΓ (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) (h ++ [onew])
      G' L next wf mode qthis lc lm /\
    gext h G G'.
  Proof.
    intros x qc C Ts ys l1 qthisr vals Htype Hthis0 Hvals Hmut HPdom onew G'.
    inversion Htype; subst.
    apply get_this_runtime_getVal in Hthis0.
    assert (l1 = ι) by congruence. subst l1.
    assert (Hq : qthisr = rqtype (rt_type o)).
    { unfold r_muttype in Hmut. rewrite Hobj in Hmut. congruence. }
    subst qthisr.
    pose proof (heap_ext_app h onew) as Hext.
    pose proof (gext_new h G (new_color qc wf mode) None (map (ldyn Fc) Ts))
      as Hgx. fold G' in Hgx.
    pose proof (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF) as HwfL.
    pose proof (hp_live _ _ _ _ _ _ HG _ HwfL) as Hwn.
    destruct (fp_bound _ _ _ _ _ _ _ _ _ _ _ _ HF) as [Hblc Hblm].
    pose proof (act_frame_bound next qthis wf mode lc lm Hwn Hblc Hblm) as HFb.
    pose proof (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hec.
    pose proof (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF) as Hem.
    pose proof Hwf as (Hct & Hheap & Hrenv & _).
    set (qn := vpa_mutability_object_creation qthis qc) in *.
    assert (HlcE : Forall rlost_free (map erase lc)) by (rewrite Hec; exact Hlfc).
    assert (HlmE : Forall rlost_free (map erase lm)) by (rewrite Hem; exact Hlfm).
    assert (Hshape : Forall (sbnd CT Δ) Ts /\
                     length Ts = length (ctparams (signature def))).
    { inversion Hwf_new as [? ? ? ? def' Hfind' Hhead' Hlen' Hargs' Hbnd'| |].
      rewrite Hfind in Hfind'. inversion Hfind'; subst def'. split; auto.
      eapply Forall_impl; [|exact Hargs']. intros a Ha.
      exact (sbnd_of_wf _ _ _ _ Ha). }
    destruct Hshape as [HsbT HlenT].
    assert (Hob : obP CT L qn (new_color qc wf mode) C (map (ldyn Fc) Ts)).
    { exact (alloc_obP CT L Δ qthis wf mode lc lm qc C def Ts Hct Hrs Hbc Hfit
               pfcoh HlcE HlmE Hfind Hqc Hlost_free HsbT Hbounds). }
    pose proof Hob as (Hi & Hk & _).
    assert (Hkk : qc = Mut_c -> forall C' As',
              oview CT qn (olab (new_color qc wf mode)) C (map (ldyn Fc) Ts)
                C' As' ->
              forall q' l', pclassf CT C' As' = Some (q', l') ->
                q' = Mut /\ norm L l' = norm L (LIn wf)).
    { intros Hqc0 C' As' Hv q' l' Hp.
      destruct (hinv_oview CT L _ _ C _ C' As' Hct Hv Hi) as [_ Hpo].
      assert (Hcol : new_color qc wf mode = Some wf) by (rewrite Hqc0; reflexivity).
      pose proof (Hk wf Hcol) as Hk0. rewrite Hcol in Hpo.
      exact (Hpo Hk0 q' l' Hp). }
    assert (Harg : forall f fd v D fd0 Vs,
              nth_error fds f = Some fd ->
              nth_error vals f = Some (Iot v) ->
              fdecl CT C f D fd0 ->
              oview CT qn (olab (new_color qc wf mode)) C (map (ldyn Fc) Ts) D Vs ->
              lhasp CT h G L v
                (ldyn (hfr CT qn (olab (new_color qc wf mode)) D Vs) (ftype fd0))).
    { intros f fd v D fd0 Vs Hfd Hv Hd Hvw.
      destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hvals Hv)
        as (y & A & HyA & Hyv & HnA).
      pose proof (Forall2_nth_error_rel _ _ _ f Harg_sub) as Hrel.
      rewrite HnA in Hrel. rewrite Hfd in Hrel. destruct Hrel as [Hsub Hok].
      destruct (pvar_typed _ _ _ HyA Hyv) as [Hty Hl].
      pose proof (plsub _ _ _ Hsub Hty Hl) as Hm.
      assert (Hro : vpa_q mt (qc2q qc) RO = RO).
      { destruct Hrs as [-> | ->]; destruct qc; reflexivity. }
      destruct (field_chain _ _ _ _ _ Hd _ _ Hfields Hfd L Fc
                  (vpa_q mt (qc2q qc)) qn (olab (new_color qc wf mode))
                  (map (ldyn Fc) Ts) (map (ldyn Fc) Ts) Hro) as (V & HvV & _ & Hag).
      - intros C' As' Hv' cs. apply new_step_cond; auto.
        intros Hq0 q' l' Hp. exact (Hkk Hq0 C' As' Hv' q' l' Hp).
      - apply Forall2_lagree_refl.
      - rewrite (oview_deterministic _ _ _ _ _ _ _ Hct Hvw _ HvV).
        eapply lhasp_agree; [exact Hm|]. apply lagree_sym.
        + unfold member_type, adapt. rewrite ldyn_subst. exact Hag.
        + rewrite erase_ldyn. simpl. rewrite Hec. rewrite Hem.
          destruct Hok as [Hlf | (C' & Ts' & ->)].
          * apply dyn_lost_free; auto. apply qr2q_concrete.
          * exfalso. eapply (typable_head_not_bot _ _ _ _ _ _ _ Hty). reflexivity. }
    assert (Hold : forall l, l < dom h ->
              g_col G' l = g_col G l /\ g_birth G' l = g_birth G l /\
              g_args G' l = g_args G l) by exact Hgx.
    assert (Hlt : forall l o0, runtime_getObj (h ++ [onew]) l = Some o0 ->
              l <> dom h -> l < dom h).
    { intros l o0 Ho Hne. apply runtime_getObj_dom in Ho.
      rewrite length_app in Ho. simpl in Ho. lia. }
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
    assert (HG' : heapP P CT (h ++ [onew]) G' L next).
    { constructor.
      - intros l w Hc.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold G' in Hc. rewrite g_new_col_same in Hc.
          assert (Hw : w = wf).
          { destruct qc, mode; simpl in Hc; congruence. }
          subst w. refine (conj _ (conj _ (conj _ Hwn))).
          * rewrite length_app. simpl. lia.
          * intros HP. apply HPdom in HP. lia.
          * unfold r_muttype, onew. rewrite runtime_getObj_last. simpl. f_equal.
            apply creation_mut.
            destruct qc, mode; simpl in Hc; try discriminate; auto.
            right. split; auto.
            destruct (fp_this _ _ _ _ _ _ _ _ _ _ _ _ HF)
              as (ι0 & o0 & Hth0 & Ho0 & _ & Hc0).
            assert (ι0 = ι) by congruence. subst ι0.
            destruct (hp_col _ _ _ _ _ _ HG _ _ (Hc0 eq_refl))
              as (_ & _ & Hm & _).
            unfold r_muttype in Hm. rewrite Hobj in Hm. congruence.
        + destruct (g_new_other G (dom h) (new_color qc wf mode) None
                      (map (ldyn Fc) Ts) l Hne) as (Hc1 & _ & _).
          fold G' in Hc1. rewrite Hc1 in Hc.
          destruct (hp_col _ _ _ _ _ _ HG _ _ Hc) as (Ka & Kb & Kc & Kd).
          refine (conj _ (conj Kb (conj _ Kd))).
          * rewrite length_app. lia.
          * unfold r_muttype in *. unfold onew. rewrite runtime_getObj_last2; auto.
      - intros l o0 Ho.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
          inversion Ho; subst o0.
          unfold G'. rewrite g_new_args_same. rewrite map_erase_ldyn. simpl.
          rewrite Hec. rewrite Hem. reflexivity.
        + pose proof (Hlt _ _ Ho Hne) as Hl.
          unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
          destruct (Hold _ Hl) as (_ & _ & Ha). rewrite Ha.
          exact (hp_erase _ _ _ _ _ _ HG _ _ Ho).
      - intros l o0 f D fd0 Vs v Ho Hd Hvw Hval.
        eapply lhasp_ext; [exact Hext | exact Hgx |].
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
          inversion Ho; subst o0.
          cbn [rt_type rqtype rctype fields_map] in Hd, Hvw, Hval |- *.
          unfold G' in Hvw |- *. rewrite g_new_col_same in Hvw |- *.
          rewrite g_new_args_same in Hvw.
          destruct (fdecl_collect _ _ _ _ _ Hd) as (fs & Hcf & Hlen).
          assert (fs = fds) by eauto using collect_fields_deterministic_rel.
          subst fs.
          destruct (nth_error fds f) as [fd|] eqn:Hfd;
            [|apply nth_error_None in Hfd; lia].
          eapply Harg; eauto.
        + pose proof (Hlt _ _ Ho Hne) as Hl.
          unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
          destruct (Hold _ Hl) as (Hc1 & _ & Hc3).
          rewrite Hc1 in Hvw |- *. rewrite Hc3 in Hvw.
          eapply (hp_fields _ _ _ _ _ _ HG); eauto.
      - exact (hp_live _ _ _ _ _ _ HG).
      - intros l.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold G'. rewrite g_new_args_same.
          apply map_ldyn_lbound. exact HFb.
        + destruct (g_new_other G (dom h) (new_color qc wf mode) None
                      (map (ldyn Fc) Ts) l Hne) as (_ & _ & Hc3).
          fold G' in Hc3. rewrite Hc3.
          exact (hp_bound _ _ _ _ _ _ HG l).
      - intros l o0 Ho.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
          inversion Ho; subst o0. cbn [rt_type rqtype rctype].
          unfold G'. rewrite g_new_col_same. rewrite g_new_args_same.
          exact Hob.
        + pose proof (Hlt _ _ Ho Hne) as Hl.
          unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
          destruct (Hold _ Hl) as (Hc1 & _ & Hc3). rewrite Hc1. rewrite Hc3.
          exact (hp_obj _ _ _ _ _ _ HG _ _ Ho).
      - intros l o0 Ho.
        destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
        + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
          inversion Ho; subst o0. cbn [rt_type rqtype rctype].
          unfold G'. rewrite g_new_args_same. split.
          * intros d0 Hd0. rewrite Hfind in Hd0. inversion Hd0; subst d0.
            exact Hlvc.
          * intros d0 Hd0. rewrite Hfind in Hd0. inversion Hd0; subst d0.
            rewrite length_map. symmetry. exact HlenT.
        + pose proof (Hlt _ _ Ho Hne) as Hl.
          unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
          destruct (Hold _ Hl) as (_ & _ & Hc3). rewrite Hc3.
          exact (hp_cls _ _ _ _ _ _ HG _ _ Ho). }
    refine (conj HG' (conj _ Hgx)).
    assert (HF0 : frameP CT sΓ rΓ (h ++ [onew]) G' L next wf mode qthis lc lm).
    { eapply frameP_ext; eauto. }
    eapply frameP_update; eauto.
    intros w Hw. inversion Hw; subst w.
    apply (lhasp_subtype P CT Δ (h ++ [onew]) G' L next mt qthis wf mode lc lm
             _ _ Hct HG' HwfL Hrs eq_refl
             (vbp_of_fits CT Δ (h ++ [onew]) G' L Fc _ _ qthis Hct
                (hp_cls _ _ _ _ _ _ HG')
                (fun v0 ob d0 Hob0 Hd0 =>
                   proj1 (proj2 (proj2 (proj1 (hp_obj _ _ _ _ _ _ HG' v0 ob Hob0)))
                            d0 Hd0))
                (proj2 Hfit) eq_refl Hec Hem)
             (fun o0 n0 B0 Hb0 => nomut_bounds_head Δ o0 n0 B0 Hnb Hb0)
             Hfb Hec Hem _ _ Hresult_sub).
    + unfold wf_r_typable, loc_has_rtype. simpl.
      unfold onew. rewrite runtime_getObj_last. simpl.
      split.
      * rewrite creation_dynq. unfold head_ok. auto.
      * eexists. split; [apply rsi_refl | apply Forall2_rarg_sub_refl].
    + exists onew. split; [apply runtime_getObj_last|].
      change (ldyn Fc (TClass (qc2q qc) C Ts))
        with (LT (dynq (qr2q qthis) (qc2q qc)) (lab_of Fc (qc2q qc)) C
                (map (ldyn Fc) Ts)).
      split.
      * unfold headL. intros Hm. unfold G'. rewrite g_new_col_same.
        destruct qc; cbn [qc2q dynq] in Hm; try discriminate;
          unfold Fc; cbn [qc2q lab_of act_frame lf_mut lf_rdm new_color];
          try (rewrite (norm_live _ _ HwfL); reflexivity).
        destruct mode; [rewrite (norm_live _ _ HwfL); reflexivity|].
        simpl. intros w Hc. discriminate.
      * exists (map (ldyn Fc) Ts). split.
        -- unfold G'. rewrite g_new_args_same. rewrite g_new_col_same.
           simpl. apply v_refl.
        -- apply Forall2_lagree_refl.
  Qed.
End Cases.

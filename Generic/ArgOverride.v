From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases ArgClean GhostOverride.

(** Overriding at the level of labels, over payload views. *)

(* ------------------THE VIEW OF A CLASS FROM A SUBCLASS------------------*)

(** One step of an object's view against a reading of the static view in a
    frame, for an object whose payload at this class is of its own label. *)
Lemma ostatic_step_g : forall L f F hq l pn As cs ms ks,
  (forall As0,
     label_cond2 L (fun q0 => q0) f
       (mk_lframe hq l l As0 [] []) (lf_with_args F cs ms ks)) ->
  (dynq (lf_q F) (f Mut) = Lost \/
   forall l', pn = Some (Mut, l') -> norm L l' = norm L l) ->
  lc2 L (rd_map false (fun q0 => q0) pn) f
    (hframe hq l pn As) (lf_with_args F cs ms ks).
Proof.
  intros L f F hq l pn As cs ms ks Hbase Hpay q1.
  rewrite rd_map_obj.
  destruct (Hbase As q1) as [H1 H2]. cbn [hframe lf_q lf_with_args] in H1, H2 |- *.
  split; [exact H1|].
  destruct H2 as [H2 | [H2 | H2]]; auto.
  destruct (q_eq_dec q1 Mut) as [-> | Hne].
  - destruct Hpay as [Hpay | Hpay]; [left; exact Hpay|].
    right. right.
    assert (Hlab : norm L (lab_of (mk_lframe hq (rd_lab l pn) l As [] []) Mut) =
                   norm L (lab_of (mk_lframe hq l l As [] []) Mut)).
    { simpl. destruct pn as [[qp lp]|]; simpl; auto.
      destruct qp; simpl; auto. }
    rewrite Hlab. exact H2.
  - right. right.
    assert (Hlab : lab_of (mk_lframe hq (rd_lab l pn) l As [] []) q1 =
                   lab_of (mk_lframe hq l l As [] []) q1).
    { destruct q1; simpl; try reflexivity; congruence. }
    rewrite Hlab. exact H2.
Qed.

(** The view the typing rules compute, in any mode and after any further
    qualifier map [g], is one an object with payloads of its own label agrees
    into. *)
Lemma oview_vs_static_g : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F g qo l As,
    g RO = RO ->
    (forall As0 cs ms ks,
       label_cond2 L (fun q0 => q0) (fun q0 => g (vpa_q mt qh q0))
         (mk_lframe (qr2q qo) l l As0 [] []) (lf_with_args F cs ms ks)) ->
    (dynq (lf_q F) (g (vpa_q mt qh Mut)) = Lost \/ opcoh CT L qo l C As l) ->
    Forall2 (lagree L) As (map (ldyn F) (map (map_qual g) Ts)) ->
    exists Vs', oview CT qo l C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) (map (map_qual g) Vs)).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L F g qo l As Hg Hbase Hpc Hargs.
  - exists As. split; [apply v_refl | exact Hargs].
  - destruct (IHsuper_inst L F g qo l
                (hstep false (qr2q qo) (fun q0 => q0) l (pclassf CT C As) As Ss)
                Hg Hbase) as (Vs' & Hv & Hle).
    { destruct Hpc as [Hpc | Hpc]; [left; exact Hpc | right].
      exact (opcoh_step _ _ _ _ _ _ _ _ _ Hpc Hparent). }
    { assert (Heq : map (ldyn F)
                      (map (map_qual g) (map (subst Ts [] []) (map (adapt mt qh) Ss))) =
                    map (fun S => ldyn (lf_with_args F
                                          (map (ldyn F) (map (map_qual g) Ts)) [] [])
                                    (map_qual (fun q0 => g (vpa_q mt qh q0)) S)) Ss).
      { clear - Hg. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite (map_qual_subst g Ts [] [] _ Hg).
        rewrite ldyn_subst. unfold adapt. rewrite map_qual_comp. reflexivity. }
      rewrite Heq. unfold hstep.
      clear IHsuper_inst H Heq. generalize Ss as Ss0.
      induction Ss0 as [|S Ss0 IH]; simpl; [constructor|].
      constructor; [|exact IH].
      apply ldyn_agree2.
      - apply (ostatic_step_g L (fun q0 => g (vpa_q mt qh q0)) F (qr2q qo) l
                 (pclassf CT C As) As
                 (map (ldyn F) (map (map_qual g) Ts)) []).
        + intros As0. apply Hbase.
        + destruct Hpc as [Hpc | Hpc]; [left; exact Hpc | right].
          intros l' Hp. apply (Hpc C As); [apply v_refl | exact Hp].
      - exact Hargs.
      - constructor.
      - reflexivity. }
    exists Vs'. split; auto. unfold oview. eapply v_step; eauto.
Qed.

(* ------------------SUBTYPING WITH MUTABLE POSITIONS FORGOTTEN------------------*)

(** Subtyping of types whose written mutable positions are forgotten, for
    any value: nothing is asked of the value's payloads. *)
Lemma lhasp_subtype_fl : forall P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka,
  wf_class_table CT ->
  heapP P CT h G L next ->
  List.In wf L ->
  readonly_state_method_scope mt ->
  tv_mode Δ = mt ->
  (forall o n B v,
     tv_bound Δ o n = Some B ->
     wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ka ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (TVar TVSub o n)) ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) B)) ->
  (forall o n B, tv_bound Δ o n = Some B -> fT B = B) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ka ->
  map erase lc = ca -> map erase lm = ma -> map fst lk = ka ->
  forall T U,
    qualified_type_subtype CT Δ T U ->
    forall v,
      wf_r_typable CT h v T qthis ca ma ka ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (fT T)) ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm lk) (fT U)).
Proof.
  intros P CT Δ h G L next mt qthis wf mode lc lm lk ca ma ka
    Hwf HG HwfL Hrs Hmode Hcb Hfl Hfb Hec Hem Hek T U Hsub.
  set (Fc := act_frame qthis wf mode lc lm lk).
  induction Hsub; intros v Hty Hl.
  - (* same class, widen the qualifier *)
    destruct Hl as (o & Ho & Hh & Vs & Hs & Hle).
    exists o. split; auto. simpl. split.
    + unfold headL. intros Hm. inversion Hqsub; subst.
      * apply Hh. exact Hm.
      * simpl in Hm. discriminate.
      * exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
    + exists Vs. split; auto.
      eapply Forall2_lagree_trans; [exact Hle|].
      apply map_ldyn_targ_sub.
      clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* up the hierarchy *)
    pose proof Hl as (o & Ho & Hh & As & Hs & Hle).
    rewrite Hmode in Hsuper.
    assert (Hcond : forall As0 cs ms ks,
              label_cond L (fun q0 => fl (vpa_q mt q1 q0))
                (obj_frame (rqtype (rt_type o)) (g_col G v) (g_col G v) As0)
                (act_frame qthis wf mode cs ms ks)).
    { intros As0 cs ms ks.
      destruct (q_eq_dec q1 Mut) as [-> | Hne].
      - apply fl_label_cond_mut. exact Hrs.
      - apply label_cond_fl.
        destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty)
          as (o' & Vs' & Ho' & Hhead & _).
        rewrite Ho in Ho'. inversion Ho'; subst o'. clear Ho'.
        assert (Hnb : q1 <> Bot).
        { intros ->. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl). }
        change (headL L (g_col G v) (dynq (qr2q qthis) (fl q1))
                  (lab_of Fc (fl q1))) in Hh.
        rewrite (fl_ne _ Hne) in Hh. unfold headL in Hh.
        apply rs_label_cond; auto.
        + intros E. contradiction.
        + intros -> Hqo. rewrite Hqo in Hhead.
          assert (qthis = Mut_r).
          { destruct qthis; auto. unfold head_ok in Hhead. simpl in Hhead.
            destruct Hhead as [Hx | [Hx | Hx]]; discriminate. }
          subst qthis. specialize (Hh eq_refl).
          change (lab_of Fc RDM) with (if mode then LIn wf else LOut) in Hh.
          destruct mode.
          * rewrite (norm_live _ _ HwfL) in Hh. exact Hh.
          * exact Hh. }
    destruct (oview_vs_static_g _ _ _ _ _ _ _ Hsuper L Fc fl
                (rqtype (rt_type o)) (olab (g_col G v)) As eq_refl)
      as (Vs0 & Hs0 & Hle0).
    + intros As0 cs ms ks. exact (Hcond As0 cs ms ks).
    + left. destruct Hrs as [-> | ->]; destruct q1; reflexivity.
    + exact Hle.
    + exists o. split; auto. simpl. split; [exact Hh|].
      exists Vs0. split; auto. eapply oview_trans; eauto.
  - exact Hl.
  - (* a type variable at its bound *)
    rewrite (Hfl _ _ _ Hbound).
    eapply Hcb; eauto.
  - (* widen the written qualifier of a variable use *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto].
    unfold headL. intros Hm. inversion Hqsub; subst.
    + apply Hh. exact Hm.
    + simpl in Hm. discriminate.
    + exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ _ Hty). reflexivity.
  - (* view the supplied type as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto]. unfold headL. intros Hm. discriminate.
  - exact Hl.
  - (* a use under a qualifier parameter, viewed as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto]. unfold headL. intros Hm. discriminate.
  - (* a qualified variable use at an argument-free bound *)
    pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ _ Hfb
                  (qtype_qvar_bound CT Δ q1 o n qb C Hsub) Hty) as Hty'.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty')
      as (ob & Rs' & Hob & _ & Hrs' & Hle').
    simpl in Hle'. inversion Hle'; subst.
    destruct (oview_exists _ _ _ _ _ _ Hrs' (rqtype (rt_type ob))
                (olab (g_col G v)) (g_args G v) eq_refl
                (hp_erase _ _ _ _ _ _ HG _ _ Hob)) as (Vs & Hs & He).
    apply map_eq_nil in He. subst Vs.
    destruct Hl as (ob' & Hob' & Hl).
    exists ob. split; auto. simpl. split.
    + simpl in Hl.
      destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
        as [qa la Ca Aa].
      simpl in Hl. tauto.
    + exists (@nil ltype). split; [exact Hs | constructor].
  - (* a variable-headed class type viewed as readonly *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [unfold headL; intros Hm; discriminate|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub.
    clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* compatible arguments under the same variable head *)
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [exact Hh|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub.
    clear - Hargs. induction Hargs; simpl; constructor; auto using targ_sub_fl.
  - (* up the hierarchy under the same variable head *)
    rewrite Hmode in Hsuper.
    destruct Hl as (ob & Hob & Hl).
    assert (Hcond : forall As0 cs ms ks,
              label_cond L (fun q0 => fl (vpa_q mt RO q0))
                (obj_frame (rqtype (rt_type ob)) (g_col G v) (g_col G v) As0)
                (act_frame qthis wf mode cs ms ks)).
    { intros As0 cs ms ks. apply label_cond_fl.
      apply rs_label_cond; auto; try discriminate.
      unfold head_ok. left. reflexivity. }
    exists ob. split; auto.
    cbn [ldyn map_qual] in Hl |- *.
destruct Hl as (Hh & As & Hs & Hle).
    destruct (oview_vs_static_g _ _ _ _ _ _ _ Hsuper L Fc fl
                (rqtype (rt_type ob)) (olab (g_col G v)) As eq_refl)
      as (Vs0 & Hs0 & Hle0).
    + intros As0 cs ms ks. exact (Hcond As0 cs ms ks).
    + left. destruct Hrs as [-> | ->]; reflexivity.
    + exact Hle.
    + split; [exact Hh|].
      exists Vs0. split; auto. eapply oview_trans; eauto.
  - (* the bottom-qualified type of the class *)
    exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ _ Hty eq_refl).
  - (* transitivity *)
    apply IHHsub2.
    + eapply wf_r_typable_subtype; eauto.
    + apply IHHsub1; auto.
Qed.

Lemma map_map_qual_id : forall Ts, map (map_qual (fun q0 => q0)) Ts = Ts.
Proof.
  induction Ts as [|T Ts IH]; simpl; auto. rewrite map_qual_id. rewrite IH.
  reflexivity.
Qed.

Lemma oview_vs_static_id : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F qo l As,
    (forall As0 cs ms ks,
       label_cond2 L (fun q0 => q0) (vpa_q mt qh)
         (mk_lframe (qr2q qo) l l As0 [] []) (lf_with_args F cs ms ks)) ->
    (dynq (lf_q F) (vpa_q mt qh Mut) = Lost \/ opcoh CT L qo l C As l) ->
    Forall2 (lagree L) As (map (ldyn F) Ts) ->
    exists Vs', oview CT qo l C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) Vs).
Proof.
  intros CT mt qh C Ts D Vs H L F qo l As Hbase Hpc Hargs.
  destruct (oview_vs_static_g _ _ _ _ _ _ _ H L F (fun q0 => q0) qo l As
              eq_refl Hbase Hpc) as (Vs' & Hv & Hle).
  - rewrite map_map_qual_id. exact Hargs.
  - exists Vs'. split; auto. rewrite map_map_qual_id in Hle. exact Hle.
Qed.

(* ------------------ONE OVERRIDE STEP------------------*)

Lemma map_lqnth_seq : forall lk, map (lqnth lk) (seq 0 (length lk)) = lk.
Proof.
  unfold lqnth. induction lk as [|a lk IH]; simpl; auto.
  f_equal. rewrite <- seq_shift. rewrite map_map. exact IH.
Qed.

(** The identity qualifier arguments read as the frame's own. *)
Lemma lqarg_qvar_args : forall F,
  map (lqarg F) (qvar_args (length (lf_qargs F))) = lf_qargs F.
Proof.
  intros F. unfold qvar_args. rewrite map_map. simpl. apply map_lqnth_seq.
Qed.

Section StepP.
  Variables (CT : class_table) (qr : q_r) (D' : class_name) (ca' : list rtype).
  Variables (qC : q_c) (sig' sig1 : method_sig) (D1 : class_name).
  Variables (ca1 : list rtype) (Vs : list qualified_type).
  Hypothesis Hct : wf_class_table CT.
  Hypothesis Hag : vpa_mutability_runtime_bound_agree qr qC = true.
  Hypothesis Hsi :
    super_inst CT AbstractState (qc2q qC) D' (class_var_types (length ca')) D1 Vs.
  Hypothesis Hcompat :
    method_override_compatible CT (method_tv_env CT D' sig') qC Vs sig' sig1.
  Hypothesis Hca1 : forall ma ka, ca1 = map (dyn (qr2q qr) ca' ma ka) Vs.
  Hypothesis Hview : forall ma ka T,
    length ma = length (mtparams sig1) ->
    length ka = mqparams sig1 ->
    dyn (qr2q qr) ca' ma ka
      (member_type AbstractState (qc2q qC) Vs
         (method_var_types (length (mtparams sig1))) (qvar_args (mqparams sig1)) T) =
    dyn (qr2q qr) ca1 ma ka T.
  Hypothesis Hfbf : forall ma ka,
    length ka = mqparams sig1 ->
    rbounds_ok CT (qr2q qr) ca1 ma ka ma (mtparams sig1) ->
    frame_bounds_ok CT (method_tv_env CT D' sig') (qr2q qr) ca' ma ka.
  Hypothesis Hrsc : readonly_state_method_scope (mscope sig').
  Hypothesis Hnb : nomut_bounds (method_tv_env CT D' sig').

  Lemma view_agree_flp : forall L c lca' lc1 wf m lm lk T,
    map erase lca' = ca' ->
    oview CT qr (olab c) D' lca' D1 lc1 ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    length lm = length (mtparams sig1) ->
    length lk = mqparams sig1 ->
    lagree L (ldyn (act_frame qr wf m lc1 lm lk) (fT T))
      (ldyn (act_frame qr wf m lca' lm lk)
         (fT (member_type AbstractState (qc2q qC) Vs
                (method_var_types (length (mtparams sig1))) (qvar_args (mqparams sig1)) T))).
  Proof using All.
    intros L c lca' lc1 wf m lm lk T Hec Hls Hn Hlen_lm Hlen_lk.
    set (F' := act_frame qr wf m lca' lm lk).
    unfold member_type, adapt. rewrite fT_subst. rewrite fT_method_var_types.
    rewrite fQ_qvar_args.
    rewrite map_qual_comp. rewrite ldyn_subst.
    assert (Hm : map (ldyn F') (method_var_types (length (mtparams sig1))) = lm).
    { rewrite <- Hlen_lm. apply (ldyn_method_var_types F'). }
    assert (Hk : map (lqarg F') (qvar_args (mqparams sig1)) = lk).
    { rewrite <- Hlen_lk. apply (lqarg_qvar_args F'). }
    fold F'. rewrite Hm. rewrite Hk.
    replace (map_qual (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0)) T)
      with (map_qual (fun q0 => fl (vpa_q AbstractState (qc2q qC) q0)) (fT T)).
    2:{ rewrite map_qual_comp. apply map_qual_ext.
        intros q0. destruct q0, qC; reflexivity. }
    apply ldyn_map_qual_agree.
    - exact (lc_override_types L qr qC wf m lc1 lm lk
               (map (ldyn F') (map fT Vs)) lm lk Hag).
    - assert (Hrefl : Forall2 (lagree L) lca'
                (map (ldyn F') (map fT (class_var_types (length ca'))))).
      { rewrite fT_class_var_types.
        replace (length ca') with (length (lf_cargs F')).
        2:{ simpl. rewrite <- Hec. rewrite length_map. reflexivity. }
        rewrite ldyn_class_var_types. apply Forall2_lagree_refl. }
      destruct (oview_vs_static_g _ _ _ _ _ _ _ Hsi L F' fl qr (olab c) lca'
                  eq_refl) as (Vs0 & Hs0 & Hle0).
      + intros As0 cs ms ks.
        exact (lc_override_args L qr qC c c As0 wf m cs ms ks Hag Hn).
      + left. destruct qC; reflexivity.
      + exact Hrefl.
      + assert (Vs0 = lc1) by (eapply oview_deterministic; eauto).
        subst Vs0. exact Hle0.
    - simpl. apply Forall2_lagree_refl.
    - reflexivity.
  Qed.

  Lemma lref_params_stepp : forall c lca' lc1 wf m lm lk P h G L next,
    map erase lca' = ca' ->
    oview CT qr (olab c) D' lca' D1 lc1 ->
    heapP P CT h G L next -> List.In wf L ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    length lk = mqparams sig1 ->
    rbounds_ok CT (qr2q qr) ca1 (map erase lm) (map fst lk) (map erase lm) (mtparams sig1) ->
    ffit CT L (method_tv_env CT D' sig') (act_frame qr wf m lca' lm lk) ->
    Forall2
      (fun P1 P' => forall v,
         loc_has_rtype CT h v (dyn (qr2q qr) ca1 (map erase lm) (map fst lk) P1) ->
         lhasp CT h G L v (ldyn (act_frame qr wf m lc1 lm lk) (fT P1)) ->
         lhasp CT h G L v (ldyn (act_frame qr wf m lca' lm lk) (fT P')))
      (mparams sig1) (mparams sig').
  Proof using All.
    intros c lca' lc1 wf m lm lk P h G L next Hec Hls HG HwfL Hn Hlen_lk Hb1 Hfit.
    assert (Hlen : length (map erase lm) = length (mtparams sig1))
      by apply (Forall2_length Hb1).
    assert (Hlen_lm : length lm = length (mtparams sig1)).
    { rewrite length_map in Hlen. exact Hlen. }
    assert (Hlenk' : length (map fst lk) = mqparams sig1)
      by (rewrite length_map; exact Hlen_lk).
    destruct Hcompat as (_ & Hscope & Hmtp & Hret & Hpar & _).
    eapply Forall2_impl; [|exact Hpar].
    intros P1 P' Hsub v Hty Hl. simpl in Hsub.
    apply (lhasp_subtype_fl P CT (method_tv_env CT D' sig') h G L next
             (mscope sig') qr wf m lca' lm lk ca' (map erase lm)
             _ Hct HG HwfL Hrsc eq_refl
             (vbp_of_fits CT _ h G L (act_frame qr wf m lca' lm lk) _ _ _ qr
                Hct (hp_cls _ _ _ _ _ _ HG)
                (fun v0 ob def Hob Hdef =>
                   proj1 (proj2 (proj2 (proj1 (hp_obj _ _ _ _ _ _ HG v0 ob Hob)))
                            def Hdef))
                (proj2 Hfit) eq_refl Hec eq_refl eq_refl)
             (fun o n B Hb => no_mut_fT _ _ (proj2 (Hnb o n B Hb)))
             (Hfbf _ _ Hlenk' Hb1) Hec eq_refl eq_refl _ _ Hsub).
    - unfold wf_r_typable. rewrite Hview; auto.
    - eapply lhasp_agree; [exact Hl|].
      apply (view_agree_flp L c lca' lc1 wf m lm lk P1 Hec Hls Hn Hlen_lm Hlen_lk).
  Qed.

  Lemma lref_result_stepp : forall c lca' lc1 wf m lm lk P h G L next,
    map erase lca' = ca' ->
    oview CT qr (olab c) D' lca' D1 lc1 ->
    heapP P CT h G L next -> (m = true -> List.In wf L) ->
    norm L (olab c) = norm L (LIn wf) ->
    (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
    (qC = Mut_c -> norm L (olab c) = norm L (LIn wf)) ->
    opcoh CT L qr (olab c) D' lca' (olab c) ->
    length lk = mqparams sig1 ->
    rbounds_ok CT (qr2q qr) ca1 (map erase lm) (map fst lk) (map erase lm) (mtparams sig1) ->
    ffit CT L (method_tv_env CT D' sig') (act_frame qr wf m lca' lm lk) ->
    Forall rlost_free ca1 ->
    forall v,
      loc_has_rtype CT h v (dyn (qr2q qr) ca' (map erase lm) (map fst lk) (mret sig')) ->
      hexTp G wf (mret sig') v ->
      lhasp CT h G L v (ldyn (act_frame qr wf m lca' lm lk) (mret sig')) ->
      lhasp CT h G L v (ldyn (act_frame qr wf m lc1 lm lk) (mret sig1)) /\
      hexTp G wf (mret sig1) v.
  Proof using All.
    intros c lca' lc1 wf m lm lk P h G L next Hec Hls HG HwfL N1 N2 N3 Hop Hlen_lk Hb1
      Hfit Hlf1 v Hty Hex Hl.
    assert (Hlen : length (map erase lm) = length (mtparams sig1))
      by apply (Forall2_length Hb1).
    assert (Hlen_lm : length lm = length (mtparams sig1)).
    { rewrite length_map in Hlen. exact Hlen. }
    assert (Hlenk' : length (map fst lk) = mqparams sig1)
      by (rewrite length_map; exact Hlen_lk).
    destruct Hcompat as (_ & Hscope & Hmtp & Hret & Hpar & _).
    set (F' := act_frame qr wf m lca' lm lk).
    destruct (lhasp_subtype_ex P CT (method_tv_env CT D' sig') h G L next
                (mscope sig') qr wf m lca' lm lk ca' (map erase lm)
                _ Hct HG HwfL Hrsc eq_refl
                (vbp_of_fits CT _ h G L (act_frame qr wf m lca' lm lk) _ _ _ qr
                   Hct (hp_cls _ _ _ _ _ _ HG)
                   (fun v0 ob def Hob Hdef =>
                      proj1 (proj2 (proj2 (proj1 (hp_obj _ _ _ _ _ _ HG v0 ob Hob)))
                               def Hdef))
                   (proj2 Hfit) eq_refl Hec eq_refl eq_refl)
                (fun o n B Hb => nomut_bounds_head _ o n B Hnb Hb)
                (Hfbf _ _ Hlenk' Hb1) Hec eq_refl eq_refl _ _ Hret
                v Hty Hex Hl) as [Hv Hexv].
    split.
    - eapply lhasp_agree; [exact Hv|].
      unfold member_type, adapt. rewrite ldyn_subst.
      assert (Hm : map (ldyn F') (method_var_types (length (mtparams sig1))) = lm).
      { rewrite <- Hlen_lm. apply (ldyn_method_var_types F'). }
      assert (Hk : map (lqarg F') (qvar_args (mqparams sig1)) = lk).
      { rewrite <- Hlen_lk. apply (lqarg_qvar_args F'). }
      fold F'. rewrite Hm. rewrite Hk.
      apply ldyn_map_qual_agree_inv.
      + apply (lc_override_inv2 L qr qC wf m lc1 lm lk (map (ldyn F') Vs) lm lk Hag).
        intros HqC.
        assert (qr = Mut_r).
        { apply agree_mutc. rewrite <- HqC. exact Hag. }
        rewrite <- (N2 H). exact (N3 HqC).
      + simpl.
        assert (Hargs : Forall2 (lagree L) lca'
                  (map (ldyn F') (class_var_types (length ca')))).
        { replace (length ca') with (length (lf_cargs F')).
          2:{ simpl. rewrite <- Hec. rewrite length_map. reflexivity. }
          rewrite ldyn_class_var_types. apply Forall2_lagree_refl. }
        destruct (oview_vs_static_id _ _ _ _ _ _ _ Hsi L F' qr (olab c) lca')
          as (Vs0 & Hs0 & Hle0).
        * intros As0 cs ms ks.
          exact (lc_override_post L qr qC c c As0 wf m cs ms ks Hag N1 N2 N3).
        * right. exact Hop.
        * exact Hargs.
        * assert (Vs0 = lc1) by (eapply oview_deterministic; eauto).
          subst Vs0.
          apply Forall2_lagree_sym; [exact Hle0|].
          rewrite map_erase_ldyn. simpl. rewrite Hec.
          rewrite <- (Hca1 (map erase lm) (map fst lk)). exact Hlf1.
      + simpl. apply Forall2_lagree_refl.
      + reflexivity.
    - intros Hw. apply Hexv.
      rewrite (whead_member_some _ _ _ _ _ _ _ Hw). destruct qC; reflexivity.
  Qed.
End StepP.


(* ------------------ALONG THE LOOKUP CHAIN------------------*)

(** What is used of the receiver object at a class [K] of its chain. *)
Definition ofacts (CT : class_table) (L : list nat) (qr : q_r) (l : lab)
    (K : class_name) (Vs : list ltype) (d : class_def) : Prop :=
  hinv CT L qr l K Vs /\ frame_fitsp CT L (class_env d) (hfr CT qr l K Vs).

Lemma hfr_as_obj : forall CT qo c C As,
  exists b, hfr CT qo (olab c) C As = obj_frame qo b c As.
Proof.
  intros CT qo c C As. unfold hfr, hframe, obj_frame.
  destruct (rd_lab (olab c) (pclassf CT C As)) as [w|] eqn:E.
  - exists (Some w). destruct c; reflexivity.
  - exists (@None nat). destruct c; reflexivity.
Qed.

(** The activation of a method of a class without mutable positions in its
    bounds fits its bounds in both senses. *)
Lemma act_ffit : forall CT L qr c wf m D' def' sig' lca lm lk,
  wf_class_table CT ->
  find_class CT D' = Some def' ->
  nomut_bounds (method_tv_env CT D' sig') ->
  ofacts CT L qr (olab c) D' lca def' ->
  (qr = Mut_r -> norm L (olab c) = norm L (if m then LIn wf else LOut)) ->
  (forall n B,
     nth_error (mtparams sig') n = Some B ->
     lsubt CT L (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub MethodVar n))
       (ldyn (act_frame qr wf m lca lm lk) B) /\
     fit3p CT L (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub MethodVar n))
       (ldyn (act_frame qr wf m lca lm lk) B)) ->
  ffit CT L (method_tv_env CT D' sig') (act_frame qr wf m lca lm lk).
Proof.
  intros CT L qr c wf m D' def' sig' lca lm lk Hct Hfind Hnb [Hi Hfp] Hn HMV.
  destruct (hfr_as_obj CT qr c D' lca) as [b Hb].
  destruct Hi as (Hfit & _).
  pose proof (Hfit def' Hfind) as Hob. rewrite Hb in Hob. rewrite Hb in Hfp.
  split.
  - apply (act_fits CT L qr b c wf m D' def' sig' lca lm lk Hct Hfind Hnb Hob Hn).
    intros n B HnB. exact (proj1 (HMV n B HnB)).
  - intros o n B Hbd. destruct o.
    + assert (HbC : nth_error (ctparams (signature def')) n = Some B).
      { unfold tv_bound, method_tv_env, class_tparams in Hbd. simpl in Hbd.
        rewrite Hfind in Hbd. exact Hbd. }
      pose proof (Hfp ClassVar n B HbC) as Hs.
      change (ldyn (act_frame qr wf m lca lm lk) (TVar TVSub ClassVar n))
        with (ldyn (obj_frame qr b c lca) (TVar TVSub ClassVar n)).
      apply (fit3p_agree CT L _ _ _ Hs).
      destruct (Hnb _ _ _ Hbd) as [_ HnmB].
      pose proof (class_bounds_wf _ _ _ Hct Hfind) as Hwfb.
      rewrite Forall_forall in Hwfb.
      pose proof (Hwfb _ (nth_error_In _ _ HbC)) as HwB.
      rewrite <- (ldyn_no_method_vars _ _ _ _ HwB eq_refl (obj_frame qr b c lca) lm lk).
      rewrite <- (map_qual_id B) at 2.
      rewrite (no_mut_unm _ _ (fun q0 => q0) HnmB).
      apply ldyn_map_qual_agree.
      * apply obj_act_cond. exact Hn.
      * simpl. apply Forall2_lagree_refl.
      * simpl. apply Forall2_lagree_refl.
      * reflexivity.
    + exact (proj2 (HMV n B Hbd)).
Qed.

Lemma lookup_lref_boundsp : forall CT qr c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm lk L,
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      length lk = mqparams (msignature mdef) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map fst lk) (map erase lm)
        (mtparams (msignature mdef)) ->
      Forall2
        (fun Bu Bl =>
           lagree L (ldyn (act_frame qr wf m0 lc lm lk) Bu)
             (ldyn (act_frame qr wf m0 lc' lm lk) Bl))
        (mtparams (msignature mdef)) (mtparams (msignature mdef')).
Proof.
  intros CT qr c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm lk L Hn Hlk0 Hb.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    apply Forall2_same. intros a. apply lagree_refl.
  - subst qo.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & (Hhd & _ & Hmq) & Hma).
      destruct (Hma _ _ (eq_trans (length_map fst lk) Hlk0) Hb) as (Hb1 & _ & _).
      assert (Hlen_lm : length lm = length (mtparams (msignature mdef1))).
      { pose proof (Forall2_length Hb1) as Hx. rewrite length_map in Hx. exact Hx. }
      assert (Hlen_lk : length lk = mqparams (msignature mdef1)) by congruence.
      pose proof Hcompat as (_ & Hscope & [Hmtp _] & _).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (Hnb1 : nomut_bounds (method_tv_env CT D1 (msignature mdef1))).
      { destruct (find_method_In _ _ _ _ _ HfP) as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 lm lk L Hn Hlk0 Hb) as Htop.
      eapply Forall2_compose; [exact Htop | |].
      2:{ intros Bu B1 Bl Ha Hbb. eapply lagree_trans; [exact Ha | exact Hbb]. }
      rewrite Hmtp. apply Forall2_map_self.
      intros B1 HinB.
      destruct (In_nth_error _ _ HinB) as [n HnB].
      assert (Hf1 : fT B1 = B1).
      { apply (no_mut_fT (method_tv_env CT D1 (msignature mdef1))).
        exact (proj2 (Hnb1 MethodVar n B1 HnB)). }
      set (vB := member_type AbstractState
                    (qc2q (class_qualifier (signature def))) Vs0
                    (method_var_types (length (mtparams (msignature mdef1)))) (qvar_args (mqparams (msignature mdef1))) B1).
      assert (HnV : nth_error (mtparams (msignature mdef')) n = Some vB).
      { rewrite Hmtp. rewrite nth_error_map. rewrite HnB. reflexivity. }
      assert (Hf2 : fT vB = vB).
      { apply (no_mut_fT (method_tv_env CT D' (msignature mdef'))).
        exact (proj2 (Hnb' MethodVar n vB HnV)). }
      rewrite <- Hf1 at 1. rewrite <- Hf2.
      exact (view_agree_flp CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi Hcompat Hca1
               Hview Hfbf Hrsc Hnb' L c Ao lc1 wf m0 lm lk B1 HeA
               (v_step CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1 Hparent Hl1) Hn Hlen_lm Hlen_lk).
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm lk L Hn Hlk0 Hb).
Qed.

Lemma lookup_lref_paramsp : forall CT qr c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm lk P h G L next,
      heapP P CT h G L next -> List.In wf L ->
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      length lk = mqparams (msignature mdef) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map fst lk) (map erase lm)
        (mtparams (msignature mdef)) ->
      (forall K Vs0 d, oview CT qr (olab c) Co Ao K Vs0 ->
         find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d) ->
      (forall n B,
         nth_error (mtparams (msignature mdef)) n = Some B ->
         lsubt CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B) /\
         fit3p CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B)) ->
      Forall2
        (fun Pu Pl => forall v,
           loc_has_rtype CT h v (dyn (qr2q qr) ca (map erase lm) (map fst lk) Pu) ->
           lhasp CT h G L v (ldyn (act_frame qr wf m0 lc lm lk) (fT Pu)) ->
           lhasp CT h G L v (ldyn (act_frame qr wf m0 lc' lm lk) (fT Pl)))
        (mparams (msignature mdef)) (mparams (msignature mdef')).
Proof.
  intros CT qr c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm lk P0 h G L next HG HwfL HN Hlk0 Hb Hall HMV.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst ca'.
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    apply Forall2_same. intros a v _ Hv. exact Hv.
  - subst qo.
    assert (Hfull : rsuper_inst CT (qr2q qr) C Rs D0 Vs) by (eapply rsi_step; eauto).
    pose proof (lookup_lref_boundsp CT qr c wf m0 C Rs D0 Vs Hct Hcl Hfull Hrt
                  Ao HeA _ _ _ _ _ _ _ _ _ Hf' Hf Hs' Hs Hl' Hl Hrsc lm lk L HN Hlk0 Hb)
      as Hbds.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    assert (HallP : forall K Vs0 d,
              oview CT qr (olab c) P
                (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                K Vs0 ->
              find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d).
    { intros K Vs0 d Hv Hd. apply (Hall K Vs0 d); auto.
      unfold oview in *. eapply v_step; eauto. }
    assert (HupP : forall d, find_class CT P = Some d ->
              class_qualifier (signature d) = Mut_c ->
              class_qualifier (signature def) = Mut_c).
    { intros d Hd Hq.
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent')
        as (sd0 & Hsd0 & _ & _ & _ & Hpin & _).
      rewrite Hsd0 in Hd. inversion Hd; subst d.
      destruct Hpin as [Hp | Hp]; congruence. }
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (override_step CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                    Hct Hrt Hfind Hparent' Hwm HfP' Hs1') as (_ & _ & Hma1).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & (Hhd & _ & Hmq) & Hma).
      destruct (Hma _ _ (eq_trans (length_map fst lk) Hlk0) Hb) as (Hb1 & Hp & Hr).
      destruct (Hma1 _ _ (eq_trans (eq_trans (length_map fst lk) Hlk0) (eq_sym Hmq)) Hb1) as (_ & _ & Hr1).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (HMVb : forall n B,
                nth_error (mtparams (msignature mdef')) n = Some B ->
                lsubt CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B) /\
                fit3p CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B)).
      { intros n B HnB.
        pose proof (Forall2_nth_error_rel _ _ _ n Hbds) as Hrel.
        rewrite HnB in Hrel.
        destruct (nth_error (mtparams (msignature mdef)) n) as [Bt|] eqn:HBt;
          [|contradiction].
        destruct (HMV n Bt HBt) as [HM1 HM2]. split.
        - eapply lsubt_agree_r; [exact HM1 | exact Hrel].
        - eapply fit3p_agree; [exact HM2 | exact Hrel]. }
      assert (Hflv : ffit CT L (method_tv_env CT D' (msignature mdef'))
                       (act_frame qr wf m0 Ao lm lk)).
      { exact (act_ffit CT L qr c wf m0 D' def (msignature mdef') Ao lm lk
                 Hct Hfind Hnb'
                 (Hall D' Ao def (v_refl _ _ _ _ _ _ _) Hfind) HN HMVb). }
      pose proof (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
                    Hrsc1 lm lk P0 h G L next HG HwfL HN Hlk0 Hb HallP HMV) as Htop.
      pose proof (lref_params_stepp CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi
                    Hcompat Hca1 Hview Hfbf Hrsc Hnb' c Ao lc1 wf m0 lm lk P0 h G L
                    next HeA (v_step CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1 Hparent Hl1)
                    HG HwfL HN (eq_trans Hlk0 (eq_sym Hmq)) Hb1 Hflv) as Hstep.
      eapply Forall2_compose;
        [exact (Forall2_conj _ _ _ _ Htop Hp) | exact Hstep |].
      intros Pu P1 Pl [Ha Hty1] Hb2 v Hty Hl0.
      apply Hb2; [apply Hty1; exact Hty | apply Ha; auto].
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm lk P0 h G L next HG HwfL HN Hlk0 Hb HallP HMV).
Qed.

Lemma lookup_lref_resultp : forall CT qr c wf m0 Co Ro C Rs1,
  wf_class_table CT -> clean_bounds_ct CT ->
  rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
  wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
  forall Ao, erases Ao Ro ->
  forall mth D' mdef' D mdef ca' ca lc' lc,
    FindMethodWithName CT Co mth D' mdef' ->
    FindMethodWithName CT C mth D mdef ->
    rsuper_inst CT (qr2q qr) Co Ro D' ca' ->
    rsuper_inst CT (qr2q qr) Co Ro D ca ->
    oview CT qr (olab c) Co Ao D' lc' ->
    oview CT qr (olab c) Co Ao D lc ->
    readonly_state_method_scope (mscope (msignature mdef')) ->
    forall lm lk P h G L next,
      heapP P CT h G L next -> (m0 = true -> List.In wf L) ->
      norm L (olab c) = norm L (LIn wf) ->
      (qr = Mut_r -> norm L (olab c) = norm L (if m0 then LIn wf else LOut)) ->
      (forall d, find_class CT Co = Some d ->
         class_qualifier (signature d) = Mut_c ->
         norm L (olab c) = norm L (LIn wf)) ->
      length lk = mqparams (msignature mdef) ->
      rbounds_ok CT (qr2q qr) ca (map erase lm) (map fst lk) (map erase lm)
        (mtparams (msignature mdef)) ->
      (forall K Vs0 d, oview CT qr (olab c) Co Ao K Vs0 ->
         find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d) ->
      (forall n B,
         nth_error (mtparams (msignature mdef)) n = Some B ->
         lsubt CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B) /\
         fit3p CT L (ldyn (act_frame qr wf m0 lc lm lk) (TVar TVSub MethodVar n))
           (ldyn (act_frame qr wf m0 lc lm lk) B)) ->
      forall v,
        loc_has_rtype CT h v
          (dyn (qr2q qr) ca' (map erase lm) (map fst lk) (mret (msignature mdef'))) ->
        hexTp G wf (mret (msignature mdef')) v ->
        lhasp CT h G L v (ldyn (act_frame qr wf m0 lc' lm lk) (mret (msignature mdef'))) ->
        lhasp CT h G L v (ldyn (act_frame qr wf m0 lc lm lk) (mret (msignature mdef))) /\
        hexTp G wf (mret (msignature mdef)) v.
Proof.
  intros CT qr c wf m0 Co Ro C Rs1 Hct Hcl H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt Ao HeA mth D' mdef' D mdef ca' ca lc' lc Hf' Hf Hs' Hs Hl' Hl
      Hrsc lm lk P0 h G L next HG HwfL N1 HN N3 Hlk0 Hb Hall HMV v Hty Hex Hlv.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    assert (ca' = ca) by (eapply rsuper_inst_deterministic; eauto). subst ca'.
    assert (lc' = lc) by (eapply oview_deterministic; eauto). subst lc'.
    split; assumption.
  - subst qo.
    assert (Hfull : rsuper_inst CT (qr2q qr) C Rs D0 Vs) by (eapply rsi_step; eauto).
    pose proof (lookup_lref_boundsp CT qr c wf m0 C Rs D0 Vs Hct Hcl Hfull Hrt
                  Ao HeA _ _ _ _ _ _ _ _ _ Hf' Hf Hs' Hs Hl' Hl Hrsc lm lk L HN Hlk0 Hb)
      as Hbds.
    pose proof (rsuper_inst_le _ _ _ _ _ _ Hct Hrest) as HleC.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent') as (sd & _ & HltP & _).
    assert (HallP : forall K Vs0 d,
              oview CT qr (olab c) P
                (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                K Vs0 ->
              find_class CT K = Some d -> ofacts CT L qr (olab c) K Vs0 d).
    { intros K Vs0 d Hv Hd. apply (Hall K Vs0 d); auto.
      unfold oview in *. eapply v_step; eauto. }
    assert (HupP : forall d, find_class CT P = Some d ->
              class_qualifier (signature d) = Mut_c ->
              class_qualifier (signature def) = Mut_c).
    { intros d Hd Hq.
      destruct (wf_class_super_inv _ _ _ _ _ Hct Hfind Hparent')
        as (sd0 & Hsd0 & _ & _ & _ & Hpin & _).
      rewrite Hsd0 in Hd. inversion Hd; subst d.
      destruct Hpin as [Hp | Hp]; congruence. }
    pose proof (base_subtype_le _ _ _ Hct (find_method_with_name_base _ _ _ _ _ Hf))
      as HleD.
    assert (HsD : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D ca).
    { inversion Hs; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    assert (HeAP : erases (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss)
                     (map (dyn (qr2q qr) Rs [] []) Ss)).
    { unfold erases. rewrite map_erase_hstep_obj. unfold erases in HeA.
      rewrite HeA. reflexivity. }
    assert (HlD : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D lc).
    { inversion Hl; subst; [lia|].
      rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      assert (ca' = Rs).
      { eapply rsuper_inst_deterministic; [exact Hct | exact Hs' | apply rsi_refl]. }
      subst ca'.
      assert (lc' = Ao).
      { eapply oview_deterministic; [exact Hct | exact Hl' | apply v_refl]. }
      subst lc'.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      destruct (find_rsuper_exists _ _ _ _ _ HfP (qr2q qr)
                  (map (dyn (qr2q qr) Rs [] []) Ss)) as [ca1 Hs1].
      destruct (oview_exists _ _ _ _ _ _ Hs1 qr (olab c) _ eq_refl HeAP)
        as (lc1 & Hl1 & He1).
      pose proof (find_method_wf _ _ _ _ _ Hct Hf') as Hwm.
      assert (HfP' : FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1).
      { rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP. }
      assert (Hs1' : rsuper_inst CT (qr2q qr) D' Rs D1 ca1)
        by (eapply rsi_step; eauto).
      destruct (override_data CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                  Hct Hrt Hfind Hparent' Hwm HfP' Hs1')
        as (Vs0 & Hag & Hsi & Hcompat & Hca1 & Hview & Hfbf).
      pose proof (override_step CT qr D' Rs def mdef' P Ss D1 mdef1 ca1
                    Hct Hrt Hfind Hparent' Hwm HfP' Hs1') as (_ & _ & Hma1).
      pose proof (lookup_refines _ _ _ _ _ _ Hct Hrest HrtP _ _ _ _ _ _ _
                    HfP Hf Hs1 HsD) as (Hsc & (Hhd & _ & Hmq) & Hma).
      destruct (Hma _ _ (eq_trans (length_map fst lk) Hlk0) Hb) as (Hb1 & Hp & Hr).
      destruct (Hma1 _ _ (eq_trans (eq_trans (length_map fst lk) Hlk0) (eq_sym Hmq)) Hb1) as (_ & _ & Hr1).
      assert (Hrsc1 : readonly_state_method_scope (mscope (msignature mdef1))).
      { destruct Hcompat as (_ & Hscope & _). rewrite <- Hscope. exact Hrsc. }
      assert (Hnb' : nomut_bounds (method_tv_env CT D' (msignature mdef'))).
      { destruct (find_method_In _ _ _ _ _ Hf') as (defD & HfD & Hin).
        eapply Hcl; eauto. }
      assert (HMVb : forall n B,
                nth_error (mtparams (msignature mdef')) n = Some B ->
                lsubt CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B) /\
                fit3p CT L (ldyn (act_frame qr wf m0 Ao lm lk) (TVar TVSub MethodVar n))
                  (ldyn (act_frame qr wf m0 Ao lm lk) B)).
      { intros n B HnB.
        pose proof (Forall2_nth_error_rel _ _ _ n Hbds) as Hrel.
        rewrite HnB in Hrel.
        destruct (nth_error (mtparams (msignature mdef)) n) as [Bt|] eqn:HBt;
          [|contradiction].
        destruct (HMV n Bt HBt) as [HM1 HM2]. split.
        - eapply lsubt_agree_r; [exact HM1 | exact Hrel].
        - eapply fit3p_agree; [exact HM2 | exact Hrel]. }
      assert (Hflv : ffit CT L (method_tv_env CT D' (msignature mdef'))
                       (act_frame qr wf m0 Ao lm lk)).
      { exact (act_ffit CT L qr c wf m0 D' def (msignature mdef') Ao lm lk
                 Hct Hfind Hnb'
                 (Hall D' Ao def (v_refl _ _ _ _ _ _ _) Hfind) HN HMVb). }
      assert (N3P : forall d, find_class CT P = Some d ->
                class_qualifier (signature d) = Mut_c ->
                norm L (olab c) = norm L (LIn wf)).
      { intros d Hd Hq. exact (N3 def eq_refl (HupP d Hd Hq)). }
      assert (Hlf1 : Forall rlost_free ca1).
      { pose proof (rsuper_wf _ _ _ _ _ _ Hct Hs1' Hrt) as Hv1.
        unfold wf_rtypeuse in Hv1. simpl in Hv1.
        destruct (find_class CT D1); [|contradiction].
        destruct Hv1 as (_ & Hlf & _). exact Hlf. }
      assert (Hop : opcoh CT L qr (olab c) D' Ao (olab c)).
      { destruct (Hall D' Ao def (v_refl _ _ _ _ _ _ _) Hfind) as [Hi _].
        assert (Hpn : pclassf CT D' Ao = None).
        { apply pclassf_clean. intros d0 Hd0. rewrite Hfind in Hd0.
          inversion Hd0; subst d0.
          exact (nomut_bounds_clean CT D' _ def Hfind Hnb'). }
        apply opcoh_of_pown; auto.
        intros q' l' Hpx. rewrite Hpn in Hpx. discriminate. }
      destruct (lref_result_stepp CT qr D' Rs _ _ _ D1 ca1 Vs0 Hct Hag Hsi
                  Hcompat Hca1 Hview Hfbf Hrsc Hnb' c Ao lc1 wf m0 lm lk P0 h G L
                  next HeA (v_step CT false (qr2q qr) (fun q0 => q0) (olab c) D' Ao P Ss D1 lc1 Hparent Hl1)
                  HG HwfL N1 HN (N3 def eq_refl) Hop (eq_trans Hlk0 (eq_sym Hmq)) Hb1 Hflv Hlf1 v Hty Hex Hlv)
        as [Hlv1 Hex1].
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc1 lc HfP Hf Hs1 HsD Hl1 HlD
               Hrsc1 lm lk P0 h G L next HG HwfL N1 HN N3P Hlk0 Hb HallP HMV
               v (Hr1 _ _ Hty) Hex1 Hlv1).
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      pose proof (base_subtype_le _ _ _ Hct
                    (find_method_with_name_base _ _ _ _ _ Hparent_fmn)) as HleD'.
      assert (HsD' : rsuper_inst CT (qr2q qr) P (map (dyn (qr2q qr) Rs [] []) Ss) D' ca').
      { inversion Hs'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (HlD' : oview CT qr (olab c) P
                       (hstep false (qr2q qr) (fun q0 => q0) (olab c) (pclassf CT C Ao) Ao Ss) D' lc').
      { inversion Hl'; subst; [lia|].
        rewrite Hparent in Hparent0. inversion Hparent0; subst. auto. }
      assert (N3P : forall d, find_class CT P = Some d ->
                class_qualifier (signature d) = Mut_c ->
                norm L (olab c) = norm L (LIn wf)).
      { intros d Hd Hq. exact (N3 def eq_refl (HupP d Hd Hq)). }
      exact (IH HrtP _ HeAP _ _ _ _ _ _ _ lc' lc Hparent_fmn Hf HsD' HsD HlD' HlD
               Hrsc lm lk P0 h G L next HG HwfL N1 HN N3P Hlk0 Hb HallP HMV
               v Hty Hex Hlv).
Qed.

Print Assumptions lookup_lref_paramsp.
Print Assumptions lookup_lref_resultp.

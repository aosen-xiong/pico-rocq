From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit
  ArgInvariant ArgOverriding ArgCalls ArgStatements.

(** Place in the proof: the state at the start of a protected call and the
    runtime invariant that makes it fit, at the level of labels (RSF) and over
    payload views: no object is in a world and every position is labelled as
    outside the running calls.
    Counterpart in the non-generic proof (ReadonlyWorlds.v): "transport of the
    invariant" at the entry of a call, and the start of "the theorems". *)

(* ------------------PART 1: THE STARTING STATE AT THE LEVEL OF LABELS------------------*)

(** The state at the start of a protected call, and the runtime invariant
    that makes it fit: every object and every activation satisfies its
    bounds in the protected reading. *)

(* ------------------THE STARTING STATE------------------*)

(** Every position outside the live worlds. *)
Fixpoint lift (R : rtype) : ltype :=
  match R with
  | RClass q0 C args => LT q0 LOut C (map lift args)
  end.

Lemma erase_lift : forall R, erase (lift R) = R.
Proof.
  induction R using rtype_ind'. simpl. f_equal. rewrite map_map.
  induction H; simpl; auto. f_equal; auto.
Qed.

Lemma map_erase_lift : forall Rs, map erase (map lift Rs) = Rs.
Proof. induction Rs; simpl; f_equal; auto using erase_lift. Qed.

Lemma lbound_lift : forall n R, lbound n (lift R).
Proof.
  intros n R. induction R using rtype_ind'. simpl lift. apply lbound_node.
  split; [exact I|]. induction H; simpl; constructor; auto.
Qed.

Lemma Forall_lbound_lift : forall n Rs, Forall (lbound n) (map lift Rs).
Proof. induction Rs; simpl; constructor; auto using lbound_lift. Qed.

Lemma lagree_lift : forall L R U, rarg_sub R U -> lagree L (lift R) (lift U).
Proof.
  intros L R U H. induction H using rarg_sub_ind'. simpl. constructor.
  - assumption.
  - right. right. reflexivity.
  - match goal with
    | H0 : Forall2 rarg_sub _ _ |- _ => clear H0
    end.
    match goal with
    | HH : Forall2 (fun R U => lagree L (lift R) (lift U)) _ _ |- _ =>
        induction HH; simpl; constructor; auto
    end.
Qed.

Lemma lrehead_lift : forall q0 R,
  lrehead q0 LOut (lift R) = lift (rrequalify q0 R).
Proof. intros q0 [q1 C args]. reflexivity. Qed.

(** Qualifier arguments with every label outside. *)
Definition qlift (ka : list q) : list (q * lab) := map (fun q0 => (q0, LOut)) ka.

Lemma lqnth_qlift : forall ka n, lqnth (qlift ka) n = (qnth ka n, LOut).
Proof.
  intros ka n. unfold lqnth, qlift, qnth.
  change (RO, LOut) with ((fun q0 : q => (q0, LOut)) RO). apply map_nth.
Qed.

Lemma map_fst_qlift : forall ka, map fst (qlift ka) = ka.
Proof.
  intros ka. unfold qlift. rewrite map_map. simpl. apply map_id.
Qed.

Lemma ldyn_lift_obj : forall q Rs T,
  ldyn (obj_frame q None None (map lift Rs)) T = lift (dyn (qr2q q) Rs [] [] T).
Proof.
  intros q Rs T. induction T using qualified_type_ind'.
  - simpl. f_equal.
    + destruct qual; reflexivity.
    + rewrite map_map. induction H; simpl; auto. f_equal; auto.
  - assert (Hl : match tv_lookup o (map lift Rs) (@nil ltype) n with
                 | Some A => A | None => ldefault end =
                 lift (match tv_lookup o Rs (@nil rtype) n with
                       | Some R => R | None => default_rtype end)).
    { destruct o; simpl.
      - rewrite nth_error_map. destruct (nth_error Rs n); reflexivity.
      - destruct n; reflexivity. }
    destruct u as [|qv|mp];
      cbn [ldyn dyn obj_frame lf_cargs lf_margs lf_q].
    + exact Hl.
    + rewrite Hl.
      replace (lab_of (obj_frame q None None (map lift Rs)) qv)
        with LOut by (destruct qv; reflexivity).
      apply lrehead_lift.
    + cbn [lf_qargs]. rewrite Hl. unfold lqnth, qnth.
      destruct mp; simpl nth; cbn [fst snd]; apply lrehead_lift.
  - assert (Hargs : map (ldyn (obj_frame q None None (map lift Rs))) args =
                    map lift (map (dyn (qr2q q) Rs [] []) args)).
    { rewrite map_map. induction H; simpl; auto. f_equal; auto. }
    cbn [ldyn dyn obj_frame lf_qargs]. rewrite Hargs.
    unfold lqnth, qnth. destruct n; reflexivity.
Qed.

Lemma ldyn_lift_act : forall Δ q wf ca ma ka T,
  no_mut Δ T ->
  ldyn (act_frame q wf false (map lift ca) (map lift ma) (qlift ka)) T =
  lift (dyn (qr2q q) ca ma ka T).
Proof.
  intros Δ q wf ca ma ka T. induction T using qualified_type_ind'; intros Hnm.
  - inversion Hnm; subst. simpl. f_equal.
    + destruct qual; try reflexivity. congruence.
    + rewrite map_map. clear Hnm Hq. induction H; simpl; auto.
      inversion Hargs; subst. f_equal; auto.
  - assert (Hl : match tv_lookup o (map lift ca) (map lift ma) n with
                 | Some A => A | None => ldefault end =
                 lift (match tv_lookup o ca ma n with
                       | Some R => R | None => default_rtype end)).
    { destruct o; simpl; rewrite nth_error_map;
        destruct (nth_error _ n); reflexivity. }
    inversion Hnm; subst;
      cbn [ldyn dyn act_frame lf_cargs lf_margs lf_q].
    + exact Hl.
    + rewrite Hl.
      replace (lab_of (act_frame q wf false (map lift ca) (map lift ma) (qlift ka)) q0)
        with LOut by (destruct q0; try reflexivity; congruence).
      apply lrehead_lift.
    + cbn [lf_qargs]. rewrite Hl. rewrite lqnth_qlift. cbn [fst snd].
      apply lrehead_lift.
  - inversion Hnm; subst.
    assert (Ha : map (ldyn (act_frame q wf false (map lift ca) (map lift ma) (qlift ka))) args =
                 map lift (map (dyn (qr2q q) ca ma ka) args)).
    { rewrite map_map. clear Hnm. induction H; simpl; auto.
      inversion Hargs; subst. f_equal; auto. }
    cbn [ldyn dyn act_frame lf_qargs]. rewrite Ha. rewrite lqnth_qlift. reflexivity.
Qed.

(** No object is in a world, none has a birth world, and every type argument
    is labelled as outside the live worlds. *)
Definition g_init (h : heap) : ghost :=
  mk_ghost (fun _ => None) (fun _ => None)
    (fun l => match runtime_getObj h l with
              | Some o => map lift (rtargs (rt_type o))
              | None => []
              end).

Lemma lsuper_inst_lift : forall CT q C Rs D Vs,
  rsuper_inst CT (qr2q q) C Rs D Vs ->
  lsuper_inst CT q None None C (map lift Rs) D (map lift Vs).
Proof.
  intros CT q C Rs D Vs H. remember (qr2q q) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D Vs Hparent Hrest IH].
  - apply lsi_refl.
  - eapply lsi_step; [exact Hparent|].
    replace (map (ldyn (obj_frame q None None (map lift Rs))) Ss)
      with (map lift (map (dyn qo Rs [] []) Ss)); [apply IH; auto|].
    subst qo. rewrite map_map. apply map_ext. intros T. symmetry.
    apply ldyn_lift_obj.
Qed.

(* ------------------BOUNDS IN THE PROTECTED READING, AT RUN TIME------------------*)

(** An activation read with every label outside. *)
Definition LF (q0 : q_r) (ca ma : list rtype) (ka : list q) : lframe :=
  mk_lframe (qr2q q0) LOut LOut (map lift ca) (map lift ma) (qlift ka).

Lemma ldyn_lift_LF : forall q0 ca ma ka T,
  ldyn (LF q0 ca ma ka) T = lift (dyn (qr2q q0) ca ma ka T).
Proof.
  intros q0 ca ma ka T. induction T using qualified_type_ind'.
  - simpl. f_equal.
    + destruct qual; reflexivity.
    + rewrite map_map. induction H; simpl; auto. f_equal; auto.
  - assert (Hl : match tv_lookup o (map lift ca) (map lift ma) n with
                 | Some A => A | None => ldefault end =
                 lift (match tv_lookup o ca ma n with
                       | Some R => R | None => default_rtype end)).
    { destruct o; simpl; rewrite nth_error_map;
        destruct (nth_error _ n); reflexivity. }
    destruct u as [|qv|mp]; cbn [ldyn dyn LF lf_cargs lf_margs lf_q].
    + exact Hl.
    + rewrite Hl.
      replace (lab_of (LF q0 ca ma ka) qv)
        with LOut by (destruct qv; reflexivity).
      apply lrehead_lift.
    + cbn [lf_qargs]. rewrite Hl. rewrite lqnth_qlift. cbn [fst snd].
      apply lrehead_lift.
  - assert (Hargs : map (ldyn (LF q0 ca ma ka)) args =
                    map lift (map (dyn (qr2q q0) ca ma ka) args)).
    { rewrite map_map. induction H; simpl; auto. f_equal; auto. }
    cbn [ldyn dyn LF lf_qargs]. rewrite Hargs. rewrite lqnth_qlift. reflexivity.
Qed.

Definition rsfit_heap (CT : class_table) (h : heap) : Prop :=
  forall L, obF CT h (g_init h) L.

Definition rsfit_frame (CT : class_table) (Δ : tv_env) (rΓ : r_env) (h : heap)
    : Prop :=
  forall ι o,
    get_this_var_mapping (vars rΓ) = Some ι ->
    runtime_getObj h ι = Some o ->
    forall L, frame_fits CT L Δ (LF (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ)).

Definition RSF (CT : class_table) (Δ : tv_env) (rΓ : r_env) (h : heap) : Prop :=
  rsfit_heap CT h /\ rsfit_frame CT Δ rΓ h.

(** The object part, unfolded. *)
Lemma rsfit_heap_obj : forall CT h l o def,
  rsfit_heap CT h ->
  runtime_getObj h l = Some o ->
  find_class CT (rctype (rt_type o)) = Some def ->
  forall L, frame_fits CT L (class_env def)
    (obj_frame (rqtype (rt_type o)) None None (map lift (rtargs (rt_type o)))).
Proof.
  intros CT h l o def Hh Ho Hfc L.
  pose proof (Hh L l o def Ho Hfc) as Hx. simpl in Hx. rewrite Ho in Hx. exact Hx.
Qed.

Lemma rsfit_heap_intro : forall CT h,
  (forall l o def,
     runtime_getObj h l = Some o ->
     find_class CT (rctype (rt_type o)) = Some def ->
     forall L, frame_fits CT L (class_env def)
       (obj_frame (rqtype (rt_type o)) None None (map lift (rtargs (rt_type o))))) ->
  rsfit_heap CT h.
Proof.
  intros CT h H L l o def Ho Hfc. simpl. rewrite Ho. exact (H l o def Ho Hfc L).
Qed.

Lemma rsfit_heap_update : forall CT h lx ox f0 vy,
  rsfit_heap CT h -> runtime_getObj h lx = Some ox ->
  rsfit_heap CT (update_field h lx f0 vy).
Proof.
  intros CT h lx ox f0 vy Hh Hox. apply rsfit_heap_intro.
  intros l o def Ho Hfc L.
  destruct (Nat.eq_dec lx l) as [-> | Hne].
  - rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Ho.
    inversion Ho; subst o. simpl in Hfc. simpl.
    exact (rsfit_heap_obj CT h l ox def Hh Hox Hfc L).
  - rewrite update_field_getObj_diff in Ho; auto.
    exact (rsfit_heap_obj CT h l o def Hh Ho Hfc L).
Qed.

(** Allocation keeps the object part. *)
Lemma rsf_new : forall CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals,
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ' ->
  runtime_getVal rΓ 0 = Some (Iot l1) ->
  r_muttype h l1 = Some qthisr ->
  RSF CT Δ rΓ h ->
  rsfit_heap CT
    (h ++ [mkObj
             (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts))
             vals]).
Proof.
  intros CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals
    Hwf Htype Hthis0 Hmut [Hh Hfr].
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & Hmut' & Hlc & Hlm & Hfb).
  apply get_this_runtime_getVal in Hthis0.
  assert (l1 = ι) by congruence. subst l1.
  assert (qthisr = rqtype (rt_type o)) by congruence. subst qthisr.
  set (qo := vpa_mutability_object_creation (rqtype (rt_type o)) qc) in *.
  set (Rs := map (dyn (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts) in *.
  assert (Hhead : head_ok qo (dynq (qr2q (rqtype (rt_type o))) (qc2q qc)))
    by apply creation_head_ok.
  apply rsfit_heap_intro. intros l o0 def0 Ho Hfc L.
  destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
  - rewrite runtime_getObj_last in Ho. inversion Ho; subst o0.
    cbn [rt_type rqtype rctype rtargs] in *.
    rewrite Hfind in Hfc. inversion Hfc; subst def0.
    intros o1 n B Hb.
    destruct (tv_bound_class_env _ _ _ _ Hb) as [-> Hnbd].
    apply alloc_bounds_mode_bridge in Hbounds.
    pose proof (Forall2_nth_error_rel _ _ _ n Hbounds) as Hrel.
    rewrite Hnbd in Hrel.
    destruct (nth_error Ts n) as [T|] eqn:HT; [|contradiction].
    destruct Hrel as [HlfB HbsB].
    rewrite ldyn_lift_obj. rewrite ldyn_lift_obj.
    assert (HX : dyn (qr2q qo) Rs [] [] (TVar TVSub ClassVar n) =
                 dyn (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ) T).
    { cbn [dyn tv_lookup]. unfold Rs. rewrite nth_error_map. rewrite HT.
      reflexivity. }
    rewrite HX.
    assert (Hconc : lf_q (LF (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ)) = Mut \/
                    lf_q (LF (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ)) = Imm).
    { simpl. destruct (rqtype (rt_type o)); auto. }
    pose proof (sub_lsubt CT (with_mode Δ ReadonlyState) L
                  (LF (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ))
                  (or_introl eq_refl) Hconc
                  (fun o0 n0 B0 Hb0 => Hfr ι o Hthis Hobj L o0 n0 B0 Hb0)
                  _ _ (HbsB ReadonlyState)) as Hs.
    rewrite ldyn_lift_LF in Hs. rewrite ldyn_lift_LF in Hs.
    unfold member_type in Hs. rewrite dyn_subst in Hs. simpl map in Hs.
    rewrite (dyn_adapt_exact AbstractState qo (rqtype (rt_type o)) (qc2q qc)
               Rs Rs [] [] [] B); auto using Forall2_rarg_sub_refl.
    fold Rs. change (@nil rtype) with
      (map (dyn (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ)) []).
    change (@nil q) with
      (map (rqarg (qr2q (rqtype (rt_type o))) (qargs rΓ)) []).
    unfold Rs. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete.
  - assert (Hl : l < dom h).
    { apply runtime_getObj_dom in Ho. rewrite length_app in Ho. simpl in Ho. lia. }
    rewrite runtime_getObj_last2 in Ho; auto.
    exact (rsfit_heap_obj CT h l o0 def0 Hh Ho Hfc L).
Qed.

(** At a call, the callee's activation fits its bounds in the protected
    reading. *)
Lemma rsf_call : forall CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D' mdef' ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D' Us Qs vals rΓ' ->
  RSF CT Δ rΓ h ->
  rsfit_frame CT (method_tv_env CT D' (msignature mdef')) rΓ' h.
Proof.
  intros CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D' mdef' vals rΓ'
    Hwf Htype Hvy Hbase Hfind Hvals Henv [Hh Hfr].
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & Hlc & Hlm & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
  rewrite Hvy in Hyty.
  pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ _ Hfb Hub Hyty) as Hyty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hyty')
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
  set (margs' := map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ)) Us) in *.
  set (kargs' := map (rqarg (qr2q qctx) (qargs rΓ)) Qs) in *.
  destruct (super_inst_dyn _ _ _ _ _ _ _ Hsuper (qr2q qr) (qr2q qctx)
              (cargs rΓ) (margs rΓ) (qargs rΓ) Rs1) as (caD & HsupX & HleX); auto.
  { intros q0. apply dynq_vpa_q_agree; auto using qr2q_concrete. }
  pose proof (rsuper_inst_trans _ _ _ _ _ _ Hsup1 _ _ HsupX) as HsupD.
  pose proof (rsuper_wf _ _ _ _ _ _ Hct Hsupc Hrt_oy) as Hview.
  unfold wf_rtypeuse in Hview. simpl in Hview.
  destruct (find_class CT D') as [defD|] eqn:HfD; [|contradiction].
  assert (Hlm' : Forall rlost_free margs').
  { apply map_dyn_lost_free; auto using qr2q_concrete. }
  assert (Hmrefl : Forall2 rarg_sub margs' margs') by apply Forall2_rarg_sub_refl.
  assert (HbD : rbounds_ok CT (qr2q qr) caD margs' kargs' margs'
                  (mtparams (msignature mdef))).
  { unfold rbounds_ok. unfold margs' at 2.
    eapply Forall2_map_left; [exact Htargs_bnd|].
    intros U B0 [HlfB Hsub]. apply bound_sub_self in Hsub. simpl in HlfB, Hsub.
    pose proof (subtype_dyn _ _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub) as Hrs0.
    unfold member_type in Hrs0. rewrite dyn_subst in Hrs0.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ)) Vs)
               margs' margs' kargs' B0); auto.
    unfold margs', kargs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete. }
  assert (Hklen : length kargs' = mqparams (msignature mdef)).
  { unfold kargs'. rewrite length_map. exact Hqargs_len. }
  assert (Hconc : lf_q (LF qctx (cargs rΓ) (margs rΓ) (qargs rΓ)) = Mut \/
                  lf_q (LF qctx (cargs rΓ) (margs rΓ) (qargs rΓ)) = Imm).
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
    pose proof (lsuper_inst_lift CT qr Co Ro D' ca' Hsupc) as Hls.
    assert (HrtA : wf_rtypeuse CT
                     (mkruntime_type qr Co (map erase (map lift Ro)))).
    { rewrite map_erase_lift. exact Hrt_oy. }
    pose proof (ob_view CT L qr None None Co (map lift Ro) D' (map lift ca')
                  Hct Hls HrtA (fun _ => eq_refl)
                  (fun d Hd => rsfit_heap_obj CT h ly
                                 (mkObj (mkruntime_type qr Co Ro) fso) d Hh Hoy Hd L)
                  defD HfD ClassVar n B HbC) as Hs.
    rewrite ldyn_lift_obj in Hs. rewrite ldyn_lift_obj in Hs.
    pose proof (class_bounds_wf _ _ _ Hct HfD) as Hwfb.
    rewrite Forall_forall in Hwfb.
    pose proof (Hwfb _ (nth_error_In _ _ HbC)) as HwB.
    rewrite (dyn_no_method_vars _ _ _ HwB eq_refl (qr2q qr) ca' margs' kargs').
    exact Hs.
  - (* a method type parameter: from the caller's check *)
    assert (HbM : nth_error (mtparams (msignature mdef')) n = Some B) by exact Hb.
    pose proof (lookup_bounds_eq CT qr Co Ro C Rs1 Hct Hsup1 Hrt_oy _ _ _ _ _ _ _
                  margs' kargs' Hfind Hfind_m Hsupc HsupD Hklen HbD) as Heq.
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
    assert (HY : dyn (qr2q qr) ca' margs' kargs' (TVar TVSub MethodVar n) =
                 dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ) U).
    { cbn [dyn tv_lookup]. unfold margs', kargs'. rewrite nth_error_map. rewrite HU.
      reflexivity. }
    rewrite HY.
    pose proof (sub_lsubt CT (with_mode Δ ReadonlyState) L
                  (LF qctx (cargs rΓ) (margs rΓ) (qargs rΓ)) (or_introl eq_refl) Hconc
                  (fun o0 n0 B0 Hb0 => Hfr ι o Hthis Hobj L o0 n0 B0 Hb0)
                  _ _ (HsubB ReadonlyState)) as Hs.
    rewrite ldyn_lift_LF in Hs. rewrite ldyn_lift_LF in Hs.
    unfold member_type in Hs. rewrite dyn_subst in Hs. fold margs' kargs' in Hs.
    rewrite (dyn_adapt_exact mt qr qctx qy caD
               (map (dyn (qr2q qctx) (cargs rΓ) (margs rΓ) (qargs rΓ)) Vs)
               margs' margs' kargs' Bs); auto.
    unfold margs', kargs'. rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete.
Qed.

(** The activation part is kept by every statement: the receiver and the
    type arguments of an activation never change. *)
Lemma rsfit_frame_step : forall CT Δ sΓ mt s sΓ' rΓ h rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_stmt CT rΓ h s OK rΓ' h' ->
  rsfit_frame CT Δ rΓ h -> rsfit_frame CT Δ rΓ' h'.
Proof.
  intros CT Δ sΓ mt s sΓ' rΓ h rΓ' h' Hwf Htype Heval Hfr ι o' Hth Ho' L.
  destruct (eval_stmt_frame _ _ _ _ _ _ Heval _ _ _ _ Htype) as (Hte & Hce & Hme).
  destruct (wf_r_config_this _ _ _ _ _ Hwf) as (ι0 & o & Hthis & Hobj & _).
  assert (ι = ι0) by congruence. subst ι0.
  destruct (heap_ext_getObj _ _ _ _ (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) Hobj)
    as (o2 & Ho2 & Hrt).
  rewrite Ho' in Ho2. inversion Ho2; subst o2.
  rewrite Hrt. rewrite Hce. rewrite Hme.
  rewrite (eval_stmt_qargs _ _ _ _ _ _ _ Heval eq_refl). exact (Hfr ι o Hthis Hobj L).
Qed.

(** Every well-typed statement, in any mode, keeps the invariant. *)
Lemma rsfit_heap_preservation : forall CT,
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ',
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      RSF CT Δ rΓ h ->
      rsfit_heap CT h'.
Proof.
  intros CT rΓ h s res rΓ' h' Heval.
  induction Heval; intros Hres Δ sΓ mt0 sΓ' Hwf Htype HR; try discriminate;
    try exact (proj1 HR).
  - (* field write *)
    subst. exact (rsfit_heap_update CT h _ _ _ _ (proj1 HR) Hobj).
  - (* new *)
    subst. eapply rsf_new; eauto.
  - (* call *)
    subst.
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ & _ & Hwm & Hcfg & _).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _).
    eapply (IHHeval eq_refl _ _ _ _ Hcfg Hbody).
    split; [exact (proj1 HR)|].
    exact (rsf_call CT Δ sΓ rΓ h mt0 x m y Us Qs zs sΓ' ly cy D mdef vals rΓ'
             Hwf Htype Hval_y Hbase Hfind Hargs Hframe HR).
  - (* sequence *)
    inversion Htype; subst.
    pose proof (IHHeval1 eq_refl _ _ _ _ Hwf Htype1 HR) as Hh1.
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    eapply (IHHeval2 eq_refl _ _ _ _ Hwf1 Htype2).
    split; [exact Hh1|].
    exact (rsfit_frame_step CT Δ sΓ mt0 s1 _ rΓ h rΓ' h' Hwf Htype1 Heval1
             (proj2 HR)).
Qed.

Theorem rsf_preservation : forall CT Δ sΓ mt s sΓ' rΓ h rΓ' h',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt s sΓ' ->
  eval_stmt CT rΓ h s OK rΓ' h' ->
  RSF CT Δ rΓ h -> RSF CT Δ rΓ' h'.
Proof.
  intros CT Δ sΓ mt s sΓ' rΓ h rΓ' h' Hwf Htype Heval HR. split.
  - eapply rsfit_heap_preservation; eauto.
  - exact (rsfit_frame_step CT Δ sΓ mt s sΓ' rΓ h rΓ' h' Hwf Htype Heval (proj2 HR)).
Qed.

(* ------------------PART 2: THE STARTING STATE OVER PAYLOAD VIEWS------------------*)

(** The starting state over payload views: no object is in a world and every
    position is labelled as outside the running calls. *)

(* ------------------LABEL-FREE ARGUMENTS------------------*)

Lemma lab_bound_0 : forall l, lab_bound 0 l -> l = LOut.
Proof. intros [w|] H; simpl in H; [lia | reflexivity]. Qed.

Lemma pclassf_lift : forall CT C Rs q' l',
  pclassf CT C (map lift Rs) = Some (q', l') -> l' = LOut.
Proof.
  intros CT C Rs q' l' Hp. apply lab_bound_0.
  eapply pclassf_lbound; [|exact Hp]. apply Forall_lbound_lift.
Qed.

Lemma hfr_lift : forall CT q C Rs,
  hfr CT q LOut C (map lift Rs) = obj_frame q None None (map lift Rs).
Proof.
  intros CT q C Rs. unfold hfr, hframe, obj_frame.
  destruct (pclassf CT C (map lift Rs)) as [[q' l']|] eqn:Hp; [|reflexivity].
  rewrite (pclassf_lift _ _ _ _ _ Hp). destruct q'; reflexivity.
Qed.

Lemma oview_lift : forall CT q C Rs D Vs,
  rsuper_inst CT (qr2q q) C Rs D Vs ->
  oview CT q LOut C (map lift Rs) D (map lift Vs).
Proof.
  intros CT q C Rs D Vs H. remember (qr2q q) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D Vs Hparent Hrest IH].
  - apply v_refl.
  - unfold oview. eapply v_step; [exact Hparent|]. cbn [vpay].
    replace (hstep false (qr2q q) (fun q0 => q0) LOut
               (pclassf CT C (map lift Rs)) (map lift Rs) Ss)
      with (map lift (map (dyn qo Rs [] []) Ss)); [apply IH; auto|].
    subst qo. rewrite hstep_obj.
    change (hframe (qr2q q) LOut (pclassf CT C (map lift Rs)) (map lift Rs))
      with (hfr CT q LOut C (map lift Rs)).
    rewrite hfr_lift. rewrite map_map. apply map_ext. intros T. symmetry.
    apply ldyn_lift_obj.
Qed.

(** The plain reading of lifted arguments is their lifted view too. *)
Lemma oplain_lift : forall CT q C Rs D Vs,
  rsuper_inst CT (qr2q q) C Rs D Vs ->
  oplain CT q LOut C (map lift Rs) D (map lift Vs).
Proof.
  intros CT q C Rs D Vs H. remember (qr2q q) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D Vs Hparent Hrest IH].
  - apply v_refl.
  - unfold oplain. eapply v_step; [exact Hparent|]. cbn [vpay].
    replace (hstep true (qr2q q) (fun q0 => q0) LOut None (map lift Rs) Ss)
      with (map lift (map (dyn qo Rs [] []) Ss)); [apply IH; auto|].
    subst qo. unfold hstep. cbn [rd_map].
    change (hframe (qr2q q) LOut None (map lift Rs))
      with (obj_frame q None None (map lift Rs)).
    rewrite map_map. apply map_ext. intros T.
    rewrite map_qual_id. symmetry. apply ldyn_lift_obj.
Qed.

Lemma lhasp_lift : forall CT h L v R,
  loc_has_rtype CT h v R -> lhasp CT h (g_init h) L v (lift R).
Proof.
  intros CT h L v R. unfold loc_has_rtype.
  destruct (runtime_getObj h v) as [o|] eqn:Ho; [|contradiction].
  destruct R as [rq D Us]. intros [Hh (Vs & Hs & Hle)].
  exists o. split; auto. simpl lift. split.
  - unfold headL. intros _. simpl. intros w Hw. discriminate.
  - exists (map lift Vs), (map lift Vs). split; [|split].
    + simpl. rewrite Ho. apply oview_lift. exact Hs.
    + simpl. rewrite Ho. apply oplain_lift. exact Hs.
    + apply Forall3_xagree_of_lagree; [apply Forall2_lvar_refl|].
      clear - Hle. induction Hle; simpl; constructor; auto using lagree_lift.
Qed.

(** A field declared in an ancestor, among the ancestor's collected
    fields. *)
Lemma fdecl_at : forall CT C f D fd,
  fdecl CT C f D fd ->
  exists fsD, CollectFields CT D fsD /\ nth_error fsD f = Some fd.
Proof.
  intros CT C f D fd H. induction H.
  - exists (map (subst_field Ss) pfs ++ Syntax.fields (body def)). split.
    + eapply CF_Inherit; eauto.
    + rewrite nth_error_app2; rewrite length_map; auto.
  - exact IHfdecl.
Qed.

(* ------------------THE STARTING HEAP------------------*)

Lemma heapP_init : forall CT h,
  wf_class_table CT ->
  wf_heap CT h ->
  (forall l o, runtime_getObj h l = Some o ->
     obP CT [0] (rqtype (rt_type o)) None (rctype (rt_type o))
       (map lift (rtargs (rt_type o))) /\
     livec CT (rctype (rt_type o))) ->
  heapP (fun l => l < dom h) CT h (g_init h) [0] 1.
Proof.
  intros CT h Hct Hheap Hobs. constructor.
  - intros l w Hc. discriminate.
  - intros l o Ho. simpl. rewrite Ho. apply map_erase_lift.
  - intros l o f D fd0 Vs v Ho Hd Hv Hval.
    simpl in Hv |- *. rewrite Ho in Hv.
    pose proof (Hheap l (runtime_getObj_dom _ _ _ Ho)) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Ho in Hwfo.
    destruct Hwfo as (_ & fsO & HcfO & _ & Hall).
    pose proof (oview_erase _ _ _ _ _ _ _ Hv) as Hrs.
    rewrite map_erase_lift in Hrs.
    assert (HVs : Vs = map lift (map erase Vs)).
    { eapply oview_deterministic; [exact Hct | exact Hv |].
      apply oview_lift. exact Hrs. }
    destruct (fdecl_at _ _ _ _ _ Hd) as (fsD & HcfD & HnD).
    destruct (field_inherit _ _ _ _ _ _ Hrs _ _ _ _ HcfD HcfO HnD)
      as (fdO & HnO & _ & Heq).
    pose proof (Forall2_nth_error_rel _ _ _ f Hall) as Hrel.
    rewrite Hval in Hrel. rewrite HnO in Hrel.
    unfold wf_r_typable in Hrel. rewrite Heq in Hrel.
    rewrite HVs. rewrite hfr_lift. rewrite ldyn_lift_obj.
    apply lhasp_lift. exact Hrel.
  - intros l o f D fd Vr Vp Ho Hc Hfd Hvr Hvp.
    simpl in Hvr, Hvp. rewrite Ho in Hvr, Hvp.
    pose proof (oview_erase _ _ _ _ _ _ _ Hvr) as Hrs.
    rewrite map_erase_lift in Hrs.
    assert (HVr : Vr = map lift (map erase Vr)).
    { eapply oview_deterministic; [exact Hct | exact Hvr |].
      apply oview_lift. exact Hrs. }
    assert (HVp : Vp = map lift (map erase Vr)).
    { eapply oplain_deterministic; [exact Hct | exact Hvp |].
      apply oplain_lift. exact Hrs. }
    rewrite HVr. rewrite HVp. rewrite hfr_lift.
    change (hframe (qr2q (rqtype (rt_type o))) LOut None (map lift (map erase Vr)))
      with (obj_frame (rqtype (rt_type o)) None None (map lift (map erase Vr))).
    split; apply lagree_refl.
  - intros l o Ho Hc. simpl. rewrite Ho.
    intros D Vs Hv w Hp.
    pose proof (oview_erase _ _ _ _ _ _ _ Hv) as Hrs.
    rewrite map_erase_lift in Hrs.
    assert (HVs : Vs = map lift (map erase Vs)).
    { eapply oview_deterministic; [exact Hct | exact Hv |].
      apply oview_lift. exact Hrs. }
    rewrite HVs in Hp. rewrite (pclassf_lift _ _ _ _ _ Hp). reflexivity.
  - intros w [<- | []]. lia.
  - intros l. simpl.
    destruct (runtime_getObj h l); [apply Forall_lbound_lift | constructor].
  - intros l o Ho. simpl. rewrite Ho. exact (proj1 (Hobs l o Ho)).
  - intros l o Ho. simpl. rewrite Ho. split.
    + exact (proj2 (Hobs l o Ho)).
    + intros def Hdef.
      pose proof (Hheap l (runtime_getObj_dom _ _ _ Ho)) as Hwfo.
      unfold wf_obj in Hwfo. rewrite Ho in Hwfo.
      destruct Hwfo as (Hrt & _). unfold wf_rtypeuse in Hrt. rewrite Hdef in Hrt.
      destruct Hrt as (_ & _ & Hb). rewrite length_map.
      symmetry. exact (Forall2_length Hb).
Qed.

Print Assumptions heapP_init.

(* ------------------THE THEOREMS------------------*)

(** The callee's activation fits its bounds in the payload reading, with
    every label outside. *)
Definition rsfitp_frame (CT : class_table) (Δ : tv_env) (rΓ : r_env) (h : heap)
    : Prop :=
  forall ι o,
    get_this_var_mapping (vars rΓ) = Some ι ->
    runtime_getObj h ι = Some o ->
    forall L, frame_fitsp CT L Δ (LF (rqtype (rt_type o)) (cargs rΓ) (margs rΓ) (qargs rΓ)).

(** Every object of the heap satisfies the per-object invariant with every
    label outside, and its class can have objects. *)
Definition rsfitp_heap (CT : class_table) (h : heap) : Prop :=
  forall l o, runtime_getObj h l = Some o ->
    obP CT [0] (rqtype (rt_type o)) None (rctype (rt_type o))
      (map lift (rtargs (rt_type o))) /\
    livec CT (rctype (rt_type o)).

(** A call that selects a readonly-state or transitive-state method leaves
    the protected fields of every object of the entry heap unchanged.
    There is no condition on what the protected code allocates.  The
    conditions on the class table are on the bounds in scope of protected
    methods only.  The entry state satisfies its bounds in the protected
    reading: the earlier form ([RSF], kept by every well-typed execution)
    and the payload form for the heap and for the callee's activation. *)
(** The body of a selected readonly-state or transitive-state method, however
    it ends, leaves the protected fields of the entry heap unchanged. *)
Lemma rs_ts_body_preservation_payload :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' ly cy D mdef valsc rΓc res rΓ' h',
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSF CT Δ rΓ h ->
    rsfitp_heap CT h ->
    (forall vals rΓc,
       runtime_lookup_list rΓ zs = Some vals ->
       callee_env CT rΓ h ly D Us Qs vals rΓc ->
       rsfitp_frame CT (method_tv_env CT D (msignature mdef)) rΓc h) ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    runtime_lookup_list rΓ zs = Some valsc ->
    callee_env CT rΓ h ly D Us Qs valsc rΓc ->
    eval_stmt CT rΓc h (mbody_stmt (mbody mdef)) res rΓ' h' ->
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
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' ly cy D mdef valsc rΓc res rΓ' h'
    Hcl Hwf HR Hhp Hfp Htype Hargs Hframe Heval_body Hvy Hbase Hfind Hrs
    l qr C Rs vals f Hl Hprot.
  pose proof Hwf as (Hct & Hheap & _).
  destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ Hwf Htype Hvy Hbase Hfind Hargs Hframe)
    as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ & _ & Hwm & Hcfg & _).
  destruct (find_method_In _ _ _ _ _ Hfind) as (defD & HfD & HinD).
  pose proof (Hcl _ _ _ HfD HinD Hrs) as Hcb'.
  pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _ & Hroots).
  destruct (Hroots Hrs) as (Hnm_recv & Hnm_par & _).
  destruct (wf_r_config_this _ _ _ _ _ Hcfg)
    as (ι2 & o2 & Hth2 & Hobj2 & _ & _ & _ & _).
  set (P := fun l0 : Loc => l0 < dom h).
  assert (HF : frameP CT
                 (mreceiver (msignature mdef) :: mparams (msignature mdef))
                 rΓc h (g_init h) [0] 1 0 false (rqtype (rt_type o2))
                 (map lift (cargs rΓc)) (map lift (margs rΓc)) (qlift (qargs rΓc))).
  { constructor.
    - left. reflexivity.
    - exists ι2, o2. refine (conj Hth2 (conj Hobj2 (conj eq_refl _))).
      discriminate.
    - apply map_erase_lift.
    - apply map_erase_lift.
    - apply map_fst_qlift.
    - split; apply Forall_lbound_lift.
    - unfold qlift. rewrite Forall_map. apply Forall_forall.
      intros q0 _. simpl. auto.
    - intros x0 T v HT Hv.
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hcfg Hth2 Hobj2 HT) as Hty.
      rewrite Hv in Hty.
      assert (HnmT : no_mut (method_tv_env CT D (msignature mdef)) T).
      { unfold static_getType in HT. destruct x0 as [|i]; simpl in HT.
        - inversion HT; subst. exact Hnm_recv.
        - rewrite Forall_forall in Hnm_par. apply Hnm_par.
          eapply nth_error_In; eauto. }
      rewrite (ldyn_lift_act _ _ _ _ _ _ _ HnmT).
      apply lhasp_lift. exact Hty. }
  pose proof (rsf_call CT Δ sΓ rΓ h mt x m y Us Qs zs sΓ' ly cy D mdef valsc rΓc
                Hwf Htype Hvy Hbase Hfind Hargs Hframe HR) as Hfrc.
  pose proof (Hfp valsc rΓc Hargs Hframe) as Hfrp.
  assert (Hfl0 : ffit CT [0] (method_tv_env CT D (msignature mdef))
                   (act_frame (rqtype (rt_type o2)) 0 false
                      (map lift (cargs rΓc)) (map lift (margs rΓc)) (qlift (qargs rΓc)))).
  { split.
    - intros o0 n B Hb.
      pose proof (Hfrc ι2 o2 Hth2 Hobj2 [0] o0 n B Hb) as Hx.
      change (ldyn (act_frame (rqtype (rt_type o2)) 0 false
                      (map lift (cargs rΓc)) (map lift (margs rΓc)) (qlift (qargs rΓc)))
                (TVar TVSub o0 n))
        with (ldyn (LF (rqtype (rt_type o2)) (cargs rΓc) (margs rΓc) (qargs rΓc))
                (TVar TVSub o0 n)).
      rewrite (ldyn_lift_act _ _ _ _ _ _ _ (proj2 (Hcb' o0 n B Hb))).
      rewrite <- ldyn_lift_LF. exact Hx.
    - intros o0 n B Hb.
      pose proof (Hfrp ι2 o2 Hth2 Hobj2 [0] o0 n B Hb) as Hx.
      change (ldyn (act_frame (rqtype (rt_type o2)) 0 false
                      (map lift (cargs rΓc)) (map lift (margs rΓc)) (qlift (qargs rΓc)))
                (TVar TVSub o0 n))
        with (ldyn (LF (rqtype (rt_type o2)) (cargs rΓc) (margs rΓc) (qargs rΓc))
                (TVar TVSub o0 n)).
      rewrite (ldyn_lift_act _ _ _ _ _ _ _ (proj2 (Hcb' o0 n B Hb))).
      rewrite <- ldyn_lift_LF. exact Hx. }
  destruct (pg_step_any P CT Hcl _ _ _ _ _ _ Heval_body
              (method_tv_env CT D (msignature mdef)) _ sΓb (g_init h) [0] 1 0
              false _ _ _ _ Hrs Hcb' Hcfg Hbody
              (heapP_init CT h Hct Hheap Hhp) HF Hfl0
              (fun l0 H => H))
    as [Hpres _].
  eapply Hpres; eauto.
  unfold P. eapply runtime_getObj_dom; eauto.
Qed.

(** The call theorem for a call that ends in any way: normally, in a null
    dereference, or in a rejected write. *)
Theorem rs_ts_call_preservation_payload_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSF CT Δ rΓ h ->
    rsfitp_heap CT h ->
    (forall vals rΓc,
       runtime_lookup_list rΓ zs = Some vals ->
       callee_env CT rΓ h ly D Us Qs vals rΓc ->
       rsfitp_frame CT (method_tv_env CT D (msignature mdef)) rΓc h) ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
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
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res
    Hcl Hwf HR Hhp Hfp Htype Heval Hvy Hbase Hfind Hrs l qr C Rs vals f Hl Hprot.
  inversion Heval; subst;
    try (exists vals; split; [exact Hl | reflexivity]);
    (rewrite Hvy in Hval_y; inversion Hval_y; subst ly0; clear Hval_y;
     rewrite Hbase in Hbase0; inversion Hbase0; subst cy0; clear Hbase0;
     destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfind Hfind0)
       as [<- <-];
     exact (rs_ts_body_preservation_payload CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ'
              ly cy D mdef _ _ _ _ _ Hcl Hwf HR Hhp Hfp Htype Hargs Hframe
              Heval_body Hvy Hbase Hfind Hrs l qr C Rs vals f Hl Hprot)).
Qed.

Theorem rs_ts_call_preservation_payload :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSF CT Δ rΓ h ->
    rsfitp_heap CT h ->
    (forall vals rΓc,
       runtime_lookup_list rΓ zs = Some vals ->
       callee_env CT rΓ h ly D Us Qs vals rΓc ->
       rsfitp_frame CT (method_tv_env CT D (msignature mdef)) rΓc h) ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
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
  intros. eapply rs_ts_call_preservation_payload_any; eauto.
Qed.

(** Readonly-state preservation: non-assignable fields keep their values. *)
Corollary readonly_state_preservation_payload :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSF CT Δ rΓ h ->
    rsfitp_heap CT h ->
    (forall vals rΓc,
       runtime_lookup_list rΓ zs = Some vals ->
       callee_env CT rΓ h ly D Us Qs vals rΓc ->
       rsfitp_frame CT (method_tv_env CT D (msignature mdef)) rΓc h) ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
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
  intros. eapply rs_ts_call_preservation_payload; eauto.
  unfold prot_cond. tauto.
Qed.

(** Transitive-state preservation: every field keeps its value. *)
Corollary transitive_state_preservation_payload :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    clean_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSF CT Δ rΓ h ->
    rsfitp_heap CT h ->
    (forall vals rΓc,
       runtime_lookup_list rΓ zs = Some vals ->
       callee_env CT rΓ h ly D Us Qs vals rΓc ->
       rsfitp_frame CT (method_tv_env CT D (msignature mdef)) rΓc h) ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) OK rΓ' h' ->
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
  intros until mdef. intros Hcc Hwf HR Hhp Hfp Htype Heval Hvy Hbase Hfind Hts.
  intros. eapply rs_ts_call_preservation_payload; eauto.
  - rewrite Hts. right. reflexivity.
  - rewrite Hts. right. right. right. reflexivity.
Qed.

Print Assumptions readonly_state_preservation_payload.
Print Assumptions transitive_state_preservation_payload.

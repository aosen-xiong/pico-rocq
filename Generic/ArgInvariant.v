From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews GhostTyping
  GhostFit ArgTyping GhostInvariant ArgFit.

(** The label invariant over payload views.

    The ghost state gives each object a world (or none) and labelled type
    arguments.  No world of creation is recorded. *)

(* ------------------VALUES ACROSS HEAP GROWTH AND WORLDS------------------*)

Lemma lhasp_ext : forall CT h h' G G' L v A,
  heap_ext h h' -> gext h G G' ->
  lhasp CT h G L v A -> lhasp CT h' G' L v A.
Proof.
  intros CT h h' G G' L v A Hext Hg (o & Ho & HA).
  destruct (heap_ext_getObj _ _ _ _ Hext Ho) as (o' & Ho' & Hrt).
  destruct (Hg v (runtime_getObj_dom _ _ _ Ho)) as (E1 & E2 & E3).
  exists o'. split; auto. destruct A as [q0 l D Us].
  rewrite E1. rewrite E3. rewrite Hrt. exact HA.
Qed.

Lemma lhasp_pop : forall CT h G L w0 v A,
  lhasp CT h G (w0 :: L) v A -> lhasp CT h G L v A.
Proof.
  intros CT h G L w0 v A (o & Ho & HA). exists o. split; auto.
  destruct A as [q0 l D Us]. destruct HA as (Hh & Vs & Hs & Hle).
  split; [eapply headL_pop; eauto|].
  exists Vs. split; auto. eapply Forall2_lagree_pop; eauto.
Qed.

Lemma olab_bound : forall n c,
  (forall w, c = Some w -> w < n) -> lab_bound n (olab c).
Proof. intros n [w|] H; simpl; auto. Qed.

Lemma lhasp_push : forall CT h G L next v A,
  (forall w, g_col G v = Some w -> w < next) ->
  Forall (lbound next) (g_args G v) ->
  lhasp CT h G L v A -> lbound next A ->
  lhasp CT h G (next :: L) v A.
Proof.
  intros CT h G L next v A Hc Hargs (o & Ho & HA) Hb. exists o. split; auto.
  destruct A as [q0 l D Us]. destruct HA as (Hh & Vs & Hs & Hle).
  apply lbound_node in Hb. destruct Hb as [Hl HUs].
  split; [apply headL_push; auto|].
  exists Vs. split; auto.
  apply Forall2_lagree_push; auto.
  eapply view_lbound; eauto. apply olab_bound. exact Hc.
Qed.

(* ------------------FIELDS BY DECLARING CLASS------------------*)

(** Field [f] of class [C] is declared in the superclass [D], with the
    definition [fd] as written there. *)
Inductive fdecl (CT : class_table)
    : class_name -> nat -> class_name -> field_def -> Prop :=
  | fd_own : forall C def P Ss pfs f fd
      (Hfind : find_class CT C = Some def)
      (Hsuper : super (signature def) = Some (P, Ss))
      (Hpcf : CollectFields CT P pfs)
      (Hge : length pfs <= f)
      (Hnth : nth_error (Syntax.fields (body def)) (f - length pfs) = Some fd),
      fdecl CT C f C fd
  | fd_inh : forall C def P Ss pfs f D fd
      (Hfind : find_class CT C = Some def)
      (Hsuper : super (signature def) = Some (P, Ss))
      (Hpcf : CollectFields CT P pfs)
      (Hlt : f < length pfs)
      (Hrest : fdecl CT P f D fd),
      fdecl CT C f D fd.

(* ------------------THE HEAP PART------------------*)

(** What is kept about one object: the header fits of its arguments (in
    the head view, which locates payloads, and in the payload view, which
    values use), and, when it is in a world, a payload of that world. *)
Definition obP (CT : class_table) (L : list nat) (qo : q_r) (c : option nat)
    (C : class_name) (As : list ltype) : Prop :=
  hinv CT L qo (olab c) C As /\
  (forall w, c = Some w -> pown CT L (LIn w) C As) /\
  (forall D Vs def,
     oview CT qo (olab c) C As D Vs ->
     find_class CT D = Some def ->
     frame_fitsp CT L (class_env def) (hfr CT qo (olab c) D Vs) /\
     fcoh CT L (class_env def) (hfr CT qo (olab c) D Vs)).

Record heapP (P : Loc -> Prop) (CT : class_table) (h : heap) (G : ghost)
    (L : list nat) (next : nat) : Prop := {
  (* an object in a world exists, is unprotected and is really mutable *)
  hp_col : forall l w, g_col G l = Some w ->
    l < dom h /\ ~ P l /\ r_muttype h l = Some Mut_r /\ w < next;
  (* the labelled type arguments are a labelling of the stored ones *)
  hp_erase : forall l o, runtime_getObj h l = Some o ->
    map erase (g_args G l) = rtargs (rt_type o);
  (* every field value inhabits the field's declared type, read at the class
     that declares it through the object's view at that class *)
  hp_fields : forall l o f D fd Vs v,
    runtime_getObj h l = Some o ->
    fdecl CT (rctype (rt_type o)) f D fd ->
    oview CT (rqtype (rt_type o)) (olab (g_col G l)) (rctype (rt_type o))
      (g_args G l) D Vs ->
    nth_error (fields_map o) f = Some (Iot v) ->
    lhasp CT h G L v
      (ldyn (hfr CT (rqtype (rt_type o)) (olab (g_col G l)) D Vs) (ftype fd));
  hp_live : forall w, List.In w L -> w < next;
  hp_bound : forall l, Forall (lbound next) (g_args G l);
  hp_obj : forall l o, runtime_getObj h l = Some o ->
    obP CT L (rqtype (rt_type o)) (g_col G l) (rctype (rt_type o)) (g_args G l);
  (* every object's class has bounds that leave nothing open, and the object
     has as many arguments as its class has parameters *)
  hp_cls : forall l o, runtime_getObj h l = Some o ->
    clsok CT (rctype (rt_type o)) (length (g_args G l));
}.

Lemma heapP_colbound : forall P CT h G L next l w,
  heapP P CT h G L next -> g_col G l = Some w -> w < next.
Proof.
  intros P CT h G L next l w HG Hc.
  destruct (hp_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & H). exact H.
Qed.

Lemma lhasp_push_heap : forall P CT h G L next v A,
  heapP P CT h G L next ->
  lhasp CT h G L v A -> lbound next A ->
  lhasp CT h G (next :: L) v A.
Proof.
  intros P CT h G L next v A HG Hl Hb.
  eapply lhasp_push; eauto.
  - intros w Hw. eapply heapP_colbound; eauto.
  - exact (hp_bound _ _ _ _ _ _ HG v).
Qed.

(* ------------------THE ACTIVATION PART------------------*)

Record frameP (CT : class_table) (sΓ : s_env) (rΓ : r_env) (h : heap)
    (G : ghost) (L : list nat) (next wf : nat) (mode : bool) (qthis : q_r)
    (lc lm : list ltype) : Prop := {
  fp_live : List.In wf L;
  fp_this : exists ι o,
    get_this_var_mapping (vars rΓ) = Some ι /\
    runtime_getObj h ι = Some o /\
    rqtype (rt_type o) = qthis /\
    (mode = true -> g_col G ι = Some wf);
  fp_ec : map erase lc = cargs rΓ;
  fp_em : map erase lm = margs rΓ;
  fp_bound : Forall (lbound next) lc /\ Forall (lbound next) lm;
  fp_vars : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) T);
}.

(** What a frame's own type variables satisfy: both kinds of fit. *)
Definition ffit (CT : class_table) (L : list nat) (Δ : tv_env) (F : lframe)
    : Prop :=
  frame_fits CT L Δ F /\ frame_fitsp CT L Δ F.

Lemma frameP_update : forall CT sΓ rΓ h G L next wf mode qthis lc lm x v Tx,
  frameP CT sΓ rΓ h G L next wf mode qthis lc lm ->
  x <> 0 ->
  static_getType sΓ x = Some Tx ->
  (forall w, v = Iot w ->
     lhasp CT h G L w (ldyn (act_frame qthis wf mode lc lm) Tx)) ->
  frameP CT sΓ (set_vars rΓ (update x v (vars rΓ))) h G L next wf mode qthis lc lm.
Proof.
  intros CT sΓ rΓ h G L next wf mode qthis lc lm x v Tx HF Hx HTx Hnew.
  constructor.
  - exact (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fp_this _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι & o & Hth & Hrest).
    exists ι, o. simpl. rewrite get_this_var_mapping_update; auto.
  - exact (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_bound _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - intros y T w HT Hv. unfold runtime_getVal in Hv. simpl in Hv.
    destruct (Nat.eq_dec x y) as [-> | Hne].
    + apply nth_error_update_same_inv in Hv. subst v.
      assert (T = Tx) by (unfold static_getType in *; congruence). subst T.
      apply Hnew. reflexivity.
    + rewrite update_diff in Hv; auto.
      eapply (fp_vars _ _ _ _ _ _ _ _ _ _ _ _ HF); eauto.
Qed.

Lemma frameP_ext : forall CT sΓ rΓ h h' G G' L next wf mode qthis lc lm,
  frameP CT sΓ rΓ h G L next wf mode qthis lc lm ->
  heap_ext h h' -> gext h G G' ->
  frameP CT sΓ rΓ h' G' L next wf mode qthis lc lm.
Proof.
  intros CT sΓ rΓ h h' G G' L next wf mode qthis lc lm HF Hext Hg.
  constructor.
  - exact (fp_live _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - destruct (fp_this _ _ _ _ _ _ _ _ _ _ _ _ HF) as (ι & o & Hth & Ho & Hq & Hm).
    destruct (heap_ext_getObj _ _ _ _ Hext Ho) as (o' & Ho' & Hrt).
    exists ι, o'. refine (conj Hth (conj Ho' (conj _ _))).
    + congruence.
    + intros Hmode. destruct (Hg ι (runtime_getObj_dom _ _ _ Ho)) as (E1 & _).
      rewrite E1. auto.
  - exact (fp_ec _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_em _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - exact (fp_bound _ _ _ _ _ _ _ _ _ _ _ _ HF).
  - intros x T v HT Hv.
    eapply lhasp_ext; eauto. exact (fp_vars _ _ _ _ _ _ _ _ _ _ _ _ HF x T v HT Hv).
Qed.

(* ------------------AN OBJECT AGAINST A STATIC VIEW------------------*)

(** One step: the object's reading of a header, with its payload, against
    the reading of the protected-mode view in a frame. *)
Lemma ostatic_step_cond : forall L mt F hq l qh pn As cs ms,
  readonly_state_method_scope mt ->
  (forall As0,
     label_cond2 L (fun q0 => q0) (vpa_q mt qh)
       (mk_lframe hq l l As0 []) (lf_with_args F cs ms)) ->
  (qh = Mut ->
   match pn with
   | Some (Mut, l') => norm L l' = norm L (lf_mut F)
   | _ => True
   end) ->
  lc2 L (rd_map false (fun q0 => q0) pn) (vpa_q mt qh)
    (hframe hq l pn As) (lf_with_args F cs ms).
Proof.
  intros L mt F hq l qh pn As cs ms Hrs Hbase Hpay q1.
  rewrite rd_map_obj.
  destruct (Hbase As q1) as [H1 H2]. cbn [hframe lf_q lf_with_args] in H1, H2 |- *.
  split; [exact H1|].
  destruct (q_eq_dec q1 Mut) as [-> | Hne].
  - destruct H2 as [H2 | [H2 | H2]]; auto.
    destruct (q_eq_dec qh Mut) as [-> | Hqh].
    + specialize (Hpay eq_refl).
      assert (Hst : vpa_q mt Mut Mut = Mut)
        by (destruct Hrs as [-> | ->]; reflexivity).
      rewrite Hst in H2 |- *.
      right. right. cbn [lab_of lf_mut lf_with_args] in H2 |- *.
      unfold hframe. cbn [lf_mut].
      destruct pn as [[qp lp]|]; [|exact H2].
      destruct (q_eq_dec qp Mut) as [-> | Hqp].
      * simpl rd_lab. exact Hpay.
      * rewrite (rd_lab_other l qp lp Hqp). exact H2.
    + left.
      assert (Hst : vpa_q mt qh Mut = Lost)
        by (destruct Hrs as [-> | ->]; destruct qh; simpl; congruence).
      rewrite Hst. reflexivity.
  - destruct H2 as [H2 | [H2 | H2]]; auto.
    right. right.
    assert (Hlab : lab_of (mk_lframe hq (rd_lab l pn) l As []) q1 =
                   lab_of (mk_lframe hq l l As []) q1).
    { destruct q1; simpl; try reflexivity; congruence. }
    rewrite Hlab. exact H2.
Qed.

(** The payloads along an object's views are of one label. *)
Definition opcoh (CT : class_table) (L : list nat) (qo : q_r) (l : lab)
    (C : class_name) (As : list ltype) (lm : lab) : Prop :=
  forall C' As', oview CT qo l C As C' As' ->
    forall l', pclassf CT C' As' = Some (Mut, l') -> norm L l' = norm L lm.

Lemma opcoh_step : forall CT L qo l C As lm P Ss,
  opcoh CT L qo l C As lm ->
  parent_lookup CT C = Some (P, Ss) ->
  opcoh CT L qo l P
    (hstep false (qr2q qo) (fun q0 => q0) l (pclassf CT C As) As Ss) lm.
Proof.
  intros CT L qo l C As lm P Ss H Hparent C' As' Hv.
  apply H. unfold oview in *. eapply v_step; eauto.
Qed.

(** The view of an object against the reading of a static protected-mode
    view. *)
Lemma oview_vs_static : forall CT mt qh C Ts D Vs,
  super_inst CT mt qh C Ts D Vs ->
  forall L F qo l As,
    readonly_state_method_scope mt ->
    (forall As0 cs ms,
       label_cond2 L (fun q0 => q0) (vpa_q mt qh)
         (mk_lframe (qr2q qo) l l As0 []) (lf_with_args F cs ms)) ->
    (qh = Mut -> opcoh CT L qo l C As (lf_mut F)) ->
    Forall2 (lagree L) As (map (ldyn F) Ts) ->
    exists Vs', oview CT qo l C As D Vs' /\
                Forall2 (lagree L) Vs' (map (ldyn F) Vs).
Proof.
  intros CT mt qh C Ts D Vs H.
  induction H; intros L F qo l As Hrs Hbase Hpc Hargs.
  - exists As. split; [apply v_refl | exact Hargs].
  - destruct (IHsuper_inst L F qo l
                (hstep false (qr2q qo) (fun q0 => q0) l (pclassf CT C As) As Ss)
                Hrs Hbase) as (Vs' & Hv & Hle).
    { intros Hqh. exact (opcoh_step _ _ _ _ _ _ _ _ _ (Hpc Hqh) Hparent). }
    { assert (Heq : map (ldyn F) (map (subst Ts []) (map (adapt mt qh) Ss)) =
                    map (fun S => ldyn (lf_with_args F (map (ldyn F) Ts) [])
                                    (map_qual (vpa_q mt qh) S)) Ss).
      { clear. induction Ss as [|S Ss IH]; simpl; auto.
        f_equal; auto. rewrite ldyn_subst. reflexivity. }
      rewrite Heq. unfold hstep.
      clear IHsuper_inst H Heq. generalize Ss as Ss0.
      induction Ss0 as [|S Ss0 IH]; simpl; [constructor|].
      constructor; [|exact IH].
      apply ldyn_agree2.
      - apply (ostatic_step_cond L mt F (qr2q qo) l qh (pclassf CT C As) As
                 (map (ldyn F) Ts) [] Hrs).
        + intros As0. apply Hbase.
        + intros Hqh.
          destruct (pclassf CT C As) as [[qp lp]|] eqn:Hp; auto.
          destruct qp; auto.
          apply (Hpc Hqh C As); [apply v_refl | exact Hp].
      - exact Hargs.
      - constructor. }
    exists Vs'. split; auto. unfold oview. eapply v_step; eauto.
Qed.

(** An object whose payload at its own class is of its own label has
    payloads of that label along every view. *)
Lemma opcoh_of_pown : forall CT L qo l C As,
  wf_class_table CT ->
  hinv CT L qo l C As -> pown CT L l C As -> opcoh CT L qo l C As l.
Proof.
  intros CT L qo l C As Hwf Hi Hk C' As' Hv l' Hp.
  destruct (hinv_oview CT L qo l C As C' As' Hwf Hv Hi) as [_ Hk'].
  destruct (Hk' Hk _ _ Hp) as [_ Hl]. exact Hl.
Qed.

Lemma opcoh_view : forall CT L qo l C As lm D Vs,
  opcoh CT L qo l C As lm -> oview CT qo l C As D Vs ->
  opcoh CT L qo l D Vs lm.
Proof.
  intros CT L qo l C As lm D Vs H Hv C' As' Hv'.
  apply H. eapply oview_trans; eauto.
Qed.

(* ------------------SUBTYPING KEEPS LABELS, FOR VALUES------------------*)

(** A value held at a type written mutable is exactly in the world. *)
Definition hexTp (G : ghost) (wf : nat) (T : qualified_type) (v : Loc) : Prop :=
  whead T = Some Mut -> g_col G v = Some wf.

(** Subtyping keeps labels.  The activation's world need not be live when
    the activation does not count its receiver as in the world; what is
    needed instead is that a value held at a type written mutable is exactly
    in that world, and this is kept too. *)
Lemma lhasp_subtype_ex : forall P CT Δ h G L next mt qthis wf mode lc lm ca ma,
  wf_class_table CT ->
  heapP P CT h G L next ->
  (mode = true -> List.In wf L) ->
  readonly_state_method_scope mt ->
  tv_mode Δ = mt ->
  (forall o n B v,
     tv_bound Δ o n = Some B ->
     wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) (TVar TVSub o n)) ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) B)) ->
  (forall o n B, tv_bound Δ o n = Some B -> whead B <> Some Mut) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ->
  map erase lc = ca -> map erase lm = ma ->
  forall T U,
    qualified_type_subtype CT Δ T U ->
    forall v,
      wf_r_typable CT h v T qthis ca ma ->
      hexTp G wf T v ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) T) ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) U) /\
      hexTp G wf U v.
Proof.
  intros P CT Δ h G L next mt qthis wf mode lc lm ca ma
    Hwf HG HwfL Hrs Hmode Hcb Hfl Hfb Hec Hem T U Hsub.
  set (Fc := act_frame qthis wf mode lc lm).
  induction Hsub; intros v Hty Hex Hl.
  - (* same class, widen the qualifier *)
    split.
    + destruct Hl as (o & Ho & Hh & Vs & Hs & Hle).
      exists o. split; auto. simpl. split.
      * unfold headL. intros Hm. inversion Hqsub; subst.
        -- apply Hh. exact Hm.
        -- simpl in Hm. discriminate.
        -- exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl).
      * exists Vs. split; auto.
        eapply Forall2_lagree_trans; [exact Hle|].
        apply map_ldyn_targ_sub; auto.
    + intros Hw. simpl in Hw. inversion Hw; subst q2. inversion Hqsub; subst.
      * apply Hex. reflexivity.
      * exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl).
  - (* up the hierarchy *)
    split; [|exact Hex].
    pose proof Hl as (o & Ho & Hh & As & Hs & Hle).
    rewrite Hmode in Hsuper.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hty)
      as (o' & Vs' & Ho' & Hhead & _).
    rewrite Ho in Ho'. inversion Ho'; subst o'. clear Ho'.
    assert (Hnb : q1 <> Bot).
    { intros ->. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl). }
    assert (Hcond : label_cond L (vpa_q mt q1)
                      (obj_frame (rqtype (rt_type o)) (g_col G v) (g_col G v) [])
                      Fc).
    { change (headL L (g_col G v) (dynq (qr2q qthis) q1) (lab_of Fc q1)) in Hh.
      unfold headL in Hh.
      apply rs_label_cond2; auto.
      - intros ->. pose proof (Hex eq_refl) as Hc. auto.
      - intros -> Hqo. rewrite Hqo in Hhead.
        assert (qthis = Mut_r).
        { destruct qthis; auto. unfold head_ok in Hhead. simpl in Hhead.
          destruct Hhead as [Hx | [Hx | Hx]]; discriminate. }
        subst qthis. specialize (Hh eq_refl).
        change (lab_of Fc RDM) with (if mode then LIn wf else LOut) in Hh.
        destruct mode.
        + rewrite (norm_live _ _ (HwfL eq_refl)) in Hh. exact Hh.
        + exact Hh. }
    destruct (oview_vs_static _ _ _ _ _ _ _ Hsuper L Fc (rqtype (rt_type o))
                (olab (g_col G v)) As Hrs) as (Vs0 & Hs0 & Hle0).
    + intros As0 cs ms q0. exact (Hcond q0).
    + intros ->.
      assert (Hc : g_col G v = Some wf) by (apply Hex; reflexivity).
      destruct (hp_obj _ _ _ _ _ _ HG v o Ho) as (Hi & Hk & _).
      specialize (Hk wf Hc). rewrite Hc in Hi, Hs |- *.
      eapply opcoh_view; [|exact Hs].
      apply opcoh_of_pown; auto.
    + exact Hle.
    + exists o. split; auto. simpl. split; [exact Hh|].
      exists Vs0. split; auto. eapply oview_trans; eauto.
  - split; assumption.
  - (* a type variable at its bound *)
    split.
    + eapply Hcb; eauto.
    + intros Hw. exfalso. exact (Hfl _ _ _ Hbound Hw).
  - (* widen the written qualifier of a variable use *)
    split.
    + destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
      simpl in *.
      destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
        as [qa la Ca Aa].
      simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
      split; [|eauto].
      unfold headL. intros Hm. inversion Hqsub; subst.
      * apply Hh. exact Hm.
      * simpl in Hm. discriminate.
      * exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ Hty). reflexivity.
    + intros Hw. simpl in Hw. inversion Hw; subst q2. inversion Hqsub; subst.
      * apply Hex. reflexivity.
      * exfalso. eapply (typable_whead_not_bot _ _ _ _ _ _ _ Hty). reflexivity.
  - (* view the supplied type as readonly *)
    split; [|intros Hw; simpl in Hw; discriminate].
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [|eauto]. unfold headL. intros Hm. discriminate.
  - (* a qualified variable use at an argument-free bound *)
    split; [|exact Hex].
    pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ Hfb
                  (qtype_qvar_bound CT Δ q1 o n qb C Hsub) Hty) as Hty'.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hty')
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
    split; [|intros Hw; simpl in Hw; discriminate].
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [unfold headL; intros Hm; discriminate|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub; auto.
  - (* compatible arguments under the same variable head *)
    split; [|intros Hw; simpl in Hw; discriminate].
    destruct Hl as (ob & Hob & Hl). exists ob. split; auto.
    simpl in *.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in *. destruct Hl as (Hh & Vs & Hs & Hle).
    split; [exact Hh|].
    exists Vs. split; auto.
    eapply Forall2_lagree_trans; [exact Hle|].
    apply map_ldyn_targ_sub; auto.
  - (* up the hierarchy under the same variable head *)
    split; [|intros Hw; simpl in Hw; discriminate].
    rewrite Hmode in Hsuper.
    destruct Hl as (ob & Hob & Hl).
    assert (Hcond : label_cond L (vpa_q mt RO)
                      (obj_frame (rqtype (rt_type ob)) (g_col G v) (g_col G v) [])
                      Fc).
    { apply rs_label_cond2; auto; try discriminate.
      unfold head_ok. left. reflexivity. }
    exists ob. split; auto.
    change (ldyn Fc (THead o n C Ts)) with
      (lheadby (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
         C (map (ldyn Fc) Ts)) in Hl.
    change (ldyn Fc (THead o n D Vs)) with
      (lheadby (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
         D (map (ldyn Fc) Vs)).
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl lheadby in *. destruct Hl as (Hh & As & Hs & Hle).
    destruct (oview_vs_static _ _ _ _ _ _ _ Hsuper L Fc (rqtype (rt_type ob))
                (olab (g_col G v)) As Hrs) as (Vs0 & Hs0 & Hle0).
    + intros As0 cs ms q0. exact (Hcond q0).
    + intros Hx. discriminate.
    + exact Hle.
    + split; [exact Hh|].
      exists Vs0. split; auto. eapply oview_trans; eauto.
  - (* the bottom-qualified type of the class *)
    exfalso. exact (typable_head_not_bot _ _ _ _ _ _ _ Hty eq_refl).
  - (* transitivity *)
    destruct (IHHsub1 v Hty Hex Hl) as [Hl2 Hex2].
    apply IHHsub2; auto.
    eapply wf_r_typable_subtype; eauto.
Qed.

(** In a live world, a value held at a type written mutable is exactly in
    it. *)
Lemma hexp_of_live : forall CT h G L qthis wf mode lc lm T v,
  List.In wf L ->
  lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) T) ->
  hexTp G wf T v.
Proof.
  intros CT h G L qthis wf mode lc lm T v HwfL Hl Hw.
  destruct T as [q0 C args | [|q0] o n | o n C args]; simpl in Hw;
    inversion Hw; subst.
  - destruct Hl as (ob & _ & Hh & _). specialize (Hh eq_refl).
    change (lab_of (act_frame qthis wf mode lc lm) Mut) with (LIn wf) in Hh.
    rewrite (norm_live _ _ HwfL) in Hh. exact Hh.
  - destruct Hl as (ob & _ & Hl). simpl in Hl.
    destruct (match tv_lookup o lc lm n with Some A => A | None => ldefault end)
      as [qa la Ca Aa].
    simpl in Hl. destruct Hl as (Hh & _). specialize (Hh eq_refl).
    rewrite (norm_live _ _ HwfL) in Hh. exact Hh.
Qed.

Lemma lhasp_subtype : forall P CT Δ h G L next mt qthis wf mode lc lm ca ma,
  wf_class_table CT ->
  heapP P CT h G L next ->
  List.In wf L ->
  readonly_state_method_scope mt ->
  tv_mode Δ = mt ->
  (forall o n B v,
     tv_bound Δ o n = Some B ->
     wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) (TVar TVSub o n)) ->
     lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) B)) ->
  (forall o n B, tv_bound Δ o n = Some B -> whead B <> Some Mut) ->
  frame_bounds_ok CT Δ (qr2q qthis) ca ma ->
  map erase lc = ca -> map erase lm = ma ->
  forall T U,
    qualified_type_subtype CT Δ T U ->
    forall v,
      wf_r_typable CT h v T qthis ca ma ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) T) ->
      lhasp CT h G L v (ldyn (act_frame qthis wf mode lc lm) U).
Proof.
  intros P CT Δ h G L next mt qthis wf mode lc lm ca ma
    Hwf HG HwfL Hrs Hmode Hcb Hfl Hfb Hec Hem T U Hsub v Hty Hl.
  destruct (lhasp_subtype_ex P CT Δ h G L next mt qthis wf mode lc lm ca ma
              Hwf HG (fun _ => HwfL) Hrs Hmode Hcb Hfl Hfb Hec Hem T U Hsub v Hty
              (hexp_of_live _ _ _ _ _ _ _ _ _ _ _ HwfL Hl) Hl) as [H _].
  exact H.
Qed.

(** A type variable used at its bound, from the payload-aware fit. *)
Lemma vbp_of_fits : forall CT Δ h G L F ca ma qthis,
  wf_class_table CT ->
  (forall v ob, runtime_getObj h v = Some ob ->
     clsok CT (rctype (rt_type ob)) (length (g_args G v))) ->
  (forall v ob def, runtime_getObj h v = Some ob ->
     find_class CT (rctype (rt_type ob)) = Some def ->
     vpa_mutability_runtime_bound_agree (rqtype (rt_type ob))
       (class_qualifier (signature def)) = true) ->
  frame_fitsp CT L Δ F ->
  lf_q F = qr2q qthis ->
  map erase (lf_cargs F) = ca -> map erase (lf_margs F) = ma ->
  forall o n B v,
    tv_bound Δ o n = Some B ->
    wf_r_typable CT h v (TVar TVSub o n) qthis ca ma ->
    lhasp CT h G L v (ldyn F (TVar TVSub o n)) ->
    lhasp CT h G L v (ldyn F B).
Proof.
  intros CT Δ h G L F ca ma qthis Hwf Hlv Hag Hfit Hq Hec Hem o n B v Hb Hty Hl.
  assert (Hty' : loc_has_rtype CT h v (erase (ldyn F (TVar TVSub o n)))).
  { rewrite erase_ldyn. rewrite Hq. rewrite Hec. rewrite Hem. exact Hty. }
  destruct (Hfit o n B Hb) as [Hf | [Hd | [Hi _]]].
  - eapply lsubtp_sound; eauto.
  - exfalso.
    destruct (ldyn F (TVar TVSub o n)) as [qa la Ca Aa].
    destruct Hl as (ob & Hob & _ & Vs & Hv & Hle). simpl in Hd.
    apply Hd. destruct (Hlv v ob Hob) as [Hlc Har]. split.
    + destruct (Nat.eq_dec (rctype (rt_type ob)) Ca) as [He | Hne].
      * rewrite <- He. exact Hlc.
      * eapply view_live; eauto.
    + intros dd Hdd. rewrite <- (Forall2_length Hle).
      eapply (view_arity _ _ _ _ _ _ _ _ _ Hwf Hv); eauto.
  - exfalso.
    destruct (ldyn F (TVar TVSub o n)) as [qa la Ca Aa].
    destruct Hi as (-> & di & Hdi & Himm).
    destruct Hl as (ob & Hob & _ & Vs & Hv & Hle).
    destruct (view_imm _ _ _ _ _ _ _ _ _ Hwf Hv di Hdi Himm) as (dc & Hdc & Hic).
    pose proof (Hag v ob dc Hob Hdc) as Hagree. rewrite Hic in Hagree.
    unfold loc_has_rtype in Hty'. rewrite Hob in Hty'. simpl in Hty'.
    destruct Hty' as [Hhead _]. unfold head_ok in Hhead.
    destruct (rqtype (rt_type ob)); simpl in Hagree; try discriminate.
    destruct Hhead as [Hx | [Hx | Hx]]; discriminate.
Qed.

(* ------------------WORLDS OPENING AND CLOSING------------------*)

Lemma lsubtp_pop : forall CT L w0 A B,
  lsubtp CT (w0 :: L) A B -> lsubtp CT L A B.
Proof.
  intros CT L w0 [q1 l1 C As] [q2 l2 D Bs] H.
  destruct H as [H | (Hrq & Hl & Vs & Hv & Hle)]; [left; exact H|].
  right. refine (conj Hrq (conj _ _)).
  - intros Hm. apply (norm_pop L w0). exact (Hl Hm).
  - exists Vs. split; auto. eapply Forall2_lagree_pop; eauto.
Qed.

Lemma lsubtp_push : forall CT L n A B,
  lsubtp CT L A B -> lbound n A -> lbound n B -> lsubtp CT (n :: L) A B.
Proof.
  intros CT L n [q1 l1 C As] [q2 l2 D Bs] H HA HB.
  apply lbound_node in HA. destruct HA as [Hl1 HAs].
  apply lbound_node in HB. destruct HB as [Hl2 HBs].
  destruct H as [H | (Hrq & Hl & Vs & Hv & Hle)]; [left; exact H|].
  right. refine (conj Hrq (conj _ _)).
  - intros Hm. rewrite (norm_push L n l1 Hl1). rewrite (norm_push L n l2 Hl2).
    exact (Hl Hm).
  - exists Vs. split; auto. apply Forall2_lagree_push; auto.
    eapply view_lbound; eauto.
Qed.

Lemma frame_fitsp_pop : forall CT L w0 Δ F,
  frame_fitsp CT (w0 :: L) Δ F -> frame_fitsp CT L Δ F.
Proof.
  intros CT L w0 Δ F H o n B Hb.
  destruct (H o n B Hb) as [Hx | [Hx | [Hi Hx]]];
    [left; eapply lsubtp_pop; eauto | right; left; exact Hx
    | right; right; split; [exact Hi | eapply lsubtp_pop; eauto]].
Qed.

Lemma frame_fitsp_push : forall CT L n Δ F,
  frame_bound n F -> frame_fitsp CT L Δ F -> frame_fitsp CT (n :: L) Δ F.
Proof.
  intros CT L n Δ F HF H o m B Hb.
  destruct (H o m B Hb) as [Hx | [Hx | [Hi Hx]]];
    [left | right; left; exact Hx | right; right; split; [exact Hi|]].
  - apply lsubtp_push; auto using ldyn_lbound.
  - apply lsubtp_push; auto using ldyn_lbound.
    pose proof (ldyn_lbound n F (TVar TVSub o m) HF) as Hlb.
    destruct (ldyn F (TVar TVSub o m)) as [qa la Ca Aa].
    apply lbound_node in Hlb. destruct Hlb as [_ Hargs].
    apply lbound_node. split; [exact I | exact Hargs].
Qed.

Lemma frame_fits_pop : forall CT L w0 Δ F,
  frame_fits CT (w0 :: L) Δ F -> frame_fits CT L Δ F.
Proof. intros CT L w0 Δ F H o n B Hb. eapply lsubt_pop. eauto. Qed.

Lemma frame_fits_push : forall CT L n Δ F,
  frame_bound n F -> frame_fits CT L Δ F -> frame_fits CT (n :: L) Δ F.
Proof.
  intros CT L n Δ F HF H o m B Hb.
  apply lsubt_push; auto using ldyn_lbound.
Qed.

Lemma hfr_bound : forall CT n qo l C As,
  lab_bound n l -> Forall (lbound n) As -> frame_bound n (hfr CT qo l C As).
Proof.
  intros CT n qo l C As Hl HAs. unfold frame_bound, hfr, hframe. simpl.
  repeat split; auto.
  apply rd_lab_bound; auto. intros q0 l0 Hp. eapply pclassf_lbound; eauto.
Qed.

Lemma hinv_pop : forall CT L w0 qo l C As,
  hinv CT (w0 :: L) qo l C As -> hinv CT L qo l C As.
Proof.
  intros CT L w0 qo l C As (Hfit & Hlf & Hcls).
  refine (conj _ (conj Hlf _)).
  - intros def Hfd. eapply frame_fits_pop. eauto.
  - intros def Hfd. destruct (Hcls def Hfd) as [Hag Hmc]. split; auto.
    intros Hm. apply (norm_pop L w0). exact (Hmc Hm).
Qed.

Lemma hinv_push : forall CT L n qo l C As,
  lab_bound n l -> Forall (lbound n) As ->
  hinv CT L qo l C As -> hinv CT (n :: L) qo l C As.
Proof.
  intros CT L n qo l C As Hl HAs (Hfit & Hlf & Hcls).
  pose proof (hfr_bound CT n qo l C As Hl HAs) as HFb.
  refine (conj _ (conj Hlf _)).
  - intros def Hfd. apply frame_fits_push; auto.
  - intros def Hfd. destruct (Hcls def Hfd) as [Hag Hmc]. split; auto.
    intros Hm. destruct HFb as (Hb1 & _).
    rewrite (norm_push L n _ Hb1). rewrite (norm_push L n l Hl). exact (Hmc Hm).
Qed.

Lemma pown_pop : forall CT L w0 l C As,
  pown CT (w0 :: L) l C As -> pown CT L l C As.
Proof.
  intros CT L w0 l C As H q' l' Hp. destruct (H q' l' Hp) as [Hq Hl].
  split; auto. apply (norm_pop L w0). exact Hl.
Qed.

Lemma pown_push : forall CT L n l C As,
  lab_bound n l -> Forall (lbound n) As ->
  pown CT L l C As -> pown CT (n :: L) l C As.
Proof.
  intros CT L n l C As Hl HAs H q' l' Hp. destruct (H q' l' Hp) as [Hq Hl'].
  split; auto.
  rewrite (norm_push L n l' (pclassf_lbound _ _ _ _ _ _ HAs Hp)).
  rewrite (norm_push L n l Hl). exact Hl'.
Qed.

Lemma pcoh_pop : forall CT L w0 q0 l C As lm,
  pcoh CT (w0 :: L) q0 l C As lm -> pcoh CT L q0 l C As lm.
Proof.
  intros CT L w0 q0 l C As lm H C' As' Hv. specialize (H C' As' Hv).
  destruct (pclassf CT C' As') as [[q' l']|]; auto. destruct q'; auto.
  apply (norm_pop L w0). exact H.
Qed.

Lemma pcoh_push : forall CT L n q0 l C As lm,
  lab_bound n l -> Forall (lbound n) As -> lab_bound n lm ->
  pcoh CT L q0 l C As lm -> pcoh CT (n :: L) q0 l C As lm.
Proof.
  intros CT L n q0 l C As lm Hl HAs Hlm H C' As' Hv. specialize (H C' As' Hv).
  pose proof (view_lbound _ _ _ _ _ _ _ _ _ n Hv Hl HAs) as HAs'.
  destruct (pclassf CT C' As') as [[q' l']|] eqn:Hp; auto. destruct q'; auto.
  rewrite (norm_push L n l' (pclassf_lbound _ _ _ _ _ _ HAs' Hp)).
  rewrite (norm_push L n lm Hlm). exact H.
Qed.

Lemma fcoh_pop : forall CT L w0 Δ F,
  fcoh CT (w0 :: L) Δ F -> fcoh CT L Δ F.
Proof.
  intros CT L w0 Δ F H o n K Bs Hb Hnd Hsn. specialize (H o n K Bs Hb Hnd Hsn).
  destruct (ldyn F (TVar TVSub o n)) as [qA lA CA AsA]. simpl in H |- *.
  intros Hq Va Hva. eapply pcoh_pop. eauto.
Qed.

Lemma fcoh_push : forall CT L n Δ F,
  frame_bound n F -> fcoh CT L Δ F -> fcoh CT (n :: L) Δ F.
Proof.
  intros CT L n Δ F HF H o m K Bs Hb Hnd Hsn. specialize (H o m K Bs Hb Hnd Hsn).
  pose proof (ldyn_lbound n F (TVar TVSub o m) HF) as Hlb.
  destruct (ldyn F (TVar TVSub o m)) as [qA lA CA AsA]. simpl in H |- *.
  apply lbound_node in Hlb. destruct Hlb as [HlA HAs].
  intros Hq Va Hva. apply pcoh_push; auto.
  unfold tview in Hva. eapply view_lbound; eauto.
Qed.

Lemma obP_pop : forall CT L w0 qo c C As,
  obP CT (w0 :: L) qo c C As -> obP CT L qo c C As.
Proof.
  intros CT L w0 qo c C As (Hi & Hk & Hf).
  refine (conj (hinv_pop _ _ _ _ _ _ _ Hi) (conj _ _)).
  - intros w Hc. eapply pown_pop. eauto.
  - intros D Vs def Hv Hfd. destruct (Hf D Vs def Hv Hfd) as [H1 H2]. split.
    + eapply frame_fitsp_pop. eauto.
    + eapply fcoh_pop. eauto.
Qed.

Lemma obP_push : forall CT L n qo c C As,
  (forall w, c = Some w -> w < n) -> Forall (lbound n) As ->
  obP CT L qo c C As -> obP CT (n :: L) qo c C As.
Proof.
  intros CT L n qo c C As Hc HAs (Hi & Hk & Hf).
  pose proof (olab_bound n c Hc) as Hl.
  refine (conj (hinv_push _ _ _ _ _ _ _ Hl HAs Hi) (conj _ _)).
  - intros w Hw. apply pown_push; auto. simpl. apply Hc. exact Hw.
  - intros D Vs def Hv Hfd. destruct (Hf D Vs def Hv Hfd) as [H1 H2].
    assert (HFb : frame_bound n (hfr CT qo (olab c) D Vs)).
    { apply hfr_bound; auto. eapply view_lbound; eauto. }
    split; [apply frame_fitsp_push | apply fcoh_push]; auto.
Qed.

(** Opening a fresh world keeps the heap part of the invariant. *)
Lemma heapP_push : forall P CT h G L next,
  heapP P CT h G L next -> heapP P CT h G (next :: L) (S next).
Proof.
  intros P CT h G L next HG.
  assert (Hcb : forall l w, g_col G l = Some w -> w < next).
  { intros l w Hw. eapply heapP_colbound; eauto. }
  constructor.
  - intros l w Hc. destruct (hp_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
    repeat split; auto.
  - exact (hp_erase _ _ _ _ _ _ HG).
  - intros l o f D fd Vs v Ho Hfd Hv Hn.
    eapply lhasp_push_heap; eauto.
    + eapply (hp_fields _ _ _ _ _ _ HG); eauto.
    + apply ldyn_lbound. apply hfr_bound.
      * apply olab_bound. apply Hcb.
      * eapply view_lbound; eauto.
        -- apply olab_bound. apply Hcb.
        -- exact (hp_bound _ _ _ _ _ _ HG l).
  - intros w [<- | Hin]; [lia|].
    pose proof (hp_live _ _ _ _ _ _ HG _ Hin). lia.
  - intros l. eapply Forall_lbound_mono; [|exact (hp_bound _ _ _ _ _ _ HG l)]. lia.
  - intros l o Ho. apply obP_push.
    + apply Hcb.
    + exact (hp_bound _ _ _ _ _ _ HG l).
    + exact (hp_obj _ _ _ _ _ _ HG l o Ho).
  - exact (hp_cls _ _ _ _ _ _ HG).
Qed.

(** Closing a world keeps the heap part of the invariant. *)
Lemma heapP_pop : forall P CT h G L w0 next,
  heapP P CT h G (w0 :: L) next -> heapP P CT h G L next.
Proof.
  intros P CT h G L w0 next HG. constructor.
  - exact (hp_col _ _ _ _ _ _ HG).
  - exact (hp_erase _ _ _ _ _ _ HG).
  - intros l o f D fd Vs v Ho Hfd Hv Hn.
    eapply lhasp_pop. eapply (hp_fields _ _ _ _ _ _ HG); eauto.
  - intros w Hin. apply (hp_live _ _ _ _ _ _ HG). right. exact Hin.
  - exact (hp_bound _ _ _ _ _ _ HG).
  - intros l o Ho. eapply obP_pop. exact (hp_obj _ _ _ _ _ _ HG l o Ho).
  - exact (hp_cls _ _ _ _ _ _ HG).
Qed.

(* ------------------INHERITED FIELDS------------------*)

Lemma map_qual_requalify : forall g q0 U,
  map_qual g (requalify q0 U) = requalify (g q0) (map_qual g U).
Proof. intros g q0 [q1 C args|u o n|? ? ? ?]; simpl; auto. destruct u; auto. Qed.

Lemma map_qual_headby : forall g U C args,
  map_qual g (headby U C args) =
  headby (map_qual g U) C (map (map_qual g) args).
Proof. intros g [q1 C1 a|[|qv] o n|o n C1 a] C args; reflexivity. Qed.

(** Adapting a substituted type is substituting adapted types. *)
Lemma map_qual_subst : forall g Ts Us T,
  g RO = RO ->
  map_qual g (subst Ts Us T) =
  subst (map (map_qual g) Ts) (map (map_qual g) Us) (map_qual g T).
Proof.
  intros g Ts Us T Hro. induction T using qualified_type_ind'.
  - simpl. f_equal. rewrite !map_map.
    induction H; simpl; auto. f_equal; auto.
  - assert (HU : map_qual g
                   match tv_lookup o Ts Us n with
                   | Some U => U | None => default_type end =
                 match tv_lookup o (map (map_qual g) Ts) (map (map_qual g) Us) n with
                 | Some U => U | None => default_type end).
    { rewrite tv_lookup_map. destruct (tv_lookup o Ts Us n); simpl; auto.
      rewrite Hro. reflexivity. }
    destruct u; simpl.
    + exact HU.
    + rewrite map_qual_requalify. rewrite HU. reflexivity.
  - assert (HU : map_qual g
                   match tv_lookup o Ts Us n with
                   | Some U => U | None => default_type end =
                 match tv_lookup o (map (map_qual g) Ts) (map (map_qual g) Us) n with
                 | Some U => U | None => default_type end).
    { rewrite tv_lookup_map. destruct (tv_lookup o Ts Us n); simpl; auto.
      rewrite Hro. reflexivity. }
    cbn [subst map_qual]. rewrite map_qual_headby. rewrite HU. f_equal.
    rewrite !map_map. induction H; simpl; auto. f_equal; auto.
Qed.

Lemma collect_fields_step : forall CT C def P Ss pfs fs,
  find_class CT C = Some def ->
  super (signature def) = Some (P, Ss) ->
  CollectFields CT P pfs ->
  CollectFields CT C fs ->
  fs = map (subst_field Ss) pfs ++ Syntax.fields (body def).
Proof.
  intros CT C def P Ss pfs fs Hfind Hsuper Hpcf Hcf.
  eapply collect_fields_deterministic_rel; [exact Hcf|].
  eapply CF_Inherit; eauto.
Qed.

(** A field found in a class's field list is declared somewhere above. *)
Lemma fdecl_of_collect : forall CT C fs,
  CollectFields CT C fs ->
  forall f fd, nth_error fs f = Some fd -> exists D fd0, fdecl CT C f D fd0.
Proof.
  intros CT C fs H. induction H; intros f fd Hn.
  - destruct f; discriminate.
  - destruct f; discriminate.
  - destruct (Nat.lt_ge_cases f (length parent_fields)) as [Hlt | Hge].
    + rewrite nth_error_app1 in Hn; [rewrite length_map; exact Hlt|].
      rewrite nth_error_map in Hn.
      destruct (nth_error parent_fields f) as [fdP|] eqn:HnP; [|discriminate].
      destruct (IHCollectFields f fdP HnP) as (D & fd0 & Hd).
      exists D, fd0. eapply fd_inh; eauto.
    + rewrite nth_error_app2 in Hn; [rewrite length_map; exact Hge|].
      rewrite length_map in Hn. subst own_fields.
      exists C, fd. eapply fd_own; eauto.
Qed.

(** The field, read by the object at its declaring class, against the
    reading of its adapted type as found in a subclass's field list. *)
Lemma field_chain : forall CT C f D fd0,
  fdecl CT C f D fd0 ->
  forall fs fd, CollectFields CT C fs -> nth_error fs f = Some fd ->
  forall L Fc g qo l As W,
    g RO = RO ->
    (forall C' As', oview CT qo l C As C' As' ->
       forall cs,
         lc2 L (fun q0 => q0) g
           (hframe (qr2q qo) l (pclassf CT C' As') As') (lf_with_args Fc cs [])) ->
    Forall2 (lagree L) As W ->
    exists V,
      oview CT qo l C As D V /\
      assignability fd0 = assignability fd /\
      lagree L (ldyn (hfr CT qo l D V) (ftype fd0))
        (ldyn (lf_with_args Fc W []) (map_qual g (ftype fd))).
Proof.
  intros CT C f D fd0 H.
  induction H; intros fs fd1 Hcf Hn L Fc g qo l As W Hro Hstep Hle.
  - (* declared here *)
    rewrite (collect_fields_step _ _ _ _ _ _ _ Hfind Hsuper Hpcf Hcf) in Hn.
    rewrite nth_error_app2 in Hn; [rewrite length_map; exact Hge|].
    rewrite length_map in Hn. rewrite Hnth in Hn. inversion Hn; subst fd1.
    exists As. refine (conj (v_refl _ _ _ _ _ _ _) (conj eq_refl _)).
    rewrite <- (map_qual_id (ftype fd)) at 1.
    apply ldyn_agree2.
    + unfold hfr. apply (Hstep C As). apply v_refl.
    + exact Hle.
    + constructor.
  - (* inherited *)
    rewrite (collect_fields_step _ _ _ _ _ _ _ Hfind Hsuper Hpcf Hcf) in Hn.
    rewrite nth_error_app1 in Hn; [rewrite length_map; exact Hlt|].
    rewrite nth_error_map in Hn.
    destruct (nth_error pfs f) as [fdP|] eqn:HnP; [|discriminate].
    simpl in Hn. inversion Hn; subst fd1. clear Hn.
    assert (Hparent : parent_lookup CT C = Some (P, Ss)).
    { unfold parent_lookup. rewrite Hfind. exact Hsuper. }
    set (As' := hstep false (qr2q qo) (fun q0 => q0) l (pclassf CT C As) As Ss).
    set (W' := map (fun S => ldyn (lf_with_args Fc W []) (map_qual g S)) Ss).
    assert (Hle' : Forall2 (lagree L) As' W').
    { unfold As', W', hstep. rewrite rd_map_obj. generalize Ss as Ss0.
      induction Ss0 as [|S Ss0 IH]; simpl; [constructor|].
      constructor; [|exact IH].
      apply ldyn_agree2.
      - apply (Hstep C As). apply v_refl.
      - exact Hle.
      - constructor. }
    destruct (IHfdecl pfs fdP Hpcf HnP L Fc g qo l As' W' Hro) as (V & Hv & Ha & Hag);
      auto.
    { intros C' As'' Hv' cs. apply Hstep. unfold oview in *.
      eapply v_step; eauto. }
    exists V. refine (conj _ (conj Ha _)).
    + unfold oview in *. eapply v_step; eauto.
    + simpl ftype. rewrite (map_qual_subst g Ss [] (ftype fdP) Hro).
      rewrite ldyn_subst. simpl map.
      assert (HW : map (ldyn (lf_with_args Fc W [])) (map (map_qual g) Ss) = W').
      { unfold W'. rewrite map_map. reflexivity. }
      rewrite HW. exact Hag.
Qed.

Print Assumptions oview_vs_static.
Print Assumptions lhasp_subtype.
Print Assumptions heapP_push.
Print Assumptions field_chain.

(* ------------------A NEW OBJECT------------------*)

(** The new object reads its headers as the allocating code reads them
    through the allocation qualifier. *)
Lemma new_step_cond : forall L mt qthis qc wf mode lc lm pn As' cs,
  readonly_state_method_scope mt ->
  (qc = Mut_c -> forall q' l', pn = Some (q', l') ->
     q' = Mut /\ norm L l' = norm L (LIn wf)) ->
  lc2 L (fun q0 => q0) (vpa_q mt (qc2q qc))
    (hframe (qr2q (vpa_mutability_object_creation qthis qc))
       (olab (new_color qc wf mode)) pn As')
    (lf_with_args (act_frame qthis wf mode lc lm) cs []).
Proof.
  intros L mt qthis qc wf mode lc lm pn As' cs Hrs Hpn q0.
  assert (HM : qc = Mut_c -> norm L (rd_lab (LIn wf) pn) = norm L (LIn wf)).
  { intros Hq. destruct pn as [[q' l']|]; simpl; auto.
    destruct (Hpn Hq q' l' eq_refl) as [-> Hl]. exact Hl. }
  destruct Hrs as [-> | ->]; destruct qc, q0, qthis, mode;
    cbv [hframe act_frame lf_with_args lf_q lab_of lf_mut lf_rdm vpa_q
         vpa_mutability_qq_readonly_state qc2q qr2q dynq
         vpa_mutability_object_creation new_color olab arg_q_sub];
    (split;
     [ solve [left; reflexivity] || solve [right; split; auto]
     | solve [left; reflexivity] || solve [right; left; discriminate]
       || solve [right; right; reflexivity]
       || solve [right; right; apply HM; reflexivity] ]).
Qed.

Lemma alloc_obP : forall CT L Δ qthis wf mode lc lm qc C def Ts,
  wf_class_table CT ->
  readonly_state_method_scope (tv_mode Δ) ->
  (forall o n B, tv_bound Δ o n = Some B -> is_class_type B) ->
  ffit CT L Δ (act_frame qthis wf mode lc lm) ->
  fcoh CT L Δ (act_frame qthis wf mode lc lm) ->
  Forall rlost_free (map erase lc) -> Forall rlost_free (map erase lm) ->
  find_class CT C = Some def ->
  vpa_mutability_bound (qc2q qc) (class_qualifier (signature def)) = qc2q qc ->
  Forall lost_free Ts -> Forall (sbnd CT Δ) Ts ->
  Forall2
    (fun T B =>
       lost_free (member_type AbstractState (qc2q qc) Ts [] B) /\
       bound_sub CT Δ T (member_type AbstractState (qc2q qc) Ts [] B))
    Ts (ctparams (signature def)) ->
  obP CT L (vpa_mutability_object_creation qthis qc) (new_color qc wf mode) C
    (map (ldyn (act_frame qthis wf mode lc lm)) Ts).
Proof.
  intros CT L Δ qthis wf mode lc lm qc C def Ts Hwf Hrs Hbc [Hfits Hfitp] Hcoh
    Hlc Hlm Hfind Hqc HlfT HsbT Hbounds.
  destruct (alloc_hinv CT L Δ qthis wf mode lc lm qc C def Ts Hwf Hrs Hfits Hlc
              Hlm Hfind Hqc HlfT Hbounds) as [Hi Hk].
  refine (conj Hi (conj _ _)).
  - intros w Hc.
    assert (w = wf) by (destruct qc, mode; simpl in Hc; congruence). subst w.
    exact (Hk Hc).
  - intros D Vs dd Hv Hfd.
    eapply (fitsp_oview CT L _ _ C _ D Vs Hwf Hv Hi); [|exact Hfd].
    intros d0 Hd0. rewrite Hfind in Hd0. inversion Hd0; subst d0.
    eapply alloc_fitsp; eauto.
Qed.

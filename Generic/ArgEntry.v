From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases GhostOverride ArgClean ArgOverride GhostCall ArgCall GhostEntry ArgMain.

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
  - unfold oview. eapply v_step; [exact Hparent|].
    replace (hstep false (qr2q q) (fun q0 => q0) LOut
               (pclassf CT C (map lift Rs)) (map lift Rs) Ss)
      with (map lift (map (dyn qo Rs [] []) Ss)); [apply IH; auto|].
    subst qo. rewrite hstep_obj.
    change (hframe (qr2q q) LOut (pclassf CT C (map lift Rs)) (map lift Rs))
      with (hfr CT q LOut C (map lift Rs)).
    rewrite hfr_lift. rewrite map_map. apply map_ext. intros T. symmetry.
    apply ldyn_lift_obj.
Qed.

Lemma lhasp_lift : forall CT h L v R,
  loc_has_rtype CT h v R -> lhasp CT h (g_init h) L v (lift R).
Proof.
  intros CT h L v R. unfold loc_has_rtype.
  destruct (runtime_getObj h v) as [o|] eqn:Ho; [|contradiction].
  destruct R as [rq D Us]. intros [Hh (Vs & Hs & Hle)].
  exists o. split; auto. simpl lift. split.
  - unfold headL. intros _. simpl. intros w Hw. discriminate.
  - exists (map lift Vs). split.
    + simpl. rewrite Ho. apply oview_lift. exact Hs.
    + clear - Hle. induction Hle; simpl; constructor; auto using lagree_lift.
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
  destruct (Hroots Hrs) as [Hnm_recv Hnm_par].
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

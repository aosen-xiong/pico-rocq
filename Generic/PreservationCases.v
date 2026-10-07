From Stdlib Require Import List Lia.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas.

(** Per-statement lemmas for type preservation. *)

(* ------------------CLASS TABLE FACTS------------------*)

Lemma wf_class_table_class : forall CT C def,
  wf_class_table CT -> find_class CT C = Some def -> wf_class CT def.
Proof.
  intros CT C def [Hall _] Hfind.
  rewrite Forall_forall in Hall. apply Hall.
  unfold find_class, gget in Hfind. eapply nth_error_In; eauto.
Qed.

Lemma wf_class_table_supers_in_dom : forall CT,
  wf_class_table CT -> supers_in_dom CT.
Proof.
  intros CT Hwf C P Ss Hparent. unfold parent_lookup in Hparent.
  destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
  pose proof (wf_class_table_class _ _ _ Hwf Hfind) as Hcls.
  inversion Hcls; subst.
  - congruence.
  - rewrite Hsuper in Hparent. inversion Hparent; subst.
    eapply find_class_dom; eauto.
Qed.

(** A class declared mutable or immutable pins that mutability for all its
    subclasses. *)
Lemma base_subtype_pinned : forall CT C D,
  wf_class_table CT ->
  base_subtype CT C D ->
  forall dD, find_class CT D = Some dD ->
  class_qualifier (signature dD) <> RDM_c ->
  exists dC, find_class CT C = Some dC /\
             class_qualifier (signature dC) = class_qualifier (signature dD).
Proof.
  intros CT C D Hwf Hsub. induction Hsub; intros dD HD Hpin.
  - eauto.
  - destruct (IHHsub2 Hwf dD HD Hpin) as [dM [HM HqM]].
    destruct (IHHsub1 Hwf dM HM) as [dC [HC HqC]]; [congruence|].
    exists dC. split; auto. congruence.
  - unfold parent_lookup in Hparent.
    destruct (find_class CT C) as [dC|] eqn:HC; [|discriminate].
    exists dC. split; auto.
    pose proof (wf_class_table_class _ _ _ Hwf HC) as Hcls.
    inversion Hcls; subst.
    + congruence.
    + rewrite Hsuper in Hparent. inversion Hparent; subst.
      assert (super_def = dD) by congruence. subst super_def.
      destruct H3 as [Heq | Hrdm]; [exact Heq | contradiction].
Qed.

(* ------------------FIELD INHERITANCE------------------*)

Lemma CollectFields_inherit_inv : forall CT C P Ss fs,
  parent_lookup CT C = Some (P, Ss) ->
  CollectFields CT C fs ->
  exists def pfs,
    find_class CT C = Some def /\
    CollectFields CT P pfs /\
    fs = map (subst_field Ss) pfs ++ Syntax.fields (body def).
Proof.
  intros CT C P Ss fs Hparent Hcf. unfold parent_lookup in Hparent.
  inversion Hcf; subst.
  - rewrite Hnone in Hparent. discriminate.
  - rewrite Hfind in Hparent. congruence.
  - rewrite Hfind in Hparent. rewrite Hsuper in Hparent.
    inversion Hparent; subst. eauto.
Qed.

(** A field found in a superclass is found at the same index in the subclass,
    with the same assignability, and its declared type read in the object's
    own arguments equals the superclass declaration read in the object's
    arguments viewed at the superclass. *)
Lemma field_inherit : forall CT qo Co Ro C Vs,
  rsuper_inst CT qo Co Ro C Vs ->
  forall fsC fsO f fd,
    CollectFields CT C fsC ->
    CollectFields CT Co fsO ->
    nth_error fsC f = Some fd ->
    exists fd',
      nth_error fsO f = Some fd' /\
      assignability fd' = assignability fd /\
      dyn qo Ro [] (ftype fd') = dyn qo Vs [] (ftype fd).
Proof.
  intros CT qo Co Ro C Vs H.
  induction H; intros fsC fsO f fd HcfC HcfO Hnth.
  - assert (fsO = fsC) by eauto using collect_fields_deterministic_rel.
    subst. eauto.
  - destruct (CollectFields_inherit_inv _ _ _ _ _ Hparent HcfO)
      as (def & pfs & Hfind & Hpcf & ->).
    destruct (IHrsuper_inst fsC pfs f fd HcfC Hpcf Hnth)
      as (fdP & HnthP & Hassign & Hdyn).
    exists (subst_field Ss fdP). split; [|split].
    + rewrite nth_error_app1.
      * rewrite length_map. apply nth_error_Some. congruence.
      * rewrite nth_error_map. rewrite HnthP. reflexivity.
    + exact Hassign.
    + simpl. rewrite dyn_subst. simpl. exact Hdyn.
Qed.

(* ------------------LOCAL DECLARATION------------------*)

Lemma get_this_var_mapping_app_null_last : forall vs,
  get_this_var_mapping (vs ++ [Null_a]) = get_this_var_mapping vs.
Proof.
  intros vs. destruct vs; reflexivity.
Qed.

Lemma preservation_local : forall CT Δ sΓ rΓ h T,
  wf_r_config CT Δ sΓ rΓ h ->
  wf_stypeuse CT Δ T ->
  wf_r_config CT Δ (sΓ ++ [T]) (set_vars rΓ (vars rΓ ++ [Null_a])) h.
Proof.
  intros CT Δ sΓ rΓ h T Hwf HT.
  destruct Hwf as (Hct & Hheap & Hrenv & Hsenv & Hframe & Hlen & Hcorr).
  refine (conj Hct (conj Hheap (conj _ (conj _ (conj _ (conj _ _)))))).
  - destruct Hrenv as (Hd & Hthis & Hall).
    refine (conj _ (conj _ _)); simpl.
    + rewrite length_app. lia.
    + rewrite get_this_var_mapping_app_null_last. exact Hthis.
    + apply Forall_app. split; auto.
  - destruct Hsenv as [Hd Hall]. split.
    + rewrite length_app. lia.
    + apply Forall_app. split; auto.
  - destruct Hframe as (ι & o & Cthis & Hthis & Hrest).
    exists ι, o, Cthis. simpl.
    rewrite get_this_var_mapping_app_null_last. auto.
  - simpl. rewrite !length_app. simpl. lia.
  - intros ι qcontext Hthis Hmut i Hi sqt Hnth.
    simpl in Hthis. rewrite get_this_var_mapping_app_null_last in Hthis.
    unfold runtime_getVal. simpl.
    destruct (Nat.lt_ge_cases i (dom sΓ)) as [Hlt | Hge].
    + rewrite nth_error_app1 in Hnth; auto.
      rewrite nth_error_app1; [lia|].
      apply (Hcorr ι qcontext Hthis Hmut i Hlt sqt Hnth).
    + rewrite length_app in Hi. simpl in Hi.
      assert (i = dom (vars rΓ)) by lia. subst i.
      rewrite nth_error_app2; [lia|].
      replace (dom (vars rΓ) - dom (vars rΓ)) with 0 by lia. exact I.
Qed.

(* ------------------EXPRESSIONS------------------*)

Lemma ubound_subtype : forall CT Δ T U,
  ubound Δ T = Some U -> T = U \/ qualified_type_subtype CT Δ T U.
Proof.
  intros CT Δ T U H. destruct T as [q0 C Ts | u o n | o n C Ts]; simpl in H.
  - left. congruence.
  - destruct (tv_bound Δ o n) as [B|] eqn:Hb; [|destruct u; discriminate].
    destruct B as [qb C Ts| |]; [|destruct u; discriminate..].
    destruct u as [|q0].
    + inversion H; subst. right. apply qtype_var_bound; auto.
    + destruct Ts; [|discriminate]. inversion H; subst.
      right. eapply qtype_qvar_bound. apply qtype_var_bound. exact Hb.
  - destruct (tv_bound Δ o n) as [B|] eqn:Hb; [|discriminate].
    inversion H; subst. right. eapply qtype_head_ro; eauto.
    apply Forall2_targ_sub_refl.
Qed.

Lemma wf_r_typable_ubound : forall CT Δ h ι T U qctx ca ma,
  frame_bounds_ok CT Δ (qr2q qctx) ca ma ->
  ubound Δ T = Some U ->
  wf_r_typable CT h ι T qctx ca ma ->
  wf_r_typable CT h ι U qctx ca ma.
Proof.
  intros. destruct (ubound_subtype CT _ _ _ H0) as [-> | Hsub]; auto.
  eapply wf_r_typable_subtype; eauto.
Qed.

(** What a receiver's runtime typability at a class type says about its
    object. *)
Lemma wf_r_typable_class_inv : forall CT h ι qx C Ts qctx ca ma,
  wf_r_typable CT h ι (TClass qx C Ts) qctx ca ma ->
  exists o Vs,
    runtime_getObj h ι = Some o /\
    head_ok (rqtype (rt_type o)) (dynq (qr2q qctx) qx) /\
    rsuper_inst CT (qr2q (rqtype (rt_type o)))
      (rctype (rt_type o)) (rtargs (rt_type o)) C Vs /\
    Forall2 rarg_sub Vs (map (dyn (qr2q qctx) ca ma) Ts).
Proof.
  intros CT h ι qx C Ts qctx ca ma H.
  unfold wf_r_typable, loc_has_rtype in H. simpl in H.
  destruct (runtime_getObj h ι) as [o|]; [|contradiction].
  destruct H as [Hhead [Vs [Hsup Hle]]]. eauto 8.
Qed.

(** The value stored in a field inhabits the field's declared type, read in
    the object's arguments viewed at the class through which the field was
    looked up. *)
Lemma object_field_typable : forall CT h ι o C Vs f fd v,
  wf_heap CT h ->
  runtime_getObj h ι = Some o ->
  rsuper_inst CT (qr2q (rqtype (rt_type o)))
    (rctype (rt_type o)) (rtargs (rt_type o)) C Vs ->
  sf_def_rel CT C f fd ->
  getVal (fields_map o) f = Some v ->
  match v with
  | Null_a => True
  | Iot loc =>
      loc_has_rtype CT h loc (dyn (qr2q (rqtype (rt_type o))) Vs [] (ftype fd))
  end.
Proof.
  intros CT h ι o C Vs f fd v Hheap Hobj Hsup Hfld Hval.
  pose proof (Hheap ι (runtime_getObj_dom _ _ _ Hobj)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hobj in Hwfo.
  destruct Hwfo as (_ & fsO & HcfO & Hlen & Hall).
  inversion Hfld as [? ? fsC ? ? HcfC Hget]; subst.
  destruct (field_inherit _ _ _ _ _ _ Hsup _ _ _ _ HcfC HcfO Hget)
    as (fd' & Hnth' & _ & Hdyn).
  pose proof (Forall2_nth_error_rel _ _ _ f Hall) as Hrel.
  unfold getVal in Hval. rewrite Hval in Hrel. rewrite Hnth' in Hrel.
  destruct v as [|loc]; auto.
  unfold wf_r_typable in Hrel. rewrite Hdyn in Hrel. exact Hrel.
Qed.

Lemma expr_eval_typable : forall CT Δ sΓ rΓ h mt e T v ι o,
  wf_r_config CT Δ sΓ rΓ h ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  frame_bounds_ok CT Δ (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) ->
  expr_has_type CT Δ sΓ mt e T ->
  eval_expr CT rΓ h e v OK rΓ h ->
  val_typable CT h v T (rqtype (rt_type o)) (cargs rΓ) (margs rΓ).
Proof.
  intros CT Δ sΓ rΓ h mt e T v ι o Hwf Hthis Hobj Hfb Htype Heval.
  inversion Htype; subst; inversion Heval; subst.
  - exact I.
  - pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget) as Hv.
    rewrite Hval in Hv. destruct v; auto.
  - pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hv.
    rewrite Hval in Hv.
    pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ Hfb Hub Hv) as Hv'.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hv')
      as (ox & Vs & Hobjx & Hhead & Hsup & Hle).
    rewrite Hobj0 in Hobjx. inversion Hobjx; subst ox. clear Hobjx.
    destruct Hwf as (_ & Hheap & _).
    pose proof (object_field_typable _ _ _ _ _ _ _ _ _ Hheap Hobj0 Hsup Hfld_def Hfield)
      as Hfv.
    destruct v as [|loc]; [exact I|]. simpl.
    unfold wf_r_typable, member_type. rewrite dyn_subst. simpl map at 2.
    eapply loc_has_rtype_adapt; eauto.
Qed.

(* ------------------ASSIGNMENT AND CAST------------------*)

Lemma val_typable_subtype : forall CT Δ h v T U qctx ca ma,
  frame_bounds_ok CT Δ (qr2q qctx) ca ma ->
  qualified_type_subtype CT Δ T U ->
  val_typable CT h v T qctx ca ma ->
  val_typable CT h v U qctx ca ma.
Proof.
  intros. destruct v; simpl in *; auto.
  eapply wf_r_typable_subtype; eauto.
Qed.

Lemma preservation_varass : forall CT Δ sΓ rΓ h mt x e v sΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SVarAss x e) sΓ' ->
  eval_expr CT rΓ h e v OK rΓ h ->
  wf_r_config CT Δ sΓ' (set_vars rΓ (update x v (vars rΓ))) h.
Proof.
  intros CT Δ sΓ rΓ h mt x e v sΓ' Hwf Htype Heval.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  eapply wf_r_config_update_var; eauto.
  eapply val_typable_subtype; eauto.
  eapply expr_eval_typable; eauto.
Qed.

Lemma bound_agree_qr2q : forall qr qc,
  vpa_mutability_runtime_bound_agree qr qc = true ->
  qc <> RDM_c -> qr2q qr = qc2q qc.
Proof.
  intros [] []; simpl; intros H1 H2; try reflexivity; try discriminate;
    exfalso; apply H2; reflexivity.
Qed.

Lemma cast_narrowing_typable : forall CT h ι S T qctx ca ma,
  wf_class_table CT -> wf_heap CT h ->
  cast_narrowing_ok CT S T ->
  wf_r_typable CT h ι S qctx ca ma ->
  wf_r_typable CT h ι T qctx ca ma.
Proof.
  intros CT h ι S T qctx ca ma Hct Hheap Hnarrow Hty.
  destruct S as [qs Cs args_s| |]; [|contradiction..].
  destruct T as [qt Ct args_t| |]; [|contradiction..].
  destruct Hnarrow as (-> & -> & Hqt & _ & _ & dD & HD & Hpin).
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hty)
    as (o & Vs & Hobj & Hhead & Hsup & Hle).
  pose proof (Hheap ι (runtime_getObj_dom _ _ _ Hobj)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hobj in Hwfo.
  destruct Hwfo as (Hrt & _). unfold wf_rtypeuse in Hrt.
  destruct (find_class CT (rctype (rt_type o))) as [dO|] eqn:HO; [|contradiction].
  destruct Hrt as (Hagree & _).
  assert (Hbase : base_subtype CT (rctype (rt_type o)) Ct).
  { eapply rsuper_inst_base; eauto using wf_class_table_supers_in_dom, find_class_dom. }
  assert (Hnr : class_qualifier (signature dD) <> RDM_c).
  { intros Heq. rewrite Heq in Hpin. simpl in Hpin.
    destruct Hqt; congruence. }
  destruct (base_subtype_pinned _ _ _ Hct Hbase dD HD Hnr) as (dO' & HO' & Hq).
  assert (dO' = dO) by congruence. subst dO'.
  assert (Hqo : qr2q (rqtype (rt_type o)) = qt).
  { rewrite <- Hpin. rewrite <- Hq. apply bound_agree_qr2q; [auto | congruence]. }
  unfold wf_r_typable, loc_has_rtype. simpl. rewrite Hobj.
  split; [|eauto].
  unfold head_ok. right. right.
  destruct Hqt as [-> | ->]; simpl; auto.
Qed.

Lemma preservation_cast : forall CT Δ sΓ rΓ h mt x T y v sΓ',
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCast x T y) sΓ' ->
  runtime_getVal rΓ y = Some v ->
  wf_r_config CT Δ sΓ' (set_vars rΓ (update x v (vars rΓ))) h.
Proof.
  intros CT Δ sΓ rΓ h mt x T y v sΓ' Hwf Htype Hval.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  eapply wf_r_config_update_var; eauto.
  eapply val_typable_subtype; eauto.
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hv.
  rewrite Hval in Hv. destruct v as [|loc]; [exact I|]. simpl.
  destruct Hsource as [Hsub' | Hnarrow].
  - eapply wf_r_typable_subtype; eauto.
  - destruct Hwf as (Hct & Hheap & _).
    eapply cast_narrowing_typable; eauto.
Qed.

(* ------------------FIELD WRITE------------------*)

Lemma update_field_getObj_same : forall h l f v o,
  runtime_getObj h l = Some o ->
  runtime_getObj (update_field h l f v) l =
    Some (set_fields_map o (update f v (fields_map o))).
Proof.
  intros h l f v o Hobj. unfold update_field. rewrite Hobj.
  unfold runtime_getObj. apply update_same.
  eapply runtime_getObj_dom; eauto.
Qed.

Lemma update_field_getObj_diff : forall h l f v l',
  l <> l' ->
  runtime_getObj (update_field h l f v) l' = runtime_getObj h l'.
Proof.
  intros h l f v l' Hne. unfold update_field.
  destruct (runtime_getObj h l); auto.
  unfold runtime_getObj. apply update_diff; auto.
Qed.

Lemma update_field_heap_ext : forall h l f v,
  heap_ext h (update_field h l f v).
Proof.
  intros h l f v. split.
  - rewrite update_field_length. lia.
  - intros ι Hι. unfold r_type.
    destruct (Nat.eq_dec l ι) as [-> | Hne].
    + destruct (runtime_getObj h ι) as [o|] eqn:Hobj.
      * rewrite (update_field_getObj_same _ _ _ _ _ Hobj). reflexivity.
      * unfold update_field. rewrite Hobj. rewrite Hobj. reflexivity.
    + rewrite update_field_getObj_diff; auto.
Qed.

Lemma val_typable_bot_null : forall CT h v C Ts qctx ca ma,
  val_typable CT h v (TClass Bot C Ts) qctx ca ma -> v = Null_a.
Proof.
  intros CT h [|loc] C Ts qctx ca ma H; auto.
  simpl in H. unfold wf_r_typable, loc_has_rtype in H. simpl in H.
  destruct (runtime_getObj h loc); [|contradiction].
  destruct H as [Hh _]. exfalso. eapply head_ok_not_bot; eauto.
Qed.

(** A value that may be stored where the client sees a member at type
    [member_type mt qx Ts Us T] inhabits the declaration [T] read in the
    target's own activation. *)
Lemma assignable_to_member : forall CT Δ h v A mt qx Ts Us T qctx ca ma qo Vs Ms,
  frame_bounds_ok CT Δ (qr2q qctx) ca ma ->
  Forall rlost_free ca -> Forall rlost_free ma ->
  assignable_to CT Δ A (member_type mt qx Ts Us T) ->
  val_typable CT h v A qctx ca ma ->
  head_ok qo (dynq (qr2q qctx) qx) ->
  Forall2 rarg_sub Vs (map (dyn (qr2q qctx) ca ma) Ts) ->
  Forall2 rarg_sub Ms (map (dyn (qr2q qctx) ca ma) Us) ->
  match v with
  | Null_a => True
  | Iot loc => loc_has_rtype CT h loc (dyn (qr2q qo) Vs Ms T)
  end.
Proof.
  intros CT Δ h v A mt qx Ts Us T qctx ca ma qo Vs Ms
    Hfb Hlc Hlm [Hsub Hok] Hv Hhead HVs HMs.
  destruct Hok as [Hlf | (C & Ts' & ->)].
  - destruct v as [|loc]; [exact I|]. simpl in Hv.
    pose proof (wf_r_typable_subtype _ _ _ _ _ _ _ _ _ Hfb Hsub Hv) as Hv'.
    unfold wf_r_typable, member_type in Hv'. rewrite dyn_subst in Hv'.
    rewrite (dyn_adapt_exact mt qo qctx qx Vs
               (map (dyn (qr2q qctx) ca ma) Ts) Ms
               (map (dyn (qr2q qctx) ca ma) Us) T); auto.
    rewrite <- dyn_subst.
    apply dyn_lost_free; auto using qr2q_concrete.
  - apply val_typable_bot_null in Hv. subst v. exact I.
Qed.

Lemma preservation_fldwrite : forall CT Δ sΓ rΓ h mt x f y sΓ' lx ox vf vy,
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SFldWrite x f y) sΓ' ->
  runtime_getVal rΓ x = Some (Iot lx) ->
  runtime_getObj h lx = Some ox ->
  getVal (fields_map ox) f = Some vf ->
  runtime_getVal rΓ y = Some vy ->
  wf_r_config CT Δ sΓ' rΓ (update_field h lx f vy).
Proof.
  intros CT Δ sΓ rΓ h mt x f y sΓ' lx ox vf vy Hwf Htype Hvx Hox Hvf Hvy.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & Hlc & Hlm & Hfb).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hxty.
  rewrite Hvx in Hxty.
  pose proof (wf_r_typable_ubound _ _ _ _ _ _ _ _ _ Hfb Hub Hxty) as Hxty'.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ Hxty')
    as (ox' & Vs & Hox' & Hhead & Hsup & Hle).
  rewrite Hox in Hox'. inversion Hox'; subst ox'. clear Hox'.
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
  rewrite Hvy in Hyty.
  assert (Hyval : val_typable CT h vy Ty (rqtype (rt_type o)) (cargs rΓ) (margs rΓ)).
  { destruct vy; auto. }
  pose proof (assignable_to_member _ _ _ _ _ _ _ _ _ _ _ _ _
                (rqtype (rt_type ox)) Vs [] Hfb Hlc Hlm Hsub Hyval Hhead Hle
                (Forall2_nil _)) as Hstore.
  eapply wf_r_config_heap_ext; eauto using update_field_heap_ext.
  destruct Hwf as (Hct & Hheap & _).
  intros l Hl. rewrite update_field_length in Hl.
  pose proof (Hheap l Hl) as Hwfo. unfold wf_obj in *.
  destruct (Nat.eq_dec lx l) as [-> | Hne].
  - rewrite (update_field_getObj_same _ _ _ _ _ Hox). rewrite Hox in Hwfo.
    simpl. destruct Hwfo as (Hrt & fsO & HcfO & Hlen & Hall).
    split; [exact Hrt|]. exists fsO. split; [exact HcfO|]. split.
    + rewrite update_length. exact Hlen.
    + inversion Hfld_def as [? ? fsC ? ? HcfC Hget]; subst.
      destruct (field_inherit _ _ _ _ _ _ Hsup _ _ _ _ HcfC HcfO Hget)
        as (fd' & Hnth' & _ & Hdyn).
      eapply Forall2_impl with
        (R1 := fun v fdef =>
           match v with
           | Null_a => True
           | Iot loc =>
               wf_r_typable CT h loc (ftype fdef)
                 (rqtype (rt_type ox)) (rtargs (rt_type ox)) []
           end).
      * intros [|loc] fd Hx; auto. unfold wf_r_typable in *.
        eauto using loc_has_rtype_ext, update_field_heap_ext.
      * apply Forall2_update; auto.
        -- apply nth_error_Some. congruence.
        -- intros b Hb. assert (b = fd') by congruence. subst b.
           destruct vy as [|loc]; auto.
           unfold wf_r_typable. rewrite Hdyn. exact Hstore.
  - rewrite update_field_getObj_diff; auto.
    destruct (runtime_getObj h l) as [ol|]; [|contradiction].
    destruct Hwfo as (Hrt & fsO & HcfO & Hlen & Hall).
    split; [exact Hrt|]. exists fsO. split; [exact HcfO|]. split; [exact Hlen|].
    eapply Forall2_impl; [|exact Hall].
    intros [|loc] fd Hx; auto. unfold wf_r_typable in *.
    eauto using loc_has_rtype_ext, update_field_heap_ext.
Qed.

(* ------------------OBJECT CREATION------------------*)

Lemma Forall2_map_left : forall {A A' B : Type} (P : A -> B -> Prop)
    (Q : A' -> B -> Prop) (f : A -> A') l1 l2,
  Forall2 P l1 l2 ->
  (forall a b, P a b -> Q (f a) b) ->
  Forall2 Q (map f l1) l2.
Proof.
  intros. induction H; simpl; constructor; auto.
Qed.

Lemma Forall2_compose : forall {A B C : Type} (P : A -> B -> Prop)
    (Q : B -> C -> Prop) (R : A -> C -> Prop) l1 l2 l3,
  Forall2 P l1 l2 -> Forall2 Q l2 l3 ->
  (forall a b c, P a b -> Q b c -> R a c) ->
  Forall2 R l1 l3.
Proof.
  intros A B C P Q R l1 l2 l3 H. revert l3.
  induction H; intros l3 H2 Himp; inversion H2; subst; constructor; eauto.
Qed.

Lemma heap_ext_app : forall h o, heap_ext h (h ++ [o]).
Proof.
  intros h [rt fs]. split.
  - rewrite length_app. lia.
  - intros ι Hι. unfold r_type. rewrite runtime_getObj_last2; auto.
Qed.

Lemma wf_heap_app : forall CT h o,
  wf_heap CT h -> wf_obj CT (h ++ [o]) (dom h) -> wf_heap CT (h ++ [o]).
Proof.
  intros CT h o Hheap Hnew l Hl.
  rewrite length_app in Hl. simpl in Hl.
  destruct (Nat.eq_dec l (dom h)) as [-> | Hne]; auto.
  assert (Hlt : l < dom h) by lia.
  pose proof (Hheap l Hlt) as Hwfo. unfold wf_obj in *.
  destruct o as [rt fs]. rewrite runtime_getObj_last2; auto.
  destruct (runtime_getObj h l) as [ol|]; [|contradiction].
  destruct Hwfo as (Hrt & fsO & HcfO & Hlen & Hall).
  split; [exact Hrt|]. exists fsO. split; [exact HcfO|]. split; [exact Hlen|].
  eapply Forall2_impl; [|exact Hall].
  intros [|loc] fd Hx; auto. unfold wf_r_typable in *.
  eapply loc_has_rtype_ext; eauto. apply (heap_ext_app h (mkObj rt fs)).
Qed.

Lemma get_this_runtime_getVal : forall rΓ ι,
  get_this_var_mapping (vars rΓ) = Some ι <->
  runtime_getVal rΓ 0 = Some (Iot ι).
Proof.
  intros rΓ ι. unfold runtime_getVal, get_this_var_mapping.
  destruct (vars rΓ) as [|[|l] vs]; simpl; split; intros H;
    try discriminate; congruence.
Qed.

(** The values of a list of variables inhabit the variables' static types. *)
Lemma lookup_list_typable : forall CT Δ sΓ rΓ h ι o args argtypes vals,
  wf_r_config CT Δ sΓ rΓ h ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  static_getType_list sΓ args = Some argtypes ->
  runtime_lookup_list rΓ args = Some vals ->
  Forall2 (fun v A => val_typable CT h v A (rqtype (rt_type o)) (cargs rΓ) (margs rΓ))
    vals argtypes.
Proof.
  intros CT Δ sΓ rΓ h ι o args argtypes vals Hwf Hthis Hobj.
  revert argtypes vals.
  unfold static_getType_list, runtime_lookup_list.
  induction args as [|a args IH]; intros argtypes vals Hst Hrt; simpl in *.
  - inversion Hst; inversion Hrt; subst. constructor.
  - destruct (static_getType sΓ a) as [T|] eqn:HT; [|discriminate].
    destruct (mapM (fun x => static_getType sΓ x) args) as [Ts|]; [|discriminate].
    destruct (runtime_getVal rΓ a) as [v|] eqn:Hv; [|discriminate].
    destruct (mapM (fun x => runtime_getVal rΓ x) args) as [vs|]; [|discriminate].
    inversion Hst; inversion Hrt; subst. constructor; auto.
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HT) as Hty.
    rewrite Hv in Hty. destruct v; auto.
Qed.

Lemma creation_head_ok : forall qthis qc,
  head_ok (vpa_mutability_object_creation qthis qc)
    (dynq (qr2q qthis) (qc2q qc)).
Proof.
  intros [] []; simpl; unfold head_ok; simpl; auto.
Qed.

Lemma creation_bound_agree : forall qthis qc cq,
  vpa_mutability_bound (qc2q qc) cq = qc2q qc ->
  vpa_mutability_runtime_bound_agree
    (vpa_mutability_object_creation qthis qc) cq = true.
Proof.
  intros [] [] []; simpl; intros H; try reflexivity; discriminate.
Qed.

Lemma creation_dynq : forall qthis qc,
  dynq (qr2q qthis) (qc2q qc) =
  qr2q (vpa_mutability_object_creation qthis qc).
Proof.
  intros [] []; reflexivity.
Qed.

Lemma preservation_new : forall CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals,
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ' ->
  runtime_getVal rΓ 0 = Some (Iot l1) ->
  runtime_lookup_list rΓ ys = Some vals ->
  r_muttype h l1 = Some qthisr ->
  wf_r_config CT Δ sΓ'
    (set_vars rΓ (update x (Iot (dom h)) (vars rΓ)))
    (h ++ [mkObj
             (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ)) Ts))
             vals]).
Proof.
  intros CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' l1 qthisr vals
    Hwf Htype Hthis0 Hvals Hmut.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & Hmut' & Hlc & Hlm & Hfb).
  apply get_this_runtime_getVal in Hthis0.
  assert (l1 = ι) by congruence. subst l1.
  assert (qthisr = rqtype (rt_type o)) by congruence. subst qthisr.
  set (qo := vpa_mutability_object_creation (rqtype (rt_type o)) qc) in *.
  set (Rs := map (dyn (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ)) Ts) in *.
  set (onew := mkObj (mkruntime_type qo C Rs) vals).
  pose proof (heap_ext_app h onew) as Hext.
  pose proof (lookup_list_typable _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_args Hvals)
    as Hvals_ty.
  assert (Hhead : head_ok qo (dynq (qr2q (rqtype (rt_type o))) (qc2q qc)))
    by apply creation_head_ok.
  assert (Hheap' : wf_heap CT (h ++ [onew])).
  { destruct Hwf as (Hct & Hheap & _).
    apply wf_heap_app; auto.
    unfold wf_obj. unfold onew at 1. rewrite runtime_getObj_last. simpl.
    split.
    - unfold wf_rtypeuse. simpl. rewrite Hfind.
      refine (conj _ (conj _ _)).
      + apply creation_bound_agree; auto.
      + apply map_dyn_lost_free; auto using qr2q_concrete.
      + unfold rbounds_ok. eapply Forall2_map_left; [exact Hbounds|].
        intros T B [Hlf Hsub]. apply bound_sub_self in Hsub. simpl in Hlf, Hsub.
        pose proof (subtype_dyn _ _ _ _ _ _ _ (qr2q_concrete _) Hfb Hsub) as Hrs.
        unfold member_type in Hrs. rewrite dyn_subst in Hrs. simpl map in Hrs.
        rewrite (dyn_adapt_exact AbstractState qo (rqtype (rt_type o)) (qc2q qc)
                   Rs Rs [] [] B); auto using Forall2_rarg_sub_refl.
        fold Rs. change (@nil rtype) with
          (map (dyn (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ)) []).
        unfold Rs. rewrite <- dyn_subst.
        apply dyn_lost_free; auto using qr2q_concrete.
    - exists fds. split; [exact Hfields|]. split.
      + rewrite <- (Forall2_length Harg_sub). apply (Forall2_length Hvals_ty).
      + eapply Forall2_compose; [exact Hvals_ty | exact Harg_sub |].
        intros v A fd Hv Hassign. simpl in Hv, Hassign.
        pose proof (assignable_to_member _ _ _ _ _ _ _ _ _ _ _ _ _
                      qo Rs [] Hfb Hlc Hlm Hassign Hv Hhead
                      (Forall2_rarg_sub_refl _) (Forall2_nil _)) as Hstore.
        destruct v as [|loc]; auto.
        unfold wf_r_typable. simpl. eapply loc_has_rtype_ext; eauto. }
  pose proof (wf_r_config_heap_ext _ _ _ _ _ _ Hwf Hext Hheap') as Hwf'.
  destruct (heap_ext_getObj _ _ _ _ Hext Hobj) as [o' [Hobj' Hrt]].
  eapply wf_r_config_update_var; eauto.
  rewrite Hrt. simpl.
  eapply wf_r_typable_subtype; eauto.
  unfold wf_r_typable, loc_has_rtype. simpl.
  unfold onew. rewrite runtime_getObj_last. simpl.
  split.
  - rewrite creation_dynq. unfold head_ok. auto.
  - exists Rs. split; [apply rsi_refl | apply Forall2_rarg_sub_refl].
Qed.

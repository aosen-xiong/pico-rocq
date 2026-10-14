From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation.

(** Readonly-state and transitive-state preservation, first for the fragment
    without type parameters and without receiver-dependent field types.

    The invariant: the running code has no mutable access path into the
    protected objects.  A mutable access path starts at a variable whose
    static type is mutable and continues through fields declared mutable. *)

(* ------------------THE FRAGMENT------------------*)

Definition no_tparams (CT : class_table) : Prop :=
  forall C def, find_class CT C = Some def ->
    ctparams (signature def) = [] /\
    Forall (fun md => mtparams (msignature md) = [] /\
                      mqparams (msignature md) = 0) (methods (body def)).

Definition head_of (T : qualified_type) : option q :=
  match T with
  | TClass q0 _ _ => Some q0
  | TVar _ _ _ => None
  | THead _ _ _ => None
  end.

Definition no_rdm_fields (CT : class_table) : Prop :=
  forall C fs, CollectFields CT C fs ->
    Forall (fun fd => head_of (ftype fd) <> Some RDM) fs.

Definition empty_tv_env (Δ : tv_env) : Prop :=
  class_bounds Δ = [] /\ method_bounds Δ = [] /\ qparams Δ = 0.

Definition flat_type (T : qualified_type) : Prop :=
  exists q0 C, T = TClass q0 C [].

Lemma tv_bound_empty : forall Δ o n, empty_tv_env Δ -> tv_bound Δ o n = None.
Proof.
  intros Δ o n [Hc [Hm _]]. unfold tv_bound, tv_lookup.
  rewrite Hc. rewrite Hm. destruct o; destruct n; reflexivity.
Qed.

Lemma wf_stype_flat : forall CT Δ top T,
  no_tparams CT -> empty_tv_env Δ -> wf_stype CT Δ top T -> flat_type T.
Proof.
  intros CT Δ top T Hnt HΔ H. inversion H; subst.
  - destruct (Hnt _ _ Hfind) as [Hct _]. rewrite Hct in Hlen.
    destruct Ts; [|discriminate]. exists q0, C. reflexivity.
  - rewrite tv_bound_empty in Hbound; auto. discriminate.
  - destruct HΔ as (_ & _ & Hq0). rewrite Hq0 in Hbound. inversion Hbound.
Qed.

Lemma class_tparams_nil : forall CT C, no_tparams CT -> class_tparams CT C = [].
Proof.
  intros CT C Hnt. unfold class_tparams.
  destruct (find_class CT C) as [def|] eqn:Hf; auto.
  destruct (Hnt _ _ Hf); auto.
Qed.

(** In the fragment every collected field type is a plain class type. *)
Lemma collect_fields_flat : forall CT C fs,
  wf_class_table CT -> no_tparams CT ->
  CollectFields CT C fs -> Forall (fun fd => flat_type (ftype fd)) fs.
Proof.
  intros CT C fs Hwf Hnt H. induction H.
  - constructor.
  - constructor.
  - apply Forall_app. split.
    + specialize (IHCollectFields Hwf Hnt).
      rewrite Forall_forall in IHCollectFields. rewrite Forall_forall.
      intros fd Hin. apply in_map_iff in Hin. destruct Hin as (fd0 & <- & Hin0).
      destruct (IHCollectFields fd0 Hin0) as (q0 & D & Heq).
      simpl. rewrite Heq. simpl. exists q0, D. reflexivity.
    + subst own_fields.
      pose proof (wf_class_table_class _ _ _ Hwf Hfind) as Hcls.
      inversion Hcls; subst.
      * rewrite Hno_fields. constructor.
      * eapply Forall_impl; [|exact H5]. intros fd Hfd.
        unfold wf_field, wf_stypeuse in Hfd.
        eapply wf_stype_flat; eauto.
        destruct (Hnt _ _ Hfind) as [Hct _]. split; simpl; auto.
Qed.

(* ------------------MUTABLE ACCESS PATHS------------------*)

Definition is_mut_type (T : qualified_type) : bool :=
  match T with
  | TClass Mut _ _ => true
  | _ => false
  end.

(** [mcap CT h v b l]: starting from a reference to [v] that is mutable iff
    [b], location [l] can be reached with a mutable reference, going only
    through fields declared mutable. *)
Inductive mcap (CT : class_table) (h : heap) : Loc -> bool -> Loc -> Prop :=
  | mcap_here : forall v
      (Hdom : v < dom h),
      mcap CT h v true v
  | mcap_step : forall v b o fs f fd v' l
      (Hobj : runtime_getObj h v = Some o)
      (Hcf : CollectFields CT (rctype (rt_type o)) fs)
      (Hfd : nth_error fs f = Some fd)
      (Hval : nth_error (fields_map o) f = Some (Iot v'))
      (Hrest : mcap CT h v' (b && is_mut_type (ftype fd)) l),
      mcap CT h v b l.

Lemma mcap_false_empty : forall CT h v b l,
  mcap CT h v b l -> b = false -> False.
Proof.
  intros CT h v b l H. induction H; intros Hb; [discriminate|].
  subst b. simpl in IHmcap. auto.
Qed.

Lemma mcap_dom : forall CT h v b l, mcap CT h v b l -> v < dom h.
Proof.
  intros CT h v b l H. inversion H; subst; auto.
  eapply runtime_getObj_dom; eauto.
Qed.

Definition safe (P : Loc -> Prop) (CT : class_table) (h : heap) (v : Loc) : Prop :=
  forall l, mcap CT h v true l -> ~ P l.

(** Is a variable of this static type a mutable reference?  [κ] says whether
    the activation's receiver-dependent qualifier stands for mutable in the
    eyes of the code that called it. *)
Definition bitk (κ : bool) (T : qualified_type) : bool :=
  match T with
  | TClass Mut _ _ => true
  | TClass RDM _ _ => κ
  | _ => false
  end.

Definition is_bot_type (T : qualified_type) : bool :=
  match T with
  | TClass Bot _ _ => true
  | _ => false
  end.

Definition bitp (κ : bool) (T : qualified_type) : bool :=
  bitk κ T || is_bot_type T.

(** Static subtyping between class types relates the head qualifiers. *)
Lemma subtype_head : forall CT Δ T U,
  qualified_type_subtype CT Δ T U ->
  empty_tv_env Δ ->
  forall qU D a, U = TClass qU D a ->
  exists qT C b, T = TClass qT C b /\ (qT = qU \/ qU = RO \/ qT = Bot).
Proof.
  intros CT Δ T U H HΔ. induction H; intros qU D0 a HU.
  - inversion HU; subst. eexists _, _, _. split; [reflexivity|].
    inversion Hqsub; subst; auto.
  - inversion HU; subst. eauto 8.
  - discriminate.
  - rewrite tv_bound_empty in Hbound; auto. discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (IHqualified_type_subtype _ _ _ eq_refl) as (qT & C0 & b & Heq & _).
    discriminate.
  - destruct HΔ as (_ & _ & Hq0). rewrite Hq0 in Hbound. inversion Hbound.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (IHqualified_type_subtype2 _ _ _ HU) as (q2 & C2 & b2 & -> & H2).
    destruct (IHqualified_type_subtype1 _ _ _ eq_refl) as (q1 & C1 & b1 & -> & H1).
    exists q1, C1, b1. split; auto.
    destruct H1 as [-> | [-> | ->]]; auto.
    destruct H2 as [-> | [-> | H2]]; auto. discriminate.
Qed.

Lemma subtype_bitp : forall CT Δ T U κ,
  qualified_type_subtype CT Δ T U -> empty_tv_env Δ -> flat_type U ->
  bitp κ U = true -> bitp κ T = true.
Proof.
  intros CT Δ T U κ Hsub HΔ (qU & D & ->) Hb.
  destruct (subtype_head _ _ _ _ Hsub HΔ _ _ _ eq_refl) as (qT & C & b & -> & Hq).
  unfold bitp in *. simpl in *.
  destruct Hq as [-> | [-> | ->]]; auto.
Qed.

(** A location never inhabits a bottom-headed type. *)
Lemma val_typable_not_bot : forall CT h loc T qctx ca ma ka,
  wf_r_typable CT h loc T qctx ca ma ka -> is_bot_type T = false.
Proof.
  intros CT h loc T qctx ca ma ka H.
  destruct T as [q0 C Ts| |]; auto. destruct q0; auto.
  exfalso. unfold wf_r_typable, loc_has_rtype in H. simpl in H.
  destruct (runtime_getObj h loc); [|contradiction].
  destruct H as [Hh _]. eapply head_ok_not_bot; eauto.
Qed.

(* ------------------THE INVARIANT------------------*)

(** No variable that is a mutable reference has a mutable access path into
    the protected set.  If the receiver-dependent qualifier counts as mutable
    here, the receiver object really is mutable. *)
Definition Inv (P : Loc -> Prop) (CT : class_table) (sΓ : s_env) (rΓ : r_env)
    (h : heap) (κ : bool) : Prop :=
  (κ = true ->
   exists ι o, get_this_var_mapping (vars rΓ) = Some ι /\
               runtime_getObj h ι = Some o /\ rqtype (rt_type o) = Mut_r) /\
  forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    bitk κ T = true ->
    safe P CT h v.

Definition prot_cond (CT : class_table) (C : class_name) (f : var)
    (mt : method_scope) : Prop :=
  sf_assignability_rel CT C f Final \/
  sf_assignability_rel CT C f RDA \/
  strict_assignability_method_scope mt.

Lemma senv_flat : forall CT Δ sΓ x T,
  no_tparams CT -> empty_tv_env Δ -> wf_senv CT Δ sΓ ->
  static_getType sΓ x = Some T -> flat_type T.
Proof.
  intros CT Δ sΓ x T Hnt HΔ [_ Hall] Hx.
  rewrite Forall_forall in Hall.
  eapply wf_stype_flat; eauto. apply Hall.
  unfold static_getType in Hx. eapply nth_error_In; eauto.
Qed.

Lemma Inv_heap : forall P CT sΓ rΓ h h' κ,
  Inv P CT sΓ rΓ h κ ->
  heap_ext h h' ->
  (forall v, safe P CT h v -> safe P CT h' v) ->
  Inv P CT sΓ rΓ h' κ.
Proof.
  intros P CT sΓ rΓ h h' κ [HK Hv] Hext Hsafe. split.
  - intros Hκ. destruct (HK Hκ) as (ι & o & Hthis & Hobj & Hq).
    destruct (heap_ext_getObj _ _ _ _ Hext Hobj) as (o' & Ho' & Hrt).
    exists ι, o'. rewrite Hrt. auto.
  - intros x T v HT Hval Hb. apply Hsafe. eapply Hv; eauto.
Qed.

Lemma Inv_update_var : forall P CT sΓ rΓ h κ x v Tx,
  Inv P CT sΓ rΓ h κ ->
  x <> 0 ->
  static_getType sΓ x = Some Tx ->
  (forall w, v = Iot w -> bitk κ Tx = true -> safe P CT h w) ->
  Inv P CT sΓ (set_vars rΓ (update x v (vars rΓ))) h κ.
Proof.
  intros P CT sΓ rΓ h κ x v Tx [HK Hv] Hx HTx Hnew. split.
  - intros Hκ. destruct (HK Hκ) as (ι & o & Hthis & Hrest).
    exists ι, o. simpl. rewrite get_this_var_mapping_update; auto.
  - intros y T w HT Hval Hb. unfold runtime_getVal in Hval. simpl in Hval.
    destruct (Nat.eq_dec x y) as [-> | Hne].
    + assert (Hd : y < dom (vars rΓ)).
      { destruct (Nat.lt_ge_cases y (dom (vars rΓ))) as [Hl | Hg]; auto.
        apply nth_error_None in Hg.
        assert (Hlen : dom (update y v (vars rΓ)) <= y)
          by (rewrite update_length; apply nth_error_None; exact Hg).
        apply nth_error_None in Hlen. rewrite Hlen in Hval. discriminate. }
      rewrite update_same in Hval; auto. inversion Hval; subst v.
      assert (T = Tx) by (unfold static_getType in *; congruence). subst T.
      eapply Hnew; eauto.
    + rewrite update_diff in Hval; auto. eapply Hv; eauto.
Qed.

(** A variable whose value flows, by subtyping, into a mutable position is
    safe. *)
Lemma Inv_var_sub : forall P CT Δ sΓ rΓ h κ ι o x T U v,
  no_tparams CT -> empty_tv_env Δ ->
  wf_r_config CT Δ sΓ rΓ h ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  Inv P CT sΓ rΓ h κ ->
  static_getType sΓ x = Some T ->
  runtime_getVal rΓ x = Some (Iot v) ->
  qualified_type_subtype CT Δ T U -> flat_type U ->
  bitk κ U = true ->
  safe P CT h v.
Proof.
  intros P CT Δ sΓ rΓ h κ ι o x T U v Hnt HΔ Hwf Hthis Hobj [_ Hv] HT Hval
    Hsub HU Hb.
  assert (Hp : bitp κ T = true).
  { eapply subtype_bitp; eauto. unfold bitp. rewrite Hb. reflexivity. }
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HT) as Hty.
  rewrite Hval in Hty. apply val_typable_not_bot in Hty.
  unfold bitp in Hp. rewrite Hty in Hp. rewrite orb_false_r in Hp.
  eapply Hv; eauto.
Qed.

(* ------------------HEAP CHANGES------------------*)

Lemma heap_field_dom : forall CT h v o f v',
  wf_heap CT h ->
  runtime_getObj h v = Some o ->
  nth_error (fields_map o) f = Some (Iot v') ->
  v' < dom h.
Proof.
  intros CT h v o f v' Hheap Hobj Hf.
  pose proof (Hheap v (runtime_getObj_dom _ _ _ Hobj)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hobj in Hwfo.
  destruct Hwfo as (_ & fs & _ & _ & Hall).
  pose proof (Forall2_nth_error_rel _ _ _ f Hall) as Hrel.
  rewrite Hf in Hrel. destruct (nth_error fs f); [|contradiction].
  unfold wf_r_typable in Hrel.
  destruct (loc_has_rtype_getObj _ _ _ _ Hrel) as [o' Ho'].
  eapply runtime_getObj_dom; eauto.
Qed.

Lemma mcap_app_inv : forall CT h onew v b l,
  wf_heap CT h ->
  mcap CT (h ++ [onew]) v b l ->
  v < dom h ->
  mcap CT h v b l.
Proof.
  intros CT h onew v b l Hheap H. induction H; intros Hv.
  - apply mcap_here; auto.
  - destruct onew as [rt fsn].
    rewrite runtime_getObj_last2 in Hobj; auto.
    eapply mcap_step; eauto.
    apply IHmcap. eapply heap_field_dom; eauto.
Qed.

Lemma nth_error_update_same_inv : forall {A : Type} p (v x : A) l,
  nth_error (update p v l) p = Some x -> x = v.
Proof.
  intros A p v x l H.
  destruct (Nat.lt_ge_cases p (dom l)) as [Hl | Hg].
  - rewrite update_same in H; auto. congruence.
  - assert (Hn : nth_error (update p v l) p = None).
    { apply nth_error_None. rewrite update_length. exact Hg. }
    congruence.
Qed.

(** After a field write, a mutable access path either existed before or runs
    through the written value, and then the written field is declared
    mutable. *)
Lemma mcap_update_inv : forall CT h lx f0 vy ox v b l,
  runtime_getObj h lx = Some ox ->
  mcap CT (update_field h lx f0 vy) v b l ->
  b = true ->
  mcap CT h v true l \/
  exists w fs fd,
    vy = Iot w /\
    CollectFields CT (rctype (rt_type ox)) fs /\
    nth_error fs f0 = Some fd /\
    is_mut_type (ftype fd) = true /\
    mcap CT h w true l.
Proof.
  intros CT h lx f0 vy ox v b l Hox H. induction H; intros Hb.
  - left. apply mcap_here. rewrite update_field_length in Hdom. exact Hdom.
  - subst b. simpl in *.
    destruct (is_mut_type (ftype fd)) eqn:Hmut;
      [|exfalso; eapply mcap_false_empty; eauto].
    destruct (IHmcap eq_refl) as [Hold | Hnew]; [|right; exact Hnew].
    destruct (Nat.eq_dec lx v) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Hobj.
      inversion Hobj; subst o. clear Hobj. simpl in *.
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * apply nth_error_update_same_inv in Hval. subst vy.
        right. exists v', fs, fd. auto.
      * rewrite update_diff in Hval; auto.
        left. eapply mcap_step; eauto. simpl. rewrite Hmut. exact Hold.
    + rewrite update_field_getObj_diff in Hobj; auto.
      left. eapply mcap_step; eauto. simpl. rewrite Hmut. exact Hold.
Qed.

(** In the fragment, a field looked up through a superclass view has, in the
    object's own class, the same assignability and the same head qualifier. *)
Lemma obj_field_head : forall CT qo Co Ro C Vs f fd,
  wf_class_table CT -> no_tparams CT -> no_rdm_fields CT ->
  rsuper_inst CT qo Co Ro C Vs ->
  sf_def_rel CT C f fd ->
  forall fsO, CollectFields CT Co fsO ->
  exists fd',
    nth_error fsO f = Some fd' /\
    assignability fd' = assignability fd /\
    head_of (ftype fd') = head_of (ftype fd).
Proof.
  intros CT qo Co Ro C Vs f fd Hwf Hnt Hnr Hsup Hfld fsO HcfO.
  inversion Hfld as [? ? fsC ? ? HcfC Hget]; subst.
  destruct (field_inherit _ _ _ _ _ _ Hsup _ _ _ _ HcfC HcfO Hget)
    as (fd' & Hnth' & Ha & Hdyn).
  exists fd'. split; auto. split; auto.
  pose proof (collect_fields_flat _ _ _ Hwf Hnt HcfO) as HflO.
  pose proof (collect_fields_flat _ _ _ Hwf Hnt HcfC) as HflC.
  pose proof (Hnr _ _ HcfO) as HnrO. pose proof (Hnr _ _ HcfC) as HnrC.
  rewrite Forall_forall in HflO. rewrite Forall_forall in HflC.
  rewrite Forall_forall in HnrO. rewrite Forall_forall in HnrC.
  pose proof (nth_error_In _ _ Hnth') as Hin'.
  pose proof (nth_error_In _ _ Hget) as Hin.
  destruct (HflO _ Hin') as (q1 & D1 & H1).
  destruct (HflC _ Hin) as (q2 & D2 & H2).
  specialize (HnrO _ Hin'). specialize (HnrC _ Hin).
  rewrite H1 in Hdyn. rewrite H2 in Hdyn. rewrite H1 in HnrO. rewrite H2 in HnrC.
  rewrite H1. rewrite H2. simpl in *.
  inversion Hdyn as [[Hq HD]].
  destruct q1, q2; simpl in Hq; try reflexivity; try congruence;
    destruct qo; simpl in Hq; congruence.
Qed.

(* ------------------STATEMENT CASES------------------*)

Lemma head_mut_is_mut : forall T, head_of T = Some Mut -> is_mut_type T = true.
Proof.
  intros [q0 C Ts|u o n| ? ? ?] H; simpl in *; [|discriminate..].
  inversion H; subst. reflexivity.
Qed.

Lemma is_mut_head_mut : forall T, is_mut_type T = true -> head_of T = Some Mut.
Proof.
  intros [q0 C Ts|u o n| ? ? ?] H; simpl in *; [|discriminate..].
  destruct q0; try discriminate. reflexivity.
Qed.

Lemma flat_ubound : forall Δ T qx C Ts,
  flat_type T -> ubound Δ T = Some (TClass qx C Ts) -> T = TClass qx C [] /\ Ts = [].
Proof.
  intros Δ T qx C Ts (q0 & D & ->) H. simpl in H. inversion H; subst. auto.
Qed.

Lemma rs_vpa_mut : forall mt qx qF,
  readonly_state_method_scope mt -> qF <> RDM ->
  forall κ D, bitk κ (TClass (vpa_q mt qx qF) D []) = true ->
  qx = Mut /\ qF = Mut.
Proof.
  intros mt qx qF [-> | ->] HF κ D H;
    destruct qx, qF; simpl in H; try discriminate; try congruence; auto.
Qed.

Lemma rs_assign : forall P CT Δ sΓ rΓ h mt x e v sΓ' κ,
  no_tparams CT -> no_rdm_fields CT -> empty_tv_env Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SVarAss x e) sΓ' ->
  eval_expr CT rΓ h e v OK rΓ h ->
  Inv P CT sΓ rΓ h κ ->
  Inv P CT sΓ' (set_vars rΓ (update x v (vars rΓ))) h κ.
Proof.
  intros P CT Δ sΓ rΓ h mt x e v sΓ' κ Hnt Hnr HΔ Hrs Hwf Htype Heval HInv.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof (stmt_typing_wf_env _ _ _ _ _ _ Htype) as Hsenv.
  pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hsenv Hget_x) as HTx.
  eapply Inv_update_var; eauto.
  intros w -> Hb.
  pose proof (expr_eval_typable _ _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hfb Htype_e Heval)
    as Hvty.
  simpl in Hvty.
  inversion Htype_e; subst; inversion Heval; subst.
  - eapply Inv_var_sub; eauto.
  - (* field read *)
    pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hsenv Hget_x0) as HT.
    destruct (flat_ubound _ _ _ _ _ HT Hub) as [-> ->].
    pose proof Hwf as (Hct & Hheap & _).
    inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
    pose proof (collect_fields_flat _ _ _ Hct Hnt HcfC) as HflC.
    pose proof (Hnr _ _ HcfC) as HnrC.
    rewrite Forall_forall in HflC. rewrite Forall_forall in HnrC.
    pose proof (nth_error_In _ _ HgetC) as Hin.
    destruct (HflC _ Hin) as (qF & D & HF). specialize (HnrC _ Hin).
    rewrite HF in Hsub. rewrite HF in Hvty. rewrite HF in HnrC.
    simpl in Hsub, Hvty, HnrC.
    assert (Hp : bitp κ (TClass (vpa_q mt qx qF) D []) = true).
    { eapply subtype_bitp; eauto. unfold bitp. rewrite Hb. reflexivity. }
    pose proof (val_typable_not_bot _ _ _ _ _ _ _ _ Hvty) as Hnb.
    unfold bitp in Hp. rewrite Hnb in Hp. rewrite orb_false_r in Hp.
    destruct (rs_vpa_mut mt qx qF Hrs) with (κ := κ) (D := D) as [-> ->]; auto.
    { congruence. }
    destruct HInv as [_ HInv].
    assert (Hsy : safe P CT h v) by (eapply HInv; eauto).
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x0) as Hyty.
    rewrite Hval in Hyty.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hyty)
      as (oy & Vs & Hoy & _ & Hsup & _).
    rewrite Hobj0 in Hoy. inversion Hoy; subst oy. clear Hoy.
    pose proof (Hheap v (runtime_getObj_dom _ _ _ Hobj0)) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Hobj0 in Hwfo.
    destruct Hwfo as (_ & fsO & HcfO & _).
    destruct (obj_field_head _ _ _ _ _ _ _ _ Hct Hnt Hnr Hsup Hfld_def _ HcfO)
      as (fd' & Hnth' & _ & Hhead).
    rewrite HF in Hhead. simpl in Hhead. apply head_mut_is_mut in Hhead.
    intros l Hm. apply (Hsy l).
    eapply mcap_step; eauto. simpl. rewrite Hhead. exact Hm.
Qed.

Lemma rs_cast : forall P CT Δ sΓ rΓ h mt x T y v sΓ' κ,
  no_tparams CT -> empty_tv_env Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SCast x T y) sΓ' ->
  runtime_getVal rΓ y = Some v ->
  Inv P CT sΓ rΓ h κ ->
  Inv P CT sΓ' (set_vars rΓ (update x v (vars rΓ))) h κ.
Proof.
  intros P CT Δ sΓ rΓ h mt x T y v sΓ' κ Hnt HΔ Hrs Hwf Htype Hval HInv.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hwf0 Hget_x) as HTx.
  eapply Inv_update_var; eauto.
  intros w -> Hb.
  eapply Inv_var_sub with (U := Tx); eauto.
  destruct Hsource as [Hs | Hnarrow].
  - eapply qtype_trans; eauto.
  - exfalso. destruct Hrs as [-> | ->]; simpl in Hscope; auto.
Qed.

Lemma rs_vpa_mut_target : forall mt qx,
  readonly_state_method_scope mt -> qx <> Mut -> vpa_q mt qx Mut = Lost.
Proof.
  intros mt qx [-> | ->] H; destruct qx; simpl; congruence.
Qed.

Lemma rs_fldwrite : forall P CT Δ sΓ rΓ h mt x f0 y sΓ' κ lx ox a0 vf vy,
  no_tparams CT -> no_rdm_fields CT -> empty_tv_env Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SFldWrite x f0 y) sΓ' ->
  runtime_getVal rΓ x = Some (Iot lx) ->
  runtime_getObj h lx = Some ox ->
  getVal (fields_map ox) f0 = Some vf ->
  sf_assignability_rel CT (rctype (rt_type ox)) f0 a0 ->
  runtime_getVal rΓ y = Some vy ->
  Inv P CT sΓ rΓ h κ ->
  Inv P CT sΓ' rΓ (update_field h lx f0 vy) κ /\
  (forall v, safe P CT h v -> safe P CT (update_field h lx f0 vy) v) /\
  (forall l qr C Rs vals f,
     P l ->
     runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
     prot_cond CT C f mt ->
     exists vals',
       runtime_getObj (update_field h lx f0 vy) l =
         Some (mkObj (mkruntime_type qr C Rs) vals') /\
       nth_error vals f = nth_error vals' f).
Proof.
  intros P CT Δ sΓ rΓ h mt x f0 y sΓ' κ lx ox a0 vf vy
    Hnt Hnr HΔ Hrs Hwf Htype Hvx Hox Hvf Hassign Hvy HInv.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hwf0 Hget_x) as HTx.
  destruct (flat_ubound _ _ _ _ _ HTx Hub) as [-> ->].
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hxty.
  rewrite Hvx in Hxty.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hxty)
    as (ox' & Vs & Hox' & _ & Hsup & _).
  rewrite Hox in Hox'. inversion Hox'; subst ox'. clear Hox'.
  pose proof (Hheap lx (runtime_getObj_dom _ _ _ Hox)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hox in Hwfo.
  destruct Hwfo as (_ & fsO & HcfO & _).
  destruct (obj_field_head _ _ _ _ _ _ _ _ Hct Hnt Hnr Hsup Hfld_def _ HcfO)
    as (fd' & Hnth' & Hassign_eq & Hhead).
  inversion Hfld_def as [? ? fsC ? ? HcfC HgetC]; subst.
  pose proof (collect_fields_flat _ _ _ Hct Hnt HcfC) as HflC.
  rewrite Forall_forall in HflC.
  destruct (HflC _ (nth_error_In _ _ HgetC)) as (qF & D & HF).
  assert (Hsafe : forall v, safe P CT h v ->
                    safe P CT (update_field h lx f0 vy) v).
  { intros v Hs l Hm.
    destruct (mcap_update_inv _ _ _ _ _ _ _ _ _ Hox Hm eq_refl)
      as [Hold | (w & fs & fd & -> & Hcf & Hnth & Hmut & Hm')].
    - apply Hs; auto.
    - assert (fs = fsO) by eauto using collect_fields_deterministic_rel.
      subst fs. rewrite Hnth in Hnth'. inversion Hnth'; subst fd'.
      apply is_mut_head_mut in Hmut. rewrite Hmut in Hhead.
      rewrite HF in Hhead. simpl in Hhead. inversion Hhead; subst qF.
      rewrite HF in Hsub.
      change (member_type mt qx [] [] [] (TClass Mut D []))
        with (TClass (vpa_q mt qx Mut) D []) in Hsub.
      destruct Hsub as [Hsub Hok].
      assert (Hsw : safe P CT h w).
      { destruct (q_eq_dec qx Mut) as [-> | Hnm].
        - eapply Inv_var_sub with (U := TClass (vpa_q mt Mut Mut) D []); eauto.
          + exists (vpa_q mt Mut Mut), D. reflexivity.
          + destruct Hrs as [-> | ->]; reflexivity.
        - exfalso. rewrite (rs_vpa_mut_target _ _ Hrs Hnm) in Hok.
          destruct Hok as [Hlf _].
            apply Hlf. reflexivity. }
      apply Hsw; auto. }
  refine (conj _ (conj Hsafe _)).
  - eapply Inv_heap; eauto using update_field_heap_ext.
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
            destruct mt, qx; simpl in Hassignable; discriminate.
          - pose proof (sf_assignability_deterministic_rel _ _ _ _ _ Hassign Hp)
              as Heq.
            rewrite Ha0 in Heq. rewrite Heq in Hassignable.
            destruct mt, qx; simpl in Hassignable; try discriminate; reflexivity.
          - destruct Hstrict as [-> | ->];
              destruct qx, (assignability fieldT); simpl in Hassignable;
              try discriminate; reflexivity. }
        subst qx. destruct HInv as [_ HInv].
        apply (HInv x _ l Hget_x Hvx eq_refl l); auto.
        apply mcap_here. eapply runtime_getObj_dom; eauto.
      * symmetry. apply update_diff; auto.
    + rewrite update_field_getObj_diff; auto. exists vals. split; auto.
Qed.

(* ------------------OBJECT CREATION------------------*)

Lemma lookup_lists_nth : forall sΓ rΓ ys As vals f v,
  static_getType_list sΓ ys = Some As ->
  runtime_lookup_list rΓ ys = Some vals ->
  nth_error vals f = Some v ->
  exists y A,
    static_getType sΓ y = Some A /\
    runtime_getVal rΓ y = Some v /\
    nth_error As f = Some A.
Proof.
  intros sΓ rΓ ys. unfold static_getType_list, runtime_lookup_list.
  induction ys as [|y ys IH]; intros As vals f v Hs Hr Hn; simpl in *.
  - inversion Hr; subst. destruct f; discriminate.
  - destruct (static_getType sΓ y) as [A|] eqn:HA; [|discriminate].
    destruct (mapM (fun x => static_getType sΓ x) ys) as [As'|]; [|discriminate].
    destruct (runtime_getVal rΓ y) as [v0|] eqn:Hv; [|discriminate].
    destruct (mapM (fun x => runtime_getVal rΓ x) ys) as [vs'|]; [|discriminate].
    inversion Hs; inversion Hr; subst.
    destruct f as [|f]; simpl in *.
    + inversion Hn; subst. eauto.
    + eapply IH; eauto.
Qed.

Lemma view_flat : forall mt q0 Vs Us Qs qF E,
  member_type mt q0 Vs Us Qs (TClass qF E []) = TClass (vpa_q mt q0 qF) E [].
Proof. reflexivity. Qed.

(** An initializer type that is fully known reads the same in every mode. *)
Lemma vpa_eq_as : forall mt (qc : q_c) qF,
  vpa_q mt (qc2q qc) qF <> Lost ->
  vpa_q mt (qc2q qc) qF = vpa_q AbstractState (qc2q qc) qF.
Proof. intros mt qc qF H. destruct mt, qc, qF; simpl in *; congruence. Qed.

Lemma rs_new : forall P CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' κ l1 qthisr vals,
  no_tparams CT -> empty_tv_env Δ ->
  wf_r_config CT Δ sΓ rΓ h ->
  stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ' ->
  runtime_getVal rΓ 0 = Some (Iot l1) ->
  runtime_lookup_list rΓ ys = Some vals ->
  r_muttype h l1 = Some qthisr ->
  Inv P CT sΓ rΓ h κ ->
  (forall l, P l -> l < dom h) ->
  let onew := mkObj
                (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                   (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts)) vals in
  Inv P CT sΓ' (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) (h ++ [onew]) κ /\
  (forall v, safe P CT h v -> safe P CT (h ++ [onew]) v) /\
  (forall l qr C0 Rs vals0 f,
     P l ->
     runtime_getObj h l = Some (mkObj (mkruntime_type qr C0 Rs) vals0) ->
     exists vals',
       runtime_getObj (h ++ [onew]) l =
         Some (mkObj (mkruntime_type qr C0 Rs) vals') /\
       nth_error vals0 f = nth_error vals' f).
Proof.
  intros P CT Δ sΓ rΓ h mt x qc C Ts ys sΓ' κ l1 qthisr vals
    Hnt HΔ Hwf Htype Hthis0 Hvals Hmut HInv HPdom onew.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  assert (Hnewsafe : forall l, mcap CT (h ++ [onew]) (dom h) true l -> ~ P l).
  { intros l Hm. inversion Hm; subst.
    - intros HP. apply HPdom in HP. lia.
    - unfold onew in Hobj0. rewrite runtime_getObj_last in Hobj0.
      inversion Hobj0; subst o0. clear Hobj0. simpl in *.
      destruct (is_mut_type (ftype fd)) eqn:Hmutf;
        [|exfalso; eapply mcap_false_empty; eauto].
      assert (fs = fds) by eauto using collect_fields_deterministic_rel.
      subst fs.
      destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hvals Hval)
        as (y & A & HyA & Hyv & HnA).
      pose proof (Forall2_nth_error_rel _ _ _ f Harg_sub) as Hrel.
      rewrite HnA in Hrel. rewrite Hfd in Hrel.
      pose proof (collect_fields_flat _ _ _ Hct Hnt Hfields) as Hfl.
      rewrite Forall_forall in Hfl.
      destruct (Hfl _ (nth_error_In _ _ Hfd)) as (qF & D & HF).
      rewrite HF in Hmutf. rewrite HF in Hrel.
      destruct qF; simpl in Hmutf; try discriminate.
      rewrite view_flat in Hrel. destruct Hrel as [Hsub Hok].
      assert (Hnl : vpa_q mt (qc2q qc) Mut <> Lost).
      { intros Hl. destruct Hok as [Hq _].
          apply Hq. exact Hl. }
      rewrite (vpa_eq_as _ _ _ Hnl) in Hsub.
      assert (Hsv : safe P CT h v').
      { eapply Inv_var_sub with (U := TClass (vpa_q AbstractState (qc2q qc) Mut) D []);
          eauto.
        - exists (vpa_q AbstractState (qc2q qc) Mut), D. reflexivity.
        - destruct qc; reflexivity. }
      apply Hsv. eapply mcap_app_inv; eauto.
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HyA) as Hty.
      rewrite Hyv in Hty. unfold wf_r_typable in Hty.
      destruct (loc_has_rtype_getObj _ _ _ _ Hty) as [o' Ho'].
      eapply runtime_getObj_dom; eauto. }
  assert (Hsafe : forall v, safe P CT h v -> safe P CT (h ++ [onew]) v).
  { intros v Hs l Hm.
    destruct (Nat.lt_ge_cases v (dom h)) as [Hlt | Hge].
    - apply Hs. eapply mcap_app_inv; eauto.
    - pose proof (mcap_dom _ _ _ _ _ Hm) as Hd.
      rewrite length_app in Hd. simpl in Hd.
      assert (v = dom h) by lia. subst v. apply Hnewsafe; auto. }
  refine (conj _ (conj Hsafe _)).
  - eapply Inv_update_var; eauto.
    + eapply Inv_heap; eauto. apply (heap_ext_app h onew).
    + intros w Hw _. inversion Hw; subst w. exact Hnewsafe.
  - intros l qr C0 Rs vals0 f HP Hl.
    exists vals0. split; [|reflexivity].
    unfold onew. rewrite runtime_getObj_last2;
      [eapply runtime_getObj_dom; eauto | exact Hl].
Qed.

(* ------------------OVERRIDING------------------*)

Lemma find_method_In : forall CT C m D mdef,
  FindMethodWithName CT C m D mdef ->
  exists defD, find_class CT D = Some defD /\
               List.In mdef (methods (body defD)).
Proof.
  intros CT C m D mdef H. induction H; auto.
  subst own_methods. eauto using gget_method_In.
Qed.

(** Composition of a per-override relation along the lookup chain. *)
Lemma lookup_chain : forall CT qr (R : method_def -> method_def -> Prop),
  wf_class_table CT ->
  (forall m, R m m) ->
  (forall a b c, R a b -> R b c -> R a c) ->
  (forall D' ca' def' mdef' P Ss D1 mdef1,
     wf_rtypeuse CT (mkruntime_type qr D' ca') ->
     find_class CT D' = Some def' ->
     super (signature def') = Some (P, Ss) ->
     List.In mdef' (methods (body def')) ->
     wf_method CT D' mdef' ->
     FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1 ->
     R mdef' mdef1) ->
  forall Co Ro C Rs1,
    rsuper_inst CT (qr2q qr) Co Ro C Rs1 ->
    wf_rtypeuse CT (mkruntime_type qr Co Ro) ->
    forall m D' mdef' D mdef,
      FindMethodWithName CT Co m D' mdef' ->
      FindMethodWithName CT C m D mdef ->
      R mdef' mdef.
Proof.
  intros CT qr R Hct Hrefl Htrans Hstep Co Ro C Rs1 H.
  remember (qr2q qr) as qo eqn:Hqo.
  induction H as [C Rs | C Rs P Ss D0 Vs Hparent Hrest IH];
    intros Hrt m D' mdef' D mdef Hf' Hf.
  - destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hf' Hf) as [-> ->].
    apply Hrefl.
  - subst qo.
    pose proof Hparent as Hparent'. unfold parent_lookup in Hparent'.
    destruct (find_class CT C) as [def|] eqn:Hfind; [|discriminate].
    assert (HrtP : wf_rtypeuse CT
                     (mkruntime_type qr P (map (dyn (qr2q qr) Rs [] []) Ss))).
    { eapply rsuper_wf; [exact Hct | | exact Hrt].
      eapply rsi_step; eauto. apply rsi_refl. }
    inversion Hf'; subst.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      destruct (find_from_subclass _ _ _ _ _ _ Hrest _ _ _ Hf) as (D1 & mdef1 & HfP).
      eapply Htrans; [|eapply (IH HrtP); eauto].
      eapply (Hstep _ Rs def mdef' P Ss D1 mdef1 Hrt Hfind Hparent'
                (gget_method_In _ _ _ Hget_method)).
      * eapply find_method_wf; eauto.
      * rewrite (gget_method_name_consistent _ _ _ Hget_method). exact HfP.
    + rewrite Hfind in Hfind0. inversion Hfind0; subst def0. clear Hfind0.
      rewrite Hsuper in Hparent'. inversion Hparent'; subst.
      eapply (IH HrtP); eauto.
Qed.

(** The signature of a method in the fragment. *)
Lemma sig_flat : forall CT D def mdef,
  wf_class_table CT -> no_tparams CT ->
  find_class CT D = Some def ->
  List.In mdef (methods (body def)) ->
  wf_method CT D mdef ->
  empty_tv_env (method_tv_env CT D (msignature mdef)) /\
  flat_type (mret (msignature mdef)) /\
  Forall flat_type (mparams (msignature mdef)).
Proof.
  intros CT D def mdef Hct Hnt Hfind Hin Hwm.
  assert (HΔ : empty_tv_env (method_tv_env CT D (msignature mdef))).
  { split; simpl.
    - apply class_tparams_nil; auto.
    - destruct (Hnt _ _ Hfind) as [_ Hm]. rewrite Forall_forall in Hm. auto. }
  destruct Hwm as (_ & _ & Hret & (sΓb & Tb & Hbody & _) & _).
  refine (conj HΔ (conj _ _)).
  - eapply wf_stype_flat; eauto.
  - pose proof (stmt_typing_wf_env _ _ _ _ _ _ Hbody) as [_ Hall].
    inversion Hall; subst.
    eapply Forall_impl; [|exact H2]. intros T HT. eapply wf_stype_flat; eauto.
Qed.

(** How the mutable-reference reading of an overriding signature relates to
    that of the overridden one. *)
Definition bref (κ : bool) (sig' sig : method_sig) : Prop :=
  Forall2 (fun P P' => bitp κ P' = true -> bitp κ P = true)
    (mparams sig) (mparams sig') /\
  (bitp κ (mret sig) = true -> bitp κ (mret sig') = true).

Definition bref_rel (κ : bool) (mdef' mdef : method_def) : Prop :=
  mscope (msignature mdef') = mscope (msignature mdef) /\
  (readonly_state_method_scope (mscope (msignature mdef')) ->
   bref κ (msignature mdef') (msignature mdef)).

Lemma Forall2_impl_in : forall {A B : Type} (P Q : A -> B -> Prop) l1 l2,
  Forall2 P l1 l2 ->
  (forall a b, List.In a l1 -> List.In b l2 -> P a b -> Q a b) ->
  Forall2 Q l1 l2.
Proof.
  intros A B P Q l1 l2 H. induction H; intros Himp; constructor.
  - apply Himp; simpl; auto.
  - apply IHForall2. intros a b Ha Hb. apply Himp; simpl; auto.
Qed.

Lemma bref_step : forall CT qr κ D' ca' def' mdef' P Ss D1 mdef1,
  wf_class_table CT -> no_tparams CT ->
  (κ = true -> qr = Mut_r) ->
  wf_rtypeuse CT (mkruntime_type qr D' ca') ->
  find_class CT D' = Some def' ->
  super (signature def') = Some (P, Ss) ->
  List.In mdef' (methods (body def')) ->
  wf_method CT D' mdef' ->
  FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1 ->
  bref_rel κ mdef' mdef1.
Proof.
  intros CT qr κ D' ca' def' mdef' P Ss D1 mdef1
    Hct Hnt Hκ Hrt Hfind Hsuper Hin Hwm Hfm.
  unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
  destruct Hrt as (Hagree & _).
  set (qC := class_qualifier (signature def')) in *.
  destruct (find_rsuper_exists _ _ _ _ _ Hfm Mut (map (dyn Mut [] [] []) Ss))
    as [Xs Hrs0].
  assert (Hrs : rsuper_inst CT Mut D' [] D1 Xs).
  { eapply rsi_step; [|exact Hrs0].
    unfold parent_lookup. rewrite Hfind. exact Hsuper. }
  destruct (super_inst_exists _ _ _ _ _ _ Hrs AbstractState (qc2q qC)
              (class_var_types (length (ctparams (signature def')))))
    as [Vs Hsi].
  pose proof Hwm as (_ & _ & _ & _ & Hovr & Hroots).
  pose proof (Hovr def' P Ss D1 mdef1 Vs Hfind Hsuper Hfm Hsi) as Hcompat.
  destruct (sig_flat _ _ _ _ Hct Hnt Hfind Hin Hwm) as (HΔ & Hfret' & Hfpar').
  destruct (find_method_In _ _ _ _ _ Hfm) as (def1 & Hfind1 & Hin1).
  pose proof (find_method_wf _ _ _ _ _ Hct Hfm) as Hwm1.
  destruct (sig_flat _ _ _ _ Hct Hnt Hfind1 Hin1 Hwm1) as (_ & Hfret1 & Hfpar1).
  destruct Hcompat as (_ & Hscope & _ & Hret & Hpar & _).
  split; [exact Hscope|]. intros Hrs'.
  destruct (Hroots Hrs') as [_ Hnomut].
  rewrite Forall_forall in Hfpar'. rewrite Forall_forall in Hfpar1.
  rewrite Forall_forall in Hnomut.
  split.
  - eapply Forall2_impl_in; [exact Hpar|].
    intros P1 P' Hin_1 Hin_' Hsub Hb. simpl in Hsub.
    destruct (Hfpar1 _ Hin_1) as (q1 & E1 & ->).
    pose proof (Hfpar' _ Hin_') as HflP'.
    pose proof (Hnomut _ Hin_') as Hnm.
    rewrite view_flat in Hsub.
    pose proof (subtype_bitp _ _ _ _ κ Hsub HΔ HflP' Hb) as Hv.
    destruct HflP' as (q' & E' & ->).
    destruct (subtype_head _ _ _ _ Hsub HΔ _ _ _ eq_refl)
      as (qT & CT0 & bT & HeqT & HqT).
    inversion HeqT; subst qT CT0 bT. clear HeqT.
    inversion Hnm as [? ? ? Hnmq Hnmargs | | | |]; subst.
    unfold bitp in *. unfold qC in *.
    destruct (class_qualifier (signature def')), q1; simpl in *;
      try assumption; try discriminate;
      destruct HqT as [Hx | [Hx | Hx]]; subst; simpl in *;
      try discriminate; try congruence.
  - intros Hb.
    destruct Hfret1 as (qm & Em & Hm). destruct Hfret' as (q' & E' & Hm').
    rewrite Hm in Hb. rewrite Hm in Hret. rewrite Hm' in Hret. rewrite Hm'.
    rewrite view_flat in Hret.
    destruct (subtype_head _ _ _ _ Hret HΔ _ _ _ eq_refl)
      as (qT & CT0 & bT & HeqT & HqT).
    inversion HeqT; subst qT CT0 bT. clear HeqT.
    unfold bitp in *. unfold qC in *.
    destruct (class_qualifier (signature def')), qm; simpl in *;
      try discriminate;
      try (destruct HqT as [Hx | [Hx | Hx]]; subst; simpl in *;
           try discriminate; try reflexivity; try assumption; fail);
      (* an immutable-declared class with a receiver seen as mutable *)
      destruct κ; simpl in *; try discriminate;
      rewrite (Hκ eq_refl) in Hagree; simpl in Hagree; discriminate.
Qed.

(* ------------------CALLS------------------*)

Lemma Inv_var_subp : forall P CT Δ sΓ rΓ h κ ι o x T U v,
  no_tparams CT -> empty_tv_env Δ ->
  wf_r_config CT Δ sΓ rΓ h ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  Inv P CT sΓ rΓ h κ ->
  static_getType sΓ x = Some T ->
  runtime_getVal rΓ x = Some (Iot v) ->
  qualified_type_subtype CT Δ T U -> flat_type U ->
  bitp κ U = true ->
  safe P CT h v.
Proof.
  intros P CT Δ sΓ rΓ h κ ι o x T U v Hnt HΔ Hwf Hthis Hobj [_ Hv] HT Hval
    Hsub HU Hb.
  assert (Hp : bitp κ T = true) by (eapply subtype_bitp; eauto).
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HT) as Hty.
  rewrite Hval in Hty. apply val_typable_not_bot in Hty.
  unfold bitp in Hp. rewrite Hty in Hp. rewrite orb_false_r in Hp.
  eapply Hv; eauto.
Qed.

Lemma call_typing_inv : forall CT Δ sΓ mt x m y Us Qs zs sΓ',
  stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
  exists argtypes Tx Ty qy C Ts D Vs mdef,
    sΓ' = sΓ /\
    static_getType sΓ x = Some Tx /\
    static_getType sΓ y = Some Ty /\
    static_getType_list sΓ zs = Some argtypes /\
    ubound Δ Ty = Some (TClass qy C Ts) /\
    FindMethodWithName CT C m D mdef /\
    x <> 0 /\
    qualified_type_subtype CT Δ
      (member_type mt qy Vs Us Qs (mret (msignature mdef))) Tx /\
    Forall2 (fun A P => assignable_to CT Δ A (member_type mt qy Vs Us Qs P))
      argtypes (mparams (msignature mdef)) /\
    method_scope_subtype (mscope (msignature mdef)) mt.
Proof.
  intros. inversion H; subst.
  do 9 eexists. repeat split; eauto.
Qed.

Lemma bref_rel_refl : forall κ m, bref_rel κ m m.
Proof.
  intros κ m. split; auto. intros _. split; auto.
  induction (mparams (msignature m)); constructor; auto.
Qed.

Lemma bref_rel_trans : forall κ a b c,
  bref_rel κ a b -> bref_rel κ b c -> bref_rel κ a c.
Proof.
  intros κ a b c [Hs1 H1] [Hs2 H2]. split; [congruence|].
  intros Hrs. destruct (H1 Hrs) as [Hp1 Hr1].
  rewrite Hs1 in Hrs. destruct (H2 Hrs) as [Hp2 Hr2].
  split; auto.
  eapply Forall2_compose; [exact Hp2 | exact Hp1 |]. auto.
Qed.

Lemma head_ok_mut : forall qo, head_ok qo Mut -> qo = Mut_r.
Proof.
  intros [] H; auto. unfold head_ok in H.
  destruct H as [H | [H | H]]; discriminate.
Qed.

Lemma rs_param_bit : forall mt qy qP κ C E,
  readonly_state_method_scope mt ->
  bitp (bitk κ (TClass qy C [])) (TClass qP E []) = true ->
  bitp κ (TClass (vpa_q mt qy qP) E []) = true \/
  vpa_q mt qy qP = Lost.
Proof.
  intros mt qy qP κ C E [-> | ->] H;
    destruct qy, qP, κ; simpl in *; auto; discriminate.
Qed.

Lemma rs_ret_bit : forall mt qy qm κ C E,
  readonly_state_method_scope mt -> qy <> Bot ->
  bitp κ (TClass (vpa_q mt qy qm) E []) = true ->
  bitp (bitk κ (TClass qy C [])) (TClass qm E []) = true.
Proof.
  intros mt qy qm κ C E [-> | ->] Hnb H;
    destruct qy, qm, κ; simpl in *; auto; try discriminate; congruence.
Qed.

Lemma Inv_local : forall P CT sΓ rΓ h κ T,
  dom sΓ = dom (vars rΓ) ->
  Inv P CT sΓ rΓ h κ ->
  Inv P CT (sΓ ++ [T]) (set_vars rΓ (vars rΓ ++ [Null_a])) h κ.
Proof.
  intros P CT sΓ rΓ h κ T Hlen [HK Hv]. split.
  - intros Hκ. destruct (HK Hκ) as (ι & o & Hthis & Hrest).
    exists ι, o. simpl. rewrite get_this_var_mapping_app_null_last. auto.
  - intros x T0 v HT Hval Hb. unfold static_getType in HT.
    unfold runtime_getVal in Hval. simpl in Hval.
    destruct (Nat.lt_ge_cases x (dom sΓ)) as [Hlt | Hge].
    + rewrite nth_error_app1 in HT; auto.
      rewrite nth_error_app1 in Hval; [lia|]. eapply Hv; eauto.
    + rewrite nth_error_app2 in Hval; [lia|].
      destruct (x - dom (vars rΓ)) as [|k]; simpl in Hval; [discriminate|].
      destruct k; discriminate.
Qed.

Definition prot_preserved (P : Loc -> Prop) (CT : class_table)
    (mt : method_scope) (h h' : heap) : Prop :=
  forall l qr C Rs vals f,
    P l ->
    runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
    prot_cond CT C f mt ->
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
      nth_error vals f = nth_error vals' f.

Lemma prot_preserved_refl : forall P CT mt h, prot_preserved P CT mt h h.
Proof. intros P CT mt h l qr C Rs vals f _ Hl _. eauto. Qed.

(** The main step: executing readonly-state or transitive-state code keeps
    the invariant, keeps every safe location safe, and leaves the protected
    fields of the protected objects unchanged. *)
Lemma rs_step : forall P CT,
  no_tparams CT -> no_rdm_fields CT ->
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ' κ,
      empty_tv_env Δ ->
      readonly_state_method_scope mt ->
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      Inv P CT sΓ rΓ h κ ->
      (forall l, P l -> l < dom h) ->
      Inv P CT sΓ' rΓ' h' κ /\
      (forall v, safe P CT h v -> safe P CT h' v) /\
      prot_preserved P CT mt h h'.
Proof.
  intros P CT Hnt Hnr rΓ h s res rΓ' h' Heval.
  induction Heval; intros Hres Δ sΓ mt0 sΓ' κ HΔ Hrs Hwf Htype HInv HPdom;
    try discriminate.
  - (* skip *)
    inversion Htype; subst. auto using prot_preserved_refl.
  - (* local *)
    inversion Htype; subst.
    refine (conj _ (conj (fun v H => H) (prot_preserved_refl _ _ _ _))).
    apply Inv_local; auto. destruct Hwf as (_ & _ & _ & _ & _ & Hlen & _). exact Hlen.
  - (* assignment *)
    refine (conj _ (conj (fun v H => H) (prot_preserved_refl _ _ _ _))).
    eapply rs_assign; eauto.
  - (* field write *)
    subst. eapply rs_fldwrite; eauto.
  - (* object creation *)
    subst.
    destruct (rs_new P _ _ _ _ _ _ _ _ _ _ _ _ κ _ _ _ Hnt HΔ Hwf Htype
                Hthis Hargs Hmut HInv HPdom) as (HI & HS & HPp).
    refine (conj HI (conj HS _)).
    intros l qr C0 Rs vals0 f HP Hl _. eapply HPp; eauto.
  - (* call *)
    subst.
    pose proof Hwf as (Hct & Hheap & _).
    destruct (call_typing_inv _ _ _ _ _ _ _ _ _ _ _ Htype)
      as (argtypes & Tx & Ty & qy & C & Ts & Ds & Vs & smdef & -> & Hget_x &
          Hget_y & Hget_args & Hub & Hfind_s & Hx & Hret_sub & Harg_sub & Hscope_s).
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx' & Hthis & Hobj & Hoy & _ & _ & _ &
          Hfb & Hwm & Hcfg & Hthis' & _ & Hscope).
    pose proof (stmt_typing_wf_env _ _ _ _ _ _ Htype) as Hsenv.
    pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hsenv Hget_y) as HTy.
    destruct (flat_ubound _ _ _ _ _ HTy Hub) as [-> ->].
    pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hsenv Hget_x) as HTx.
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
    rewrite Hval_y in Hyty.
    pose proof (val_typable_not_bot _ _ _ _ _ _ _ _ Hyty) as Hynb.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hyty)
      as (oy' & Rs1 & Hoy' & Hhead & Hsup1 & _).
    rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'.
    pose proof (Hheap ly (runtime_getObj_dom _ _ _ Hoy)) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Hoy in Hwfo. destruct Hwfo as (Hrt_oy & _).
    unfold r_basetype in Hbase. rewrite Hoy in Hbase. inversion Hbase; subst cy.
    clear Hbase.
    destruct oy as [[qr Co Ro] fso]. simpl in *.
    set (κ' := bitk κ (TClass qy C [])).
    assert (HK' : κ' = true -> qr = Mut_r).
    { unfold κ'. intros Hk. destruct HInv as [HK _].
      destruct qy; simpl in Hk; try discriminate.
      - simpl in Hhead. apply head_ok_mut; auto.
      - destruct (HK Hk) as (ι0 & o0 & Hth0 & Ho0 & Hq0).
        assert (ι0 = ι) by congruence. subst ι0.
        rewrite Hobj in Ho0. inversion Ho0; subst o0.
        rewrite Hq0 in Hhead. simpl in Hhead. apply head_ok_mut; auto. }
    (* the selected method refines the statically seen one *)
    destruct (lookup_chain CT qr (bref_rel κ') Hct (bref_rel_refl κ')
                (bref_rel_trans κ')
                (fun D' ca' def' mdef' P0 Ss D1 mdef1 H1 H2 H3 H4 H5 H6 =>
                   bref_step CT qr κ' D' ca' def' mdef' P0 Ss D1 mdef1
                     Hct Hnt HK' H1 H2 H3 H4 H5 H6)
                _ _ _ _ Hsup1 Hrt_oy _ _ _ _ _ Hfind Hfind_s)
      as [Hsc Hbref].
    assert (Hrs' : readonly_state_method_scope (mscope (msignature mdef))).
    { eapply readonly_state_submethod; eauto. }
    destruct (Hbref Hrs') as [Hbpar Hbret].
    destruct (find_method_In _ _ _ _ _ Hfind) as (defD & HfD & HinD).
    destruct (sig_flat _ _ _ _ Hct Hnt HfD HinD Hwm) as (HΔ' & Hfret' & Hfpar').
    destruct (find_method_In _ _ _ _ _ Hfind_s) as (defS & HfS & HinS).
    pose proof (find_method_wf _ _ _ _ _ Hct Hfind_s) as Hwm_s.
    destruct (sig_flat _ _ _ _ Hct Hnt HfS HinS Hwm_s) as (_ & Hfret_s & Hfpar_s).
    pose proof Hwm as
      (Hrecv' & _ & _ & (sΓb & Tb & Hbody & Hnthb & Hsubb) & _ & Hroots').
    destruct (Hroots' Hrs') as [Hnm_recv _].
    pose proof (callee_env_targs _ _ _ _ _ _ _ _ _ Hframe) as Hvars'.
    (* the invariant for the callee activation *)
    assert (HInv' : Inv P CT
                      (mreceiver (msignature mdef) :: mparams (msignature mdef))
                      rΓ' h κ').
    { split.
      - intros Hk. exists ly, (mkObj (mkruntime_type qr Co Ro) fso).
        refine (conj Hthis' (conj Hoy _)). simpl. exact (HK' Hk).
      - intros x0 T v HT Hv Hb.
        unfold runtime_getVal in Hv. rewrite Hvars' in Hv.
        unfold static_getType in HT.
        destruct x0 as [|i]; simpl in HT, Hv.
        + inversion HT; subst T. inversion Hv; subst v.
          destruct (proj1 Hrecv') as (args0' & _ & [[q2 Hreq] | [n2 Hreq]]);
            [|rewrite Hreq in Hb; simpl in Hb; discriminate].
          rewrite Hreq in Hb. rewrite Hreq in Hnm_recv.
          inversion Hnm_recv as [? ? ? Hnmq _ | | | |]; subst.
          destruct q2; simpl in Hb; try discriminate; [congruence|].
          destruct HInv as [_ HInv]. eapply HInv; eauto.
        + pose proof (Forall2_nth_error_rel _ _ _ i Hbpar) as Hrel.
          rewrite HT in Hrel.
          destruct (nth_error (mparams (msignature smdef)) i) as [Ps|] eqn:HPs;
            [|contradiction].
          assert (Hbp : bitp κ' Ps = true).
          { apply Hrel. unfold bitp. rewrite Hb. reflexivity. }
          destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hargs Hv)
            as (yi & A & HyA & Hyv & HnA).
          pose proof (Forall2_nth_error_rel _ _ _ i Harg_sub) as Hrel2.
          rewrite HnA in Hrel2. rewrite HPs in Hrel2.
          rewrite Forall_forall in Hfpar_s.
          destruct (Hfpar_s _ (nth_error_In _ _ HPs)) as (qP & E & ->).
          rewrite view_flat in Hrel2. destruct Hrel2 as [Hsub Hok].
          destruct (rs_param_bit mt0 qy qP κ C E Hrs Hbp) as [Hbt | Hlost].
          * eapply (Inv_var_subp P CT Δ sΓ rΓ h κ ι o yi A
                      (TClass (vpa_q mt0 qy qP) E []) v
                      Hnt HΔ Hwf Hthis Hobj HInv HyA Hyv Hsub);
              [eexists _, _; reflexivity | exact Hbt].
          * rewrite Hlost in Hok. rewrite Hlost in Hsub.
            destruct Hok as [Hlf _]; congruence. }
    destruct (IHHeval Hnt Hnr eq_refl _ _ _ _ κ' HΔ' Hrs' Hcfg Hbody HInv' HPdom)
      as (HInv'' & Hsafe & Hprot).
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) as Hext.
    refine (conj _ (conj Hsafe _)).
    + eapply Inv_update_var; eauto.
      * eapply Inv_heap; eauto.
      * intros w -> Hb.
        pose proof (preservation_pico _ _ _ _ _ _ _ Heval eq_refl _ _ _ _ Hcfg Hbody)
          as Hcfg''.
        destruct (wf_r_config_this _ _ _ _ _ Hcfg'')
          as (ι2 & o2 & Hth2 & Hobj2 & _).
        pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hcfg'' Hth2 Hobj2 Hnthb) as Hrv.
        rewrite Hretval in Hrv.
        pose proof (val_typable_not_bot _ _ _ _ _ _ _ _ Hrv) as Hrnb.
        destruct Hfret_s as (qm & Em & Hm).
        rewrite Hm in Hret_sub. rewrite view_flat in Hret_sub.
        assert (Hb1 : bitp κ (TClass (vpa_q mt0 qy qm) Em []) = true).
        { eapply subtype_bitp; eauto. unfold bitp. rewrite Hb. reflexivity. }
        assert (Hqy : qy <> Bot) by (intros ->; discriminate).
        pose proof (rs_ret_bit _ _ _ _ C _ Hrs Hqy Hb1) as Hb2.
        fold κ' in Hb2. rewrite <- Hm in Hb2.
        pose proof (Hbret Hb2) as Hb3.
        assert (Hb4 : bitp κ' Tb = true) by (eapply subtype_bitp; eauto).
        unfold bitp in Hb4. rewrite Hrnb in Hb4. rewrite orb_false_r in Hb4.
        destruct HInv'' as [_ HInv'']. eapply HInv''; eauto.
    + intros l qr0 C0 Rs0 vals0 f HP Hl Hprot0.
      eapply Hprot; eauto.
      destruct Hprot0 as [Hp | [Hp | Hstrict]]; [left; auto | right; left; auto |].
      right. right. eapply concrete_assignability_submethod; eauto.
  - (* cast *)
    refine (conj _ (conj (fun v H => H) (prot_preserved_refl _ _ _ _))).
    eapply rs_cast; eauto.
  - (* sequence *)
    inversion Htype; subst.
    destruct (IHHeval1 Hnt Hnr eq_refl _ _ _ _ κ HΔ Hrs Hwf Htype1 HInv HPdom)
      as (HI1 & HS1 & HP1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval1) as [Hd1 _].
    assert (HPdom1 : forall l, P l -> l < dom h').
    { intros l HP. specialize (HPdom l HP). lia. }
    destruct (IHHeval2 Hnt Hnr eq_refl _ _ _ _ κ HΔ Hrs Hwf1 Htype2 HI1 HPdom1)
      as (HI2 & HS2 & HP2).
    refine (conj HI2 (conj (fun v H => HS2 v (HS1 v H)) _)).
    intros l qr C Rs vals f HP Hl Hprot.
    destruct (HP1 l qr C Rs vals f HP Hl Hprot) as (vals1 & Hl1 & He1).
    destruct (HP2 l qr C Rs vals1 f HP Hl1 Hprot) as (vals2 & Hl2 & He2).
    exists vals2. split; auto. congruence.
Qed.

(* ------------------THE THEOREMS------------------*)

(** A call that selects a readonly-state or transitive-state method leaves
    the protected fields of every object of the entry heap unchanged.  The
    objects reachable from the receiver and the arguments are a special
    case. *)
Theorem rs_ts_call_preservation_flat :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    no_tparams CT -> no_rdm_fields CT ->
    wf_r_config CT Δ sΓ rΓ h ->
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
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef
    Hnt Hnr Hwf Htype Heval Hvy Hbase Hfind Hrs l qr C Rs vals f Hl Hprot.
  pose proof Hwf as (Hct & _).
  inversion Heval; subst.
  rewrite Hvy in Hval_y. inversion Hval_y; subst ly0. clear Hval_y.
  rewrite Hbase in Hbase0. inversion Hbase0; subst cy0. clear Hbase0.
  destruct (find_method_with_name_deterministic _ _ _ _ _ _ _ Hfind Hfind0)
    as [<- <-].
  destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ Hwf Htype Hvy Hbase Hfind Hargs Hframe)
    as (ι & o & oy & Tx & _ & _ & _ & _ & _ & _ & _ & Hwm & Hcfg & _).
  destruct (find_method_In _ _ _ _ _ Hfind) as (defD & HfD & HinD).
  destruct (sig_flat _ _ _ _ Hct Hnt HfD HinD Hwm) as (HΔ' & _ & Hfpar).
  pose proof Hwm as (Hrecv & _ & _ & (sΓb & Tb & Hbody & _) & _ & Hroots).
  destruct (Hroots Hrs) as [Hnm_recv Hnm_par].
  set (P := fun l0 : Loc => l0 < dom h).
  assert (HInv : Inv P CT
                   (mreceiver (msignature mdef) :: mparams (msignature mdef))
                   rΓ'0 h false).
  { split; [discriminate|].
    intros x0 T v HT _ Hb. exfalso.
    assert (Hnm : no_mut (method_tv_env CT D (msignature mdef)) T).
    { unfold static_getType in HT. destruct x0 as [|i]; simpl in HT.
      - inversion HT; subst. exact Hnm_recv.
      - rewrite Forall_forall in Hnm_par. apply Hnm_par.
        eapply nth_error_In; eauto. }
    destruct T as [q0 C0 Ts0| |]; simpl in Hb; [|discriminate..].
    destruct q0; try discriminate.
    inversion Hnm; subst. congruence. }
  destruct (rs_step P CT Hnt Hnr _ _ _ _ _ _ Heval_body eq_refl _ _ _ _ false
              HΔ' Hrs Hcfg Hbody HInv (fun l0 H => H)) as (_ & _ & Hpres).
  eapply Hpres; eauto.
  unfold P. eapply runtime_getObj_dom; eauto.
Qed.

(** Readonly-state preservation: non-assignable fields keep their values. *)
Corollary readonly_state_preservation_flat :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    no_tparams CT -> no_rdm_fields CT ->
    wf_r_config CT Δ sΓ rΓ h ->
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
  intros. eapply rs_ts_call_preservation_flat; eauto.
  unfold prot_cond. tauto.
Qed.

(** Transitive-state preservation: every field keeps its value. *)
Corollary transitive_state_preservation_flat :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    no_tparams CT -> no_rdm_fields CT ->
    wf_r_config CT Δ sΓ rΓ h ->
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
  intros until mdef. intros Hnt Hnr Hwf Htype Heval Hvy Hbase Hfind Hts.
  intros. eapply rs_ts_call_preservation_flat; eauto.
  - rewrite Hts. right. reflexivity.
  - rewrite Hts. right. right. right. reflexivity.
Qed.

Print Assumptions readonly_state_preservation_flat.
Print Assumptions transitive_state_preservation_flat.

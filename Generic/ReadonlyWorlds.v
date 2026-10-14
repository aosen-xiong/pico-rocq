From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat.

(** Readonly-state and transitive-state preservation with receiver-dependent
    field types (still without type parameters).

    The invariant is stated with worlds.  Every activation works in one
    world.  An object allocated as mutable belongs to the world of the
    allocating activation; so does an object allocated as receiver-dependent
    when the receiver itself belongs to that world.  A callee whose receiver
    belongs to a live world continues in that world; any other callee opens a
    fresh world, which dies when it returns.  Mutable references never cross
    worlds: a variable typed mutable holds an object of its activation's
    world, and the mutable and receiver-dependent fields of an object of a
    live world stay in that world.  Protected objects belong to no world, so
    no mutable reference reaches them. *)

Definition coloring := Loc -> option nat.

Definition live (col : coloring) (L : list nat) (v : Loc) : Prop :=
  exists w, col v = Some w /\ List.In w L.

Lemma live_dec : forall col L v, {live col L v} + {~ live col L v}.
Proof.
  intros col L v. unfold live. destruct (col v) as [w|] eqn:Hc.
  - destruct (in_dec Nat.eq_dec w L) as [Hin | Hnin].
    + left. eauto.
    + right. intros (w' & Heq & Hin). inversion Heq; subst. contradiction.
  - right. intros (w' & Heq & _). discriminate.
Qed.

(** Heap part of the invariant. *)
Record heapG (P : Loc -> Prop) (CT : class_table) (h : heap)
    (col : coloring) (L : list nat) (next : nat) : Prop := {
  (* a coloured object exists, is unprotected, and is really mutable *)
  hg_col : forall l w, col l = Some w ->
    l < dom h /\ ~ P l /\ r_muttype h l = Some Mut_r /\ w < next;
  (* mutable and receiver-dependent fields of a live-world object stay in
     its world *)
  hg_in : forall l w o fs f fd v,
    col l = Some w -> List.In w L ->
    runtime_getObj h l = Some o ->
    CollectFields CT (rctype (rt_type o)) fs ->
    nth_error fs f = Some fd ->
    nth_error (fields_map o) f = Some (Iot v) ->
    (head_of (ftype fd) = Some Mut \/ head_of (ftype fd) = Some RDM) ->
    col v = Some w;
  (* receiver-dependent fields of an object outside the live worlds stay
     outside them *)
  hg_out : forall l o fs f fd v,
    ~ live col L l ->
    runtime_getObj h l = Some o ->
    CollectFields CT (rctype (rt_type o)) fs ->
    nth_error fs f = Some fd ->
    nth_error (fields_map o) f = Some (Iot v) ->
    head_of (ftype fd) = Some RDM ->
    ~ live col L v;
  hg_live : forall w, List.In w L -> w < next;
}.

(** Activation part of the invariant.  [wf] is the activation's world;
    [mode] says whether the receiver belongs to it. *)
Record frameF (CT : class_table) (sΓ : s_env) (rΓ : r_env)
    (col : coloring) (L : list nat) (wf : nat) (mode : bool) : Prop := {
  ff_live : List.In wf L;
  ff_this : mode = true ->
    exists ι, get_this_var_mapping (vars rΓ) = Some ι /\ col ι = Some wf;
  ff_mut : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    head_of T = Some Mut ->
    col v = Some wf;
  ff_rdm : forall x T v,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    head_of T = Some RDM ->
    if mode then col v = Some wf else ~ live col L v;
}.

(* ------------------FIELDS IN THE FRAGMENT------------------*)

Lemma subst_field_flat : forall Ss fd,
  flat_type (ftype fd) -> subst_field Ss fd = fd.
Proof.
  intros Ss [a0 T] (q0 & D & HT). simpl in HT. subst T. reflexivity.
Qed.

(** Without type parameters, a field of a superclass is literally the same
    declaration in the subclass. *)
Lemma collect_fields_prefix : forall CT qh Co Ro C Vs,
  wf_class_table CT -> no_tparams CT ->
  rsuper_inst CT qh Co Ro C Vs ->
  forall fsC fsO f fd,
    CollectFields CT C fsC -> CollectFields CT Co fsO ->
    nth_error fsC f = Some fd -> nth_error fsO f = Some fd.
Proof.
  intros CT qh Co Ro C Vs Hct Hnt H.
  induction H; intros fsC fsO f fd HcfC HcfO Hn.
  - assert (fsO = fsC) by eauto using collect_fields_deterministic_rel.
    subst. exact Hn.
  - destruct (CollectFields_inherit_inv _ _ _ _ _ Hparent HcfO)
      as (def & pfs & Hfind & Hpcf & ->).
    pose proof (IHrsuper_inst fsC pfs f fd HcfC Hpcf Hn) as HnP.
    rewrite nth_error_app1.
    + rewrite length_map. apply nth_error_Some. congruence.
    + rewrite nth_error_map. rewrite HnP. simpl. f_equal.
      apply subst_field_flat.
      pose proof (collect_fields_flat _ _ _ Hct Hnt Hpcf) as Hfl.
      rewrite Forall_forall in Hfl. apply Hfl. eapply nth_error_In; eauto.
Qed.

(** The field a statement names, as declared in the receiver object's own
    class. *)
Lemma static_field_in_object : forall CT Δ h loc qx C qctx ca ma ka f fd,
  wf_class_table CT -> no_tparams CT -> wf_heap CT h ->
  wf_r_typable CT h loc (TClass qx C []) qctx ca ma ka ->
  sf_def_rel CT C f fd ->
  empty_tv_env Δ ->
  exists o fsO,
    runtime_getObj h loc = Some o /\
    head_ok (rqtype (rt_type o)) (dynq (qr2q qctx) qx) /\
    CollectFields CT (rctype (rt_type o)) fsO /\
    nth_error fsO f = Some fd.
Proof.
  intros CT Δ h loc qx C qctx ca ma ka f fd Hct Hnt Hheap Hty Hfld _.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hty)
    as (o & Vs & Hobj & Hhead & Hsup & _).
  pose proof (Hheap loc (runtime_getObj_dom _ _ _ Hobj)) as Hwfo.
  unfold wf_obj in Hwfo. rewrite Hobj in Hwfo.
  destruct Hwfo as (_ & fsO & HcfO & _).
  inversion Hfld as [? ? fsC ? ? HcfC HgetC]; subst.
  exists o, fsO. repeat split; auto.
  eapply collect_fields_prefix; eauto.
Qed.

Lemma head_flat : forall T, flat_type T -> exists q0, head_of T = Some q0.
Proof. intros T (q0 & D & ->). exists q0. reflexivity. Qed.

Lemma subtype_head_of : forall CT Δ T U qU,
  qualified_type_subtype CT Δ T U -> empty_tv_env Δ ->
  head_of U = Some qU ->
  exists qT, head_of T = Some qT /\ (qT = qU \/ qU = RO \/ qT = Bot).
Proof.
  intros CT Δ T U qU Hsub HΔ HU.
  destruct U as [q0 D a| |]; simpl in HU; [|discriminate..]. inversion HU; subst.
  destruct (subtype_head _ _ _ _ Hsub HΔ _ _ _ eq_refl) as (qT & C & b & -> & Hq).
  simpl. eauto.
Qed.

Lemma typable_head_not_bot : forall CT h loc T qctx ca ma ka,
  wf_r_typable CT h loc T qctx ca ma ka -> head_of T <> Some Bot.
Proof.
  intros CT h loc T qctx ca ma ka H Hb.
  apply val_typable_not_bot in H.
  destruct T as [q0 C Ts| |]; simpl in *; [|discriminate..].
  inversion Hb; subst. discriminate.
Qed.

(** A location that inhabits a mutable-headed type is a mutable object; one
    that inhabits an immutable-headed type is an immutable object. *)
Lemma typable_mut_obj : forall CT h loc C Ts qctx ca ma ka,
  wf_r_typable CT h loc (TClass Mut C Ts) qctx ca ma ka ->
  r_muttype h loc = Some Mut_r.
Proof.
  intros CT h loc C Ts qctx ca ma ka H.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ H)
    as (o & Vs & Hobj & Hhead & _).
  simpl in Hhead. apply head_ok_mut in Hhead.
  unfold r_muttype. rewrite Hobj. congruence.
Qed.

Lemma typable_imm_obj : forall CT h loc C Ts qctx ca ma ka,
  wf_r_typable CT h loc (TClass Imm C Ts) qctx ca ma ka ->
  r_muttype h loc = Some Imm_r.
Proof.
  intros CT h loc C Ts qctx ca ma ka H.
  destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ H)
    as (o & Vs & Hobj & Hhead & _).
  simpl in Hhead. unfold head_ok in Hhead.
  unfold r_muttype. rewrite Hobj.
  destruct (rqtype (rt_type o)); auto.
  destruct Hhead as [Hx | [Hx | Hx]]; discriminate.
Qed.

Lemma not_live_of_imm : forall P CT h col L next l,
  heapG P CT h col L next -> r_muttype h l = Some Imm_r -> ~ live col L l.
Proof.
  intros P CT h col L next l HG Himm (w & Hc & _).
  destruct (hg_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & Hm & _). congruence.
Qed.

(* ------------------WHAT A STATIC HEAD SAYS ABOUT A VALUE------------------*)

Definition good (col : coloring) (L : list nat) (wf : nat) (mode : bool)
    (q0 : q) (v : Loc) : Prop :=
  match q0 with
  | Mut => col v = Some wf
  | RDM => if mode then col v = Some wf else ~ live col L v
  | Imm => ~ live col L v
  | _ => True
  end.

Section Frame.
  Variables (P : Loc -> Prop) (CT : class_table) (Δ : tv_env).
  Variables (sΓ : s_env) (rΓ : r_env) (h : heap).
  Variables (col : coloring) (L : list nat) (next wf : nat) (mode : bool).
  Hypothesis Hnt : no_tparams CT.
  Hypothesis HΔ : empty_tv_env Δ.
  Hypothesis Hwf : wf_r_config CT Δ sΓ rΓ h.
  Hypothesis HG : heapG P CT h col L next.
  Hypothesis HF : frameF CT sΓ rΓ col L wf mode.

  Lemma typable_good_imm : forall loc T qctx ca ma ka,
    wf_r_typable CT h loc T qctx ca ma ka -> head_of T = Some Imm ->
    ~ live col L loc.
  Proof.
    intros loc T qctx ca ma ka Hty Hh.
    destruct T as [q0 C Ts| |]; simpl in Hh; [|discriminate..].
    inversion Hh; subst.
    eapply not_live_of_imm; eauto using typable_imm_obj.
  Qed.

  Lemma var_good : forall ι o x T v q0,
    get_this_var_mapping (vars rΓ) = Some ι ->
    runtime_getObj h ι = Some o ->
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot v) ->
    head_of T = Some q0 ->
    good col L wf mode q0 v.
  Proof.
    intros ι o x T v q0 Hthis Hobj HT Hv Hh.
    destruct q0; simpl; auto.
    - eapply (ff_mut _ _ _ _ _ _ _ HF); eauto.
    - pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HT) as Hty.
      rewrite Hv in Hty. eapply typable_good_imm; eauto.
    - eapply (ff_rdm _ _ _ _ _ _ _ HF); eauto.
  Qed.

  (** Goodness is kept along subtyping. *)
  Lemma good_sub : forall T U v qT qU qctx ca ma ka,
    qualified_type_subtype CT Δ T U ->
    wf_r_typable CT h v T qctx ca ma ka ->
    frame_bounds_ok CT Δ (qr2q qctx) ca ma ka ->
    head_of T = Some qT -> head_of U = Some qU ->
    good col L wf mode qT v ->
    good col L wf mode qU v.
  Proof.
    intros T U v qT qU qctx ca ma ka Hsub Hty Hfb HhT HhU Hg.
    destruct (subtype_head_of _ _ _ _ _ Hsub HΔ HhU) as (qT' & HhT' & Hq).
    rewrite HhT in HhT'. inversion HhT'; subst qT'.
    destruct Hq as [-> | [-> | ->]]; auto.
    - simpl. exact I.
    - exfalso. eapply typable_head_not_bot; eauto.
  Qed.
End Frame.

Lemma frameF_update : forall CT sΓ rΓ col L wf mode x v Tx,
  frameF CT sΓ rΓ col L wf mode ->
  x <> 0 ->
  static_getType sΓ x = Some Tx ->
  (forall w q0, v = Iot w -> head_of Tx = Some q0 -> good col L wf mode q0 w) ->
  frameF CT sΓ (set_vars rΓ (update x v (vars rΓ))) col L wf mode.
Proof.
  intros CT sΓ rΓ col L wf mode x v Tx HF Hx HTx Hnew.
  assert (Hget : forall y w, runtime_getVal (set_vars rΓ (update x v (vars rΓ))) y
                               = Some (Iot w) ->
                  (y = x /\ v = Iot w) \/ (y <> x /\ runtime_getVal rΓ y = Some (Iot w))).
  { intros y w Hv. unfold runtime_getVal in *. simpl in Hv.
    destruct (Nat.eq_dec x y) as [-> | Hne].
    - left. split; auto. apply nth_error_update_same_inv in Hv. congruence.
    - right. rewrite update_diff in Hv; auto. }
  constructor.
  - exact (ff_live _ _ _ _ _ _ _ HF).
  - intros Hm. destruct (ff_this _ _ _ _ _ _ _ HF Hm) as (ι & Hthis & Hc).
    exists ι. simpl. rewrite get_this_var_mapping_update; auto.
  - intros y T w HT Hv Hh.
    destruct (Hget y w Hv) as [[-> ->] | [Hne Hv']].
    + assert (T = Tx) by (unfold static_getType in *; congruence). subst T.
      exact (Hnew w Mut eq_refl Hh).
    + eapply (ff_mut _ _ _ _ _ _ _ HF); eauto.
  - intros y T w HT Hv Hh.
    destruct (Hget y w Hv) as [[-> ->] | [Hne Hv']].
    + assert (T = Tx) by (unfold static_getType in *; congruence). subst T.
      exact (Hnew w RDM eq_refl Hh).
    + eapply (ff_rdm _ _ _ _ _ _ _ HF); eauto.
Qed.

(* ------------------EXPRESSIONS, ASSIGNMENT, CAST------------------*)

Lemma rs_vpa_cases : forall mt qy qF,
  readonly_state_method_scope mt ->
  (vpa_q mt qy qF = Mut -> qy = Mut /\ (qF = Mut \/ qF = RDM)) /\
  (vpa_q mt qy qF = RDM -> qy = RDM /\ qF = RDM).
Proof.
  intros mt qy qF [-> | ->]; destruct qy, qF; simpl; split; intros H;
    try discriminate; auto.
Qed.

Lemma expr_good : forall P CT Δ sΓ rΓ h col L next wf mode mt e Te w ι o q0,
  no_tparams CT -> empty_tv_env Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapG P CT h col L next ->
  frameF CT sΓ rΓ col L wf mode ->
  get_this_var_mapping (vars rΓ) = Some ι ->
  runtime_getObj h ι = Some o ->
  frame_bounds_ok CT Δ (qr2q (rqtype (rt_type o))) (cargs rΓ) (margs rΓ) (qargs rΓ) ->
  expr_has_type CT Δ sΓ mt e Te ->
  eval_expr CT rΓ h e (Iot w) OK rΓ h ->
  head_of Te = Some q0 ->
  good col L wf mode q0 w.
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt e Te w ι o q0
    Hnt HΔ Hrs Hwf HG HF Hthis Hobj Hfb Htype Heval Hh.
  pose proof (expr_eval_typable _ _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hfb Htype Heval)
    as Hty. simpl in Hty.
  inversion Htype; subst; inversion Heval; subst.
  - eapply var_good; eauto.
  - pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hwf0 Hget_x) as HT.
    destruct (flat_ubound _ _ _ _ _ HT Hub) as [-> ->].
    pose proof Hwf as (Hct & Hheap & _).
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hyty.
    rewrite Hval in Hyty.
    destruct (static_field_in_object _ Δ _ _ _ _ _ _ _ _ _ _ Hct Hnt Hheap Hyty
                Hfld_def HΔ) as (oy & fsO & Hoy & _ & HcfO & HnO).
    rewrite Hobj0 in Hoy. inversion Hoy; subst oy. clear Hoy.
    pose proof (collect_fields_flat _ _ _ Hct Hnt HcfO) as Hfl.
    rewrite Forall_forall in Hfl.
    destruct (Hfl _ (nth_error_In _ _ HnO)) as (qF & D & HF0).
    rewrite HF0 in Hh. rewrite HF0 in Hty. rewrite view_flat in Hh.
    simpl in Hh. inversion Hh; subst q0.
    pose proof (var_good P CT Δ sΓ rΓ h col L next wf mode Hwf HG HF
                  _ _ _ _ _ qx Hthis Hobj Hget_x Hval eq_refl) as Hgy.
    destruct (rs_vpa_cases mt qx qF Hrs) as [Hmut Hrdm].
    destruct (vpa_q mt qx qF) eqn:Hv; simpl; auto.
    + destruct (Hmut eq_refl) as [-> HqF]. simpl in Hgy.
      eapply (hg_in _ _ _ _ _ _ HG); eauto using (ff_live _ _ _ _ _ _ _ HF).
      rewrite HF0. simpl. destruct HqF as [-> | ->]; auto.
    + rewrite view_flat in Hty. rewrite Hv in Hty.
      eapply typable_good_imm; eauto.
    + destruct (Hrdm eq_refl) as [-> ->]. simpl in Hgy.
      destruct mode.
      * eapply (hg_in _ _ _ _ _ _ HG); eauto using (ff_live _ _ _ _ _ _ _ HF).
        rewrite HF0. simpl. auto.
      * eapply (hg_out _ _ _ _ _ _ HG); eauto. rewrite HF0. reflexivity.
Qed.

Lemma rw_assign : forall P CT Δ sΓ rΓ h col L next wf mode mt x e v sΓ',
  no_tparams CT -> empty_tv_env Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapG P CT h col L next ->
  frameF CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SVarAss x e) sΓ' ->
  eval_expr CT rΓ h e v OK rΓ h ->
  frameF CT sΓ' (set_vars rΓ (update x v (vars rΓ))) col L wf mode.
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x e v sΓ'
    Hnt HΔ Hrs Hwf HG HF Htype Heval.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  eapply frameF_update; eauto.
  intros w q0 -> HhTx.
  pose proof (expr_eval_typable _ _ _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hfb Htype_e Heval)
    as Hty. simpl in Hty.
  destruct (subtype_head_of _ _ _ _ _ Hsub HΔ HhTx) as (qe & Hhe & _).
  eapply good_sub; eauto.
  eapply expr_good; eauto.
Qed.

Lemma rw_cast : forall P CT Δ sΓ rΓ h col L next wf mode mt x T y v sΓ',
  no_tparams CT -> empty_tv_env Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapG P CT h col L next ->
  frameF CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SCast x T y) sΓ' ->
  runtime_getVal rΓ y = Some v ->
  frameF CT sΓ' (set_vars rΓ (update x v (vars rΓ))) col L wf mode.
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x T y v sΓ'
    Hnt HΔ Hrs Hwf HG HF Htype Hval.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  eapply frameF_update; eauto.
  intros w q0 -> HhTx.
  assert (Hsub' : qualified_type_subtype CT Δ Ty Tx).
  { destruct Hsource as [Hs | Hnarrow].
    - eapply qtype_trans; eauto.
    - exfalso. destruct Hrs as [-> | ->]; simpl in Hscope; auto. }
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hty.
  rewrite Hval in Hty.
  destruct (subtype_head_of _ _ _ _ _ Hsub' HΔ HhTx) as (qy & Hhy & _).
  eapply good_sub; eauto.
  eapply var_good; eauto.
Qed.

(* ------------------FIELD WRITE------------------*)

Lemma update_field_r_muttype : forall h lx f0 vy l,
  r_muttype (update_field h lx f0 vy) l = r_muttype h l.
Proof.
  intros. unfold r_muttype.
  destruct (Nat.eq_dec lx l) as [-> | Hne].
  - destruct (runtime_getObj h l) as [o|] eqn:Ho.
    + rewrite (update_field_getObj_same _ _ _ _ _ Ho). reflexivity.
    + unfold update_field. rewrite Ho. rewrite Ho. reflexivity.
  - rewrite update_field_getObj_diff; auto.
Qed.

Lemma heapG_update : forall P CT h col L next lx ox fsO f0 fd vy,
  heapG P CT h col L next ->
  runtime_getObj h lx = Some ox ->
  CollectFields CT (rctype (rt_type ox)) fsO ->
  nth_error fsO f0 = Some fd ->
  (forall w wv, col lx = Some w -> List.In w L -> vy = Iot wv ->
     (head_of (ftype fd) = Some Mut \/ head_of (ftype fd) = Some RDM) ->
     col wv = Some w) ->
  (forall wv, ~ live col L lx -> vy = Iot wv ->
     head_of (ftype fd) = Some RDM -> ~ live col L wv) ->
  heapG P CT (update_field h lx f0 vy) col L next.
Proof.
  intros P CT h col L next lx ox fsO f0 fd vy HG Hox HcfO HnO HO1 HO2.
  constructor.
  - intros l w Hc. destruct (hg_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
    rewrite update_field_length. rewrite update_field_r_muttype. auto.
  - intros l w o fs f fd0 v Hc Hin Hobj Hcf Hn Hval Hh.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Hobj.
      inversion Hobj; subst o. simpl in *.
      assert (fs = fsO) by eauto using collect_fields_deterministic_rel. subst fs.
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * apply nth_error_update_same_inv in Hval. subst vy.
        assert (fd0 = fd) by congruence. subst fd0. eapply HO1; eauto.
      * rewrite update_diff in Hval; auto.
        eapply (hg_in _ _ _ _ _ _ HG); eauto.
    + rewrite update_field_getObj_diff in Hobj; auto.
      eapply (hg_in _ _ _ _ _ _ HG); eauto.
  - intros l o fs f fd0 v Hnl Hobj Hcf Hn Hval Hh.
    destruct (Nat.eq_dec lx l) as [-> | Hne].
    + rewrite (update_field_getObj_same _ _ _ _ _ Hox) in Hobj.
      inversion Hobj; subst o. simpl in *.
      assert (fs = fsO) by eauto using collect_fields_deterministic_rel. subst fs.
      destruct (Nat.eq_dec f0 f) as [-> | Hnf].
      * apply nth_error_update_same_inv in Hval. subst vy.
        assert (fd0 = fd) by congruence. subst fd0. eapply HO2; eauto.
      * rewrite update_diff in Hval; auto.
        eapply (hg_out _ _ _ _ _ _ HG); eauto.
    + rewrite update_field_getObj_diff in Hobj; auto.
      eapply (hg_out _ _ _ _ _ _ HG); eauto.
  - exact (hg_live _ _ _ _ _ _ HG).
Qed.

(** The case analysis behind a typed field write: what the static receiver
    and field qualifiers say about the worlds of the receiver object and of
    the stored value. *)
Lemma write_worlds : forall mt qx qF col L wf mode lx wv,
  readonly_state_method_scope mt ->
  vpa_q mt qx qF <> Lost -> qx <> Bot ->
  List.In wf L ->
  good col L wf mode qx lx ->
  good col L wf mode (vpa_q mt qx qF) wv ->
  (forall w, col lx = Some w -> List.In w L ->
     (qF = Mut \/ qF = RDM) -> col wv = Some w) /\
  (~ live col L lx -> qF = RDM -> ~ live col L wv).
Proof.
  intros mt qx qF col L wf mode lx wv Hrs Hnl Hnb HinL Hgx Hgv.
  assert (Hlive : col lx = Some wf -> live col L lx) by (intros; exists wf; auto).
  split.
  - intros w Hc Hin HqF.
    destruct Hrs as [-> | ->]; destruct qx, qF, mode; simpl in *;
      try congruence; try (destruct HqF; discriminate);
      try (exfalso; apply Hgx; exists w; auto; fail).
  - intros Hnlx HqF. subst qF.
    destruct Hrs as [-> | ->]; destruct qx, mode; simpl in *;
      try congruence; auto; try (exfalso; auto; fail).
Qed.

Lemma rw_fldwrite : forall P CT Δ sΓ rΓ h col L next wf mode mt x f0 y sΓ'
    lx ox a0 vf vy,
  no_tparams CT -> empty_tv_env Δ ->
  readonly_state_method_scope mt ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapG P CT h col L next ->
  frameF CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SFldWrite x f0 y) sΓ' ->
  runtime_getVal rΓ x = Some (Iot lx) ->
  runtime_getObj h lx = Some ox ->
  getVal (fields_map ox) f0 = Some vf ->
  sf_assignability_rel CT (rctype (rt_type ox)) f0 a0 ->
  runtime_getVal rΓ y = Some vy ->
  heapG P CT (update_field h lx f0 vy) col L next /\
  prot_preserved P CT mt h (update_field h lx f0 vy).
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x f0 y sΓ' lx ox a0 vf vy
    Hnt HΔ Hrs Hwf HG HF Htype Hvx Hox Hvf Hassign Hvy.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & _ & _ & _ & Hfb).
  pose proof Hwf as (Hct & Hheap & _).
  pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hwf0 Hget_x) as HTx.
  destruct (flat_ubound _ _ _ _ _ HTx Hub) as [-> ->].
  pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_x) as Hxty.
  rewrite Hvx in Hxty.
  destruct (static_field_in_object _ Δ _ _ _ _ _ _ _ _ _ _ Hct Hnt Hheap Hxty
              Hfld_def HΔ) as (ox' & fsO & Hox' & _ & HcfO & HnO).
  rewrite Hox in Hox'. inversion Hox'; subst ox'. clear Hox'.
  pose proof (collect_fields_flat _ _ _ Hct Hnt HcfO) as Hfl.
  rewrite Forall_forall in Hfl.
  destruct (Hfl _ (nth_error_In _ _ HnO)) as (qF & D & HF0).
  pose proof (var_good P CT Δ sΓ' rΓ h col L next wf mode Hwf HG HF
                _ _ _ _ _ qx Hthis Hobj Hget_x Hvx eq_refl) as Hgx.
  assert (Hqxb : qx <> Bot).
  { intros ->. eapply typable_head_not_bot; eauto. }
  rewrite HF0 in Hsub. rewrite view_flat in Hsub. destruct Hsub as [Hsub Hok].
  split.
  - eapply heapG_update; eauto.
    + intros w wv Hc Hin -> Hh.
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
      rewrite Hvy in Hyty.
      assert (Hnl : vpa_q mt qx qF <> Lost).
      { intros Hl. rewrite Hl in Hok.
        destruct Hok as [Hlf _]; congruence. }
      destruct (subtype_head_of _ _ _ _ _ Hsub HΔ eq_refl) as (qy & Hhy & _).
      assert (Hgv : good col L wf mode (vpa_q mt qx qF) wv).
      { eapply good_sub; eauto. eapply var_good; eauto. }
      destruct (write_worlds mt qx qF col L wf mode lx wv Hrs Hnl Hqxb
                  (ff_live _ _ _ _ _ _ _ HF) Hgx Hgv) as [H1 _].
      apply H1; auto. rewrite HF0 in Hh. simpl in Hh.
      destruct Hh as [Hh | Hh]; inversion Hh; auto.
    + intros wv Hnlx -> Hh.
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
      rewrite Hvy in Hyty.
      assert (Hnl : vpa_q mt qx qF <> Lost).
      { intros Hl. rewrite Hl in Hok.
        destruct Hok as [Hlf _]; congruence. }
      destruct (subtype_head_of _ _ _ _ _ Hsub HΔ eq_refl) as (qy & Hhy & _).
      assert (Hgv : good col L wf mode (vpa_q mt qx qF) wv).
      { eapply good_sub; eauto. eapply var_good; eauto. }
      destruct (write_worlds mt qx qF col L wf mode lx wv Hrs Hnl Hqxb
                  (ff_live _ _ _ _ _ _ _ HF) Hgx Hgv) as [_ H2].
      apply H2; auto. rewrite HF0 in Hh. simpl in Hh. inversion Hh; auto.
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
        subst qx. simpl in Hgx.
        destruct (hg_col _ _ _ _ _ _ HG _ _ Hgx) as (_ & HnP & _). auto.
      * symmetry. apply update_diff; auto.
    + rewrite update_field_getObj_diff; auto. exists vals. split; auto.
Qed.

(* ------------------OBJECT CREATION------------------*)

Definition new_color (qc : q_c) (wf : nat) (mode : bool) : option nat :=
  match qc with
  | Mut_c => Some wf
  | RDM_c => if mode then Some wf else None
  | Imm_c => None
  end.

Definition col_ext (col : coloring) (n : Loc) (c : option nat) : coloring :=
  fun l => if Nat.eqb l n then c else col l.

Lemma col_ext_other : forall col n c l, l <> n -> col_ext col n c l = col l.
Proof.
  intros. unfold col_ext. destruct (Nat.eqb l n) eqn:E; auto.
  apply Nat.eqb_eq in E. contradiction.
Qed.

Lemma col_ext_same : forall col n c, col_ext col n c n = c.
Proof. intros. unfold col_ext. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma live_col_ext_other : forall col n c L v,
  v <> n -> (live (col_ext col n c) L v <-> live col L v).
Proof.
  intros. unfold live. rewrite col_ext_other; auto. reflexivity.
Qed.

Lemma var_value_dom : forall CT rΓ h x v,
  wf_renv CT rΓ h -> runtime_getVal rΓ x = Some (Iot v) -> v < dom h.
Proof.
  intros CT rΓ h x v (_ & _ & Hall) Hv.
  rewrite Forall_forall in Hall.
  specialize (Hall (Iot v) (nth_error_In _ _ Hv)). simpl in Hall.
  destruct (runtime_getObj h v) eqn:Ho; [|contradiction].
  eapply runtime_getObj_dom; eauto.
Qed.

Lemma creation_mut : forall qthisr qc,
  qc = Mut_c \/ (qc = RDM_c /\ qthisr = Mut_r) ->
  vpa_mutability_object_creation qthisr qc = Mut_r.
Proof.
  intros qthisr qc [-> | [-> ->]]; [destruct qthisr|]; reflexivity.
Qed.

Lemma rw_new : forall P CT Δ sΓ rΓ h col L next wf mode mt x qc C Ts ys sΓ'
    l1 qthisr vals,
  no_tparams CT -> empty_tv_env Δ ->
  wf_r_config CT Δ sΓ rΓ h ->
  heapG P CT h col L next ->
  frameF CT sΓ rΓ col L wf mode ->
  stmt_typing CT Δ sΓ mt (SNew x qc C Ts ys) sΓ' ->
  runtime_getVal rΓ 0 = Some (Iot l1) ->
  runtime_lookup_list rΓ ys = Some vals ->
  r_muttype h l1 = Some qthisr ->
  (forall l, P l -> l < dom h) ->
  let onew := mkObj
                (mkruntime_type (vpa_mutability_object_creation qthisr qc) C
                   (map (dyn (qr2q qthisr) (cargs rΓ) (margs rΓ) (qargs rΓ)) Ts)) vals in
  let col' := col_ext col (dom h) (new_color qc wf mode) in
  heapG P CT (h ++ [onew]) col' L next /\
  frameF CT sΓ' (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) col' L wf mode /\
  (forall l, l < dom h -> col' l = col l).
Proof.
  intros P CT Δ sΓ rΓ h col L next wf mode mt x qc C Ts ys sΓ' l1 qthisr vals
    Hnt HΔ Hwf HG HF Htype Hthis0 Hvals Hmut HPdom onew col'.
  inversion Htype; subst.
  destruct (wf_r_config_this _ _ _ _ _ Hwf)
    as (ι & o & Hthis & Hobj & Hmut' & _ & _ & Hfb).
  pose proof Hwf as (Hct & Hheap & Hrenv & _).
  apply get_this_runtime_getVal in Hthis0.
  assert (l1 = ι) by congruence. subst l1.
  pose proof (ff_live _ _ _ _ _ _ _ HF) as HwfL.
  assert (Hold : forall l, l < dom h -> col' l = col l).
  { intros l Hl. unfold col'. apply col_ext_other. lia. }
  assert (Hliveold : forall v, v < dom h -> (live col' L v <-> live col L v)).
  { intros v Hv. unfold col'. apply live_col_ext_other. lia. }
  assert (Hnew : col' (dom h) = new_color qc wf mode)
    by (unfold col'; apply col_ext_same).
  assert (Hcolored_dom : forall l w, col l = Some w -> l < dom h).
  { intros l w Hc. destruct (hg_col _ _ _ _ _ _ HG _ _ Hc); auto. }
  pose proof (collect_fields_flat _ _ _ Hct Hnt Hfields) as Hfl.
  rewrite Forall_forall in Hfl.
  (* what an initializer's field type says about the initializer *)
  assert (Harg : forall f fd v,
            nth_error fds f = Some fd ->
            nth_error vals f = Some (Iot v) ->
            exists qF D,
              ftype fd = TClass qF D [] /\ v < dom h /\
              good col L wf mode (vpa_q AbstractState (qc2q qc) qF) v).
  { intros f fd v Hfd Hv.
    destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hvals Hv)
      as (y & A & HyA & Hyv & HnA).
    pose proof (Forall2_nth_error_rel _ _ _ f Harg_sub) as Hrel.
    rewrite HnA in Hrel. rewrite Hfd in Hrel.
    destruct (Hfl _ (nth_error_In _ _ Hfd)) as (qF & D & HF0).
    rewrite HF0 in Hrel. rewrite view_flat in Hrel. destruct Hrel as [Hsub Hok].
    exists qF, D. split; auto. split; [eapply var_value_dom; eauto|].
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HyA) as Hty.
    rewrite Hyv in Hty.
    assert (Hnl : vpa_q mt (qc2q qc) qF <> Lost).
    { intros Hl. destruct Hok as [Hq _].
        apply Hq. exact Hl. }
    rewrite (vpa_eq_as _ _ _ Hnl) in Hsub.
    destruct (subtype_head_of _ _ _ _ _ Hsub HΔ eq_refl) as (qy & Hhy & _).
    eapply good_sub; eauto. eapply var_good; eauto. }
  assert (HG' : heapG P CT (h ++ [onew]) col' L next).
  { constructor.
    - intros l w Hc.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + rewrite Hnew in Hc.
        assert (Hw : w = wf).
        { destruct qc, mode; simpl in Hc; congruence. }
        subst w. refine (conj _ (conj _ (conj _ _))).
        * rewrite length_app. simpl. lia.
        * intros HP. apply HPdom in HP. lia.
        * unfold r_muttype, onew. rewrite runtime_getObj_last. simpl. f_equal.
          apply creation_mut.
          destruct qc, mode; simpl in Hc; try discriminate; auto.
          right. split; auto.
          destruct (ff_this _ _ _ _ _ _ _ HF eq_refl) as (ι0 & Hth0 & Hc0).
          assert (ι0 = ι) by congruence. subst ι0.
          destruct (hg_col _ _ _ _ _ _ HG _ _ Hc0) as (_ & _ & Hm & _). congruence.
        * exact (hg_live _ _ _ _ _ _ HG _ HwfL).
      + unfold col' in Hc. rewrite col_ext_other in Hc; auto.
        destruct (hg_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
        refine (conj _ (conj H2 (conj _ H4))).
        * rewrite length_app. lia.
        * unfold r_muttype in *. unfold onew. rewrite runtime_getObj_last2; auto.
    - intros l w o0 fs f fd v Hc Hin Ho Hcf Hn Hval Hh.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
        inversion Ho; subst o0. simpl in *.
        assert (fs = fds) by eauto using collect_fields_deterministic_rel. subst fs.
        destruct (Harg _ _ _ Hn Hval) as (qF & D & HF0 & Hvd & Hgood).
        rewrite Hold; auto. rewrite Hnew in Hc. rewrite HF0 in Hh. simpl in Hh.
        destruct qc, mode, qF; simpl in *;
          try discriminate; try (destruct Hh; discriminate); congruence.
      + unfold col' in Hc. rewrite col_ext_other in Hc; auto.
        pose proof (Hcolored_dom _ _ Hc) as Hl.
        unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
        rewrite Hold; [eapply heap_field_dom; eauto|].
        eapply (hg_in _ _ _ _ _ _ HG); eauto.
    - intros l o0 fs f fd v Hnl Ho Hcf Hn Hval Hh.
      destruct (Nat.eq_dec l (dom h)) as [-> | Hne].
      + unfold onew in Ho. rewrite runtime_getObj_last in Ho.
        inversion Ho; subst o0. simpl in *.
        assert (fs = fds) by eauto using collect_fields_deterministic_rel. subst fs.
        destruct (Harg _ _ _ Hn Hval) as (qF & D & HF0 & Hvd & Hgood).
        rewrite Hliveold; auto. rewrite HF0 in Hh. simpl in Hh.
        inversion Hh; subst qF.
        assert (Hnc : new_color qc wf mode = None).
        { destruct (new_color qc wf mode) as [w|] eqn:Hnc; auto.
          exfalso. apply Hnl. exists w. split; [rewrite Hnew; auto|].
          destruct qc, mode; simpl in Hnc; try discriminate;
            inversion Hnc; subst; auto. }
        destruct qc, mode; simpl in *; try discriminate; auto.
      + assert (Hl : l < dom h).
        { apply runtime_getObj_dom in Ho. rewrite length_app in Ho. simpl in Ho. lia. }
        unfold onew in Ho. rewrite runtime_getObj_last2 in Ho; auto.
        rewrite Hliveold in Hnl; auto.
        rewrite Hliveold; [eapply heap_field_dom; eauto|].
        eapply (hg_out _ _ _ _ _ _ HG); eauto.
    - exact (hg_live _ _ _ _ _ _ HG). }
  refine (conj HG' (conj _ Hold)).
  (* the activation, first with the old variables, then with the new one *)
  assert (HF0 : frameF CT sΓ' rΓ col' L wf mode).
  { constructor.
    - exact HwfL.
    - intros Hm. destruct (ff_this _ _ _ _ _ _ _ HF Hm) as (ι0 & Hth0 & Hc0).
      exists ι0. split; auto. rewrite Hold; eauto.
    - intros y T v HT Hv Hh. rewrite Hold; [eapply var_value_dom; eauto|].
      eapply (ff_mut _ _ _ _ _ _ _ HF); eauto.
    - intros y T v HT Hv Hh.
      pose proof (ff_rdm _ _ _ _ _ _ _ HF _ _ _ HT Hv Hh) as Hr.
      assert (Hvd : v < dom h) by (eapply var_value_dom; eauto).
      destruct mode.
      + rewrite Hold; auto.
      + rewrite Hliveold; auto. }
  eapply frameF_update; eauto.
  intros w q0 Hw HhTx. inversion Hw; subst w.
  destruct (subtype_head_of _ _ _ _ _ Hresult_sub HΔ HhTx) as (qn & Hhn & Hq).
  simpl in Hhn. inversion Hhn; subst qn.
  assert (Hnl : new_color qc wf mode = None -> ~ live col' L (dom h)).
  { intros Hnc (w & Hc & _). rewrite Hnew in Hc. congruence. }
  destruct Hq as [<- | [-> | Hq]].
  - destruct qc, mode; simpl in *; auto; try (rewrite Hnew; reflexivity).
  - simpl. exact I.
  - destruct qc; discriminate.
Qed.

(* ------------------OVERRIDING------------------*)

(** What the selected method's signature says, given the statically seen
    one, about receiver-dependent parameters and about the result. *)
Definition wref (qr : q_r) (sig' sig : method_sig) : Prop :=
  Forall2
    (fun P0 P' =>
       (head_of P' = Some RDM -> head_of P0 = Some RDM \/ head_of P0 = Some Bot) /\
       (head_of P' = Some Bot -> head_of P0 = Some Bot))
    (mparams sig) (mparams sig') /\
  (head_of (mret sig) = Some Mut ->
     head_of (mret sig') = Some Mut \/ head_of (mret sig') = Some Bot) /\
  (head_of (mret sig) = Some RDM ->
     head_of (mret sig') = Some RDM \/ head_of (mret sig') = Some Mut \/
     head_of (mret sig') = Some Bot \/
     (head_of (mret sig') = Some Imm /\ qr = Imm_r)) /\
  (head_of (mret sig) = Some Imm ->
     head_of (mret sig') = Some Imm \/ head_of (mret sig') = Some Bot) /\
  (head_of (mret sig) = Some Bot -> head_of (mret sig') = Some Bot).

Definition wref_rel (qr : q_r) (mdef' mdef : method_def) : Prop :=
  mscope (msignature mdef') = mscope (msignature mdef) /\
  wref qr (msignature mdef') (msignature mdef).

Lemma wref_rel_refl : forall qr m, wref_rel qr m m.
Proof.
  intros qr m. split; auto. unfold wref.
  refine (conj _ (conj _ (conj _ (conj _ _)))); auto.
  induction (mparams (msignature m)); constructor; auto.
Qed.

Lemma wref_rel_trans : forall qr a b c,
  wref_rel qr a b -> wref_rel qr b c -> wref_rel qr a c.
Proof.
  intros qr a b c [Hs1 (Hp1 & Hm1 & Hr1 & Hi1 & Hb1)]
    [Hs2 (Hp2 & Hm2 & Hr2 & Hi2 & Hb2)].
  split; [congruence|].
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - eapply Forall2_compose; [exact Hp2 | exact Hp1 |].
    intros Pc Pb Pa [H1 H2] [H3 H4]. split.
    + intros H. destruct (H3 H) as [Hx | Hx]; auto.
    + intros H. auto.
  - intros H. destruct (Hm2 H) as [Hx | Hx]; auto.
  - intros H. destruct (Hr2 H) as [Hx | [Hx | [Hx | [Hx Hq]]]].
    + destruct (Hr1 Hx) as [Hy | [Hy | [Hy | Hy]]]; auto.
    + destruct (Hm1 Hx) as [Hy | Hy]; auto.
    + auto.
    + destruct (Hi1 Hx) as [Hy | Hy]; auto.
  - intros H. destruct (Hi2 H) as [Hx | Hx]; auto.
  - intros H. auto.
Qed.

Lemma wref_step : forall CT qr D' ca' def' mdef' P Ss D1 mdef1,
  wf_class_table CT -> no_tparams CT ->
  wf_rtypeuse CT (mkruntime_type qr D' ca') ->
  find_class CT D' = Some def' ->
  super (signature def') = Some (P, Ss) ->
  List.In mdef' (methods (body def')) ->
  wf_method CT D' mdef' ->
  FindMethodWithName CT P (mname (msignature mdef')) D1 mdef1 ->
  wref_rel qr mdef' mdef1.
Proof.
  intros CT qr D' ca' def' mdef' P Ss D1 mdef1
    Hct Hnt Hrt Hfind Hsuper Hin Hwm Hfm.
  unfold wf_rtypeuse in Hrt. simpl in Hrt. rewrite Hfind in Hrt.
  destruct Hrt as (Hagree & _).
  destruct (find_rsuper_exists _ _ _ _ _ Hfm Mut (map (dyn Mut [] [] []) Ss))
    as [Xs Hrs0].
  assert (Hrs : rsuper_inst CT Mut D' [] D1 Xs).
  { eapply rsi_step; [|exact Hrs0].
    unfold parent_lookup. rewrite Hfind. exact Hsuper. }
  destruct (super_inst_exists _ _ _ _ _ _ Hrs AbstractState
              (qc2q (class_qualifier (signature def')))
              (class_var_types (length (ctparams (signature def')))))
    as [Vs Hsi].
  pose proof Hwm as (_ & _ & _ & _ & Hovr & _).
  pose proof (Hovr def' P Ss D1 mdef1 Vs Hfind Hsuper Hfm Hsi) as Hcompat.
  destruct (sig_flat _ _ _ _ Hct Hnt Hfind Hin Hwm) as (HΔ & Hfret' & Hfpar').
  destruct (find_method_In _ _ _ _ _ Hfm) as (def1 & Hfind1 & Hin1).
  pose proof (find_method_wf _ _ _ _ _ Hct Hfm) as Hwm1.
  destruct (sig_flat _ _ _ _ Hct Hnt Hfind1 Hin1 Hwm1) as (_ & Hfret1 & Hfpar1).
  destruct Hcompat as (_ & Hscope & _ & Hret & Hpar & _).
  split; [exact Hscope|].
  rewrite Forall_forall in Hfpar'. rewrite Forall_forall in Hfpar1.
  assert (Hparams :
    Forall2
      (fun P0 P' =>
         (head_of P' = Some RDM -> head_of P0 = Some RDM \/ head_of P0 = Some Bot) /\
         (head_of P' = Some Bot -> head_of P0 = Some Bot))
      (mparams (msignature mdef1)) (mparams (msignature mdef'))).
  { eapply Forall2_impl_in; [exact Hpar|].
    intros P1 P' Hin_1 Hin_' Hsub. simpl in Hsub.
    destruct (Hfpar1 _ Hin_1) as (q1 & E1 & ->).
    destruct (Hfpar' _ Hin_') as (q' & E' & ->).
    rewrite view_flat in Hsub.
    destruct (subtype_head _ _ _ _ Hsub HΔ _ _ _ eq_refl)
      as (qT & CT0 & bT & HeqT & HqT).
    inversion HeqT; subst qT CT0 bT. clear HeqT. simpl.
    destruct (class_qualifier (signature def')), q1; simpl in HqT;
      split; intros Hh; inversion Hh; subst;
      destruct HqT as [Hx | [Hx | Hx]]; try discriminate; auto. }
  destruct Hfret1 as (qm & Em & Hm). destruct Hfret' as (q' & E' & Hm').
  rewrite Hm in Hret. rewrite Hm' in Hret. rewrite view_flat in Hret.
  destruct (subtype_head _ _ _ _ Hret HΔ _ _ _ eq_refl)
    as (qT & CT0 & bT & HeqT & HqT).
  inversion HeqT; subst qT CT0 bT. clear HeqT.
  unfold wref. rewrite Hm. rewrite Hm'. simpl.
  refine (conj Hparams (conj _ (conj _ (conj _ _))));
    intros Hh; inversion Hh; subst;
    destruct (class_qualifier (signature def')); simpl in HqT;
    destruct HqT as [Hx | [Hx | Hx]]; subst; try discriminate; auto;
    (* immutable-declared class: the receiver object is immutable *)
    right; right; right; split; auto;
    destruct qr; simpl in Hagree; auto; discriminate.
Qed.

(* ------------------TRANSPORT OF THE INVARIANT------------------*)

Lemma frameF_agree : forall CT sΓ rΓ h col col' L wf mode,
  frameF CT sΓ rΓ col L wf mode ->
  wf_renv CT rΓ h ->
  (forall l, l < dom h -> col' l = col l) ->
  frameF CT sΓ rΓ col' L wf mode.
Proof.
  intros CT sΓ rΓ h col col' L wf mode HF Hrenv Hag.
  constructor.
  - exact (ff_live _ _ _ _ _ _ _ HF).
  - intros Hm. destruct (ff_this _ _ _ _ _ _ _ HF Hm) as (ι & Hth & Hc).
    exists ι. split; auto. rewrite Hag; auto.
    destruct Hrenv as (_ & (i & Hi & Hd) & _). congruence.
  - intros x T v HT Hv Hh. rewrite Hag; [eapply var_value_dom; eauto|].
    eapply (ff_mut _ _ _ _ _ _ _ HF); eauto.
  - intros x T v HT Hv Hh.
    pose proof (ff_rdm _ _ _ _ _ _ _ HF _ _ _ HT Hv Hh) as Hr.
    assert (Hvd : v < dom h) by (eapply var_value_dom; eauto).
    destruct mode.
    + rewrite Hag; auto.
    + unfold live in *. rewrite Hag; auto.
Qed.

Lemma frameF_local : forall CT sΓ rΓ col L wf mode T,
  dom sΓ = dom (vars rΓ) ->
  frameF CT sΓ rΓ col L wf mode ->
  frameF CT (sΓ ++ [T]) (set_vars rΓ (vars rΓ ++ [Null_a])) col L wf mode.
Proof.
  intros CT sΓ rΓ col L wf mode T Hlen HF.
  assert (Hold : forall x T0 v,
            static_getType (sΓ ++ [T]) x = Some T0 ->
            runtime_getVal (set_vars rΓ (vars rΓ ++ [Null_a])) x = Some (Iot v) ->
            static_getType sΓ x = Some T0 /\ runtime_getVal rΓ x = Some (Iot v)).
  { intros x T0 v HT Hv. unfold static_getType, runtime_getVal in *. simpl in Hv.
    destruct (Nat.lt_ge_cases x (dom sΓ)) as [Hlt | Hge].
    - rewrite nth_error_app1 in HT; auto.
      rewrite nth_error_app1 in Hv; [lia|]. auto.
    - rewrite nth_error_app2 in Hv; [lia|].
      destruct (x - dom (vars rΓ)) as [|k]; simpl in Hv; [discriminate|].
      destruct k; discriminate. }
  constructor.
  - exact (ff_live _ _ _ _ _ _ _ HF).
  - intros Hm. destruct (ff_this _ _ _ _ _ _ _ HF Hm) as (ι & Hth & Hc).
    exists ι. simpl. rewrite get_this_var_mapping_app_null_last. auto.
  - intros x T0 v HT Hv Hh. destruct (Hold _ _ _ HT Hv).
    eapply (ff_mut _ _ _ _ _ _ _ HF); eauto.
  - intros x T0 v HT Hv Hh. destruct (Hold _ _ _ HT Hv).
    eapply (ff_rdm _ _ _ _ _ _ _ HF); eauto.
Qed.

(** Opening a fresh world keeps the heap part of the invariant. *)
Lemma heapG_push : forall P CT h col L next,
  heapG P CT h col L next ->
  heapG P CT h col (next :: L) (S next).
Proof.
  intros P CT h col L next HG.
  assert (Hnc : forall l, col l <> Some next).
  { intros l Hc. destruct (hg_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & Hlt). lia. }
  assert (Hlv : forall v, live col (next :: L) v <-> live col L v).
  { intros v. unfold live. split; intros (w & Hc & Hin).
    - destruct Hin as [<- | Hin]; [exfalso; eapply Hnc; eauto | eauto].
    - exists w. split; auto. right. auto. }
  constructor.
  - intros l w Hc. destruct (hg_col _ _ _ _ _ _ HG _ _ Hc) as (H1 & H2 & H3 & H4).
    repeat split; auto.
  - intros l w o fs f fd v Hc Hin. destruct Hin as [<- | Hin].
    + exfalso. eapply Hnc; eauto.
    + eapply (hg_in _ _ _ _ _ _ HG); eauto.
  - intros l o fs f fd v Hnl Ho Hcf Hn Hval Hh.
    rewrite Hlv in Hnl. rewrite Hlv.
    eapply (hg_out _ _ _ _ _ _ HG); eauto.
  - intros w [<- | Hin]; [lia|].
    pose proof (hg_live _ _ _ _ _ _ HG _ Hin). lia.
Qed.

(** Closing a world keeps the heap part of the invariant: its objects stop
    being live, and their fields stay inside it. *)
Lemma heapG_pop : forall P CT h col L w0 next,
  heapG P CT h col (w0 :: L) next ->
  ~ List.In w0 L ->
  heapG P CT h col L next.
Proof.
  intros P CT h col L w0 next HG Hnin.
  constructor.
  - exact (hg_col _ _ _ _ _ _ HG).
  - intros l w o fs f fd v Hc Hin.
    eapply (hg_in _ _ _ _ _ _ HG); eauto. right. auto.
  - intros l o fs f fd v Hnl Ho Hcf Hn Hval Hh.
    destruct (live_dec col (w0 :: L) l) as [(w & Hc & Hin) | Hnl'].
    + destruct Hin as [<- | Hin]; [|exfalso; apply Hnl; exists w; auto].
      assert (Hcv : col v = Some w0).
      { eapply (hg_in _ _ _ _ _ _ HG); eauto; simpl; auto. }
      intros (w' & Hc' & Hin'). congruence.
    + pose proof (hg_out _ _ _ _ _ _ HG _ _ _ _ _ _ Hnl' Ho Hcf Hn Hval Hh) as Hv.
      intros (w' & Hc' & Hin'). apply Hv. exists w'. split; auto. right. auto.
  - intros w Hin. apply (hg_live _ _ _ _ _ _ HG). right. auto.
Qed.

(* ------------------CALLS------------------*)

Lemma live_push : forall P CT h col L next v,
  heapG P CT h col L next ->
  (live col (next :: L) v <-> live col L v).
Proof.
  intros P CT h col L next v HG. unfold live. split; intros (w & Hc & Hin).
  - destruct Hin as [<- | Hin]; [|eauto].
    destruct (hg_col _ _ _ _ _ _ HG _ _ Hc) as (_ & _ & _ & Hlt). lia.
  - exists w. split; auto. right. auto.
Qed.

Lemma no_mut_head : forall Δ T, no_mut Δ T -> head_of T <> Some Mut.
Proof.
  intros Δ T H Hh. destruct T as [q0 C Ts| |]; simpl in Hh; [|discriminate..].
  inversion Hh; subst. inversion H; subst. congruence.
Qed.

Lemma callee_result_head : forall CT Δ qr sig' sig Tb qb qm,
  wref qr sig' sig ->
  empty_tv_env Δ ->
  qualified_type_subtype CT Δ Tb (mret sig') ->
  flat_type (mret sig') ->
  head_of Tb = Some qb -> qb <> Bot ->
  head_of (mret sig) = Some qm ->
  (qm = Mut -> qb = Mut) /\
  (qm = RDM -> qb = RDM \/ qb = Mut \/ (qb = Imm /\ qr = Imm_r)).
Proof.
  intros CT Δ qr sig' sig Tb qb qm (_ & HrM & HrR & _ & _) HΔ Hsub Hfl Hb Hnb Hm.
  destruct (head_flat _ Hfl) as (q' & Hq').
  destruct (subtype_head_of _ _ _ _ _ Hsub HΔ Hq') as (qb' & Hb' & Hrel).
  rewrite Hb in Hb'. inversion Hb'; subst qb'.
  rewrite Hq' in HrM. rewrite Hq' in HrR. rewrite Hm in HrM. rewrite Hm in HrR.
  split; intros ->.
  - destruct (HrM eq_refl) as [Hx | Hx]; inversion Hx; subst;
      destruct Hrel as [Hy | [Hy | Hy]]; try discriminate; congruence.
  - destruct (HrR eq_refl) as [Hx | [Hx | [Hx | [Hx Hq]]]]; inversion Hx; subst;
      destruct Hrel as [Hy | [Hy | Hy]]; try discriminate; subst; auto; congruence.
Qed.

Lemma static_ret_cases : forall CT Δ mt qy qm E Tx q0,
  readonly_state_method_scope mt -> empty_tv_env Δ ->
  qualified_type_subtype CT Δ (TClass (vpa_q mt qy qm) E []) Tx ->
  head_of Tx = Some q0 -> qy <> Bot ->
  (q0 = Mut -> (qy = Mut /\ (qm = Mut \/ qm = RDM)) \/ qm = Bot) /\
  (q0 = RDM -> (qy = RDM /\ qm = RDM) \/ qm = Bot).
Proof.
  intros CT Δ mt qy qm E Tx q0 Hrs HΔ Hsub Hh Hnb.
  destruct (subtype_head_of _ _ _ _ _ Hsub HΔ Hh) as (qv & Hv & Hrel).
  simpl in Hv. inversion Hv; subst qv.
  split; intros ->;
    destruct Hrs as [-> | ->]; destruct qy, qm; simpl in Hrel;
    destruct Hrel as [Hx | [Hx | Hx]]; try discriminate; try congruence; auto.
Qed.

(** The world of a call's result in the caller, from the world of the result
    in the callee. *)
Lemma call_result_good : forall (col col'' : coloring) L wf mode Lc wc modec
    (qr : q_r) q0 qy qm qb rv ly,
  List.In wf L ->
  ((q0 = Mut -> qy = Mut /\ (qm = Mut \/ qm = RDM)) /\
   (q0 = RDM -> qy = RDM /\ qm = RDM)) ->
  ((qm = Mut -> qb = Mut) /\
   (qm = RDM -> qb = RDM \/ qb = Mut \/ (qb = Imm /\ qr = Imm_r))) ->
  good col'' Lc wc modec qb rv ->
  good col L wf mode qy ly ->
  (q0 = Imm -> ~ live col'' L rv) ->
  ((col ly = Some wc /\ List.In wc L /\ Lc = L /\ modec = true /\ qr = Mut_r) \/
   (~ live col L ly /\ Lc = wc :: L /\ ~ List.In wc L /\ modec = false)) ->
  good col'' L wf mode q0 rv.
Proof.
  intros col col'' L wf mode Lc wc modec qr q0 qy qm qb rv ly
    HwfL [HsM HsR] [HcM HcR] Hgb Hgy Himm Hworld.
  destruct q0; simpl; auto.
  - (* mutable in the caller *)
    destruct (HsM eq_refl) as [-> HqM]. simpl in Hgy.
    destruct Hworld as [(Hc & Hin & -> & -> & Hqr) | (Hnl & _)].
    + assert (wc = wf) by congruence. subst wc.
      destruct HqM as [-> | ->].
      * rewrite (HcM eq_refl) in Hgb. exact Hgb.
      * destruct (HcR eq_refl) as [-> | [-> | [-> Hq]]]; simpl in Hgb; auto;
          congruence.
    + exfalso. apply Hnl. exists wf. auto.
  - (* receiver-dependent in the caller *)
    destruct (HsR eq_refl) as [-> ->]. simpl in Hgy.
    destruct Hworld as [(Hc & Hin & -> & -> & Hqr) | (Hnl & -> & Hnin & ->)].
    + destruct mode.
      * assert (wc = wf) by congruence. subst wc.
        destruct (HcR eq_refl) as [-> | [-> | [-> Hq]]]; simpl in Hgb; auto;
          congruence.
      * exfalso. apply Hgy. exists wc. auto.
    + destruct mode.
      * exfalso. apply Hnl. exists wf. auto.
      * destruct (HcR eq_refl) as [-> | [-> | [-> Hq]]]; simpl in Hgb.
        -- intros (w & Hc & Hin). apply Hgb. exists w. split; auto. right. auto.
        -- intros (w & Hc & Hin). congruence.
        -- intros (w & Hc & Hin). apply Hgb. exists w. split; auto. right. auto.
Qed.

(* ------------------THE MAIN STEP------------------*)

Lemma vpa_bot : forall mt qy, vpa_q mt qy Bot = Bot.
Proof. intros mt qy. destruct mt, qy; reflexivity. Qed.

Lemma rw_step : forall P CT,
  no_tparams CT ->
  forall rΓ h s res rΓ' h',
    eval_stmt CT rΓ h s res rΓ' h' ->
    res = OK ->
    forall Δ sΓ mt sΓ' col L next wf mode,
      empty_tv_env Δ ->
      readonly_state_method_scope mt ->
      wf_r_config CT Δ sΓ rΓ h ->
      stmt_typing CT Δ sΓ mt s sΓ' ->
      heapG P CT h col L next ->
      frameF CT sΓ rΓ col L wf mode ->
      (forall l, P l -> l < dom h) ->
      exists col' next',
        heapG P CT h' col' L next' /\
        frameF CT sΓ' rΓ' col' L wf mode /\
        (forall l, l < dom h -> col' l = col l) /\
        next <= next' /\
        prot_preserved P CT mt h h'.
Proof.
  intros P CT Hnt rΓ h s res rΓ' h' Heval.
  induction Heval;
    intros Hres Δ sΓ mt0 sΓ' col L next wf mode HΔ Hrs Hwf Htype HG HF HPdom;
    try discriminate.
  - (* skip *)
    inversion Htype; subst. exists col, next.
    auto using prot_preserved_refl.
  - (* local *)
    inversion Htype; subst. exists col, next.
    refine (conj HG (conj _ (conj (fun l H => eq_refl) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    apply frameF_local; auto.
    destruct Hwf as (_ & _ & _ & _ & _ & Hlen & _). exact Hlen.
  - (* assignment *)
    exists col, next.
    refine (conj HG (conj _ (conj (fun l H => eq_refl) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    eapply rw_assign; eauto.
  - (* field write *)
    subst. exists col, next.
    destruct (rw_fldwrite P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hnt HΔ Hrs Hwf HG HF Htype Hval_x Hobj Hfield Hassign Hval_y)
      as [HG' Hp].
    refine (conj HG' (conj _ (conj (fun l H => eq_refl) (conj (le_n _) Hp)))).
    inversion Htype; subst. exact HF.
  - (* object creation *)
    subst.
    destruct (rw_new P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                Hnt HΔ Hwf HG HF Htype Hthis Hargs Hmut HPdom) as (HG' & HF' & Hag).
    eexists _, next.
    refine (conj HG' (conj HF' (conj Hag (conj (le_n _) _)))).
    intros l qr C0 Rs vals0 f HP Hl _.
    exists vals0. split; [|reflexivity].
    rewrite runtime_getObj_last2; [eapply runtime_getObj_dom; eauto | exact Hl].
  - (* call *)
    subst.
    pose proof Hwf as (Hct & Hheap & Hrenv & _).
    destruct (call_typing_inv _ _ _ _ _ _ _ _ _ _ _ Htype)
      as (argtypes & Tx & Ty & qy & C & Ts & Ds & Vs & smdef & -> & Hget_x &
          Hget_y & Hget_args & Hub & Hfind_s & Hx & Hret_sub & Harg_sub & Hscope_s).
    destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι & o & oy & Tx' & Hthis & Hobj & Hoy & HTx' & _ & _ &
          Hfb & Hwm & Hcfg & Hthis' & Hretf & Hscope).
    assert (Tx' = Tx) by (unfold static_getType in *; congruence). subst Tx'.
    pose proof (stmt_typing_wf_env _ _ _ _ _ _ Htype) as Hsenv.
    pose proof (senv_flat _ _ _ _ _ Hnt HΔ Hsenv Hget_y) as HTy.
    destruct (flat_ubound _ _ _ _ _ HTy Hub) as [-> ->].
    pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj Hget_y) as Hyty.
    rewrite Hval_y in Hyty.
    assert (Hqyb : qy <> Bot).
    { intros ->. eapply typable_head_not_bot; eauto. }
    pose proof (var_good P CT Δ sΓ rΓ h col L next wf mode Hwf HG HF
                  _ _ _ _ _ qy Hthis Hobj Hget_y Hval_y eq_refl) as Hgy.
    destruct (wf_r_typable_class_inv _ _ _ _ _ _ _ _ _ _ Hyty)
      as (oy' & Rs1 & Hoy' & _ & Hsup1 & _).
    rewrite Hoy in Hoy'. inversion Hoy'; subst oy'. clear Hoy'.
    pose proof (Hheap ly (runtime_getObj_dom _ _ _ Hoy)) as Hwfo.
    unfold wf_obj in Hwfo. rewrite Hoy in Hwfo. destruct Hwfo as (Hrt_oy & _).
    unfold r_basetype in Hbase. rewrite Hoy in Hbase. inversion Hbase; subst cy.
    clear Hbase.
    destruct oy as [[qr Co Ro] fso]. simpl in *.
    destruct (lookup_chain CT qr (wref_rel qr) Hct (wref_rel_refl qr)
                (wref_rel_trans qr)
                (fun D' ca' def' mdef' P0 Ss D1 mdef1 H1 H2 H3 H4 H5 H6 =>
                   wref_step CT qr D' ca' def' mdef' P0 Ss D1 mdef1
                     Hct Hnt H1 H2 H3 H4 H5 H6)
                _ _ _ _ Hsup1 Hrt_oy _ _ _ _ _ Hfind Hfind_s)
      as [Hsc Hwref].
    assert (Hrs' : readonly_state_method_scope (mscope (msignature mdef))).
    { eapply readonly_state_submethod; eauto. }
    destruct (find_method_In _ _ _ _ _ Hfind) as (defD & HfD & HinD).
    destruct (sig_flat _ _ _ _ Hct Hnt HfD HinD Hwm) as (HΔ' & Hfret' & Hfpar').
    destruct (find_method_In _ _ _ _ _ Hfind_s) as (defS & HfS & HinS).
    pose proof (find_method_wf _ _ _ _ _ Hct Hfind_s) as Hwm_s.
    destruct (sig_flat _ _ _ _ Hct Hnt HfS HinS Hwm_s) as (_ & Hfret_s & Hfpar_s).
    pose proof Hwm as
      (_ & _ & _ & (sΓb & Tb & Hbody & Hnthb & Hsubb) & _ & Hroots').
    destruct (Hroots' Hrs') as [Hnm_recv Hnm_par].
    pose proof (callee_env_targs _ _ _ _ _ _ _ _ _ Hframe) as Hvars'.
    pose proof (ff_live _ _ _ _ _ _ _ HF) as HwfL.
    (* no callee variable is typed mutable *)
    assert (Hnomut : forall x0 T,
              static_getType
                (mreceiver (msignature mdef) :: mparams (msignature mdef)) x0
                = Some T -> head_of T <> Some Mut).
    { intros x0 T HT. eapply no_mut_head. unfold static_getType in HT.
      destruct x0 as [|i]; simpl in HT.
      - inversion HT; subst. exact Hnm_recv.
      - rewrite Forall_forall in Hnm_par. apply Hnm_par.
        eapply nth_error_In; eauto. }
    (* receiver-dependent parameters follow the receiver's world *)
    assert (Hparam : forall i P' v,
              nth_error (mparams (msignature mdef)) i = Some P' ->
              nth_error vals i = Some (Iot v) ->
              head_of P' = Some RDM ->
              (forall w, col ly = Some w -> List.In w L -> col v = Some w) /\
              (~ live col L ly -> ~ live col L v)).
    { intros i P' v HP' Hv Hh.
      destruct Hwref as (Hpar_w & _).
      pose proof (Forall2_nth_error_rel _ _ _ i Hpar_w) as Hrel.
      rewrite HP' in Hrel.
      destruct (nth_error (mparams (msignature smdef)) i) as [Ps|] eqn:HPs;
        [|contradiction].
      destruct Hrel as [Hrel _]. specialize (Hrel Hh).
      destruct (lookup_lists_nth _ _ _ _ _ _ _ Hget_args Hargs Hv)
        as (yi & A & HyA & Hyv & HnA).
      pose proof (Forall2_nth_error_rel _ _ _ i Harg_sub) as Hrel2.
      rewrite HnA in Hrel2. rewrite HPs in Hrel2.
      rewrite Forall_forall in Hfpar_s.
      destruct (Hfpar_s _ (nth_error_In _ _ HPs)) as (qP & E & HeqP).
      rewrite HeqP in Hrel2. rewrite HeqP in Hrel. simpl in Hrel.
      rewrite view_flat in Hrel2. destruct Hrel2 as [Hsub Hok].
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hwf Hthis Hobj HyA) as Hty.
      rewrite Hyv in Hty.
      destruct (subtype_head_of _ _ _ _ _ Hsub HΔ eq_refl) as (qa & Hha & Hqa).
      assert (Hqab : qa <> Bot).
      { intros ->. eapply typable_head_not_bot; eauto. }
      destruct Hrel as [HqP | HqP]; inversion HqP; subst qP.
      - assert (Hnl : vpa_q mt0 qy RDM <> Lost).
        { intros Hl. rewrite Hl in Hok.
          destruct Hok as [Hlf _]; congruence. }
        assert (Hgv : good col L wf mode (vpa_q mt0 qy RDM) v).
        { eapply (good_sub CT Δ h col L wf mode HΔ A
                      (TClass (vpa_q mt0 qy RDM) E []) v qa (vpa_q mt0 qy RDM)
                      _ _ _ _ Hsub Hty Hfb Hha eq_refl).
          exact (var_good P CT Δ sΓ rΓ h col L next wf mode Hwf HG HF
                   ι o yi A v qa Hthis Hobj HyA Hyv Hha). }
        destruct (write_worlds mt0 qy RDM col L wf mode ly v Hrs Hnl Hqyb
                    HwfL Hgy Hgv) as [H1 H2].
        split; [intros w Hc Hin; apply H1; auto | intros Hn; apply H2; auto].
      - exfalso. rewrite vpa_bot in Hqa.
        destruct Hqa as [Hq | [Hq | Hq]]; congruence. }
    (* the result, once the callee's invariant at its end is known *)
    assert (Hresult : forall col'' Lc wc modec next'' rΓe he,
              eval_stmt CT rΓ' h (mbody_stmt (mbody mdef)) OK rΓe he ->
              runtime_getVal rΓe (mreturn (mbody mdef)) = Some retval ->
              heapG P CT he col'' Lc next'' ->
              frameF CT sΓb rΓe col'' Lc wc modec ->
              heapG P CT he col'' L next'' ->
              ((col ly = Some wc /\ List.In wc L /\ Lc = L /\ modec = true /\
                qr = Mut_r) \/
               (~ live col L ly /\ Lc = wc :: L /\ ~ List.In wc L /\
                modec = false)) ->
              forall rv q0, retval = Iot rv -> head_of Tx = Some q0 ->
                good col'' L wf mode q0 rv).
    { intros col'' Lc wc modec next'' rΓe he Hev Hrv HGc HFc HGL Hworld rv q0 -> Hh0.
      pose proof (preservation_pico _ _ _ _ _ _ _ Hev eq_refl _ _ _ _ Hcfg Hbody)
        as Hcfg''.
      destruct (wf_r_config_this _ _ _ _ _ Hcfg'')
        as (ι2 & o2 & Hth2 & Hobj2 & _ & _ & _ & Hfb2).
      pose proof (wf_r_config_var _ _ _ _ _ _ _ _ _ Hcfg'' Hth2 Hobj2 Hnthb) as Hrty.
      rewrite Hrv in Hrty.
      pose proof Hcfg'' as (_ & _ & _ & Hsenv'' & _).
      destruct (head_flat _ (senv_flat _ _ _ _ _ Hnt HΔ' Hsenv'' Hnthb))
        as (qb & Hhb).
      assert (Hqbb : qb <> Bot).
      { intros ->. eapply typable_head_not_bot; eauto. }
      pose proof (var_good P CT _ sΓb rΓe he col'' Lc next'' wc modec Hcfg'' HGc HFc
                    _ _ _ _ _ qb Hth2 Hobj2 Hnthb Hrv Hhb) as Hgb.
      destruct Hfret_s as (qm & Em & Hm).
      pose proof Hret_sub as Hret_sub'.
      rewrite Hm in Hret_sub'. rewrite view_flat in Hret_sub'.
      destruct (static_ret_cases _ _ _ _ _ _ _ _ Hrs HΔ Hret_sub' Hh0 Hqyb)
        as [HsM HsR].
      pose proof Hwref as Hwref0.
      destruct Hwref as (_ & HrM & HrR & HrI & HrB).
      assert (Hm' : head_of (mret (msignature smdef)) = Some qm)
        by (rewrite Hm; reflexivity).
      (* a bottom-typed static result is null *)
      assert (Hqmb : qm <> Bot).
      { intros ->. specialize (HrB Hm').
        destruct (subtype_head_of _ _ _ _ _ Hsubb HΔ' HrB) as (qb' & Hb' & Hq).
        rewrite Hhb in Hb'. inversion Hb'; subst qb'.
        destruct Hq as [Hq | [Hq | Hq]]; congruence. }
      assert (Hstat : (q0 = Mut -> qy = Mut /\ (qm = Mut \/ qm = RDM)) /\
                      (q0 = RDM -> qy = RDM /\ qm = RDM)).
      { split; intros Hq.
        + destruct (HsM Hq) as [Hs | Hs]; [exact Hs | contradiction].
        + destruct (HsR Hq) as [Hs | Hs]; [exact Hs | contradiction]. }
      pose proof (callee_result_head CT _ qr _ _ Tb qb qm Hwref0 HΔ' Hsubb Hfret'
                    Hhb Hqbb Hm') as Hcal.
      assert (Himm : q0 = Imm -> ~ live col'' L rv).
      { intros ->.
        assert (Hrt : val_typable CT he (Iot rv) Tx (rqtype (rt_type o))
                        (cargs rΓ) (margs rΓ) (qargs rΓ)).
        { apply Hretf. simpl.
          destruct (eval_stmt_frame _ _ _ _ _ _ Hev _ _ _ _ Hbody)
            as (Hth_eq & Hca_eq & Hma_eq).
        pose proof (eval_stmt_qargs _ _ _ _ _ _ _ Hev eq_refl) as Hqa_eq.
          destruct (heap_ext_getObj _ _ _ _ (eval_stmt_heap_ext _ _ _ _ _ _ _ Hev) Hoy)
            as (oye & Hoye & Hrte).
          assert (ι2 = ly) by congruence. subst ι2.
          rewrite Hoye in Hobj2. inversion Hobj2; subst o2.
          rewrite Hrte in Hrty. simpl in Hrty.
          rewrite Hca_eq in Hrty. rewrite Hma_eq in Hrty. try rewrite Hqa_eq in Hrty.
          eapply wf_r_typable_subtype; [|exact Hsubb|exact Hrty].
          rewrite Hca_eq in Hfb2. rewrite Hma_eq in Hfb2. try rewrite Hqa_eq in Hfb2.
          rewrite Hrte in Hfb2. exact Hfb2. }
        simpl in Hrt.
        destruct Tx as [qx0 Cx Tsx| |]; simpl in Hh0; [|discriminate..].
        inversion Hh0; subst qx0.
        eapply not_live_of_imm; [exact HGL|].
        eapply typable_imm_obj; eauto. }
      exact (call_result_good col col'' L wf mode Lc wc modec qr q0 qy qm qb rv ly
               HwfL Hstat Hcal Hgb Hgy Himm Hworld). }
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval) as Hext.
    assert (Hprot_up : forall C0 f,
              prot_cond CT C0 f mt0 ->
              prot_cond CT C0 f (mscope (msignature mdef))).
    { intros C0 f [Hp | [Hp | Hstrict]]; [left; auto | right; left; auto |].
      right. right. eapply concrete_assignability_submethod; eauto. }
    destruct (live_dec col L ly) as [(w & Hcw & HinW) | Hnlive].
    + (* the receiver belongs to a live world: the callee continues in it *)
      assert (HF' : frameF CT
                      (mreceiver (msignature mdef) :: mparams (msignature mdef))
                      rΓ' col L w true).
      { constructor.
        - exact HinW.
        - intros _. exists ly. split; auto.
        - intros x0 T v HT Hv Hh. exfalso. eapply Hnomut; eauto.
        - intros x0 T v HT Hv Hh.
          unfold runtime_getVal in Hv. rewrite Hvars' in Hv.
          unfold static_getType in HT.
          destruct x0 as [|i]; simpl in HT, Hv.
          + inversion Hv; subst v. exact Hcw.
          + destruct (Hparam _ _ _ HT Hv Hh) as [H1 _]. apply H1; auto. }
      destruct (IHHeval Hnt eq_refl _ _ _ _ col L next w true
                  HΔ' Hrs' Hcfg Hbody HG HF' HPdom)
        as (col'' & next'' & HG'' & HF'' & Hag & Hle & Hprot).
      exists col'', next''.
      refine (conj HG'' (conj _ (conj Hag (conj Hle _)))).
      * eapply frameF_update; eauto.
        -- eapply frameF_agree; eauto.
        -- intros rv q0 Hrv Hh0.
           eapply (Hresult col'' L w true next'' _ _ Heval Hretval HG'' HF'' HG'');
             eauto.
           left. repeat split; auto.
           destruct (hg_col _ _ _ _ _ _ HG _ _ Hcw) as (_ & _ & Hm & _).
           unfold r_muttype in Hm. rewrite Hoy in Hm. simpl in Hm. congruence.
      * intros l qr0 C0 Rs0 vals0 f HP Hl Hp0. eapply Hprot; eauto.
    + (* otherwise the callee opens a fresh world *)
      pose proof (heapG_push _ _ _ _ _ _ HG) as HG1.
      assert (Hnin : ~ List.In next L).
      { intros Hin. pose proof (hg_live _ _ _ _ _ _ HG _ Hin). lia. }
      assert (HF' : frameF CT
                      (mreceiver (msignature mdef) :: mparams (msignature mdef))
                      rΓ' col (next :: L) next false).
      { constructor.
        - left. reflexivity.
        - discriminate.
        - intros x0 T v HT Hv Hh. exfalso. eapply Hnomut; eauto.
        - intros x0 T v HT Hv Hh.
          rewrite (live_push _ _ _ _ _ _ v HG).
          unfold runtime_getVal in Hv. rewrite Hvars' in Hv.
          unfold static_getType in HT.
          destruct x0 as [|i]; simpl in HT, Hv.
          + inversion Hv; subst v. exact Hnlive.
          + destruct (Hparam _ _ _ HT Hv Hh) as [_ H2]. apply H2; auto. }
      destruct (IHHeval Hnt eq_refl _ _ _ _ col (next :: L) (S next) next false
                  HΔ' Hrs' Hcfg Hbody HG1 HF' HPdom)
        as (col'' & next'' & HG'' & HF'' & Hag & Hle & Hprot).
      pose proof (heapG_pop _ _ _ _ _ _ _ HG'' Hnin) as HGL.
      exists col'', next''.
      refine (conj HGL (conj _ (conj Hag (conj _ _)))).
      * eapply frameF_update; eauto.
        -- eapply frameF_agree; eauto.
        -- intros rv q0 Hrv Hh0.
           eapply (Hresult col'' (next :: L) next false next'' _ _
                     Heval Hretval HG'' HF'' HGL); eauto.
      * lia.
      * intros l qr0 C0 Rs0 vals0 f HP Hl Hp0. eapply Hprot; eauto.
  - (* cast *)
    exists col, next.
    refine (conj HG (conj _ (conj (fun l H => eq_refl) (conj (le_n _)
              (prot_preserved_refl _ _ _ _))))).
    eapply rw_cast; eauto.
  - (* sequence *)
    inversion Htype; subst.
    destruct (IHHeval1 Hnt eq_refl _ _ _ _ col L next wf mode
                HΔ Hrs Hwf Htype1 HG HF HPdom)
      as (col1 & next1 & HG1 & HF1 & Hag1 & Hle1 & HP1).
    pose proof (preservation_pico _ _ _ _ _ _ _ Heval1 eq_refl _ _ _ _ Hwf Htype1)
      as Hwf1.
    pose proof (eval_stmt_heap_ext _ _ _ _ _ _ _ Heval1) as [Hd1 _].
    assert (HPdom1 : forall l, P l -> l < dom h').
    { intros l HP. specialize (HPdom l HP). lia. }
    destruct (IHHeval2 Hnt eq_refl _ _ _ _ col1 L next1 wf mode
                HΔ Hrs Hwf1 Htype2 HG1 HF1 HPdom1)
      as (col2 & next2 & HG2 & HF2 & Hag2 & Hle2 & HP2).
    exists col2, next2.
    refine (conj HG2 (conj HF2 (conj _ (conj _ _)))).
    + intros l Hl. rewrite Hag2; [lia|]. apply Hag1; auto.
    + lia.
    + intros l qr C Rs vals f HP Hl Hprot.
      destruct (HP1 l qr C Rs vals f HP Hl Hprot) as (vals1 & Hl1 & He1).
      destruct (HP2 l qr C Rs vals1 f HP Hl1 Hprot) as (vals2 & Hl2 & He2).
      exists vals2. split; auto. congruence.
Qed.

(* ------------------THE THEOREMS------------------*)

(** A call that selects a readonly-state or transitive-state method leaves
    the protected fields of every object of the entry heap unchanged.  Field
    types may be receiver-dependent; there are no type parameters. *)
Theorem rs_ts_call_preservation_rdm :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    no_tparams CT ->
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
    Hnt Hwf Htype Heval Hvy Hbase Hfind Hrs l qr C Rs vals f Hl Hprot.
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
  destruct (sig_flat _ _ _ _ Hct Hnt HfD HinD Hwm) as (HΔ' & _ & _).
  pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _ & Hroots).
  destruct (Hroots Hrs) as [Hnm_recv Hnm_par].
  set (P := fun l0 : Loc => l0 < dom h).
  set (col0 := fun _ : Loc => @None nat).
  assert (Hnl : forall v, ~ live col0 [0] v).
  { intros v (w & Hc & _). discriminate. }
  assert (HG : heapG P CT h col0 [0] 1).
  { constructor.
    - intros l0 w Hc. discriminate.
    - intros l0 w o0 fs f0 fd v Hc. discriminate.
    - intros; apply Hnl.
    - intros w [<- | []]. lia. }
  assert (HF : frameF CT
                 (mreceiver (msignature mdef) :: mparams (msignature mdef))
                 rΓ'0 col0 [0] 0 false).
  { constructor.
    - left. reflexivity.
    - discriminate.
    - intros x0 T v HT _ Hh. exfalso.
      eapply (no_mut_head (method_tv_env CT D (msignature mdef)) T); eauto.
      unfold static_getType in HT. destruct x0 as [|i]; simpl in HT.
      + inversion HT; subst. exact Hnm_recv.
      + rewrite Forall_forall in Hnm_par. apply Hnm_par.
        eapply nth_error_In; eauto.
    - intros; apply Hnl. }
  destruct (rw_step P CT Hnt _ _ _ _ _ _ Heval_body eq_refl _ _ _ _
              col0 [0] 1 0 false HΔ' Hrs Hcfg Hbody HG HF (fun l0 H => H))
    as (col' & next' & _ & _ & _ & _ & Hpres).
  eapply Hpres; eauto.
  unfold P. eapply runtime_getObj_dom; eauto.
Qed.

(** Readonly-state preservation: non-assignable fields keep their values. *)
Corollary readonly_state_preservation_rdm :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    no_tparams CT ->
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
  intros. eapply rs_ts_call_preservation_rdm; eauto.
  unfold prot_cond. tauto.
Qed.

(** Transitive-state preservation: every field keeps its value. *)
Corollary transitive_state_preservation_rdm :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    no_tparams CT ->
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
  intros until mdef. intros Hnt Hwf Htype Heval Hvy Hbase Hfind Hts.
  intros. eapply rs_ts_call_preservation_rdm; eauto.
  - rewrite Hts. right. reflexivity.
  - rewrite Hts. right. right. right. reflexivity.
Qed.

Print Assumptions readonly_state_preservation_rdm.
Print Assumptions transitive_state_preservation_rdm.

From iris.program_logic Require Import language.

Require Import Syntax PICOBridge.PicoMemoryModel.
Require Helpers.
Require Typing.
Require Bigstep.

(** * Minimal Iris Language for the PICO Weak-Memory Shell

    Expressions are weak-memory thread states.  Values are finished threads:
    a runtime environment plus a view whose statement is [SSkip].  A primitive
    step is exactly one [wm_thread_step], with no observations and no forked
    expressions yet.

    This language instance is deliberately small.  It packages the existing
    field-history step relation for Iris reasoning; it is not a full Java memory
    model. *)

(** Iris value for a finished PICO weak-memory thread. *)
Record pico_val := mkPicoVal {
  pico_val_env : r_env;
  pico_val_view : view;
}.

(** Embed a finished value back into a weak-memory thread expression. *)
Definition pico_of_val (v : pico_val) : wm_thread :=
  mkWMThread (pico_val_env v) SSkip (pico_val_view v).

(** A weak-memory thread is a value exactly when its residual statement is
    [SSkip]. *)
Definition pico_to_val (e : wm_thread) : option pico_val :=
  match wt_stmt e with
  | SSkip => Some (mkPicoVal (wt_env e) (wt_view e))
  | _ => None
  end.

Lemma pico_to_val_skip :
  forall rΓ V,
    pico_to_val (mkWMThread rΓ SSkip V) = Some (mkPicoVal rΓ V).
Proof.
  reflexivity.
Qed.

Lemma pico_to_val_inv :
  forall e v
    (Hto : pico_to_val e = Some v),
    e = pico_of_val v.
Proof.
  intros [rΓ s V] [rΓv Vv] Hto.
  destruct s; simpl in Hto; try discriminate.
  inversion Hto; subst.
  reflexivity.
Qed.

Lemma pico_to_val_some_inv :
  forall e v
    (Hto : pico_to_val e = Some v),
    wt_stmt e = SSkip /\
    wt_env e = pico_val_env v /\
    wt_view e = pico_val_view v.
Proof.
  intros e v Hto.
  pose proof (pico_to_val_inv e v Hto) as Heq.
  subst e.
  destruct v.
  simpl.
  repeat split.
Qed.

Lemma pico_to_val_non_skip :
  forall rΓ s V
    (Hneq : s <> SSkip),
    pico_to_val (mkWMThread rΓ s V) = None.
Proof.
  intros rΓ s V Hneq.
  destruct s; simpl; try reflexivity.
  exfalso.
  apply Hneq.
  reflexivity.
Qed.

Lemma pico_to_val_var_assign :
  forall rΓ x e V,
    pico_to_val (mkWMThread rΓ (SVarAss x e) V) = None.
Proof.
  reflexivity.
Qed.

Lemma pico_to_val_fld_write :
  forall rΓ x f y V,
    pico_to_val (mkWMThread rΓ (SFldWrite x f y) V) = None.
Proof.
  reflexivity.
Qed.

Lemma pico_to_val_seq :
  forall rΓ s1 s2 V,
    pico_to_val (mkWMThread rΓ (SSeq s1 s2) V) = None.
Proof.
  reflexivity.
Qed.

Definition pico_prim_step
    `{CacheMemoryModel} (CT : class_table) :
    wm_thread -> wm_state -> list unit -> wm_thread -> wm_state ->
    list wm_thread -> Prop :=
  fun e sigma k e' sigma' efs =>
    k = [] /\ efs = [] /\ wm_thread_step CT sigma e sigma' e'.

(** Finished threads are stuck, as required by the Iris language mixin. *)
Lemma pico_no_step_from_value :
  forall `{CacheMemoryModel} CT rΓ V sigma e' sigma',
    not (wm_thread_step CT sigma (mkWMThread rΓ SSkip V) sigma' e').
Proof.
  intros Hmem CT rΓ V sigma e' sigma' Hstep.
  inversion Hstep.
Qed.

(** Iris [LanguageMixin] whose primitive steps are exactly PICO
    [wm_thread_step] steps. *)
Program Definition pico_language_mixin `{CacheMemoryModel} (CT : class_table) :
  LanguageMixin
    pico_of_val
    pico_to_val
    (pico_prim_step CT) := {|
  mixin_to_of_val := _;
  mixin_of_to_val := _;
  mixin_val_stuck := _
|}.
Next Obligation.
  intros Hmem CT0 v.
  destruct v.
  reflexivity.
Qed.
Next Obligation.
  intros Hmem CT0 e v Hto.
  destruct e as [rΓ s V].
  destruct s; simpl in Hto; try discriminate.
  inversion Hto; subst.
  reflexivity.
Qed.
Next Obligation.
  intros Hmem CT0 e sigma k e' sigma' efs Hstep.
  destruct Hstep as [_ [_ Hthread]].
  destruct e as [rΓ s V].
  destruct s; simpl; try reflexivity.
  exfalso.
  eapply pico_no_step_from_value; eauto.
Qed.

Canonical Structure pico_language `{CacheMemoryModel} (CT : class_table) :
  language :=
  Language (pico_language_mixin CT).

(** ** Basic Language Facts *)

Lemma pico_language_to_val_non_skip :
  forall `{CacheMemoryModel} CT rΓ s V
    (Hneq : s <> SSkip),
    @to_val (pico_language CT) (mkWMThread rΓ s V) = None.
Proof.
  intros Hmem CT rΓ s V Hneq.
  apply pico_to_val_non_skip.
  exact Hneq.
Qed.

Lemma pico_language_to_val_inv :
  forall `{CacheMemoryModel} CT e v
    (Hto : @to_val (pico_language CT) e = Some v),
    e = of_val v.
Proof.
  intros Hmem CT e v Hto.
  apply pico_to_val_inv.
  exact Hto.
Qed.

Lemma pico_language_to_val_some_inv :
  forall `{CacheMemoryModel} CT e v
    (Hto : @to_val (pico_language CT) e = Some v),
    wt_stmt e = SSkip /\
    wt_env e = pico_val_env v /\
    wt_view e = pico_val_view v.
Proof.
  intros Hmem CT e v Hto.
  eapply pico_to_val_some_inv; eauto.
Qed.

Lemma pico_language_to_val_var_assign :
  forall `{CacheMemoryModel} CT rΓ x e V,
    @to_val (pico_language CT)
      (mkWMThread rΓ (SVarAss x e) V) = None.
Proof.
  reflexivity.
Qed.

Lemma pico_language_to_val_fld_write :
  forall `{CacheMemoryModel} CT rΓ x f y V,
    @to_val (pico_language CT)
      (mkWMThread rΓ (SFldWrite x f y) V) = None.
Proof.
  reflexivity.
Qed.

Lemma pico_language_to_val_seq :
  forall `{CacheMemoryModel} CT rΓ s1 s2 V,
    @to_val (pico_language CT)
      (mkWMThread rΓ (SSeq s1 s2) V) = None.
Proof.
  reflexivity.
Qed.

Lemma pico_prim_step_no_forks :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_language CT) e sigma k e' sigma' efs),
    efs = [].
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact (proj1 (proj2 Hstep)).
Qed.

Lemma pico_prim_step_is_thread_step :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_language CT) e sigma k e' sigma' efs),
    wm_thread_step CT sigma e sigma' e'.
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact (proj2 (proj2 Hstep)).
Qed.

Lemma pico_thread_step_is_prim_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : wm_thread_step CT sigma e sigma' e'),
    @prim_step (pico_language CT) e sigma [] e' sigma' [].
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  repeat split; assumption.
Qed.

Lemma pico_reducible_from_thread_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : wm_thread_step CT sigma e sigma' e'),
    @reducible (pico_language CT) e sigma.
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  exists [], e', sigma', [].
  apply pico_thread_step_is_prim_step.
  exact Hstep.
Qed.

Lemma pico_thread_step_from_reducible :
  forall `{CacheMemoryModel} CT e sigma
    (Hred : @reducible (pico_language CT) e sigma),
    exists e' sigma',
      wm_thread_step CT sigma e sigma' e'.
Proof.
  intros Hmem CT e sigma Hred.
  destruct Hred as [k [e' [sigma' [efs Hprim]]]].
  exists e', sigma'.
  eapply pico_prim_step_is_thread_step; eauto.
Qed.

Lemma pico_reducible_iff_thread_step :
  forall `{CacheMemoryModel} CT e sigma,
    @reducible (pico_language CT) e sigma <->
    exists e' sigma',
      wm_thread_step CT sigma e sigma' e'.
Proof.
  intros Hmem CT e sigma.
  split.
  - apply pico_thread_step_from_reducible.
  - intros [e' [sigma' Hstep]].
    eapply pico_reducible_from_thread_step; eauto.
Qed.

Lemma pico_not_stuck_from_thread_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : wm_thread_step CT sigma e sigma' e'),
    @not_stuck (pico_language CT) e sigma.
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  right.
  eapply pico_reducible_from_thread_step; eauto.
Qed.

Lemma pico_not_stuck_inv :
  forall `{CacheMemoryModel} CT e sigma
    (Hns : @not_stuck (pico_language CT) e sigma),
    (exists v, @to_val (pico_language CT) e = Some v) \/
    exists e' sigma',
      wm_thread_step CT sigma e sigma' e'.
Proof.
  intros Hmem CT e sigma Hns.
  destruct Hns as [Hval | Hred].
  - left.
    exact Hval.
  - right.
    eapply pico_thread_step_from_reducible; eauto.
Qed.

Lemma pico_not_stuck_intro :
  forall `{CacheMemoryModel} CT e sigma
    (Hns : (exists v, @to_val (pico_language CT) e = Some v) \/
     exists e' sigma',
       wm_thread_step CT sigma e sigma' e'),
    @not_stuck (pico_language CT) e sigma.
Proof.
  intros Hmem CT e sigma Hns.
  destruct Hns as [Hval | Hstep].
  - left.
    exact Hval.
  - destruct Hstep as [e' [sigma' Hstep]].
    right.
    eapply pico_reducible_from_thread_step; eauto.
Qed.

Lemma pico_not_stuck_iff_value_or_thread_step :
  forall `{CacheMemoryModel} CT e sigma,
    @not_stuck (pico_language CT) e sigma <->
    (exists v, @to_val (pico_language CT) e = Some v) \/
    exists e' sigma',
      wm_thread_step CT sigma e sigma' e'.
Proof.
  intros Hmem CT e sigma.
  split.
  - apply pico_not_stuck_inv.
  - apply pico_not_stuck_intro.
Qed.

Lemma pico_assign_int_thread_step_exists :
  forall `{CacheMemoryModel} CT sigma rΓ V x n old_v
    (Hold : Helpers.runtime_getVal rΓ x = Some old_v),
    exists e' sigma',
      wm_thread_step CT sigma
        (mkWMThread rΓ (SVarAss x (EInt n)) V)
        sigma'
        e'.
Proof.
  intros Hmem CT sigma rΓ V x n old_v Hold.
  exists
    (mkWMThread
      (set_vars rΓ (Helpers.update x (Int n) (vars rΓ)))
      SSkip
      V),
    sigma.
  eapply WMTS_AssignInt; eauto.
Qed.

Lemma pico_assign_int_not_stuck :
  forall `{CacheMemoryModel} CT sigma rΓ V x n old_v
    (Hold : Helpers.runtime_getVal rΓ x = Some old_v),
    @not_stuck (pico_language CT)
      (mkWMThread rΓ (SVarAss x (EInt n)) V)
      sigma.
Proof.
  intros Hmem CT sigma rΓ V x n old_v Hold.
  apply pico_not_stuck_intro.
  right.
  eapply pico_assign_int_thread_step_exists; eauto.
Qed.

Lemma pico_field_read_thread_step_exists :
  forall `{CacheMemoryModel} CT sigma rΓ V V' x y f loc_y v
    (Hy : Helpers.runtime_getVal rΓ y = Some (Iot loc_y))
    (Hread : wm_read sigma V (loc_y, f) v V'),
    exists e' sigma',
      wm_thread_step CT sigma
        (mkWMThread rΓ (SVarAss x (EField y f)) V)
        sigma'
        e'.
Proof.
  intros Hmem CT sigma rΓ V V' x y f loc_y v Hy Hread.
  exists
    (mkWMThread
      (set_vars rΓ (Helpers.update x v (vars rΓ)))
      SSkip
      V'),
    sigma.
  eapply WMTS_FieldRead; eauto.
Qed.

Lemma pico_field_read_not_stuck :
  forall `{CacheMemoryModel} CT sigma rΓ V V' x y f loc_y v
    (Hy : Helpers.runtime_getVal rΓ y = Some (Iot loc_y))
    (Hread : wm_read sigma V (loc_y, f) v V'),
    @not_stuck (pico_language CT)
      (mkWMThread rΓ (SVarAss x (EField y f)) V)
      sigma.
Proof.
  intros Hmem CT sigma rΓ V V' x y f loc_y v Hy Hread.
  apply pico_not_stuck_intro.
  right.
  eapply pico_field_read_thread_step_exists; eauto.
Qed.

Lemma pico_fldwrite_thread_step_exists :
  forall `{CacheMemoryModel} CT sigma sigma' rΓ V V' x f y loc_x rt a val_y
    (Hx : Helpers.runtime_getVal rΓ x = Some (Iot loc_x))
    (Htype : wm_get_type sigma loc_x = Some rt)
    (Hfield : Typing.sf_assignability_rel CT (rctype rt) f a)
    (Hy : Helpers.runtime_getVal rΓ y = Some val_y)
    (Hassign : Bigstep.runtime_vpa_assignability (rqtype rt) a = Assignable)
    (Hwrite : wm_write sigma sigma' V V' (loc_x, f) val_y),
    exists e' sigma'',
      wm_thread_step CT sigma
        (mkWMThread rΓ (SFldWrite x f y) V)
        sigma''
        e'.
Proof.
  intros Hmem CT sigma sigma' rΓ V V' x f y loc_x rt a val_y
         Hx Htype Hfield Hy Hassign Hwrite.
  exists (mkWMThread rΓ SSkip V'), sigma'.
  eapply WMTS_FldWrite; eauto.
Qed.

Lemma pico_fldwrite_not_stuck :
  forall `{CacheMemoryModel} CT sigma sigma' rΓ V V' x f y loc_x rt a val_y
    (Hx : Helpers.runtime_getVal rΓ x = Some (Iot loc_x))
    (Htype : wm_get_type sigma loc_x = Some rt)
    (Hfield : Typing.sf_assignability_rel CT (rctype rt) f a)
    (Hy : Helpers.runtime_getVal rΓ y = Some val_y)
    (Hassign : Bigstep.runtime_vpa_assignability (rqtype rt) a = Assignable)
    (Hwrite : wm_write sigma sigma' V V' (loc_x, f) val_y),
    @not_stuck (pico_language CT)
      (mkWMThread rΓ (SFldWrite x f y) V)
      sigma.
Proof.
  intros Hmem CT sigma sigma' rΓ V V' x f y loc_x rt a val_y
         Hx Htype Hfield Hy Hassign Hwrite.
  apply pico_not_stuck_intro.
  right.
  eapply pico_fldwrite_thread_step_exists; eauto.
Qed.

Lemma pico_seqskip_thread_step_exists :
  forall `{CacheMemoryModel} CT sigma rΓ V s2,
    exists e' sigma',
      wm_thread_step CT sigma
        (mkWMThread rΓ (SSeq SSkip s2) V)
        sigma'
        e'.
Proof.
  intros Hmem CT sigma rΓ V s2.
  exists (mkWMThread rΓ s2 V), sigma.
  apply WMTS_SeqSkip.
Qed.

Lemma pico_seqskip_not_stuck :
  forall `{CacheMemoryModel} CT sigma rΓ V s2,
    @not_stuck (pico_language CT)
      (mkWMThread rΓ (SSeq SSkip s2) V)
      sigma.
Proof.
  intros Hmem CT sigma rΓ V s2.
  apply pico_not_stuck_intro.
  right.
  apply pico_seqskip_thread_step_exists.
Qed.

Lemma pico_seqstep_thread_step_exists :
  forall `{CacheMemoryModel} CT sigma sigma' rΓ rΓ' V V' s1 s1' s2
    (Hstep : wm_thread_step CT sigma
      (mkWMThread rΓ s1 V)
      sigma'
      (mkWMThread rΓ' s1' V')),
    exists e' sigma'',
      wm_thread_step CT sigma
        (mkWMThread rΓ (SSeq s1 s2) V)
        sigma''
        e'.
Proof.
  intros Hmem CT sigma sigma' rΓ rΓ' V V' s1 s1' s2 Hstep.
  exists (mkWMThread rΓ' (residual_seq_wm s1' s2) V'), sigma'.
  eapply WMTS_SeqStep; eauto.
Qed.

Lemma pico_seqstep_not_stuck :
  forall `{CacheMemoryModel} CT sigma sigma' rΓ rΓ' V V' s1 s1' s2
    (Hstep : wm_thread_step CT sigma
      (mkWMThread rΓ s1 V)
      sigma'
      (mkWMThread rΓ' s1' V')),
    @not_stuck (pico_language CT)
      (mkWMThread rΓ (SSeq s1 s2) V)
      sigma.
Proof.
  intros Hmem CT sigma sigma' rΓ rΓ' V V' s1 s1' s2 Hstep.
  apply pico_not_stuck_intro.
  right.
  eapply pico_seqstep_thread_step_exists; eauto.
Qed.

Lemma pico_prim_step_no_observations :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_language CT) e sigma k e' sigma' efs),
    k = [].
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact (proj1 Hstep).
Qed.

Lemma pico_prim_step_inv :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_language CT) e sigma k e' sigma' efs),
    k = [] /\ efs = [] /\ wm_thread_step CT sigma e sigma' e'.
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact Hstep.
Qed.

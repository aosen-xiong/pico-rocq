From iris.program_logic Require Import language.

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep ViewpointAdaptation
  PICOBridge.PicoMemoryModel.

(** * Core Iris Language for PICO

    This file gives the Iris operational boundary used by the canonical
    statement-grammar LR. It
    keeps the existing surface PICO syntax, but runs it inside an explicit core
    control state with a continuation stack.  The machine state contains both
    the ordinary PICO heap and the field-history weak state.

    The step relation is still intentionally parametric in [CacheMemoryModel]:
    field reads go through [wm_read], and field writes append whole values
    through [wm_write]. *)

Record pico_core_state := mkPicoCoreState {
  pcs_heap : heap;
  pcs_weak : wm_state;
}.

Inductive pico_core_frame : Type :=
  | KSeq : stmt -> pico_core_frame
  | KCall : r_env -> var -> var -> pico_core_frame.

Definition pico_core_cont : Type := list pico_core_frame.

Inductive pico_core_expr : Type :=
  | CoreRun : r_env -> stmt -> view -> pico_core_cont -> pico_core_expr
  | CoreDone : eval_result -> r_env -> view -> pico_core_expr.

Record pico_core_val := mkPicoCoreVal {
  pcv_result : eval_result;
  pcv_env : r_env;
  pcv_view : view;
}.

Definition pico_core_of_val (v : pico_core_val) : pico_core_expr :=
  CoreDone (pcv_result v) (pcv_env v) (pcv_view v).

Definition pico_core_to_val (e : pico_core_expr) : option pico_core_val :=
  match e with
  | CoreDone r rΓ V => Some (mkPicoCoreVal r rΓ V)
  | CoreRun _ _ _ _ => None
  end.

Definition pico_core_alloc_weak
    (sigma : wm_state) (o : Obj) (V : view) : wm_state :=
  let loc := length (wm_objs sigma) in
  mkWMState
    (wm_objs sigma ++ [rt_type o])
    (fun addr =>
      if Nat.eqb (fst addr) loc then
        match nth_error (fields_map o) (snd addr) with
        | Some v => [mkWriteMsg v 0 V]
        | None => wm_mem sigma addr
        end
      else wm_mem sigma addr).

(** Agreement of heap allocation and runtime types. Field-value/history
    agreement is the stronger [pico_core_histories_initialized] invariant in
    [PicoIrisCoreInvariant]. *)
Definition heap_wm_type_agree (h : heap) (sigma : wm_state) : Prop :=
  length h = length (wm_objs sigma) /\
  forall loc o,
    runtime_getObj h loc = Some o ->
    wm_get_type sigma loc = Some (rt_type o).

Lemma heap_wm_type_agree_type :
  forall h sigma loc o
    (Hagree : heap_wm_type_agree h sigma)
    (Hobj : runtime_getObj h loc = Some o),
    wm_get_type sigma loc = Some (rt_type o).
Proof.
  intros h sigma loc o [_ Htypes] Hobj.
  eapply Htypes; eauto.
Qed.

Lemma pico_core_to_of_val :
  forall v, pico_core_to_val (pico_core_of_val v) = Some v.
Proof.
  intros [].
  reflexivity.
Qed.

Lemma pico_core_of_to_val :
  forall e v,
    pico_core_to_val e = Some v ->
    e = pico_core_of_val v.
Proof.
  intros [rΓ s V K | r rΓ V] [rv rΓv Vv] Hto; simpl in Hto.
  - discriminate.
  - inversion Hto; subst.
    reflexivity.
Qed.

Inductive pico_core_step
    `{CacheMemoryModel} (CT : class_table) :
    pico_core_expr -> pico_core_state ->
    pico_core_expr -> pico_core_state -> Prop :=
  | PCS_SkipDone : forall rΓ V sigma,
      pico_core_step CT
        (CoreRun rΓ SSkip V [])
        sigma
        (CoreDone OK rΓ V)
        sigma

  | PCS_SkipSeq : forall rΓ V s2 K sigma,
      pico_core_step CT
        (CoreRun rΓ SSkip V (KSeq s2 :: K))
        sigma
        (CoreRun rΓ s2 V K)
        sigma

  | PCS_SkipCall : forall callee caller x ret V K sigma retval,
      runtime_getVal callee ret = Some retval ->
      pico_core_step CT
        (CoreRun callee SSkip V (KCall caller x ret :: K))
        sigma
        (CoreRun (set_vars caller (update x retval (vars caller))) SSkip V K)
        sigma

  | PCS_Local : forall rΓ T x V K sigma,
      runtime_getVal rΓ x = None ->
      pico_core_step CT
        (CoreRun rΓ (SLocal T x) V K)
        sigma
        (CoreRun (set_vars rΓ (vars rΓ ++ [default_value T])) SSkip V K)
        sigma

  | PCS_AssignNull : forall rΓ x old_v V K sigma,
      runtime_getVal rΓ x = Some old_v ->
      pico_core_step CT
        (CoreRun rΓ (SVarAss x ENull) V K)
        sigma
        (CoreRun (set_vars rΓ (update x Null_a (vars rΓ))) SSkip V K)
        sigma

  | PCS_AssignVar : forall rΓ x y old_v val_y V K sigma,
      runtime_getVal rΓ x = Some old_v ->
      runtime_getVal rΓ y = Some val_y ->
      pico_core_step CT
        (CoreRun rΓ (SVarAss x (EVar y)) V K)
        sigma
        (CoreRun (set_vars rΓ (update x val_y (vars rΓ))) SSkip V K)
        sigma

  | PCS_AssignInt : forall rΓ x n old_v V K sigma,
      runtime_getVal rΓ x = Some old_v ->
      pico_core_step CT
        (CoreRun rΓ (SVarAss x (EInt n)) V K)
        sigma
        (CoreRun (set_vars rΓ (update x (Int n) (vars rΓ))) SSkip V K)
        sigma

  | PCS_AssignField : forall rΓ x y f old_v loc_y v V V' K h sigma,
      runtime_getVal rΓ x = Some old_v ->
      runtime_getVal rΓ y = Some (Iot loc_y) ->
      wm_read sigma V (loc_y, f) v V' ->
      pico_core_step CT
        (CoreRun rΓ (SVarAss x (EField y f)) V K)
        (mkPicoCoreState h sigma)
        (CoreRun (set_vars rΓ (update x v (vars rΓ))) SSkip V' K)
        (mkPicoCoreState h sigma)

  | PCS_AssignFieldNPE : forall rΓ x y f old_v V K sigma,
      runtime_getVal rΓ x = Some old_v ->
      runtime_getVal rΓ y = Some Null_a ->
      pico_core_step CT
        (CoreRun rΓ (SVarAss x (EField y f)) V K)
        sigma
        (CoreDone NPE rΓ V)
        sigma

  | PCS_FldWrite : forall rΓ x f y loc_x o a val_y h h' sigma sigma' V V' K,
      runtime_getVal rΓ x = Some (Iot loc_x) ->
      runtime_getObj h loc_x = Some o ->
      sf_assignability_rel CT (rctype (rt_type o)) f a ->
      runtime_getVal rΓ y = Some val_y ->
      runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable ->
      h' = update_field h loc_x f val_y ->
      wm_write sigma sigma' V V' (loc_x, f) val_y ->
      pico_core_step CT
        (CoreRun rΓ (SFldWrite x f y) V K)
        (mkPicoCoreState h sigma)
        (CoreRun rΓ SSkip V' K)
        (mkPicoCoreState h' sigma')

  | PCS_FldWriteNPE : forall rΓ x f y V K sigma,
      runtime_getVal rΓ x = Some Null_a ->
      pico_core_step CT
        (CoreRun rΓ (SFldWrite x f y) V K)
        sigma
        (CoreDone NPE rΓ V)
        sigma

  | PCS_FldWriteMutation : forall rΓ x f y loc_x o a val_y h sigma V K,
      runtime_getVal rΓ x = Some (Iot loc_x) ->
      runtime_getObj h loc_x = Some o ->
      sf_assignability_rel CT (rctype (rt_type o)) f a ->
      runtime_getVal rΓ y = Some val_y ->
      runtime_vpa_assignability (rqtype (rt_type o)) a = Final ->
      pico_core_step CT
        (CoreRun rΓ (SFldWrite x f y) V K)
        (mkPicoCoreState h sigma)
        (CoreDone MUTATIONEXP rΓ V)
        (mkPicoCoreState h sigma)

  | PCS_New : forall rΓ x qc C args loc_this qthisr vals o qadapted h h' sigma sigma' V K,
      runtime_getVal rΓ 0 = Some (Iot loc_this) ->
      runtime_lookup_list rΓ args = Some vals ->
      r_muttype h loc_this = Some qthisr ->
      vpa_mutability_object_creation qthisr qc = qadapted ->
      o = mkObj (mkruntime_type qadapted C) vals ->
      h' = h ++ [o] ->
      sigma' = pico_core_alloc_weak sigma o V ->
      pico_core_step CT
        (CoreRun rΓ (SNew x qc C args) V K)
        (mkPicoCoreState h sigma)
        (CoreRun (set_vars rΓ (update x (Iot (dom h)) (vars rΓ))) SSkip V K)
        (mkPicoCoreState h' sigma')

  | PCS_Call : forall rΓ x y m args vals loc_y C mdef body mstmt ret h sigma V K,
      runtime_getVal rΓ y = Some (Iot loc_y) ->
      r_basetype h loc_y = Some C ->
      FindMethodWithName CT C m mdef ->
      body = mbody mdef ->
      mstmt = mbody_stmt body ->
      ret = mreturn body ->
      runtime_lookup_list rΓ args = Some vals ->
      pico_core_step CT
        (CoreRun rΓ (SCall x y m args) V K)
        (mkPicoCoreState h sigma)
        (CoreRun (mkr_env (Iot loc_y :: vals)) mstmt V (KCall rΓ x ret :: K))
        (mkPicoCoreState h sigma)

  | PCS_CallNPE : forall rΓ x y m args V K sigma,
      runtime_getVal rΓ y = Some Null_a ->
      pico_core_step CT
        (CoreRun rΓ (SCall x y m args) V K)
        sigma
        (CoreDone NPE rΓ V)
        sigma

  | PCS_Seq : forall rΓ s1 s2 V K sigma,
      pico_core_step CT
        (CoreRun rΓ (SSeq s1 s2) V K)
        sigma
        (CoreRun rΓ s1 V (KSeq s2 :: K))
        sigma

  | PCS_IfZero : forall rΓ x s_zero s_nonzero V K sigma,
      runtime_getVal rΓ x = Some (Int 0) ->
      pico_core_step CT
        (CoreRun rΓ (SIfZero x s_zero s_nonzero) V K)
        sigma
        (CoreRun rΓ s_zero V K)
        sigma

  | PCS_IfNonzero : forall rΓ x n s_zero s_nonzero V K sigma,
      runtime_getVal rΓ x = Some (Int (S n)) ->
      pico_core_step CT
        (CoreRun rΓ (SIfZero x s_zero s_nonzero) V K)
        sigma
        (CoreRun rΓ s_nonzero V K)
        sigma

  | PCS_IfZeroNPE : forall rΓ x s_zero s_nonzero V K sigma,
      runtime_getVal rΓ x = Some Null_a ->
      pico_core_step CT
        (CoreRun rΓ (SIfZero x s_zero s_nonzero) V K)
        sigma
        (CoreDone NPE rΓ V)
        sigma.

Lemma runtime_getObj_update_field_type :
  forall h loc f v loc' o',
    runtime_getObj (update_field h loc f v) loc' = Some o' ->
    exists o,
      runtime_getObj h loc' = Some o /\
      rt_type o' = rt_type o.
Proof.
  intros h loc f v loc' o' Hobj'.
  unfold update_field in Hobj'.
  destruct (runtime_getObj h loc) as [[rt fields] |] eqn:Hobj.
  - destruct (Nat.eq_dec loc loc') as [Heq | Hneq].
    + subst loc'.
      rewrite runtime_getObj_update_same in Hobj'.
      * inversion Hobj'; subst.
        exists (mkObj rt fields).
        split; [exact Hobj | reflexivity].
      * eapply runtime_getObj_dom; eauto.
    + rewrite runtime_getObj_update_diff in Hobj'; [| exact Hneq].
      exists o'.
      split; [exact Hobj' | reflexivity].
  - exists o'.
    split; [exact Hobj' | reflexivity].
Qed.

Lemma heap_wm_type_agree_alloc :
  forall h weak o V,
    heap_wm_type_agree h weak ->
    heap_wm_type_agree
      (h ++ [o])
      (pico_core_alloc_weak weak o V).
Proof.
  intros h weak o V [Hlen Htypes].
  split.
  - unfold pico_core_alloc_weak.
    simpl.
    rewrite !length_app.
    simpl.
    lia.
  - intros loc o' Hobj'.
    destruct (Nat.eq_dec loc (dom h)) as [Heq | Hneq].
    + subst loc.
      destruct o as [rt fields].
      rewrite runtime_getObj_last in Hobj'.
      inversion Hobj'; subst.
      unfold pico_core_alloc_weak, wm_get_type.
      simpl.
      rewrite nth_error_app2.
      * rewrite Hlen.
        rewrite Nat.sub_diag.
        reflexivity.
      * lia.
    + assert (Hloc_lt : loc < dom h).
      {
        pose proof (runtime_getObj_dom loc o' (h ++ [o]) Hobj') as Hdom.
        rewrite length_app in Hdom.
        simpl in Hdom.
        lia.
      }
      unfold runtime_getObj in Hobj'.
      rewrite nth_error_app1 in Hobj'; [| exact Hloc_lt].
      unfold pico_core_alloc_weak, wm_get_type.
      simpl.
      rewrite nth_error_app1.
      * eapply Htypes; eauto.
      * lia.
Qed.

Lemma heap_wm_type_agree_write_update_field :
  forall h weak weak' V V' loc f v,
    heap_wm_type_agree h weak ->
    wm_write weak weak' V V' (loc, f) v ->
    heap_wm_type_agree (update_field h loc f v) weak'.
Proof.
  intros h weak weak' V V' loc f v [Hlen Htypes] Hwrite.
  split.
  - rewrite update_field_length.
    destruct Hwrite as [-> _].
    unfold append_write_msg.
    simpl.
    exact Hlen.
  - intros loc' o' Hobj'.
    destruct (runtime_getObj_update_field_type h loc f v loc' o' Hobj')
      as [o [Hobj Htype]].
    rewrite Htype.
    rewrite (wm_write_get_type weak weak' V V' (loc, f) v loc' Hwrite).
    eapply Htypes; eauto.
Qed.

Theorem pico_core_step_preserves_heap_wm_type_agree :
  forall `{CacheMemoryModel} CT e sigma e' sigma',
    heap_wm_type_agree (pcs_heap sigma) (pcs_weak sigma) ->
    pico_core_step CT e sigma e' sigma' ->
    heap_wm_type_agree (pcs_heap sigma') (pcs_weak sigma').
Proof.
  intros Hmem CT e sigma e' sigma' Hagree Hstep.
  inversion Hstep; subst; simpl in *; try exact Hagree.
  - eapply heap_wm_type_agree_write_update_field; eauto.
  - apply heap_wm_type_agree_alloc.
    exact Hagree.
Qed.

Inductive pico_core_steps `{CacheMemoryModel} (CT : class_table) :
    pico_core_expr -> pico_core_state ->
    pico_core_expr -> pico_core_state -> Prop :=
  | PicoCoreStepsRefl : forall e sigma,
      pico_core_steps CT e sigma e sigma
  | PicoCoreStepsStep : forall e sigma e1 sigma1 e2 sigma2,
      pico_core_step CT e sigma e1 sigma1 ->
      pico_core_steps CT e1 sigma1 e2 sigma2 ->
      pico_core_steps CT e sigma e2 sigma2.

Lemma pico_core_skip_done_unique `{CacheMemoryModel} CT rGamma V state next state' :
  pico_core_step CT (CoreRun rGamma SSkip V []) state next state' ->
  next = CoreDone OK rGamma V /\ state' = state.
Proof.
  intros Hstep. inversion Hstep; subst. split; reflexivity.
Qed.

Theorem pico_core_steps_preserve_heap_wm_type_agree :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hagree : heap_wm_type_agree (pcs_heap sigma) (pcs_weak sigma))
    (Hsteps : pico_core_steps CT e sigma e' sigma'),
    heap_wm_type_agree (pcs_heap sigma') (pcs_weak sigma').
Proof.
  intros Hmem CT e sigma e' sigma' Hagree Hsteps.
  induction Hsteps as
    [e0 sigma0
    | e0 sigma0 e1 sigma1 e2 sigma2 Hstep _ IH].
  - exact Hagree.
  - apply IH.
    eapply pico_core_step_preserves_heap_wm_type_agree; eauto.
Qed.

Definition pico_core_result_allowed (r : eval_result) : Prop :=
  r = OK \/ r = NPE \/ r = MUTATIONEXP.

Lemma pico_core_step_to_done_result_allowed :
  forall `{CacheMemoryModel} CT e sigma r rΓ V sigma'
    (Hstep : pico_core_step CT e sigma (CoreDone r rΓ V) sigma'),
    pico_core_result_allowed r.
Proof.
  intros Hmem CT e sigma r rΓ V sigma' Hstep.
  inversion Hstep; subst; unfold pico_core_result_allowed; auto.
Qed.

Lemma pico_core_steps_from_done_inv :
  forall `{CacheMemoryModel} CT r rΓ V sigma e' sigma'
    (Hsteps : pico_core_steps CT (CoreDone r rΓ V) sigma e' sigma'),
    e' = CoreDone r rΓ V /\ sigma' = sigma.
Proof.
  intros Hmem CT r rΓ V sigma e' sigma' Hsteps.
  remember (CoreDone r rΓ V) as e0 eqn:Heq.
  induction Hsteps as
    [e sigma0
    | e sigma0 e1 sigma1 e2 sigma2 Hstep Hsteps IH];
    subst.
  - split; reflexivity.
  - exfalso.
    inversion Hstep.
Qed.

Theorem pico_core_steps_to_done_result_allowed :
  forall `{CacheMemoryModel} CT e sigma r rΓ V sigma'
    (Hrun : exists rΓ0 s0 V0 K0, e = CoreRun rΓ0 s0 V0 K0)
    (Hsteps : pico_core_steps CT e sigma (CoreDone r rΓ V) sigma'),
    pico_core_result_allowed r.
Proof.
  intros Hmem CT e sigma r rΓ V sigma' Hrun Hsteps.
  remember (CoreDone r rΓ V) as done eqn:Hdone.
  revert r rΓ V Hdone Hrun.
  induction Hsteps as
    [e0 sigma0
    | e0 sigma0 e1 sigma1 e2 sigma2 Hstep Hsteps IH];
    intros r_final rΓ_final V_final Hdone Hrun.
  - subst e0.
    destruct Hrun as [rΓ0 [s0 [V0 [K0 Heq]]]].
    discriminate Heq.
  - destruct e1 as [rΓ1 s1 V1 K1 | r1 rΓ1 V1].
    + eapply (IH r_final rΓ_final V_final).
      * exact Hdone.
      * exists rΓ1, s1, V1, K1.
        reflexivity.
    + destruct
        (pico_core_steps_from_done_inv
          CT r1 rΓ1 V1 sigma1 e2 sigma2 Hsteps)
        as [Heq_done _].
      rewrite Heq_done in Hdone.
      inversion Hdone; subst.
      eapply pico_core_step_to_done_result_allowed; eauto.
Qed.

Definition pico_core_prim_step
    `{CacheMemoryModel} (CT : class_table) :
    pico_core_expr -> pico_core_state -> list unit ->
    pico_core_expr -> pico_core_state -> list pico_core_expr -> Prop :=
  fun e sigma k e' sigma' efs =>
    k = [] /\ efs = [] /\ pico_core_step CT e sigma e' sigma'.

Lemma pico_core_no_step_from_value :
  forall `{CacheMemoryModel} CT r rΓ V sigma e' sigma',
    not (pico_core_step CT (CoreDone r rΓ V) sigma e' sigma').
Proof.
  intros Hmem CT r rΓ V sigma e' sigma' Hstep.
  inversion Hstep.
Qed.

Program Definition pico_core_language_mixin `{CacheMemoryModel} (CT : class_table) :
  LanguageMixin
    pico_core_of_val
    pico_core_to_val
    (pico_core_prim_step CT) := {|
  mixin_to_of_val := _;
  mixin_of_to_val := _;
  mixin_val_stuck := _
|}.
Next Obligation.
  apply pico_core_to_of_val.
Qed.
Next Obligation.
  symmetry.
  eapply pico_core_of_to_val; eauto.
Qed.
Next Obligation.
  match goal with
  | Hstep : pico_core_prim_step _ _ _ _ _ _ _ |- _ =>
      unfold pico_core_prim_step in Hstep;
      destruct Hstep as [_ [_ Hcore]]
  end.
  destruct e as [rΓ s V K | r rΓ V]; simpl; try reflexivity.
  exfalso.
  eapply pico_core_no_step_from_value; eauto.
Qed.

Canonical Structure pico_core_language `{CacheMemoryModel} (CT : class_table) :
  language :=
  Language (pico_core_language_mixin CT).

Lemma pico_core_prim_step_no_forks :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_core_language CT) e sigma k e' sigma' efs),
    efs = [].
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact (proj1 (proj2 Hstep)).
Qed.

Lemma pico_core_prim_step_is_core_step :
  forall `{CacheMemoryModel} CT e sigma k e' sigma' efs
    (Hstep : @prim_step (pico_core_language CT) e sigma k e' sigma' efs),
    pico_core_step CT e sigma e' sigma'.
Proof.
  intros Hmem CT e sigma k e' sigma' efs Hstep.
  exact (proj2 (proj2 Hstep)).
Qed.

Lemma pico_core_step_is_prim_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : pico_core_step CT e sigma e' sigma'),
    @prim_step (pico_core_language CT) e sigma [] e' sigma' [].
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  repeat split; assumption.
Qed.

Lemma pico_core_reducible_from_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : pico_core_step CT e sigma e' sigma'),
    @reducible (pico_core_language CT) e sigma.
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  exists (@nil unit), e', sigma', (@nil pico_core_expr).
  apply pico_core_step_is_prim_step.
  exact Hstep.
Qed.

Lemma pico_core_step_from_reducible :
  forall `{CacheMemoryModel} CT e sigma
    (Hred : @reducible (pico_core_language CT) e sigma),
    exists e' sigma',
      pico_core_step CT e sigma e' sigma'.
Proof.
  intros Hmem CT e sigma Hred.
  destruct Hred as [k [e' [sigma' [efs Hprim]]]].
  exists e', sigma'.
  eapply pico_core_prim_step_is_core_step; eauto.
Qed.

Lemma pico_core_reducible_iff_step :
  forall `{CacheMemoryModel} CT e sigma,
    @reducible (pico_core_language CT) e sigma <->
    exists e' sigma',
      pico_core_step CT e sigma e' sigma'.
Proof.
  intros Hmem CT e sigma.
  split.
  - apply pico_core_step_from_reducible.
  - intros [e' [sigma' Hstep]].
    eapply pico_core_reducible_from_step; eauto.
Qed.

Lemma pico_core_not_stuck_from_step :
  forall `{CacheMemoryModel} CT e sigma e' sigma'
    (Hstep : pico_core_step CT e sigma e' sigma'),
    @not_stuck (pico_core_language CT) e sigma.
Proof.
  intros Hmem CT e sigma e' sigma' Hstep.
  right.
  eapply pico_core_reducible_from_step; eauto.
Qed.

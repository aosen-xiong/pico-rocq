From iris.program_logic Require Import language.

From Stdlib Require Import List Lia.
From Stdlib Require Import Program.Equality.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage.

(** * Runtime Invariant for PICO Core Safety

    The core operational language separates whole-value read validity from
    read progress.  [CacheMemoryModel] says that a read which occurs selects a
    complete message from the addressed field history.  The class below adds
    the progress property needed by a [NotStuck] logical relation: a nonempty
    field history admits some read.

    This file also strengthens PICO's preservation-oriented runtime
    configuration with value shapes.  The original [wf_r_config] deliberately
    treats integer values permissively; that is enough for preservation of
    terminating big-step derivations, but not enough to prove that a field or
    method receiver can take an operational step. *)

Class CacheMemoryModelProgress `{CacheMemoryModel} := {
  wm_read_nonempty :
    forall sigma V addr,
      history_of sigma addr <> [] ->
      exists v V', wm_read sigma V addr v V'
}.

#[global] Instance history_cache_memory_model_progress :
    @CacheMemoryModelProgress history_cache_memory_model.
Proof.
  constructor. intros sigma V addr Hnonempty.
  destruct (history_of sigma addr) as [|msg hist] eqn:Hhist;
    [contradiction |].
  exists (msg_val msg), V. split; [reflexivity |].
  exists msg. split; [rewrite Hhist; left; reflexivity | reflexivity].
Defined.

(** [pico_core_typed_value] is the type-indexed runtime value relation used by
    the progress-facing LR.  Null inhabits reference types, integers inhabit
    [TInt], and locations inhabit reference types through [wf_r_typable]. *)
Definition pico_core_typed_value
    (CT : class_table) (rGamma : r_env) (h : heap) (qcontext : q_r)
    (T : qualified_type) (v : value) : Prop :=
  match v with
  | Null_a => exists C, sbase T = TRef C
  | Int _ => sbase T = TInt
  | Iot loc => wf_r_typable CT rGamma h loc T qcontext
  end.

(** A typed runtime environment retains the existing PICO configuration facts
    and additionally relates every statically present variable to a
    type-indexed runtime value. *)
Definition pico_core_typed_env
    (CT : class_table) (sGamma : s_env) (rGamma : r_env) (h : heap) : Prop :=
  exists qcontext receiver,
    wf_r_config CT sGamma rGamma h /\
    get_this_var_mapping (vars rGamma) = Some receiver /\
    r_muttype h receiver = Some qcontext /\
    forall x T,
      static_getType sGamma x = Some T ->
      exists v,
        runtime_getVal rGamma x = Some v /\
        pico_core_typed_value CT rGamma h qcontext T v.

(** A runtime fact used by the cache-specific conditional rule.  The CESK
    conditional may inspect only a whole integer or [Null_a]. *)
Definition pico_core_int_guard (rGamma : r_env) (x : var) : Prop :=
  runtime_getVal rGamma x = Some Null_a \/
  exists n, runtime_getVal rGamma x = Some (Int n).

Definition pico_core_whole_int_guard (rGamma : r_env) (x : var) : Prop :=
  exists n, runtime_getVal rGamma x = Some (Int n).

Lemma pico_core_int_guard_ifzero_step `{Hmem : CacheMemoryModel} :
  forall CT rGamma h sigma V K x s_zero s_nonzero,
    pico_core_int_guard rGamma x ->
    exists e',
      pico_core_step CT
        (CoreRun rGamma (SIfZero x s_zero s_nonzero) V K)
        (mkPicoCoreState h sigma) e' (mkPicoCoreState h sigma).
Proof.
  intros CT rGamma h sigma V K x s_zero s_nonzero Hguard.
  destruct Hguard as [Hnull | [n Hinteger]].
  - exists (CoreDone NPE rGamma V).
    apply PCS_IfZeroNPE.
    exact Hnull.
  - destruct n as [|n].
    + exists (CoreRun rGamma s_zero V K).
      apply PCS_IfZero.
      exact Hinteger.
    + exists (CoreRun rGamma s_nonzero V K).
      eapply PCS_IfNonzero.
      exact Hinteger.
Qed.

(** Heap evolution visible to suspended CESK frames.  Existing locations stay
    allocated with exactly the same runtime type; field contents may change
    and fresh locations may be appended. *)
Definition pico_core_heap_types_extend (h h' : heap) : Prop :=
  length h <= length h' /\
  forall loc runtime_type,
    r_type h loc = Some runtime_type ->
    r_type h' loc = Some runtime_type.

Lemma pico_core_heap_types_extend_refl :
  forall h, pico_core_heap_types_extend h h.
Proof.
  intros h.
  split; [lia | auto].
Qed.

Lemma pico_core_heap_types_extend_trans :
  forall h1 h2 h3,
    pico_core_heap_types_extend h1 h2 ->
    pico_core_heap_types_extend h2 h3 ->
    pico_core_heap_types_extend h1 h3.
Proof.
  intros h1 h2 h3 [Hlen12 Htypes12] [Hlen23 Htypes23].
  split; [lia |].
  intros loc runtime_type Htype.
  eauto.
Qed.

Lemma pico_core_typed_env_wf_config :
  forall CT sGamma rGamma h
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    wf_r_config CT sGamma rGamma h.
Proof.
  intros CT sGamma rGamma h Henv.
  destruct Henv as (qcontext & receiver & Hwf & _).
  exact Hwf.
Qed.

Lemma pico_core_typed_env_receiver :
  forall CT sGamma rGamma h
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    exists qcontext receiver,
      get_this_var_mapping (vars rGamma) = Some receiver /\
      r_muttype h receiver = Some qcontext.
Proof.
  intros CT sGamma rGamma h Henv.
  destruct Henv as
    (qcontext & receiver & _ & Hreceiver & Hqcontext & _).
  exists qcontext, receiver.
  auto.
Qed.

Lemma pico_core_typed_env_lookup :
  forall CT sGamma rGamma h x T
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstatic : static_getType sGamma x = Some T),
    exists qcontext v,
      runtime_getVal rGamma x = Some v /\
      pico_core_typed_value CT rGamma h qcontext T v.
Proof.
  intros CT sGamma rGamma h x T Henv Hstatic.
  destruct Henv as
    (qcontext & receiver & Hwf & Hreceiver & Hqcontext & Hvalues).
  destruct (Hvalues x T Hstatic) as (v & Hruntime & Htyped).
  exists qcontext, v.
  auto.
Qed.

Lemma pico_core_typed_env_runtime_value :
  forall CT sGamma rGamma h x T v qcontext receiver
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstatic : static_getType sGamma x = Some T)
    (Hruntime : runtime_getVal rGamma x = Some v)
    (Hreceiver : get_this_var_mapping (vars rGamma) = Some receiver)
    (Hqcontext : r_muttype h receiver = Some qcontext),
    pico_core_typed_value CT rGamma h qcontext T v.
Proof.
  intros CT sGamma rGamma h x T v qcontext receiver
    Henv Hstatic Hruntime Hreceiver Hqcontext.
  destruct Henv as
    (qcontext0 & receiver0 & Hwf & Hreceiver0 & Hqcontext0 & Hvalues).
  assert (Hreceiver_eq : receiver = receiver0) by congruence.
  subst receiver.
  assert (Hqcontext_eq : qcontext = qcontext0) by congruence.
  subst qcontext.
  destruct (Hvalues x T Hstatic) as (v0 & Hruntime0 & Htyped).
  assert (v = v0) by congruence.
  subst v.
  exact Htyped.
Qed.

(** Typed weak histories are the memory-side typing invariant.  Every complete
    value written to a field history has the type required by every well-typed
    field-read context that can observe that address.  This is stronger and
    more useful than asserting a property of one chosen read: it is preserved
    as a state invariant and [wm_read_from_history] derives the read rule. *)
Definition pico_core_typed_histories
    (CT : class_table) (h : heap) (sigma : wm_state) : Prop :=
  forall sGamma mt rGamma x y f Tx Te loc v qcontext receiver,
    pico_core_typed_env CT sGamma rGamma h ->
    expr_has_type CT sGamma mt (EField y f) Te ->
    static_getType sGamma x = Some Tx ->
    qualified_type_subtype CT Te Tx ->
    runtime_getVal rGamma y = Some (Iot loc) ->
    get_this_var_mapping (vars rGamma) = Some receiver ->
    r_muttype h receiver = Some qcontext ->
    List.In v (values_written_to sigma (loc, f)) ->
    pico_core_typed_value CT rGamma h qcontext Tx v.

(** Semantic typing of weak field observations, derived from the typed-history
    invariant and the memory interface's whole-value read-from-history law. *)
Definition pico_core_reads_typed
    `{Hmem : CacheMemoryModel}
    (CT : class_table) (h : heap) (sigma : wm_state) : Prop :=
  forall sGamma mt rGamma x y f Tx Te loc v V V',
    pico_core_typed_env CT sGamma rGamma h ->
    expr_has_type CT sGamma mt (EField y f) Te ->
    static_getType sGamma x = Some Tx ->
    qualified_type_subtype CT Te Tx ->
    runtime_getVal rGamma y = Some (Iot loc) ->
    wm_read sigma V (loc, f) v V' ->
    forall qcontext receiver,
      get_this_var_mapping (vars rGamma) = Some receiver ->
      r_muttype h receiver = Some qcontext ->
      pico_core_typed_value CT rGamma h qcontext Tx v.

Lemma pico_core_typed_histories_reads_typed
    `{Hmem : CacheMemoryModel} :
  forall CT h sigma,
    pico_core_typed_histories CT h sigma ->
    pico_core_reads_typed CT h sigma.
Proof.
  intros CT h sigma Hhist
    sGamma mt rGamma x y f Tx Te loc v V V'
    Henv Hfield Hx Hsub Hy Hread qcontext receiver Hreceiver Hqcontext.
  destruct (wm_read_from_history sigma V (loc, f) v V' Hread)
    as (msg & Hmessage & Hvalue).
  subst v.
  apply
    (Hhist sGamma mt rGamma x y f Tx Te loc (msg_val msg)
      qcontext receiver Henv Hfield Hx Hsub Hy Hreceiver Hqcontext).
  unfold values_written_to.
  eapply in_map.
  exact Hmessage.
Qed.

Lemma pico_core_typed_value_null :
  forall CT rGamma h qcontext T C
    (Href : sbase T = TRef C),
    pico_core_typed_value CT rGamma h qcontext T Null_a.
Proof.
  intros CT rGamma h qcontext T C Href.
  unfold pico_core_typed_value.
  eauto.
Qed.

Lemma pico_core_typed_value_default :
  forall CT rGamma h qcontext T,
    pico_core_typed_value CT rGamma h qcontext T (default_value T).
Proof.
  intros CT rGamma h qcontext [q [|C]]; simpl; eauto.
Qed.

Lemma pico_core_typed_value_int :
  forall CT rGamma h qcontext n,
    pico_core_typed_value CT rGamma h qcontext int_type (Int n).
Proof.
  intros.
  reflexivity.
Qed.

Lemma pico_core_typed_value_int_cases :
  forall CT rGamma h qcontext T v
    (Hint : sbase T = TInt)
    (Htyped : pico_core_typed_value CT rGamma h qcontext T v),
    exists n, v = Int n.
Proof.
  intros CT rGamma h qcontext T v Hint Htyped.
  destruct v as [|loc|n].
  - simpl in Htyped.
    destruct Htyped as [C Href].
    rewrite Hint in Href.
    discriminate.
  - simpl in Htyped.
    unfold wf_r_typable in Htyped.
    destruct (r_type h loc) as [rt |] eqn:Hrt; try contradiction.
    destruct Htyped as [Hbase _].
    rewrite Hint in Hbase.
    destruct (base_subtype_from_ref CT (rctype rt) TInt Hbase)
      as [D [Hcontra _]].
    discriminate.
  - eauto.
Qed.

Lemma pico_core_typed_env_whole_int_guard :
  forall CT sGamma rGamma h x T
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstatic : static_getType sGamma x = Some T)
    (Hint : sbase T = TInt),
    pico_core_whole_int_guard rGamma x.
Proof.
  intros CT sGamma rGamma h x T Henv Hstatic Hint.
  destruct (pico_core_typed_env_lookup CT sGamma rGamma h x T Henv Hstatic)
    as (qcontext & v & Hruntime & Htyped).
  destruct (pico_core_typed_value_int_cases
    CT rGamma h qcontext T v Hint Htyped) as [n ->].
  exists n.
  exact Hruntime.
Qed.

Lemma pico_core_typed_value_ref_cases :
  forall CT rGamma h qcontext T v
    C
    (Href : sbase T = TRef C)
    (Htyped : pico_core_typed_value CT rGamma h qcontext T v),
    v = Null_a \/
    exists loc,
      v = Iot loc /\
      wf_r_typable CT rGamma h loc T qcontext.
Proof.
  intros CT rGamma h qcontext T v C Href Htyped.
  destruct v as [|loc|n].
  - left.
    reflexivity.
  - right.
    exists loc.
    split; [reflexivity | exact Htyped].
  - simpl in Htyped.
    rewrite Href in Htyped.
    discriminate.
Qed.

Lemma pico_core_typed_env_field_receiver_cases :
  forall CT sGamma rGamma h y Ty C f fdef
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstatic : static_getType sGamma y = Some Ty)
    (Href : sbase Ty = TRef C)
    (Hfield : sf_def_rel CT C f fdef),
    runtime_getVal rGamma y = Some Null_a \/
    exists qcontext loc,
      runtime_getVal rGamma y = Some (Iot loc) /\
      wf_r_typable CT rGamma h loc Ty qcontext.
Proof.
  intros CT sGamma rGamma h y Ty C f fdef Henv Hstatic Href Hfield.
  destruct
    (pico_core_typed_env_lookup
      CT sGamma rGamma h y Ty Henv Hstatic)
    as (qcontext & v & Hruntime & Htyped).
  destruct
    (pico_core_typed_value_ref_cases
      CT rGamma h qcontext Ty v C Href Htyped)
    as [Hnull | (loc & Hloc & Hloc_typed)].
  - subst v.
    left.
    exact Hruntime.
  - subst v.
    right.
    exists qcontext, loc.
    auto.
Qed.

Lemma pico_core_typed_env_method_receiver_cases :
  forall CT sGamma rGamma h y Ty C m mdef
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstatic : static_getType sGamma y = Some Ty)
    (Href : sbase Ty = TRef C)
    (Hmethod : FindMethodWithName CT C m mdef),
    runtime_getVal rGamma y = Some Null_a \/
    exists qcontext loc,
      runtime_getVal rGamma y = Some (Iot loc) /\
      wf_r_typable CT rGamma h loc Ty qcontext.
Proof.
  intros CT sGamma rGamma h y Ty C m mdef Henv Hstatic Href Hmethod.
  destruct
    (pico_core_typed_env_lookup
      CT sGamma rGamma h y Ty Henv Hstatic)
    as (qcontext & v & Hruntime & Htyped).
  destruct
    (pico_core_typed_value_ref_cases
      CT rGamma h qcontext Ty v C Href Htyped)
    as [Hnull | (loc & Hloc & Hloc_typed)].
  - subst v.
    left.
    exact Hruntime.
  - subst v.
    right.
    exists qcontext, loc.
    auto.
Qed.

Lemma pico_core_typed_receiver_field_exists :
  forall CT sGamma rGamma h loc qcontext Ty C f fdef
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Htyped : wf_r_typable CT rGamma h loc Ty qcontext)
    (Href : sbase Ty = TRef C)
    (Hfield : sf_def_rel CT C f fdef),
    exists o current,
      runtime_getObj h loc = Some o /\
      nth_error (fields_map o) f = Some current.
Proof.
  intros CT sGamma rGamma h loc qcontext Ty C f fdef
    Henv Htyped Href Hfield.
  unfold wf_r_typable, r_type in Htyped.
  destruct (runtime_getObj h loc) as [o |] eqn:Hobj; [| contradiction].
  destruct Htyped as [Hbase Hqualifier].
  assert (Hruntime_field :
    sf_def_rel CT (rctype (rt_type o)) f fdef).
  {
    destruct (base_subtype_from_ref CT (rctype (rt_type o)) (sbase Ty) Hbase)
      as [D0 [HbaseTy Hclass_sub]].
    rewrite HbaseTy in Href.
    inversion Href; subst D0.
    eapply sf_def_subtyping; eauto.
  }
  pose proof (pico_core_typed_env_wf_config CT sGamma rGamma h Henv)
    as Hconfig.
  destruct Hconfig as [_ [Hheap _]].
  assert (Hloc : loc < length h).
  {
    eapply runtime_getObj_dom; eauto.
  }
  specialize (Hheap loc Hloc).
  unfold wf_obj in Hheap.
  rewrite Hobj in Hheap.
  destruct Hheap as
    [Hruntime_type
      (field_defs & Hcollect & Hlength & Hfield_values)].
  unfold sf_def_rel in Hruntime_field.
  inversion Hruntime_field as
    [CT' C' collected f' fdef' Hcollect' Hlookup]; subst.
  assert (Hcollected : collected = field_defs).
  {
    eapply collect_fields_deterministic_rel; eauto.
  }
  subst collected.
  unfold gget in Hlookup.
  assert (Hfield_bound : f < length (fields_map o)).
  {
    rewrite Hlength.
    apply nth_error_Some.
    rewrite Hlookup.
    discriminate.
  }
  destruct (nth_error (fields_map o) f) as [current |] eqn:Hcurrent.
  - exists o, current.
    auto.
  - apply nth_error_None in Hcurrent.
    lia.
Qed.

(** Every current physical field value in the ordinary heap is represented by
    one whole-value message in the corresponding weak history.  Together with
    [CacheMemoryModelProgress], this is the state-side premise that turns a
    typed field access into an available weak read. *)
Definition pico_core_histories_initialized
    (h : heap) (sigma : wm_state) : Prop :=
  forall loc o f current,
    runtime_getObj h loc = Some o ->
    nth_error (fields_map o) f = Some current ->
    exists msg,
      List.In msg (history_of sigma (loc, f)) /\
      msg_val msg = current.

Definition pico_core_state_wf (state : pico_core_state) : Prop :=
  heap_wm_type_agree (pcs_heap state) (pcs_weak state) /\
  pico_core_histories_initialized (pcs_heap state) (pcs_weak state).

(** Operational state predicate used by the typing-directed LR.  Semantic
    validity of weak observations is deliberately not stored here: it belongs
    to the field-read protocol handler and is supplied by [SemImmI]. *)
Definition pico_core_lr_state
    `{Hmem : CacheMemoryModel}
    (_CT : class_table) (state : pico_core_state) : Prop :=
  pico_core_state_wf state.

Lemma pico_core_lr_state_wf
    `{Hmem : CacheMemoryModel} :
  forall CT state
    (Hstate : pico_core_lr_state CT state),
    pico_core_state_wf state.
Proof.
  intros CT state Hstate.
  exact Hstate.
Qed.

Lemma pico_core_state_wf_agree :
  forall state
    (Hstate : pico_core_state_wf state),
    heap_wm_type_agree (pcs_heap state) (pcs_weak state).
Proof.
  intros state Hstate.
  exact (proj1 Hstate).
Qed.

Lemma pico_core_state_wf_history_nonempty :
  forall h sigma loc o f current
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma))
    (Hobj : runtime_getObj h loc = Some o)
    (Hfield : nth_error (fields_map o) f = Some current),
    history_of sigma (loc, f) <> [].
Proof.
  intros h sigma loc o f current Hstate Hobj Hfield.
  destruct Hstate as [_ Hinitialized].
  destruct (Hinitialized loc o f current Hobj Hfield)
    as [msg [Hin _]].
  intro Hempty.
  rewrite Hempty in Hin.
  contradiction.
Qed.

Lemma pico_core_state_wf_read_exists
    `{Hmem : CacheMemoryModel}
    `{Hprogress : CacheMemoryModelProgress} :
  forall h sigma V loc o f current
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma))
    (Hobj : runtime_getObj h loc = Some o)
    (Hfield : nth_error (fields_map o) f = Some current),
    exists v V', wm_read sigma V (loc, f) v V'.
Proof.
  intros h sigma V loc o f current Hstate Hobj Hfield.
  apply wm_read_nonempty.
  eapply pico_core_state_wf_history_nonempty; eauto.
Qed.

(** Allocation initializes every field of the newly appended object with a
    singleton history and leaves histories of older objects unchanged. *)
Lemma pico_core_histories_initialized_alloc :
  forall h sigma o V
    (Hlength : length h = length (wm_objs sigma))
    (Hinitialized : pico_core_histories_initialized h sigma),
    pico_core_histories_initialized
      (h ++ [o])
      (pico_core_alloc_weak sigma o V).
Proof.
  intros h sigma o V Hlength Hinitialized loc o' f current Hobj Hfield.
  assert (Hloc_bound : loc < length h + 1).
  {
    pose proof (runtime_getObj_dom loc o' (h ++ [o]) Hobj) as Hbound.
    rewrite length_app in Hbound.
    simpl in Hbound.
    exact Hbound.
  }
  destruct (Nat.lt_ge_cases loc (length h)) as [Hold | Hnew].
  - assert (Hobj_old : runtime_getObj h loc = Some o').
    {
      unfold runtime_getObj in *.
      rewrite nth_error_app1 in Hobj; [exact Hobj | exact Hold].
    }
    unfold history_of, pico_core_alloc_weak.
    simpl.
    assert (Hneq : loc <> length (wm_objs sigma)).
    {
      rewrite <- Hlength.
      lia.
    }
    apply Nat.eqb_neq in Hneq.
    rewrite Hneq.
    eapply Hinitialized; eauto.
  - assert (Heq : loc = length h) by lia.
    subst loc.
    assert (Hobj_new : o' = o).
    {
      unfold runtime_getObj in Hobj.
      rewrite nth_error_app2 in Hobj; [| lia].
      rewrite Nat.sub_diag in Hobj.
      simpl in Hobj.
      inversion Hobj.
      reflexivity.
    }
    subst o'.
    unfold history_of, pico_core_alloc_weak.
    simpl.
    rewrite <- Hlength.
    rewrite Nat.eqb_refl.
    rewrite Hfield.
    eexists.
    split; [left; reflexivity | reflexivity].
Qed.

Lemma pico_core_state_wf_alloc :
  forall h sigma o V
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma)),
    pico_core_state_wf
      (mkPicoCoreState
        (h ++ [o])
        (pico_core_alloc_weak sigma o V)).
Proof.
  intros h sigma o V Hstate.
  destruct Hstate as [Hagree Hinitialized].
  split.
  - eapply heap_wm_type_agree_alloc.
    exact Hagree.
  - eapply pico_core_histories_initialized_alloc.
    + exact (proj1 Hagree).
    + exact Hinitialized.
Qed.

Lemma runtime_getObj_update_field_same_value :
  forall h loc f value o
    (Hobj : runtime_getObj h loc = Some o),
    runtime_getObj (update_field h loc f value) loc =
      Some (set_fields_map o (update f value (fields_map o))).
Proof.
  intros h loc f value o Hobj.
  unfold update_field.
  rewrite Hobj.
  unfold runtime_getObj.
  apply update_same.
  eapply runtime_getObj_dom; eauto.
Qed.

Lemma runtime_getObj_update_field_other_value :
  forall h loc f value o loc'
    (Hobj : runtime_getObj h loc = Some o)
    (Hneq : loc <> loc'),
    runtime_getObj (update_field h loc f value) loc' =
      runtime_getObj h loc'.
Proof.
  intros h loc f value o loc' Hobj Hneq.
  unfold update_field.
  rewrite Hobj.
  unfold runtime_getObj.
  apply update_diff.
      exact Hneq.
Qed.

Lemma pico_core_r_type_update_field :
  forall h loc f value o loc'
    (Hobj : runtime_getObj h loc = Some o),
    r_type (update_field h loc f value) loc' = r_type h loc'.
Proof.
  intros h loc f value o loc' Hobj.
  unfold r_type.
  destruct (Nat.eq_dec loc loc') as [Heq | Hneq].
  - subst loc'.
    rewrite
      (runtime_getObj_update_field_same_value
        h loc f value o Hobj).
    rewrite Hobj.
    reflexivity.
  - rewrite
      (runtime_getObj_update_field_other_value
        h loc f value o loc' Hobj Hneq).
    reflexivity.
Qed.

Lemma pico_core_heap_types_extend_write :
  forall h loc f value o
    (Hobj : runtime_getObj h loc = Some o),
    pico_core_heap_types_extend h (update_field h loc f value).
Proof.
  intros h loc f value o Hobj.
  split.
  - unfold update_field.
    rewrite Hobj.
    rewrite update_length.
    lia.
  - intros loc' runtime_type Htype.
    rewrite
      (pico_core_r_type_update_field h loc f value o loc' Hobj).
    exact Htype.
Qed.

Lemma pico_core_heap_types_extend_alloc :
  forall h o,
    pico_core_heap_types_extend h (h ++ [o]).
Proof.
  intros h o.
  split.
  - rewrite length_app.
    simpl.
    lia.
  - intros loc runtime_type Htype.
    unfold r_type in *.
    destruct (runtime_getObj h loc) as [old |] eqn:Hold;
      try discriminate.
    assert (Hloc : loc < length h).
    { eapply runtime_getObj_dom; eauto. }
    unfold runtime_getObj in Hold |- *.
    rewrite nth_error_app1; [| exact Hloc].
    rewrite Hold.
    exact Htype.
Qed.

(** A whole-value write keeps every old non-target history nonempty and makes
    the target history nonempty by appending its new message. *)
Lemma pico_core_histories_initialized_write :
  forall h sigma sigma' V V' loc f value o
    (Hinitialized : pico_core_histories_initialized h sigma)
    (Hobj : runtime_getObj h loc = Some o)
    (Hwrite : wm_write sigma sigma' V V' (loc, f) value),
    pico_core_histories_initialized
      (update_field h loc f value)
      sigma'.
Proof.
  intros h sigma sigma' V V' loc f value o
    Hinitialized Hobj Hwrite loc' o' f' current Hobj' Hfield'.
  destruct (Nat.eq_dec loc loc') as [Hloc | Hloc].
  - subst loc'.
    rewrite
      (runtime_getObj_update_field_same_value h loc f value o Hobj)
      in Hobj'.
    inversion Hobj'; subst o'.
    destruct (Nat.eq_dec f f') as [Hfield_eq | Hfield_neq].
    + subst f'.
      simpl in Hfield'.
      assert (Hbound : f < length (fields_map o)).
      {
        rewrite <- (@update_length Syntax.value f value (fields_map o)).
        apply nth_error_Some.
        rewrite Hfield'.
        discriminate.
      }
      rewrite (@update_same Syntax.value f value (fields_map o) Hbound)
        in Hfield'.
      inversion Hfield'; subst current.
      rewrite (wm_write_history_same
        sigma sigma' V V' (loc, f) value Hwrite).
      eexists.
      split.
      * apply in_or_app.
        right.
        left.
        reflexivity.
      * reflexivity.
    + simpl in Hfield'.
      rewrite update_diff in Hfield'; [| exact Hfield_neq].
      assert (Haddr : (loc, f') <> (loc, f)) by congruence.
      rewrite (wm_write_history_other
        sigma sigma' V V' (loc, f) (loc, f') value Haddr Hwrite).
      eapply Hinitialized; eauto.
  - assert (Hobj_old : runtime_getObj h loc' = Some o').
    {
      rewrite <- Hobj'.
      symmetry.
      eapply runtime_getObj_update_field_other_value; eauto.
    }
    assert (Haddr : (loc', f') <> (loc, f)) by congruence.
    rewrite (wm_write_history_other
      sigma sigma' V V' (loc, f) (loc', f') value Haddr Hwrite).
    eapply Hinitialized; eauto.
Qed.

Lemma pico_core_state_wf_write :
  forall h sigma sigma' V V' loc f value o
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma))
    (Hobj : runtime_getObj h loc = Some o)
    (Hwrite : wm_write sigma sigma' V V' (loc, f) value),
    pico_core_state_wf
      (mkPicoCoreState
        (update_field h loc f value)
        sigma').
Proof.
  intros h sigma sigma' V V' loc f value o Hstate Hobj Hwrite.
  destruct Hstate as [Hagree Hinitialized].
  split.
  - eapply heap_wm_type_agree_write_update_field; eauto.
  - eapply pico_core_histories_initialized_write; eauto.
Qed.

(** The strengthened state invariant is inductive for every core primitive
    step.  Only field writes and allocation change machine state; the two
    preceding lemmas discharge those cases. *)
Theorem pico_core_step_preserves_state_wf :
  forall `{Hmem : CacheMemoryModel} CT e state e' state'
    (Hstate : pico_core_state_wf state)
    (Hstep : pico_core_step CT e state e' state'),
    pico_core_state_wf state'.
Proof.
  intros Hmem CT e state e' state' Hstate Hstep.
  inversion Hstep; subst; try exact Hstate.
  - eapply pico_core_state_wf_write; eauto.
  - eapply pico_core_state_wf_alloc; eauto.
Qed.

Theorem pico_core_step_preserves_heap_types :
  forall `{Hmem : CacheMemoryModel} CT e state e' state'
    (Hstep : pico_core_step CT e state e' state'),
    pico_core_heap_types_extend
      (pcs_heap state) (pcs_heap state').
Proof.
  intros Hmem CT e state e' state' Hstep.
  inversion Hstep; subst; simpl;
    try apply pico_core_heap_types_extend_refl.
  - eapply pico_core_heap_types_extend_write; eauto.
  - apply pico_core_heap_types_extend_alloc.
Qed.

Theorem pico_core_steps_preserve_state_wf :
  forall `{Hmem : CacheMemoryModel} CT e state e' state'
    (Hsteps : pico_core_steps CT e state e' state')
    (Hstate : pico_core_state_wf state),
    pico_core_state_wf state'.
Proof.
  intros Hmem CT e state e' state' Hsteps.
  induction Hsteps as
    [e0 state0 | e1 state1 e2 state2 e3 state3 Hstep Hsteps IH];
    intros Hstate.
  - exact Hstate.
  - apply IH.
    eapply pico_core_step_preserves_state_wf; eauto.
Qed.

Theorem pico_core_steps_preserve_heap_types :
  forall `{Hmem : CacheMemoryModel} CT e state e' state'
    (Hsteps : pico_core_steps CT e state e' state'),
    pico_core_heap_types_extend
      (pcs_heap state) (pcs_heap state').
Proof.
  intros Hmem CT e state e' state' Hsteps.
  induction Hsteps.
  - apply pico_core_heap_types_extend_refl.
  - eapply pico_core_heap_types_extend_trans.
    + eapply pico_core_step_preserves_heap_types; eauto.
    + exact IHHsteps.
Qed.

(** Read progress for the field-assignment core operation.  This is the first
    operation-level bridge from the strengthened state invariant to an actual
    primitive step; no preselected [wm_read] witness is required. *)
Lemma pico_core_assign_field_step_exists
    `{Hmem : CacheMemoryModel}
    `{Hprogress : CacheMemoryModelProgress} :
  forall CT rGamma x y f old loc o current V K h sigma
    (Hx : runtime_getVal rGamma x = Some old)
    (Hy : runtime_getVal rGamma y = Some (Iot loc))
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma))
    (Hobj : runtime_getObj h loc = Some o)
    (Hfield : nth_error (fields_map o) f = Some current),
    exists v V',
      pico_core_step CT
        (CoreRun rGamma (SVarAss x (EField y f)) V K)
        (mkPicoCoreState h sigma)
        (CoreRun
          (set_vars rGamma (update x v (vars rGamma)))
          SSkip V' K)
        (mkPicoCoreState h sigma).
Proof.
  intros CT rGamma x y f old loc o current V K h sigma
    Hx Hy Hstate Hobj Hfield.
  destruct
    (pico_core_state_wf_read_exists
      h sigma V loc o f current Hstate Hobj Hfield)
    as (v & V' & Hread).
  exists v, V'.
  eapply PCS_AssignField; eauto.
Qed.

Lemma pico_core_assign_field_reducible
    `{Hmem : CacheMemoryModel}
    `{Hprogress : CacheMemoryModelProgress} :
  forall CT rGamma x y f old loc o current V K h sigma
    (Hx : runtime_getVal rGamma x = Some old)
    (Hy : runtime_getVal rGamma y = Some (Iot loc))
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma))
    (Hobj : runtime_getObj h loc = Some o)
    (Hfield : nth_error (fields_map o) f = Some current),
    @reducible
      (pico_core_language CT)
      (CoreRun rGamma (SVarAss x (EField y f)) V K)
      (mkPicoCoreState h sigma).
Proof.
  intros CT rGamma x y f old loc o current V K h sigma
    Hx Hy Hstate Hobj Hfield.
  destruct
    (pico_core_assign_field_step_exists
      CT rGamma x y f old loc o current V K h sigma
      Hx Hy Hstate Hobj Hfield)
    as (v & V' & Hstep).
  eapply pico_core_reducible_from_step.
  exact Hstep.
Qed.

(** Typing-facing field-read progress.  The strengthened environment derives
    the target-variable witness and the null-or-location receiver cases; heap
    well-formedness locates the physical field; the initialized-history
    invariant then supplies the weak read. *)
Lemma pico_core_typed_assign_field_reducible
    `{Hmem : CacheMemoryModel}
    `{Hprogress : CacheMemoryModelProgress} :
  forall CT sGamma rGamma h sigma x y f Tx Ty C fdef V K
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma))
    (Hget_x : static_getType sGamma x = Some Tx)
    (Hget_y : static_getType sGamma y = Some Ty)
    (Href : sbase Ty = TRef C)
    (Hfield : sf_def_rel CT C f fdef),
    @reducible
      (pico_core_language CT)
      (CoreRun rGamma (SVarAss x (EField y f)) V K)
      (mkPicoCoreState h sigma).
Proof.
  intros CT sGamma rGamma h sigma x y f Tx Ty C fdef V K
    Henv Hstate Hget_x Hget_y Href Hfield.
  destruct
    (pico_core_typed_env_lookup
      CT sGamma rGamma h x Tx Henv Hget_x)
    as (qcontext_x & old & Hx & Htyped_x).
  destruct
    (pico_core_typed_env_field_receiver_cases
      CT sGamma rGamma h y Ty C f fdef Henv Hget_y Href Hfield)
    as [Hy | (qcontext_y & loc & Hy & Htyped_y)].
  - eapply pico_core_reducible_from_step.
    eapply PCS_AssignFieldNPE; eauto.
  - destruct
      (pico_core_typed_receiver_field_exists
        CT sGamma rGamma h loc qcontext_y Ty C f fdef
        Henv Htyped_y Href Hfield)
      as (o & current & Hobj & Hcurrent).
    eapply pico_core_assign_field_reducible; eauto.
Qed.

Theorem pico_core_typed_varass_field_reducible
    `{Hmem : CacheMemoryModel}
    `{Hprogress : CacheMemoryModelProgress} :
  forall CT sGamma sGamma' rGamma h sigma mt x y f V K
    (Htyping :
      stmt_typing CT sGamma mt (SVarAss x (EField y f)) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstate : pico_core_state_wf (mkPicoCoreState h sigma)),
    @reducible
      (pico_core_language CT)
      (CoreRun rGamma (SVarAss x (EField y f)) V K)
      (mkPicoCoreState h sigma).
Proof.
  intros CT sGamma sGamma' rGamma h sigma mt x y f V K
    Htyping Henv Hstate.
  inversion Htyping; subst.
  inversion Htype_e; subst.
  - eapply pico_core_typed_assign_field_reducible; eauto.
  - eapply pico_core_typed_assign_field_reducible; eauto.
Qed.

(** Runtime cases for a statically known field write.  The location case uses
    the receiver's runtime subtype to transport the static field declaration
    to the concrete class. *)
Lemma pico_core_typed_fldwrite_runtime_cases_from_static :
  forall CT sGamma rGamma h x f y Tx C a
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hget_x : static_getType sGamma x = Some Tx)
    (Hget_y : exists Ty, static_getType sGamma y = Some Ty)
    (Href : sbase Tx = TRef C)
    (Hassign_static : sf_assignability_rel CT C f a),
    runtime_getVal rGamma x = Some Null_a \/
    exists loc o val_y,
      runtime_getVal rGamma x = Some (Iot loc) /\
      runtime_getObj h loc = Some o /\
      sf_assignability_rel CT (rctype (rt_type o)) f a /\
      runtime_getVal rGamma y = Some val_y /\
      (runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable \/
       runtime_vpa_assignability (rqtype (rt_type o)) a = Final).
Proof.
  intros CT sGamma rGamma h x f y Tx C a
    Henv Hget_x (Ty & Hget_y) Href Hassign_static.
  destruct
    (pico_core_typed_env_lookup
      CT sGamma rGamma h x Tx Henv Hget_x)
    as (qcontext_x & value_x & Hruntime_x & Htyped_x).
  destruct value_x as [|loc|n].
  - left.
    exact Hruntime_x.
  - right.
    unfold pico_core_typed_value in Htyped_x.
    unfold wf_r_typable, r_type in Htyped_x.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj.
    + destruct Htyped_x as [Hbase _Hqualifier].
      destruct
        (pico_core_typed_env_lookup
          CT sGamma rGamma h y Ty Henv Hget_y)
        as (qcontext_y & val_y & Hruntime_y & Htyped_y).
      exists loc, o, val_y.
      repeat split; try assumption.
      * destruct Hassign_static as
          (fdef & Hfield_static & Hassignability).
        exists fdef.
        split.
        -- destruct (base_subtype_from_ref CT (rctype (rt_type o)) (sbase Tx) Hbase)
             as [D0 [HbaseTx Hclass_sub]].
           rewrite HbaseTx in Href.
           inversion Href; subst D0.
           eapply field_inheritance_subtyping; eauto.
        -- exact Hassignability.
      * destruct (rqtype (rt_type o)), a; simpl; auto.
    + contradiction.
  - exfalso.
    unfold pico_core_typed_value in Htyped_x.
    rewrite Href in Htyped_x.
    discriminate.
Qed.

Lemma stmt_typing_fldwrite_static_components :
  forall CT sGamma sGamma' mt x f y
    (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'),
    exists Tx Ty C a,
      static_getType sGamma x = Some Tx /\
      static_getType sGamma y = Some Ty /\
      sbase Tx = TRef C /\
      sf_assignability_rel CT C f a.
Proof.
  intros CT sGamma sGamma' mt x f y Htyping.
  inversion Htyping; subst;
    eexists _, _, _, _;
    repeat split; eauto.
Qed.

Theorem pico_core_typed_fldwrite_runtime_cases :
  forall CT sGamma sGamma' rGamma h mt x f y
    (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    runtime_getVal rGamma x = Some Null_a \/
    exists loc o a val_y,
      runtime_getVal rGamma x = Some (Iot loc) /\
      runtime_getObj h loc = Some o /\
      sf_assignability_rel CT (rctype (rt_type o)) f a /\
      runtime_getVal rGamma y = Some val_y /\
      (runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable \/
       runtime_vpa_assignability (rqtype (rt_type o)) a = Final).
Proof.
  intros CT sGamma sGamma' rGamma h mt x f y Htyping Henv.
	  destruct
	    (stmt_typing_fldwrite_static_components
	      CT sGamma sGamma' mt x f y Htyping)
	    as (Tx & Ty & C & a & Hget_x & Hget_y & Href & Hassign_static).
	  destruct
	    (pico_core_typed_fldwrite_runtime_cases_from_static
	      CT sGamma rGamma h x f y Tx C a Henv Hget_x
	      (ex_intro _ Ty Hget_y) Href Hassign_static)
    as [Hnull |
      (loc & o & val_y & Hloc & Hobj & Hassign & Hy & Hcase)].
  - left.
    exact Hnull.
  - right.
    exists loc, o, a, val_y.
    auto.
Qed.

Theorem pico_core_typed_fldwrite_reducible :
  forall `{Hmem : CacheMemoryModel}
    CT sGamma sGamma' rGamma h sigma mt x f y V K
    (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    @reducible
      (pico_core_language CT)
      (CoreRun rGamma (SFldWrite x f y) V K)
      (mkPicoCoreState h sigma).
Proof.
  intros Hmem CT sGamma sGamma' rGamma h sigma mt x f y V K
    Htyping Henv.
  destruct
    (pico_core_typed_fldwrite_runtime_cases
      CT sGamma sGamma' rGamma h mt x f y Htyping Henv)
    as [Hnull |
      (loc & o & a & val_y & Hloc & Hobj & Hassign & Hy & Hcase)].
  - eapply pico_core_reducible_from_step.
    eapply PCS_FldWriteNPE.
    exact Hnull.
  - destruct Hcase as [Hassignable | Hfinal].
    + let weak' :=
        constr:(append_write_msg sigma (loc, f)
          (mkWriteMsg val_y (length (history_of sigma (loc, f))) V)) in
      eapply pico_core_reducible_from_step;
      eapply PCS_FldWrite with
        (o := o) (a := a) (h' := update_field h loc f val_y)
        (sigma' := weak') (V' := V);
      eauto;
      split; reflexivity.
    + eapply pico_core_reducible_from_step.
      eapply PCS_FldWriteMutation; eauto.
Qed.

Lemma pico_core_typed_env_lookup_list_exists :
  forall CT sGamma rGamma h args argtypes
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstatic : static_getType_list sGamma args = Some argtypes),
    exists vals, runtime_lookup_list rGamma args = Some vals.
Proof.
  intros CT sGamma rGamma h args.
  induction args as [|arg args IH]; intros argtypes Henv Hstatic.
  - exists (@nil value).
    reflexivity.
  - unfold static_getType_list in Hstatic.
    simpl in Hstatic.
    destruct (static_getType sGamma arg) as [T |] eqn:Harg;
      try discriminate.
    destruct (mapM (static_getType sGamma) args) as [Ts |] eqn:Hargs;
      try discriminate.
    inversion Hstatic; subst argtypes.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h arg T Henv Harg)
      as (qcontext & value & Hruntime & Htyped).
    destruct (IH Ts Henv) as (values & Hruntime_args).
    {
      unfold static_getType_list.
      exact Hargs.
    }
    exists (value :: values).
    unfold runtime_lookup_list.
    simpl.
    rewrite Hruntime.
    unfold runtime_lookup_list in Hruntime_args.
    rewrite Hruntime_args.
    reflexivity.
Qed.

Lemma pico_core_typed_env_receiver_runtime :
  forall CT sGamma rGamma h
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    exists receiver qcontext,
      runtime_getVal rGamma 0 = Some (Iot receiver) /\
      r_muttype h receiver = Some qcontext.
Proof.
  intros CT sGamma rGamma h Henv.
  destruct
    (pico_core_typed_env_receiver CT sGamma rGamma h Henv)
    as (qcontext & receiver & Hthis & Hmut).
  exists receiver, qcontext.
  split; [| exact Hmut].
  unfold get_this_var_mapping in Hthis.
  unfold runtime_getVal.
  destruct (vars rGamma) as [|value values] eqn:Hvars;
    try discriminate.
  destruct value as [|loc|n]; try discriminate.
  inversion Hthis; subst loc.
  reflexivity.
Qed.

Lemma stmt_typing_new_static_args :
  forall CT sGamma sGamma' mt x qc C args
    (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma'),
    exists argtypes,
      static_getType_list sGamma args = Some argtypes.
Proof.
  intros CT sGamma sGamma' mt x qc C args Htyping.
  inversion Htyping; subst.
  eexists.
  eauto.
Qed.

Theorem pico_core_typed_new_reducible :
  forall `{Hmem : CacheMemoryModel}
    CT sGamma sGamma' rGamma h sigma mt x qc C args V K
    (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    @reducible
      (pico_core_language CT)
      (CoreRun rGamma (SNew x qc C args) V K)
      (mkPicoCoreState h sigma).
Proof.
  intros Hmem CT sGamma sGamma' rGamma h sigma mt x qc C args V K
    Htyping Henv.
  destruct
    (stmt_typing_new_static_args
      CT sGamma sGamma' mt x qc C args Htyping)
    as (argtypes & Hget_args).
  destruct
    (pico_core_typed_env_receiver_runtime
      CT sGamma rGamma h Henv)
    as (receiver & qcontext & Hreceiver & Hqcontext).
  destruct
    (pico_core_typed_env_lookup_list_exists
      CT sGamma rGamma h args argtypes Henv Hget_args)
    as (vals & Hargs).
  eapply pico_core_reducible_from_step.
  eapply PCS_New with
    (loc_this := receiver)
    (qthisr := qcontext)
    (qadapted := vpa_mutability_object_creation qcontext qc)
    (vals := vals)
    (o := mkObj
      (mkruntime_type
        (vpa_mutability_object_creation qcontext qc) C)
      vals)
    (h' := h ++
      [mkObj
        (mkruntime_type
          (vpa_mutability_object_creation qcontext qc) C)
        vals])
    (sigma' := pico_core_alloc_weak sigma
      (mkObj
        (mkruntime_type
          (vpa_mutability_object_creation qcontext qc) C)
        vals) V);
    eauto.
Qed.

Lemma stmt_typing_call_static_components :
  forall CT sGamma sGamma' mt x y m args
    (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma'),
    exists Ty C argtypes mdef,
      static_getType sGamma y = Some Ty /\
      sbase Ty = TRef C /\
      static_getType_list sGamma args = Some argtypes /\
      FindMethodWithName CT C m mdef.
Proof.
  intros CT sGamma sGamma' mt x y m args Htyping.
  inversion Htyping; subst;
    eexists _, _, _, _;
    repeat split; eauto.
Qed.

Lemma pico_core_typed_call_runtime_cases :
  forall CT sGamma sGamma' rGamma h mt x y m args
    (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    runtime_getVal rGamma y = Some Null_a \/
    exists loc C mdef vals,
      runtime_getVal rGamma y = Some (Iot loc) /\
      r_basetype h loc = Some C /\
      FindMethodWithName CT C m mdef /\
      runtime_lookup_list rGamma args = Some vals.
Proof.
  intros CT sGamma sGamma' rGamma h mt x y m args Htyping Henv.
	  destruct
	    (stmt_typing_call_static_components
	      CT sGamma sGamma' mt x y m args Htyping)
	    as (Ty & Cstatic & argtypes & mdef_static
	        & Hget_y & Href & Hget_args & Hfind_static).
  destruct
    (pico_core_typed_env_lookup
      CT sGamma rGamma h y Ty Henv Hget_y)
    as (qcontext & receiver & Hruntime_y & Htyped_y).
  destruct receiver as [|loc|n].
  - left.
    exact Hruntime_y.
  - right.
    unfold pico_core_typed_value in Htyped_y.
    unfold wf_r_typable, r_type in Htyped_y.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj.
    + destruct Htyped_y as [Hbase _Hqualifier].
      pose proof
        (pico_core_typed_env_wf_config
          CT sGamma rGamma h Henv) as Hconfig.
      unfold wf_r_config in Hconfig.
      destruct Hconfig as (Hwf_CT & _).
	      destruct
	        (base_subtype_from_ref CT (rctype (rt_type o)) (sbase Ty) Hbase)
	        as [D0 [HbaseTy Hclass_sub]].
	      rewrite HbaseTy in Href.
	      inversion Href; subst D0.
	      destruct
	        (method_inheritance_exists
	          CT (rctype (rt_type o)) Cstatic m mdef_static
	          Hwf_CT Hclass_sub Hfind_static)
	        as (mdef & Hfind_runtime).
      destruct
        (pico_core_typed_env_lookup_list_exists
          CT sGamma rGamma h args argtypes Henv Hget_args)
        as (vals & Hargs).
      exists loc, (rctype (rt_type o)), mdef, vals.
      repeat split; try assumption.
      unfold r_basetype.
      rewrite Hobj.
      reflexivity.
    + contradiction.
	  - exfalso.
	    unfold pico_core_typed_value in Htyped_y.
	    rewrite Href in Htyped_y.
	    discriminate.
Qed.

Theorem pico_core_typed_call_reducible :
  forall `{Hmem : CacheMemoryModel}
    CT sGamma sGamma' rGamma h sigma mt x y m args V K
    (Htyping : stmt_typing CT sGamma mt (SCall x y m args) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    @reducible
      (pico_core_language CT)
      (CoreRun rGamma (SCall x y m args) V K)
      (mkPicoCoreState h sigma).
Proof.
  intros Hmem CT sGamma sGamma' rGamma h sigma mt x y m args V K
    Htyping Henv.
  destruct
    (pico_core_typed_call_runtime_cases
      CT sGamma sGamma' rGamma h mt x y m args Htyping Henv)
    as [Hnull |
      (loc & C & mdef & vals & Hreceiver & Hbase & Hfind & Hargs)].
  - eapply pico_core_reducible_from_step.
    eapply PCS_CallNPE.
    exact Hnull.
  - eapply pico_core_reducible_from_step.
    eapply PCS_Call with
      (loc_y := loc) (C := C) (mdef := mdef)
      (body := mbody mdef)
      (mstmt := mbody_stmt (mbody mdef))
      (ret := mreturn (mbody mdef))
      (vals := vals);
      eauto.
Qed.

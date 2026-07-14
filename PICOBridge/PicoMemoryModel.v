Require Import Syntax Helpers Typing Bigstep DerivedCache.

From Stdlib Require Import List PeanoNat.
Import ListNotations.

(** * Field-Addressed Weak-Memory Shell for PICO

    The existing PICO heap maps object locations to whole objects with current
    field values.  Weak-memory reasoning needs a second view: each object field
    has its own write history, and a read selects a value from that field's
    history subject to a memory-model-specific visibility rule.

    This file is intentionally only the common interface.  It does not replace
    [eval_stmt], and it does not claim a Java memory model.  Its key memory-side
    condition is whole-value reads: a cache read observes one complete message
    in the same field history. Initial/default values are represented by the
    initial history messages established by allocation and by
    [pico_core_histories_initialized]; an empty history is not readable. *)

(** Field histories are indexed by object location and field name. *)
Definition FieldAddr : Type := (Loc * var)%type.
Definition view : Type := nat.

(** Role information separates stable abstract fields from mutable derived
    cache fields. *)
Inductive field_role : Type :=
  | AbstractField
  | CacheField : nat -> field_role
  | OrdinaryRepField.

Definition abstract_field (CT : class_table) (C : class_name) (f : var) : Prop :=
  (sf_mutability_rel CT C f RDM_f \/ sf_mutability_rel CT C f Imm_f) /\
  (sf_assignability_rel CT C f RDA \/ sf_assignability_rel CT C f Final).

Definition derived_cache_field
    (CT : class_table) (C : class_name) (f : var) : Prop :=
  cache_field CT C f.

(** PICO cache fields cannot simultaneously be abstract final/readonly fields.
    This justifies separating provider state from derived cache state. *)
Lemma derived_cache_field_not_abstract :
  forall CT C f
    (Hcache : derived_cache_field CT C f)
    (Habs : abstract_field CT C f),
    False.
Proof.
  intros CT C f Hcache [_ Habs_assign].
  unfold derived_cache_field, cache_field in Hcache.
  destruct Habs_assign as [Hrda | Hfinal].
  - unfold sf_assignability_rel in *.
    destruct Hcache as [fc [Hlookup_cache Hassign_cache]].
    destruct Hrda as [fa [Hlookup_abs Hassign_abs]].
    pose proof (field_lookup_deterministic_rel
      CT C f fc fa Hlookup_cache Hlookup_abs) as Heq.
    subst fa.
    rewrite Hassign_cache in Hassign_abs.
    discriminate.
  - eapply cache_field_not_final; eauto.
Qed.

(** ** Write Histories and Whole-Value Messages *)

(** A write message records one complete field value plus abstract metadata
    used by the memory model.  The theory never decomposes a value into
    machine-word fragments. *)
Record write_msg := mkWriteMsg {
  msg_val : value;
  msg_time : nat;
  msg_view : view;
}.

Definition history := list write_msg.

(** Weak-memory states keep object type information and one history per field
    address. *)
Record wm_state := mkWMState {
  wm_objs : list runtime_type;
  wm_mem : FieldAddr -> history;
}.

Definition wm_get_type (sigma : wm_state) (loc : Loc) : option runtime_type :=
  nth_error (wm_objs sigma) loc.

Definition history_of (sigma : wm_state) (addr : FieldAddr) : history :=
  wm_mem sigma addr.

Definition values_written_to (sigma : wm_state) (addr : FieldAddr) : list value :=
  map msg_val (history_of sigma addr).

Definition field_addr_eqb (a b : FieldAddr) : bool :=
  Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b).

Definition update_history
    (mem : FieldAddr -> history) (addr : FieldAddr) (hist : history) :
    FieldAddr -> history :=
  fun addr' => if field_addr_eqb addr' addr then hist else mem addr'.

Definition append_write_msg
    (sigma : wm_state) (addr : FieldAddr) (msg : write_msg) : wm_state :=
  mkWMState
    (wm_objs sigma)
    (update_history
      (wm_mem sigma)
      addr
      (history_of sigma addr ++ [msg])).

Lemma wm_get_type_append_write_msg :
  forall sigma addr msg loc,
    wm_get_type (append_write_msg sigma addr msg) loc =
    wm_get_type sigma loc.
Proof.
  intros sigma addr msg loc.
  unfold wm_get_type, append_write_msg.
  reflexivity.
Qed.

Lemma history_of_append_write_same :
  forall sigma addr msg,
    history_of (append_write_msg sigma addr msg) addr =
    history_of sigma addr ++ [msg].
Proof.
  intros sigma addr msg.
  unfold history_of, append_write_msg, update_history.
  simpl.
  unfold field_addr_eqb.
  rewrite !Nat.eqb_refl.
  reflexivity.
Qed.

Lemma history_of_append_write_other :
  forall sigma addr addr' msg
    (Hneq : addr' <> addr),
    history_of (append_write_msg sigma addr msg) addr' =
    history_of sigma addr'.
Proof.
  intros sigma [loc f] [loc' f'] msg Hneq.
  unfold history_of, append_write_msg, update_history.
  simpl.
  unfold field_addr_eqb.
  destruct (Nat.eqb loc' loc) eqn:Hloc; simpl.
  - destruct (Nat.eqb f' f) eqn:Hfield; simpl.
    + apply Nat.eqb_eq in Hloc.
      apply Nat.eqb_eq in Hfield.
      subst.
      contradiction Hneq; reflexivity.
    + rewrite Hloc.
      simpl.
      reflexivity.
  - rewrite Hloc.
    reflexivity.
Qed.

Definition history_values_ok (P : value -> Prop) (hist : history) : Prop :=
  Forall (fun msg => P (msg_val msg)) hist.

Lemma history_values_ok_in :
  forall P hist msg
    (Hok : history_values_ok P hist)
    (Hin : In msg hist),
    P (msg_val msg).
Proof.
  intros P hist msg Hok Hin.
  unfold history_values_ok in Hok.
  apply (proj1 (Forall_forall (fun msg0 => P (msg_val msg0)) hist) Hok).
  exact Hin.
Qed.

Lemma history_values_ok_app :
  forall P hist msg
    (Hok : history_values_ok P hist)
    (Hmsg : P (msg_val msg)),
    history_values_ok P (hist ++ [msg]).
Proof.
  intros P hist msg Hok Hmsg.
  unfold history_values_ok in *.
  apply Forall_app.
  split.
  - exact Hok.
  - constructor; [exact Hmsg | constructor].
Qed.

Definition derived_cache_msg_ok
    (derived : list value -> nat) (abs_vals : list value) (v : value) : Prop :=
  derived_int_cache_value derived abs_vals v.

Definition derived_cache_history_ok
    (derived : list value -> nat) (abs_vals : list value)
    (hist : history) : Prop :=
  history_values_ok (derived_cache_msg_ok derived abs_vals) hist.

Lemma derived_cache_history_read_valid :
  forall derived abs_vals hist msg
    (Hok : derived_cache_history_ok derived abs_vals hist)
    (Hin : In msg hist),
    derived_cache_msg_ok derived abs_vals (msg_val msg).
Proof.
  intros derived abs_vals hist msg Hok Hin.
  eapply history_values_ok_in; eauto.
Qed.

Lemma derived_cache_history_append_known :
  forall derived abs_vals hist n t V
    (Hok : derived_cache_history_ok derived abs_vals hist)
    (Hderived : n = derived abs_vals)
    (Hnz : n <> 0),
    derived_cache_history_ok
      derived abs_vals
      (hist ++ [mkWriteMsg (Int n) t V]).
Proof.
  intros derived abs_vals hist n t V Hok Hderived Hnz.
  eapply history_values_ok_app; eauto.
  unfold derived_cache_msg_ok.
  apply derived_int_cache_value_known_intro; assumption.
Qed.

(** ** Memory-Model Interface *)

(** [CacheMemoryModel] supplies the abstract read relation. The crucial
    side condition is [wm_read_from_history]: every read returns the value of
    one complete message in the same field history. Initial values must already
    be represented as history messages by the language state invariant. Java plain non-volatile
    [long]/[double] cache fields do not satisfy this by default because reads
    may tear; Java [int], [boolean], and reference cache values do, modulo
    separate safe-publication obligations for object-valued caches. *)
Class CacheMemoryModel := {
  wm_read : wm_state -> view -> FieldAddr -> value -> view -> Prop;

  wm_read_from_history :
    forall sigma V addr v V',
      wm_read sigma V addr v V' ->
      exists msg,
        In msg (history_of sigma addr) /\
        msg_val msg = v
}.

(** Canonical whole-value history semantics.  A read may select any complete
    message already present in the addressed field history and does not change
    the thread view.  More restrictive memory models may refine this relation. *)
Definition history_read
    (sigma : wm_state) (V : view) (addr : FieldAddr)
    (v : value) (V' : view) : Prop :=
  V' = V /\ exists msg,
    In msg (history_of sigma addr) /\ msg_val msg = v.

#[global] Instance history_cache_memory_model : CacheMemoryModel :=
  {| wm_read := history_read;
     wm_read_from_history :=
       fun sigma V addr v V' Hread =>
         match Hread with
         | conj _ (ex_intro _ msg (conj Hin Hval)) =>
             ex_intro _ msg (conj Hin Hval)
         end |}.

(** Reads from a valid derived-cache history produce values accepted by the
    derived-cache protocol. *)
Lemma cache_history_read_valid :
  forall `{CacheMemoryModel} sigma V addr v V' derived abs_vals
    (Hok : derived_cache_history_ok derived abs_vals (history_of sigma addr))
    (Hread : wm_read sigma V addr v V'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem sigma V addr v V' derived abs_vals Hok Hread.
  destruct (wm_read_from_history sigma V addr v V' Hread) as
    [msg [Hin Hval]].
  subst v.
  eapply derived_cache_history_read_valid; eauto.
Qed.

(** Writes append one complete value to one field history and leave object type
    information unchanged. *)
Definition wm_write
    (sigma sigma' : wm_state) (V V' : view)
    (addr : FieldAddr) (v : value) : Prop :=
  sigma' =
    append_write_msg sigma addr
      (mkWriteMsg v (length (history_of sigma addr)) V) /\
  V' = V.

Lemma wm_write_history_same :
  forall sigma sigma' V V' addr v
    (Hwrite : wm_write sigma sigma' V V' addr v),
    history_of sigma' addr =
    history_of sigma addr ++
      [mkWriteMsg v (length (history_of sigma addr)) V].
Proof.
  intros sigma sigma' V V' addr v [Hsigma _].
  subst sigma'.
  apply history_of_append_write_same.
Qed.

Lemma wm_write_get_type :
  forall sigma sigma' V V' addr v loc
    (Hwrite : wm_write sigma sigma' V V' addr v),
    wm_get_type sigma' loc = wm_get_type sigma loc.
Proof.
  intros sigma sigma' V V' addr v loc [Hsigma _].
  subst sigma'.
  apply wm_get_type_append_write_msg.
Qed.

Lemma wm_write_history_other :
  forall sigma sigma' V V' addr addr' v
    (Hneq : addr' <> addr)
    (Hwrite : wm_write sigma sigma' V V' addr v),
    history_of sigma' addr' = history_of sigma addr'.
Proof.
  intros sigma sigma' V V' addr addr' v Hneq [Hsigma _].
  subst sigma'.
  eapply history_of_append_write_other; eauto.
Qed.

Lemma wm_write_known_preserves_cache_history :
  forall sigma sigma' V V' addr derived abs_vals n
    (Hok : derived_cache_history_ok derived abs_vals (history_of sigma addr))
    (Hderived : n = derived abs_vals)
    (Hnz : n <> 0)
    (Hwrite : wm_write sigma sigma' V V' addr (Int n)),
    derived_cache_history_ok derived abs_vals (history_of sigma' addr).
Proof.
  intros sigma sigma' V V' addr derived abs_vals n Hok Hderived Hnz Hwrite.
  rewrite (wm_write_history_same sigma sigma' V V' addr (Int n) Hwrite).
  eapply derived_cache_history_append_known; eauto.
Qed.

Definition wm_cache_history_state
    (sigma : wm_state) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  derived_cache_history_ok derived abs_vals (history_of sigma addr).

(** Concrete read-validity theorem for a cache history in a weak-memory state. *)
Lemma wm_cache_history_state_read_valid :
  forall `{CacheMemoryModel} sigma V addr v V' derived abs_vals
    (Hstate : wm_cache_history_state sigma addr derived abs_vals)
    (Hread : wm_read sigma V addr v V'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem sigma V addr v V' derived abs_vals Hstate Hread.
  unfold wm_cache_history_state in Hstate.
  eapply cache_history_read_valid; eauto.
Qed.

Lemma wm_cache_history_state_read_unknown_or_derived :
  forall `{CacheMemoryModel} sigma V addr v V' derived abs_vals
    (Hstate : wm_cache_history_state sigma addr derived abs_vals)
    (Hread : wm_read sigma V addr v V'),
    cache_value_unknown v \/ cache_value_known derived abs_vals v.
Proof.
  intros Hmem sigma V addr v V' derived abs_vals Hstate Hread.
  unfold derived_cache_msg_ok.
  eapply wm_cache_history_state_read_valid; eauto.
Qed.

(** A cache-safe transition either leaves the target cache history unchanged or
    writes the nonzero derived value to the target cache field. *)
Definition wm_cache_safe_transition
    (sigma sigma' : wm_state) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  history_of sigma' addr = history_of sigma addr \/
  exists n V V',
    n = derived abs_vals /\
    n <> 0 /\
    wm_write sigma sigma' V V' addr (Int n).

Lemma wm_cache_safe_transition_preserves_cache_history :
  forall sigma sigma' addr derived abs_vals
    (Hstate : wm_cache_history_state sigma addr derived abs_vals)
    (Hsafe : wm_cache_safe_transition sigma sigma' addr derived abs_vals),
    wm_cache_history_state sigma' addr derived abs_vals.
Proof.
  intros sigma sigma' addr derived abs_vals Hstate Hsafe.
  destruct Hsafe as [Heq | Hwrite].
  - unfold wm_cache_history_state in *.
    rewrite Heq.
    exact Hstate.
  - destruct Hwrite as [n [V [V' [Hderived [Hnz Hwrite]]]]].
    unfold wm_cache_history_state in *.
    eapply wm_write_known_preserves_cache_history; eauto.
Qed.

Lemma wm_write_other_cache_safe_transition :
  forall sigma sigma' V V' write_addr addr val_y derived abs_vals
    (Hneq : write_addr <> addr)
    (Hwrite : wm_write sigma sigma' V V' write_addr val_y),
    wm_cache_safe_transition sigma sigma' addr derived abs_vals.
Proof.
  intros sigma sigma' V V' write_addr addr val_y derived abs_vals Hneq Hwrite.
  left.
  eapply wm_write_history_other; eauto.
Qed.

Lemma wm_write_target_known_cache_safe_transition :
  forall sigma sigma' V V' addr derived abs_vals n
    (Hderived : n = derived abs_vals)
    (Hnz : n <> 0)
    (Hwrite : wm_write sigma sigma' V V' addr (Int n)),
    wm_cache_safe_transition sigma sigma' addr derived abs_vals.
Proof.
  intros sigma sigma' V V' addr derived abs_vals n Hderived Hnz Hwrite.
  right.
  exists n, V, V'.
  split; [exact Hderived |].
  split; [exact Hnz |].
  exact Hwrite.
Qed.

Definition wm_write_allowed_for_cache
    (write_addr addr : FieldAddr) (val_y : value)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  write_addr <> addr \/
  exists n,
    write_addr = addr /\
    val_y = Int n /\
    n = derived abs_vals /\
    n <> 0.

Lemma wm_write_allowed_cache_safe_transition :
  forall sigma sigma' V V' write_addr addr val_y derived abs_vals
    (Hwrite : wm_write sigma sigma' V V' write_addr val_y)
    (Hallowed :
      wm_write_allowed_for_cache write_addr addr val_y derived abs_vals),
    wm_cache_safe_transition sigma sigma' addr derived abs_vals.
Proof.
  intros sigma sigma' V V' write_addr addr val_y derived abs_vals
         Hwrite Hallowed.
  destruct Hallowed as [Hother | Htarget].
  - eapply wm_write_other_cache_safe_transition; eauto.
  - destruct Htarget as [n [Haddr [Hval [Hderived Hnz]]]].
    subst write_addr val_y.
    eapply wm_write_target_known_cache_safe_transition; eauto.
Qed.

Lemma wm_write_allowed_preserves_cache_history :
  forall sigma sigma' V V' write_addr addr val_y derived abs_vals
    (Hstate : wm_cache_history_state sigma addr derived abs_vals)
    (Hwrite : wm_write sigma sigma' V V' write_addr val_y)
    (Hallowed :
      wm_write_allowed_for_cache write_addr addr val_y derived abs_vals),
    wm_cache_history_state sigma' addr derived abs_vals.
Proof.
  intros sigma sigma' V V' write_addr addr val_y derived abs_vals
         Hstate Hwrite Hallowed.
  eapply wm_cache_safe_transition_preserves_cache_history; eauto.
  eapply wm_write_allowed_cache_safe_transition; eauto.
Qed.

Lemma wm_write_allowed_read_valid :
  forall `{CacheMemoryModel}
         sigma sigma' Vw Vw' Vr addr write_addr val_y v Vr'
         derived abs_vals
         (Hstate : wm_cache_history_state sigma addr derived abs_vals)
         (Hwrite : wm_write sigma sigma' Vw Vw' write_addr val_y)
         (Hallowed :
           wm_write_allowed_for_cache write_addr addr val_y derived abs_vals)
         (Hread : wm_read sigma' Vr addr v Vr'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem sigma sigma' Vw Vw' Vr addr write_addr val_y v Vr'
         derived abs_vals Hstate Hwrite Hallowed Hread.
  assert (Hstate' :
    wm_cache_history_state sigma' addr derived abs_vals).
  {
    eapply wm_write_allowed_preserves_cache_history; eauto.
  }
  eapply wm_cache_history_state_read_valid; eauto.
Qed.

Definition wm_transition_writes_allowed_for_cache
    (sigma sigma' : wm_state) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  forall V V' write_addr val_y
    (Hwrite : wm_write sigma sigma' V V' write_addr val_y),
    wm_write_allowed_for_cache write_addr addr val_y derived abs_vals.

(** Syntactic write safety for statements: every field write either avoids the
    target cache field or writes the known nonzero derived value to it. *)
Fixpoint wm_stmt_writes_allowed_for_cache
    (rΓ : r_env) (s : stmt) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  match s with
  | SSkip => True
  | SLocal _ _ => True
  | SVarAss _ _ => True
  | SFldWrite x f y =>
      forall loc_x val_y
        (Hx : runtime_getVal rΓ x = Some (Iot loc_x))
        (Hy : runtime_getVal rΓ y = Some val_y),
        wm_write_allowed_for_cache (loc_x, f) addr val_y derived abs_vals
  | SNew _ _ _ _ => True
  | SCall _ _ _ _ => True
  | SIfZero _ s_zero s_nonzero =>
      wm_stmt_writes_allowed_for_cache rΓ s_zero addr derived abs_vals /\
      wm_stmt_writes_allowed_for_cache rΓ s_nonzero addr derived abs_vals
  | SSeq s1 s2 =>
      wm_stmt_writes_allowed_for_cache rΓ s1 addr derived abs_vals /\
      wm_stmt_writes_allowed_for_cache rΓ s2 addr derived abs_vals
  end.

(** Inductive proof form for [wm_stmt_writes_allowed_for_cache].  This is the
    bridge target used by typing-shaped cache-update rules. *)
Inductive cache_safe_stmt
    (rΓ : r_env) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) :
    stmt -> Prop :=
  | CSS_Skip :
      cache_safe_stmt rΓ addr derived abs_vals SSkip
  | CSS_Local : forall T x,
      cache_safe_stmt rΓ addr derived abs_vals (SLocal T x)
  | CSS_VarAss : forall x e,
      cache_safe_stmt rΓ addr derived abs_vals (SVarAss x e)
  | CSS_FldWrite : forall x f y,
      (forall loc_x val_y
        (Hx : runtime_getVal rΓ x = Some (Iot loc_x))
        (Hy : runtime_getVal rΓ y = Some val_y),
        wm_write_allowed_for_cache (loc_x, f) addr val_y derived abs_vals) ->
      cache_safe_stmt rΓ addr derived abs_vals (SFldWrite x f y)
  | CSS_New : forall x qc C args,
      cache_safe_stmt rΓ addr derived abs_vals (SNew x qc C args)
  | CSS_Call : forall x y m args,
      cache_safe_stmt rΓ addr derived abs_vals (SCall x y m args)
  | CSS_Seq : forall s1 s2,
      cache_safe_stmt rΓ addr derived abs_vals s1 ->
      cache_safe_stmt rΓ addr derived abs_vals s2 ->
      cache_safe_stmt rΓ addr derived abs_vals (SSeq s1 s2).

(** The inductive proof form implies the executable write-safety predicate. *)
Theorem cache_safe_stmt_implies_wm_stmt_writes_allowed :
  forall rΓ s addr derived abs_vals
    (Hsafe : cache_safe_stmt rΓ addr derived abs_vals s),
    wm_stmt_writes_allowed_for_cache rΓ s addr derived abs_vals.
Proof.
  intros rΓ s addr derived abs_vals Hsafe.
  induction Hsafe; simpl; auto.
Qed.

Lemma runtime_getVal_set_vars_update_same :
  forall rΓ x v
    (Hdom : x < dom (vars rΓ)),
    runtime_getVal (set_vars rΓ (update x v (vars rΓ))) x = Some v.
Proof.
  intros rΓ x v Hdom.
  unfold runtime_getVal, set_vars.
  simpl.
  apply update_same.
  exact Hdom.
Qed.

Lemma runtime_getVal_set_vars_update_diff :
  forall rΓ x y v
    (Hneq : x <> y),
    runtime_getVal (set_vars rΓ (update x v (vars rΓ))) y =
    runtime_getVal rΓ y.
Proof.
  intros rΓ x y v Hneq.
  unfold runtime_getVal, set_vars.
  simpl.
  apply update_diff.
  exact Hneq.
Qed.

Lemma cache_safe_fldwrite_other :
  forall rΓ addr derived abs_vals x f y
    (Hother : forall loc_x,
      runtime_getVal rΓ x = Some (Iot loc_x) ->
      (loc_x, f) <> addr),
    cache_safe_stmt rΓ addr derived abs_vals (SFldWrite x f y).
Proof.
  intros rΓ addr derived abs_vals x f y Hother.
  apply CSS_FldWrite.
  intros loc_x val_y Hx _.
  left.
  eapply Hother; eauto.
Qed.

Lemma cache_safe_fldwrite_target_known :
  forall rΓ loc cache_f derived abs_vals x y n
    (Hx : runtime_getVal rΓ x = Some (Iot loc))
    (Hy : runtime_getVal rΓ y = Some (Int n))
    (Hderived : n = derived abs_vals)
    (Hnz : n <> 0),
    cache_safe_stmt
      rΓ (loc, cache_f) derived abs_vals (SFldWrite x cache_f y).
Proof.
  intros rΓ loc cache_f derived abs_vals x y n Hx Hy Hderived Hnz.
  apply CSS_FldWrite.
  intros loc_x val_y Hx' Hy'.
  right.
  exists n.
  assert (loc_x = loc) by congruence.
  assert (val_y = Int n) by congruence.
  subst loc_x val_y.
  repeat split; assumption.
Qed.

Lemma cache_safe_fldwrite_target_after_assign_int :
  forall rΓ loc cache_f derived abs_vals receiver tmp n
    (Hneq : receiver <> tmp)
    (Hreceiver : runtime_getVal rΓ receiver = Some (Iot loc))
    (Htmp_dom : tmp < dom (vars rΓ))
    (Hderived : n = derived abs_vals)
    (Hnz : n <> 0),
    cache_safe_stmt
      (set_vars rΓ (update tmp (Int n) (vars rΓ)))
      (loc, cache_f)
      derived
      abs_vals
      (SFldWrite receiver cache_f tmp).
Proof.
  intros rΓ loc cache_f derived abs_vals receiver tmp n
         Hneq Hreceiver Htmp_dom Hderived Hnz.
  eapply cache_safe_fldwrite_target_known with (n := n).
  - rewrite runtime_getVal_set_vars_update_diff; eauto.
  - apply runtime_getVal_set_vars_update_same.
    exact Htmp_dom.
  - exact Hderived.
  - exact Hnz.
Qed.

Lemma cache_safe_seq :
  forall rΓ addr derived abs_vals s1 s2
    (Hsafe1 : cache_safe_stmt rΓ addr derived abs_vals s1)
    (Hsafe2 : cache_safe_stmt rΓ addr derived abs_vals s2),
    cache_safe_stmt rΓ addr derived abs_vals (SSeq s1 s2).
Proof.
  intros.
  apply CSS_Seq; assumption.
Qed.

(** A weak-memory thread is a PICO runtime environment, residual statement, and
    view. *)
Record wm_thread := mkWMThread {
  wt_env : r_env;
  wt_stmt : stmt;
  wt_view : view;
}.

Definition wm_thread_writes_allowed_for_cache
    (t : wm_thread) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  wm_stmt_writes_allowed_for_cache
    (wt_env t) (wt_stmt t) addr derived abs_vals.

Definition cache_safe_thread
    (t : wm_thread) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  cache_safe_stmt (wt_env t) addr derived abs_vals (wt_stmt t).

(** Lift statement-level cache safety to thread-level write safety. *)
Theorem cache_safe_thread_implies_wm_thread_writes_allowed :
  forall t addr derived abs_vals
    (Hsafe : cache_safe_thread t addr derived abs_vals),
    wm_thread_writes_allowed_for_cache t addr derived abs_vals.
Proof.
  intros t addr derived abs_vals Hsafe.
  unfold cache_safe_thread in Hsafe.
  unfold wm_thread_writes_allowed_for_cache.
  apply cache_safe_stmt_implies_wm_stmt_writes_allowed.
  exact Hsafe.
Qed.

Lemma cache_safe_thread_target_write_after_assign_int :
  forall rΓ loc cache_f derived abs_vals receiver tmp n V
    (Hneq : receiver <> tmp)
    (Hreceiver : runtime_getVal rΓ receiver = Some (Iot loc))
    (Htmp_dom : tmp < dom (vars rΓ))
    (Hderived : n = derived abs_vals)
    (Hnz : n <> 0),
    cache_safe_thread
      (mkWMThread
        (set_vars rΓ (update tmp (Int n) (vars rΓ)))
        (SFldWrite receiver cache_f tmp)
        V)
      (loc, cache_f)
      derived
      abs_vals.
Proof.
  intros.
  unfold cache_safe_thread.
  eapply cache_safe_fldwrite_target_after_assign_int; eauto.
Qed.

(** A weak-memory configuration contains one shared weak-memory state and a
    pool of residual PICO threads. *)
Record wm_config := mkWMConfig {
  wc_state : wm_state;
  wc_threads : list wm_thread;
}.

Definition wm_config_cache_history_state
    (cfg : wm_config) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  wm_cache_history_state (wc_state cfg) addr derived abs_vals.

Lemma wm_config_cache_history_state_read_valid :
  forall `{CacheMemoryModel} cfg V addr v V' derived abs_vals
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg) V addr v V'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem cfg V addr v V' derived abs_vals Hstate Hread.
  unfold wm_config_cache_history_state in Hstate.
  eapply wm_cache_history_state_read_valid; eauto.
Qed.

Lemma wm_config_cache_history_state_read_unknown_or_derived :
  forall `{CacheMemoryModel} cfg V addr v V' derived abs_vals
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg) V addr v V'),
    cache_value_unknown v \/ cache_value_known derived abs_vals v.
Proof.
  intros Hmem cfg V addr v V' derived abs_vals Hstate Hread.
  unfold derived_cache_msg_ok.
  eapply wm_config_cache_history_state_read_valid; eauto.
Qed.

Definition wm_config_threads_allowed_for_cache
    (cfg : wm_config) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  Forall
    (fun t => wm_thread_writes_allowed_for_cache t addr derived abs_vals)
    (wc_threads cfg).

Definition cache_safe_config
    (cfg : wm_config) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  Forall
    (fun t => cache_safe_thread t addr derived abs_vals)
    (wc_threads cfg).

(** Config-level cache safety implies every thread's writes are allowed for the
    target cache field. *)
Theorem cache_safe_config_implies_wm_config_threads_allowed :
  forall cfg addr derived abs_vals
    (Hsafe : cache_safe_config cfg addr derived abs_vals),
    wm_config_threads_allowed_for_cache cfg addr derived abs_vals.
Proof.
  intros cfg addr derived abs_vals Hsafe.
  unfold cache_safe_config in Hsafe.
  unfold wm_config_threads_allowed_for_cache.
  induction Hsafe as [|t ts Hthread Hthreads IH].
  - constructor.
  - constructor.
    + apply cache_safe_thread_implies_wm_thread_writes_allowed.
      exact Hthread.
    + exact IH.
Qed.

Definition cache_safe_method_body
    (rΓ : r_env) (body : method_body) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  cache_safe_stmt rΓ addr derived abs_vals (mbody_stmt body).

Definition cache_safe_method_thread
    (rΓ : r_env) (body : method_body) (V : view) (addr : FieldAddr)
    (derived : list value -> nat) (abs_vals : list value) : Prop :=
  cache_safe_thread (mkWMThread rΓ (mbody_stmt body) V) addr derived abs_vals.

Theorem cache_safe_method_body_thread :
  forall rΓ body V addr derived abs_vals
    (Hbody : cache_safe_method_body rΓ body addr derived abs_vals),
    cache_safe_method_thread rΓ body V addr derived abs_vals.
Proof.
  intros rΓ body V addr derived abs_vals Hbody.
  unfold cache_safe_method_body in *.
  unfold cache_safe_method_thread, cache_safe_thread.
  exact Hbody.
Qed.

Lemma Forall_nth_error :
  forall {A : Type} (P : A -> Prop) xs i x
    (Hall : Forall P xs)
    (Hnth : nth_error xs i = Some x),
    P x.
Proof.
  intros A P xs i x Hall Hnth.
  revert i x Hnth.
  induction Hall as [|y ys Hy Hys IH]; intros i x Hnth.
  - destruct i; discriminate.
  - destruct i as [|i'].
    + simpl in Hnth. inversion Hnth; subst. exact Hy.
    + simpl in Hnth. eapply IH; eauto.
Qed.

Lemma wm_config_threads_allowed_nth :
  forall cfg addr derived abs_vals i t
    (Hall : wm_config_threads_allowed_for_cache cfg addr derived abs_vals)
    (Hnth : nth_error (wc_threads cfg) i = Some t),
    wm_thread_writes_allowed_for_cache t addr derived abs_vals.
Proof.
  intros cfg addr derived abs_vals i t Hall Hnth.
  unfold wm_config_threads_allowed_for_cache in Hall.
  eapply (Forall_nth_error
    (fun t0 => wm_thread_writes_allowed_for_cache t0 addr derived abs_vals)
    (wc_threads cfg)); eauto.
Qed.

Definition residual_seq_wm (s1 s2 : stmt) : stmt :=
  match s1 with
  | SSkip => s2
  | _ => SSeq s1 s2
  end.

(** ** Weak-Memory Small-Step Execution *)

(** One thread step of the field-history machine.  Field reads go through the
    abstract [wm_read] relation; field writes append one complete value to one
    field history. *)
Inductive wm_thread_step
    `{CacheMemoryModel} (CT : class_table) :
    wm_state -> wm_thread -> wm_state -> wm_thread -> Prop :=
  | WMTS_AssignInt : forall sigma rΓ V x n old_v,
      runtime_getVal rΓ x = Some old_v ->
      wm_thread_step CT sigma
        (mkWMThread rΓ (SVarAss x (EInt n)) V)
        sigma
        (mkWMThread (set_vars rΓ (update x (Int n) (vars rΓ))) SSkip V)

  | WMTS_FieldRead : forall sigma rΓ V V' x y f loc_y v,
      runtime_getVal rΓ y = Some (Iot loc_y) ->
      wm_read sigma V (loc_y, f) v V' ->
      wm_thread_step CT sigma
        (mkWMThread rΓ (SVarAss x (EField y f)) V)
        sigma
        (mkWMThread (set_vars rΓ (update x v (vars rΓ))) SSkip V')

  | WMTS_FldWrite : forall sigma sigma' rΓ V V' x f y loc_x rt a val_y,
      runtime_getVal rΓ x = Some (Iot loc_x) ->
      wm_get_type sigma loc_x = Some rt ->
      sf_assignability_rel CT (rctype rt) f a ->
      runtime_getVal rΓ y = Some val_y ->
      runtime_vpa_assignability (rqtype rt) a = Assignable ->
      wm_write sigma sigma' V V' (loc_x, f) val_y ->
      wm_thread_step CT sigma
        (mkWMThread rΓ (SFldWrite x f y) V)
        sigma'
        (mkWMThread rΓ SSkip V')

  | WMTS_SeqSkip : forall sigma rΓ V s2,
      wm_thread_step CT sigma
        (mkWMThread rΓ (SSeq SSkip s2) V)
        sigma
        (mkWMThread rΓ s2 V)

  | WMTS_SeqStep : forall sigma sigma' rΓ rΓ' V V' s1 s1' s2,
      wm_thread_step CT sigma
        (mkWMThread rΓ s1 V)
        sigma'
        (mkWMThread rΓ' s1' V') ->
      wm_thread_step CT sigma
        (mkWMThread rΓ (SSeq s1 s2) V)
        sigma'
        (mkWMThread rΓ' (residual_seq_wm s1' s2) V').

(** One configuration step selects a thread and steps it against the shared
    weak-memory state. *)
Inductive wm_step
    `{CacheMemoryModel} (CT : class_table) :
    wm_config -> wm_config -> Prop :=
  | WMS_Thread : forall sigma sigma' threads threads' i t t',
      nth_error threads i = Some t ->
      wm_thread_step CT sigma t sigma' t' ->
      threads' = update i t' threads ->
      wm_step CT
        (mkWMConfig sigma threads)
        (mkWMConfig sigma' threads').

(** Reflexive-transitive closure of [wm_step]. *)
Inductive wm_steps
    `{CacheMemoryModel} (CT : class_table) :
    wm_config -> wm_config -> Prop :=
  | WMS_Refl : forall cfg,
      wm_steps CT cfg cfg
  | WMS_Step : forall cfg1 cfg2 cfg3,
      wm_step CT cfg1 cfg2 ->
      wm_steps CT cfg2 cfg3 ->
      wm_steps CT cfg1 cfg3.

(** [wm_steps_allowed_configs] records the side condition available before
    each step of an execution. *)
Definition wm_steps_allowed_configs
    `{CacheMemoryModel} (CT : class_table) (cfg cfg' : wm_config)
    (Allowed : wm_config -> Prop) : Prop :=
  forall c1 c2
    (Hpre : wm_steps CT cfg c1)
    (Hstep : wm_step CT c1 c2)
    (Hpost : wm_steps CT c2 cfg'),
    Allowed c1.

Definition wm_steps_config_allowed_for_cache
    `{CacheMemoryModel} (CT : class_table) (cfg cfg' : wm_config)
    (addr : FieldAddr) (derived : list value -> nat)
    (abs_vals : list value) : Prop :=
  wm_steps_allowed_configs
    CT cfg cfg'
    (fun c => wm_config_threads_allowed_for_cache c addr derived abs_vals).

Definition wm_steps_cache_safe_config
    `{CacheMemoryModel} (CT : class_table) (cfg cfg' : wm_config)
    (addr : FieldAddr) (derived : list value -> nat)
    (abs_vals : list value) : Prop :=
  wm_steps_allowed_configs
    CT cfg cfg'
    (fun c => cache_safe_config c addr derived abs_vals).

Lemma wm_steps_allowed_configs_from_global :
  forall `{CacheMemoryModel} CT cfg cfg' Allowed
    (Hglobal : forall c1 c2, wm_step CT c1 c2 -> Allowed c1),
    wm_steps_allowed_configs CT cfg cfg' Allowed.
Proof.
  intros Hmem CT cfg cfg' Allowed Hglobal c1 c2 _ Hstep _.
  eapply Hglobal; eauto.
Qed.

#[global] Hint Resolve wm_steps_allowed_configs_from_global : core.

Lemma wm_steps_cache_safe_config_implies_config_allowed :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsafe : wm_steps_cache_safe_config CT cfg cfg' addr derived abs_vals),
    wm_steps_config_allowed_for_cache CT cfg cfg' addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hsafe c1 c2 Hpre Hstep Hpost.
  apply cache_safe_config_implies_wm_config_threads_allowed.
  eapply Hsafe; eauto.
Qed.

(** One thread step is cache-safe when all writes in the state transition are
    allowed for the target cache field. *)
Theorem wm_thread_step_cache_safe_from_allowed_writes :
  forall `{CacheMemoryModel} CT sigma sigma' t t' addr derived abs_vals
    (Hstep : wm_thread_step CT sigma t sigma' t')
    (Hallowed :
      wm_transition_writes_allowed_for_cache sigma sigma' addr derived abs_vals),
    wm_cache_safe_transition sigma sigma' addr derived abs_vals.
Proof.
  intros Hmem CT sigma sigma' t t' addr derived abs_vals Hstep Hallowed.
  induction Hstep.
  - left. reflexivity.
  - left. reflexivity.
  - eapply wm_write_allowed_cache_safe_transition.
    + eauto.
    + unfold wm_transition_writes_allowed_for_cache in Hallowed.
      eapply Hallowed; eauto.
  - left. reflexivity.
  - apply IHHstep.
    exact Hallowed.
Qed.

Theorem wm_thread_step_cache_safe_from_thread :
  forall `{CacheMemoryModel} CT sigma sigma' t t' addr derived abs_vals
    (Hstep : wm_thread_step CT sigma t sigma' t')
    (Hallowed : wm_thread_writes_allowed_for_cache t addr derived abs_vals),
    wm_cache_safe_transition sigma sigma' addr derived abs_vals.
Proof.
  intros Hmem CT sigma sigma' t t' addr derived abs_vals Hstep.
  induction Hstep; intros Hallowed; simpl in Hallowed.
  - left. reflexivity.
  - left. reflexivity.
  - eapply wm_write_allowed_cache_safe_transition.
    + eauto.
    + eapply Hallowed; eauto.
  - left. reflexivity.
  - destruct Hallowed as [Hfirst _].
    apply IHHstep.
    exact Hfirst.
Qed.

Theorem wm_thread_step_cache_safe_from_stmt :
  forall `{CacheMemoryModel} CT sigma sigma' rΓ s V t'
         addr derived abs_vals
         (Hstep : wm_thread_step CT sigma (mkWMThread rΓ s V) sigma' t')
         (Hstmt_allowed :
           wm_stmt_writes_allowed_for_cache rΓ s addr derived abs_vals),
    wm_cache_safe_transition sigma sigma' addr derived abs_vals.
Proof.
  intros Hmem CT sigma sigma' rΓ s V t' addr derived abs_vals
         Hstep Hstmt_allowed.
  eapply wm_thread_step_cache_safe_from_thread; eauto.
Qed.

Theorem wm_step_cache_safe_from_thread_allowed :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hstep : wm_step CT cfg cfg')
    (Hall_threads : forall i t,
      nth_error (wc_threads cfg) i = Some t ->
      wm_thread_writes_allowed_for_cache t addr derived abs_vals),
    wm_cache_safe_transition
      (wc_state cfg) (wc_state cfg') addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hstep Hall_threads.
  inversion Hstep as
    [sigma sigma' threads threads' i t t' Hnth Hthread Hthreads]; subst.
  pose proof (Hall_threads i t Hnth) as Hallowed.
  eapply wm_thread_step_cache_safe_from_thread.
  - exact Hthread.
  - exact Hallowed.
Qed.

Theorem wm_step_cache_safe_from_config_allowed :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hstep : wm_step CT cfg cfg')
    (Hall : wm_config_threads_allowed_for_cache cfg addr derived abs_vals),
    wm_cache_safe_transition
      (wc_state cfg) (wc_state cfg') addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hstep Hall.
  eapply wm_step_cache_safe_from_thread_allowed; eauto.
  intros i t Hnth.
  eapply wm_config_threads_allowed_nth; eauto.
Qed.

Theorem wm_step_cache_safe_from_allowed_writes :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hstep : wm_step CT cfg cfg')
    (Hallowed :
      wm_transition_writes_allowed_for_cache
        (wc_state cfg) (wc_state cfg') addr derived abs_vals),
    wm_cache_safe_transition
      (wc_state cfg) (wc_state cfg') addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hstep Hallowed.
  inversion Hstep as
    [sigma sigma' threads threads' i t t' Hnth Hthread Hthreads]; subst.
  eapply wm_thread_step_cache_safe_from_allowed_writes; eauto.
Qed.

(** Cache-safe transitions preserve the concrete cache-history invariant. *)
Theorem wm_step_preserves_cache_history :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hstep : wm_step CT cfg cfg')
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hsafe :
      wm_cache_safe_transition
        (wc_state cfg) (wc_state cfg') addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals _ Hstate Hsafe.
  unfold wm_config_cache_history_state in *.
  eapply wm_cache_safe_transition_preserves_cache_history; eauto.
Qed.

(** Multi-step preservation of the cache-history invariant. *)
Theorem wm_steps_preserve_cache_history :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hsafe_all : forall c1 c2,
      wm_step CT c1 c2 ->
      wm_cache_safe_transition
        (wc_state c1) (wc_state c2) addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hsteps Hsafe_all Hstate.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH].
  - exact Hstate.
  - apply IH.
    eapply wm_step_preserves_cache_history; eauto.
Qed.

Theorem wm_steps_preserve_cache_history_from_allowed_writes :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hallowed_all : forall c1 c2,
      wm_step CT c1 c2 ->
      wm_transition_writes_allowed_for_cache
        (wc_state c1) (wc_state c2) addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hsteps Hallowed_all Hstate.
  eapply wm_steps_preserve_cache_history; eauto.
  intros c1 c2 Hstep.
  eapply wm_step_cache_safe_from_allowed_writes; eauto.
Qed.

(** Multi-step read-validity: after an execution whose writes are allowed, any
    read from the final target cache history observes an admissible cache
    value. *)
Theorem wm_steps_read_valid_from_allowed_writes :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hallowed_all : forall c1 c2,
      wm_step CT c1 c2 ->
      wm_transition_writes_allowed_for_cache
        (wc_state c1) (wc_state c2) addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hallowed_all Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_allowed_writes; eauto.
  }
  eapply wm_config_cache_history_state_read_valid; eauto.
Qed.

Theorem wm_steps_preserve_cache_history_from_thread_allowed :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_threads : forall c1 c2,
      wm_step CT c1 c2 ->
      forall i t,
        nth_error (wc_threads c1) i = Some t ->
        wm_thread_writes_allowed_for_cache t addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hsteps Hall_threads Hstate.
  eapply wm_steps_preserve_cache_history; eauto.
  intros c1 c2 Hstep.
  eapply wm_step_cache_safe_from_thread_allowed; eauto.
Qed.

Theorem wm_steps_read_valid_from_thread_allowed :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_threads : forall c1 c2,
      wm_step CT c1 c2 ->
      forall i t,
        nth_error (wc_threads c1) i = Some t ->
        wm_thread_writes_allowed_for_cache t addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hall_threads Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_thread_allowed; eauto.
  }
  eapply wm_config_cache_history_state_read_valid; eauto.
Qed.

Theorem wm_steps_preserve_cache_history_from_config_allowed :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_configs :
      wm_steps_config_allowed_for_cache CT cfg cfg' addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals Hsteps Hall_configs Hstate.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH].
  - exact Hstate.
  - apply IH.
    + intros c1 c2 Hpre Hstep' Hpost.
      eapply Hall_configs.
      * eapply WMS_Step.
        -- exact Hstep.
        -- exact Hpre.
      * exact Hstep'.
      * exact Hpost.
    + eapply wm_step_preserves_cache_history; eauto.
      eapply wm_step_cache_safe_from_config_allowed; eauto.
      eapply Hall_configs.
      * apply WMS_Refl.
      * exact Hstep.
      * exact Hsteps_tail.
Qed.

Theorem wm_steps_read_valid_from_config_allowed :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hall_configs :
      wm_steps_config_allowed_for_cache CT cfg cfg' addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hall_configs Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_config_allowed; eauto.
  }
  eapply wm_config_cache_history_state_read_valid; eauto.
Qed.

Theorem wm_steps_preserve_cache_history_from_closed_config_safe :
  forall `{CacheMemoryModel} CT cfg cfg' addr derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hsafe_cfg : cache_safe_config cfg addr derived abs_vals)
    (Hclosed : forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals ->
      cache_safe_config c2 addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.
Proof.
  intros Hmem CT cfg cfg' addr derived abs_vals
         Hsteps Hsafe_cfg Hclosed Hstate.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Hsteps_tail IH].
  - exact Hstate.
  - apply IH.
    + eapply Hclosed; eauto.
    + eapply wm_step_preserves_cache_history; eauto.
      eapply wm_step_cache_safe_from_config_allowed; eauto.
      apply cache_safe_config_implies_wm_config_threads_allowed.
      exact Hsafe_cfg.
Qed.

Theorem wm_steps_read_valid_from_closed_config_safe :
  forall `{CacheMemoryModel} CT cfg cfg' V addr v V' derived abs_vals
    (Hsteps : wm_steps CT cfg cfg')
    (Hsafe_cfg : cache_safe_config cfg addr derived abs_vals)
    (Hclosed : forall c1 c2,
      wm_step CT c1 c2 ->
      cache_safe_config c1 addr derived abs_vals ->
      cache_safe_config c2 addr derived abs_vals)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals)
    (Hread : wm_read (wc_state cfg') V addr v V'),
    derived_cache_msg_ok derived abs_vals v.
Proof.
  intros Hmem CT cfg cfg' V addr v V' derived abs_vals
         Hsteps Hsafe_cfg Hclosed Hstate Hread.
  assert (Hstate' :
    wm_config_cache_history_state cfg' addr derived abs_vals).
  {
    eapply wm_steps_preserve_cache_history_from_closed_config_safe; eauto.
  }
  eapply wm_config_cache_history_state_read_valid; eauto.
Qed.

(** ** Semantic Cache Safety *)

(** [wm_semantic_cache_safe_execution] is the pure semantic statement exported
    by this file: every reachable final configuration preserves the target
    cache-history invariant. *)
Definition wm_semantic_cache_safe_execution
    `{CacheMemoryModel} (CT : class_table) (cfg : wm_config)
    (addr : FieldAddr) (derived : list value -> nat)
    (abs_vals : list value) : Prop :=
  forall cfg'
    (Hsteps : wm_steps CT cfg cfg')
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.

(** Same semantic property, parameterized by an allowed-config predicate that
    must hold before each step. *)
Definition wm_semantic_cache_safe_under
    `{CacheMemoryModel} (CT : class_table) (cfg : wm_config)
    (addr : FieldAddr) (derived : list value -> nat)
    (abs_vals : list value)
    (Allowed : wm_config -> Prop) : Prop :=
  forall cfg'
    (Hsteps : wm_steps CT cfg cfg')
    (Hallowed : wm_steps_allowed_configs CT cfg cfg' Allowed)
    (Hstate : wm_config_cache_history_state cfg addr derived abs_vals),
    wm_config_cache_history_state cfg' addr derived abs_vals.

Definition wm_cache_safe_config_interpretation
    (addr : FieldAddr) (derived : list value -> nat)
    (abs_vals : list value) (cfg : wm_config) : Prop :=
  wm_config_threads_allowed_for_cache cfg addr derived abs_vals.

(** If the interpretation says every thread's writes are allowed, then the
    execution is semantically cache-safe. *)
Theorem wm_config_interpretation_semantic_cache_safe :
  forall `{CacheMemoryModel} CT cfg addr derived abs_vals,
    wm_semantic_cache_safe_under
      CT cfg addr derived abs_vals
      (wm_cache_safe_config_interpretation addr derived abs_vals).
Proof.
  intros Hmem CT cfg addr derived abs_vals cfg' Hsteps Hallowed Hstate.
  eapply wm_steps_preserve_cache_history_from_config_allowed; eauto.
Qed.

Theorem cache_safe_config_semantic_cache_safe :
  forall `{CacheMemoryModel} CT cfg addr derived abs_vals,
    wm_semantic_cache_safe_under
      CT cfg addr derived abs_vals
      (fun c => cache_safe_config c addr derived abs_vals).
Proof.
  intros Hmem CT cfg addr derived abs_vals cfg' Hsteps Hsafe Hstate.
  eapply wm_steps_preserve_cache_history_from_config_allowed; eauto.
  apply wm_steps_cache_safe_config_implies_config_allowed.
  exact Hsafe.
Qed.

From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep DerivedCache
  Core.GenericDerivedCache.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoSemanticConcurrency.

(** * PICO Stable Abstractions across CESK and Pool Executions

    The invariant records the receiver's runtime class together with the exact
    [pico_stable_abs] predicate consumed by the generic cache theory. *)

Definition pico_core_stable_abs
    (CT : class_table) (C : class_name) (abs_fields : list var)
    (loc : Loc) (state : pico_core_state) (abs_vals : list value) : Prop :=
  exists o,
    runtime_getObj (pcs_heap state) loc = Some o /\
    rctype (rt_type o) = C /\
    pico_stable_abs CT C abs_fields (pcs_heap state, loc) abs_vals.

Lemma update_field_preserves_other_field_read :
  forall h write_loc write_field new_value read_loc read_field old_value
    (Hother : write_loc <> read_loc \/ write_field <> read_field)
    (Hread : field_read h read_loc read_field old_value),
    field_read
      (update_field h write_loc write_field new_value)
      read_loc read_field old_value.
Proof.
  intros h write_loc write_field new_value read_loc read_field old_value
    Hother (read_obj & Hread_obj & Hread_field).
  unfold update_field.
  destruct (runtime_getObj h write_loc) as [write_obj |] eqn:Hwrite_obj.
  - destruct (Nat.eq_dec write_loc read_loc) as [Heq | Hneq].
    + subst read_loc.
      assert (Hobjects : read_obj = write_obj) by congruence.
      subst read_obj.
      destruct Hother as [Hfalse | Hfields]; [contradiction |].
      exists
        (set_fields_map write_obj
          (update write_field new_value (fields_map write_obj))).
      split.
      * unfold runtime_getObj.
        apply update_same.
        eapply runtime_getObj_dom; eauto.
      * simpl.
        rewrite field_update_preserves_other_fields; assumption.
    + exists read_obj.
      split.
      * unfold runtime_getObj.
        rewrite update_diff; assumption.
      * exact Hread_field.
  - exists read_obj. split; assumption.
Qed.

Lemma update_field_preserves_other_field_reads :
  forall h write_loc write_field new_value read_loc fields values
    (Hother : forall field,
      List.In field fields -> write_loc <> read_loc \/ write_field <> field)
    (Hreads : field_reads h read_loc fields values),
    field_reads
      (update_field h write_loc write_field new_value)
      read_loc fields values.
Proof.
  intros h write_loc write_field new_value read_loc fields.
  induction fields as [|field fields IH]; intros values Hother Hreads.
  - inversion Hreads. constructor.
  - inversion Hreads as [|? ? value values' Hread Htail]; subst.
    constructor.
    + eapply update_field_preserves_other_field_read.
      * apply Hother. left. reflexivity.
      * exact Hread.
    + eapply IH.
      * intros field' Hin. apply Hother. right. exact Hin.
      * exact Htail.
Qed.

Lemma append_object_preserves_field_reads :
  forall h new_object loc fields values
    (Hreads : field_reads h loc fields values),
    field_reads (h ++ [new_object]) loc fields values.
Proof.
  intros h new_object loc fields values Hreads.
  induction Hreads as [|field fields value values Hread Htail IH].
  - constructor.
  - constructor.
    + destruct Hread as (o & Hobj & Hfield).
      exists o. split; [|exact Hfield].
      unfold runtime_getObj in *.
      rewrite nth_error_app1; [exact Hobj |].
      eapply runtime_getObj_dom; eauto.
    + exact IH.
Qed.

Lemma runtime_getObj_update_field_same_general :
  forall h loc field value o
    (Hobj : runtime_getObj h loc = Some o),
    runtime_getObj (update_field h loc field value) loc =
      Some (set_fields_map o (update field value (fields_map o))).
Proof.
  intros h loc field value o Hobj.
  unfold update_field. rewrite Hobj.
  unfold runtime_getObj. apply update_same.
  eapply runtime_getObj_dom; eauto.
Qed.

Lemma runtime_getObj_update_field_other_general_local :
  forall h write_loc field value read_loc
    (Hneq : write_loc <> read_loc),
    runtime_getObj (update_field h write_loc field value) read_loc =
      runtime_getObj h read_loc.
Proof.
  intros h write_loc field value read_loc Hneq.
  unfold update_field.
  destruct (runtime_getObj h write_loc); [|reflexivity].
  unfold runtime_getObj. apply update_diff. exact Hneq.
Qed.

Lemma successful_write_avoids_final_fields :
  forall CT C abs_fields h receiver receiver_obj write_loc write_obj
    write_field assignability
    (Hreceiver : runtime_getObj h receiver = Some receiver_obj)
    (Hclass : rctype (rt_type receiver_obj) = C)
    (Hwrite_obj : runtime_getObj h write_loc = Some write_obj)
    (Hassign : sf_assignability_rel CT
      (rctype (rt_type write_obj)) write_field assignability)
    (Hruntime : runtime_vpa_assignability
      (rqtype (rt_type write_obj)) assignability = Assignable)
    (Hfinals : final_fields CT C abs_fields),
    forall field,
      List.In field abs_fields ->
      write_loc <> receiver \/ write_field <> field.
Proof.
  intros CT C abs_fields h receiver receiver_obj write_loc write_obj
    write_field assignability Hreceiver Hclass Hwrite_obj Hassign Hruntime
    Hfinals field Hin.
  destruct (Nat.eq_dec write_loc receiver) as [Hloc | Hloc].
  - right. intros Hfield. subst write_loc write_field.
    assert (Hobjects : write_obj = receiver_obj) by congruence.
    subst write_obj.
    rewrite Hclass in Hassign.
    pose proof
      (final_fields_field_final CT C abs_fields field Hfinals Hin) as Hfinal.
    unfold final_field in Hfinal.
    pose proof
      (sf_assignability_deterministic_rel CT C field assignability Final
        Hassign Hfinal) as ->.
    eapply runtime_vpa_assignability_final_not_assignable; eauto.
  - left. exact Hloc.
Qed.

Theorem pico_core_step_preserves_stable_abs :
  forall `{CacheMemoryModel} CT C abs_fields loc state state' control control'
    abs_vals
    (Hstable : pico_core_stable_abs
      CT C abs_fields loc state abs_vals)
    (Hstep : pico_core_step CT control state control' state'),
    pico_core_stable_abs CT C abs_fields loc state' abs_vals.
Proof.
  intros Hmem CT C abs_fields loc state state' control control' abs_vals
    (root & Hroot & Hclass & Hfinals & Hreads) Hstep.
  inversion Hstep; subst; simpl in *;
    try solve [exists root; repeat split; assumption].
  - assert (Havoid : forall field,
      List.In field abs_fields -> loc_x <> loc \/ f <> field).
    {
      eapply successful_write_avoids_final_fields; eauto.
    }
    destruct (Nat.eq_dec loc_x loc) as [Heq | Hneq].
    + subst loc_x.
      assert (Ho : o = root) by congruence.
      exists (set_fields_map root (update f val_y (fields_map root))).
      split.
      * exact
          (runtime_getObj_update_field_same_general h loc f val_y root Hroot).
      * split; [reflexivity |].
        split; [exact Hfinals |].
        eapply update_field_preserves_other_field_reads; eauto.
    + exists root. split.
      * rewrite
          (runtime_getObj_update_field_other_general_local
            h loc_x f val_y loc Hneq).
        exact Hroot.
      * split; [reflexivity |].
        split; [exact Hfinals |].
        eapply update_field_preserves_other_field_reads; eauto.
  - exists root. split.
    + unfold runtime_getObj in *.
      rewrite nth_error_app1; [exact Hroot |].
      eapply runtime_getObj_dom; eauto.
    + split; [reflexivity |].
      split; [exact Hfinals |].
      eapply append_object_preserves_field_reads; eauto.
Qed.

Theorem pico_core_steps_preserve_stable_abs :
  forall `{CacheMemoryModel} CT C abs_fields loc state state' control control'
    abs_vals
    (Hstable : pico_core_stable_abs
      CT C abs_fields loc state abs_vals)
    (Hsteps : pico_core_steps CT control state control' state'),
    pico_core_stable_abs CT C abs_fields loc state' abs_vals.
Proof.
  intros Hmem CT C abs_fields loc state state' control control' abs_vals
    Hstable Hsteps.
  induction Hsteps as
    [control0 state0
    | control0 state0 control1 state1 control2 state2 Hstep Htail IH].
  - exact Hstable.
  - apply IH.
    eapply pico_core_step_preserves_stable_abs; eauto.
Qed.

Theorem pico_pool_step_preserves_stable_abs :
  forall `{CacheMemoryModel} CT C abs_fields loc cfg cfg' abs_vals
    (Hstable : pico_core_stable_abs
      CT C abs_fields loc (pool_state cfg) abs_vals)
    (Hstep : pico_pool_step CT cfg cfg'),
    pico_core_stable_abs CT C abs_fields loc (pool_state cfg') abs_vals.
Proof.
  intros Hmem CT C abs_fields loc cfg cfg' abs_vals Hstable Hstep.
  inversion Hstep; subst; simpl in *.
  eapply pico_core_step_preserves_stable_abs; eauto.
Qed.

Theorem pico_pool_steps_preserve_stable_abs :
  forall `{CacheMemoryModel} CT C abs_fields loc cfg cfg' abs_vals
    (Hstable : pico_core_stable_abs
      CT C abs_fields loc (pool_state cfg) abs_vals)
    (Hsteps : pico_pool_steps CT cfg cfg'),
    pico_core_stable_abs CT C abs_fields loc (pool_state cfg') abs_vals.
Proof.
  intros Hmem CT C abs_fields loc cfg cfg' abs_vals Hstable Hsteps.
  induction Hsteps as [cfg0 | cfg1 cfg2 cfg3 Hstep Htail IH].
  - exact Hstable.
  - apply IH.
    eapply pico_pool_step_preserves_stable_abs; eauto.
Qed.

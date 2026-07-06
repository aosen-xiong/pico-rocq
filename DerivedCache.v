Require Import Syntax Helpers Typing Bigstep.

From Stdlib Require Import List Lia.
Import ListNotations.

(* A first, reduced cache layer for the PICO runtime model.

   This file intentionally uses only the reduced core:
   - object mutability at runtime is still PICO's [Imm_r | Mut_r];
   - abstract fields are [Final];
   - cache fields are [Assignable].

   It does not use RO, Lost, RDA, or viewpoint-adapted method scopes. Those
   remain part of the existing PICO development, but are not needed for the
   first derived-cache preservation lemmas.
*)

Definition final_field (CT : class_table) (C : class_name) (f : var) : Prop :=
  sf_assignability_rel CT C f Final.

Definition cache_field (CT : class_table) (C : class_name) (f : var) : Prop :=
  sf_assignability_rel CT C f Assignable.

Definition field_read (h : heap) (loc : Loc) (f : var) (v : value) : Prop :=
  exists o,
    runtime_getObj h loc = Some o /\
    getVal (fields_map o) f = Some v.

Definition final_fields (CT : class_table) (C : class_name) (fs : list var) : Prop :=
  Forall (final_field CT C) fs.

Definition field_reads (h : heap) (loc : Loc) (fs : list var) (vs : list value) : Prop :=
  Forall2 (field_read h loc) fs vs.

Lemma cache_field_not_final :
  forall CT C f,
    cache_field CT C f ->
    final_field CT C f ->
    False.
Proof.
  intros CT C f Hcache Hfinal.
  unfold cache_field, final_field in *.
  pose proof (sf_assignability_deterministic_rel CT C f Assignable Final
                Hcache Hfinal) as Heq.
  discriminate Heq.
Qed.

Lemma cache_field_neq_final_field :
  forall CT C f_cache f_abs,
    cache_field CT C f_cache ->
    final_field CT C f_abs ->
    f_cache <> f_abs.
Proof.
  intros CT C f_cache f_abs Hcache Hfinal Heq.
  subst f_abs.
  eapply cache_field_not_final; eauto.
Qed.

Lemma update_cache_field_preserves_final_field_read :
  forall CT h h' loc C f_cache f_abs new_v old_v o,
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    cache_field CT C f_cache ->
    final_field CT C f_abs ->
    getVal (fields_map o) f_abs = Some old_v ->
    h' = update_field h loc f_cache new_v ->
    field_read h' loc f_abs old_v.
Proof.
  intros CT h h' loc C f_cache f_abs new_v old_v o
         Hobj HC Hcache Hfinal Hread Hupdate.
  subst h'.
  unfold field_read.
  unfold update_field.
  rewrite Hobj.
  exists (set_fields_map o (update f_cache new_v (fields_map o))).
  split.
  - apply runtime_getObj_update_same.
    eapply runtime_getObj_dom; eauto.
  - simpl.
    rewrite (field_update_preserves_other_fields
               (fields_map o) f_cache new_v f_abs).
    + eapply cache_field_neq_final_field; eauto.
    + exact Hread.
Qed.

Lemma update_cache_field_preserves_runtime_type :
  forall h loc f_cache new_v o,
    runtime_getObj h loc = Some o ->
    runtime_getObj (update_field h loc f_cache new_v) loc =
      Some (set_fields_map o (update f_cache new_v (fields_map o))).
Proof.
  intros h loc f_cache new_v o Hobj.
  unfold update_field.
  rewrite Hobj.
  apply runtime_getObj_update_same.
  eapply runtime_getObj_dom; eauto.
Qed.

Lemma update_cache_field_preserves_final_field_reads :
  forall CT h h' loc C f_cache new_v fs vs o,
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    cache_field CT C f_cache ->
    final_fields CT C fs ->
    field_reads h loc fs vs ->
    h' = update_field h loc f_cache new_v ->
    field_reads h' loc fs vs.
Proof.
  intros CT h h' loc C f_cache new_v fs vs o
         Hobj HC Hcache Hfinals Hreads Hupdate.
  unfold final_fields in Hfinals.
  unfold field_reads in *.
  generalize dependent vs.
  induction Hfinals as [|f_abs fs Hfinal Hfinals_tail IH]; intros vs Hreads.
  - inversion Hreads; constructor.
  - inversion Hreads as [|? ? old_v vs_tail Hread Hreads_tail0]; subst.
    constructor.
    + destruct Hread as [o_read [Hobj_read Hfield_read]].
      assert (o_read = o) by congruence.
      subst o_read.
      eapply update_cache_field_preserves_final_field_read; eauto.
    + eapply IH; eauto.
Qed.

Definition cache_value_unknown (v : value) : Prop :=
  v = Int 0.

Definition cache_value_known (derived : list value -> nat) (abs_vals : list value)
  (v : value) : Prop :=
  exists n,
    v = Int n /\
    n = derived abs_vals /\
    n <> 0.

Definition derived_int_cache_value
  (derived : list value -> nat) (abs_vals : list value) (v : value) : Prop :=
  cache_value_unknown v \/ cache_value_known derived abs_vals v.

Definition derived_int_cache_protocol
  (CT : class_table) (h : heap) (loc : Loc) (C : class_name)
  (abs_fields : list var) (cache_f : var) (derived : list value -> nat) : Prop :=
  exists abs_vals cache_v,
    final_fields CT C abs_fields /\
    cache_field CT C cache_f /\
    field_reads h loc abs_fields abs_vals /\
    field_read h loc cache_f cache_v /\
    derived_int_cache_value derived abs_vals cache_v.

Lemma cache_value_known_intro :
  forall derived abs_vals n,
    n = derived abs_vals ->
    n <> 0 ->
    cache_value_known derived abs_vals (Int n).
Proof.
  intros derived abs_vals n Hderived Hnz.
  exists n.
  repeat split; auto.
Qed.

Lemma derived_int_cache_value_known_intro :
  forall derived abs_vals n,
    n = derived abs_vals ->
    n <> 0 ->
    derived_int_cache_value derived abs_vals (Int n).
Proof.
  intros derived abs_vals n Hderived Hnz.
  right.
  apply cache_value_known_intro; assumption.
Qed.

Lemma update_known_int_cache_preserves_protocol :
  forall CT h h' loc C abs_fields cache_f derived abs_vals old_cache_v n o,
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    field_read h loc cache_f old_cache_v ->
    n = derived abs_vals ->
    n <> 0 ->
    h' = update_field h loc cache_f (Int n) ->
    derived_int_cache_protocol CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT h h' loc C abs_fields cache_f derived abs_vals old_cache_v n o
         Hobj HC Hfinals Hcache Hreads Hcache_read Hderived Hnz Hupdate.
  exists abs_vals, (Int n).
  repeat split.
  - exact Hfinals.
  - exact Hcache.
  - eapply update_cache_field_preserves_final_field_reads; eauto.
  - subst h'.
    unfold field_read.
    exists (set_fields_map o (update cache_f (Int n) (fields_map o))).
    unfold update_field.
    rewrite Hobj.
    split.
    + apply runtime_getObj_update_same.
      eapply runtime_getObj_dom; eauto.
    + simpl.
      unfold getVal.
      apply update_same.
      destruct Hcache_read as [o_read [Hobj_read Hfield_read]].
      assert (o_read = o) by congruence.
      subst o_read.
      eapply getVal_dom; eauto.
  - apply derived_int_cache_value_known_intro; assumption.
Qed.

Lemma update_known_int_cache_preserves_existing_protocol :
  forall CT h h' loc C abs_fields cache_f derived abs_vals old_cache_v n o,
    derived_int_cache_protocol CT h loc C abs_fields cache_f derived ->
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    field_reads h loc abs_fields abs_vals ->
    field_read h loc cache_f old_cache_v ->
    n = derived abs_vals ->
    n <> 0 ->
    h' = update_field h loc cache_f (Int n) ->
    derived_int_cache_protocol CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT h h' loc C abs_fields cache_f derived abs_vals old_cache_v n o
         Hprotocol Hobj HC Hreads Hcache_read Hderived Hnz Hupdate.
  destruct Hprotocol as [abs_vals0 [cache_v
    [Hfinals [Hcache [_ [_ _]]]]]].
  eapply update_known_int_cache_preserves_protocol; eauto.
Qed.

Lemma eval_cache_field_write_establishes_protocol :
  forall CT rΓ h h' x y loc C abs_fields cache_f derived
         abs_vals old_cache_v n o,
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      CT rΓ h
      (SFldWrite x cache_f y)
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      rΓ h' ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    runtime_getVal rΓ y = Some (Int n) ->
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    field_read h loc cache_f old_cache_v ->
    n = derived abs_vals ->
    n <> 0 ->
    derived_int_cache_protocol CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT rΓ h h' x y loc C abs_fields cache_f derived
         abs_vals old_cache_v n o
         Heval Hx Hy Hobj HC Hfinals Hcache Hreads Hcache_read Hderived Hnz.
  pose (n_cache := n).
  assert (Hy_cache : runtime_getVal rΓ y = Some (Int n_cache))
    by (unfold n_cache; exact Hy).
  inversion Heval; subst; try discriminate.
  assert (loc_x = loc) by congruence.
  assert (val_y = Int n_cache) by congruence.
  subst loc_x val_y.
  eapply update_known_int_cache_preserves_protocol
    with (n := n_cache) (old_cache_v := old_cache_v); eauto.
Qed.

Lemma eval_cache_field_write_preserves_final_reads :
  forall CT rΓ h h' x y loc C abs_fields cache_f abs_vals o,
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      CT rΓ h
      (SFldWrite x cache_f y)
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      rΓ h' ->
    runtime_getVal rΓ x = Some (Iot loc) ->
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    field_reads h' loc abs_fields abs_vals.
Proof.
  intros CT rΓ h h' x y loc C abs_fields cache_f abs_vals o
         Heval Hx Hobj HC Hfinals Hcache Hreads.
  inversion Heval; subst; try discriminate.
  assert (loc_x = loc) by congruence.
  subst loc_x.
  eapply update_cache_field_preserves_final_field_reads; eauto.
Qed.

Lemma eval_int_compute_and_cache_write_sound :
  forall CT rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f derived
         abs_vals old_cache_v n o,
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      CT rΓ h
      (SVarAss tmp (EInt n))
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      rΓ_mid h ->
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ_mid)
      CT rΓ_mid h
      (SFldWrite receiver cache_f tmp)
      OK
      (reachable_locations_from_initial_env CT h rΓ_mid)
      rΓ_mid h' ->
    runtime_getVal rΓ_mid receiver = Some (Iot loc) ->
    runtime_getVal rΓ_mid tmp = Some (Int n) ->
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    field_read h loc cache_f old_cache_v ->
    n = derived abs_vals ->
    n <> 0 ->
    field_reads h' loc abs_fields abs_vals /\
    derived_int_cache_protocol CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f derived
         abs_vals old_cache_v n o
         _ Hwrite Hreceiver_mid Htmp_mid Hobj HC Hfinals Hcache Hreads
         Hcache_read Hderived Hnz.
  split.
  - eapply eval_cache_field_write_preserves_final_reads; eauto.
  - eapply eval_cache_field_write_establishes_protocol; eauto.
Qed.

Theorem derived_cache_update_immutability :
  forall CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
         abs_vals n o,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt (SVarAss tmp (EInt n)) sΓ ->
    stmt_typing CT sΓ mt (SFldWrite receiver cache_f tmp) sΓ ->
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      CT rΓ h
      (SVarAss tmp (EInt n))
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      rΓ_mid h ->
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ_mid)
      CT rΓ_mid h
      (SFldWrite receiver cache_f tmp)
      OK
      (reachable_locations_from_initial_env CT h rΓ_mid)
      rΓ_mid h' ->
    runtime_getVal rΓ_mid receiver = Some (Iot loc) ->
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    field_reads h' loc abs_fields abs_vals.
Proof.
  intros CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
         abs_vals n o
         _ _ _ _ Hwrite Hreceiver_mid Hobj HC Hfinals Hcache Hreads.
  eapply eval_cache_field_write_preserves_final_reads; eauto.
Qed.

Theorem derived_cache_update_sound :
  forall CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
         derived abs_vals old_cache_v n o,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt (SVarAss tmp (EInt n)) sΓ ->
    stmt_typing CT sΓ mt (SFldWrite receiver cache_f tmp) sΓ ->
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      CT rΓ h
      (SVarAss tmp (EInt n))
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      rΓ_mid h ->
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ_mid)
      CT rΓ_mid h
      (SFldWrite receiver cache_f tmp)
      OK
      (reachable_locations_from_initial_env CT h rΓ_mid)
      rΓ_mid h' ->
    runtime_getVal rΓ_mid receiver = Some (Iot loc) ->
    runtime_getVal rΓ_mid tmp = Some (Int n) ->
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    field_read h loc cache_f old_cache_v ->
    n = derived abs_vals ->
    n <> 0 ->
    field_reads h' loc abs_fields abs_vals /\
    derived_int_cache_protocol CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
         derived abs_vals old_cache_v n o
         _ _ _ Hcompute Hwrite Hreceiver_mid Htmp_mid Hobj HC Hfinals Hcache
         Hreads Hcache_read Hderived Hnz.
  eapply eval_int_compute_and_cache_write_sound; eauto.
Qed.

(* PICO's current big-step semantics is sequential. It has no thread pool,
   interleaving semantics, data-race relation, or memory model. The theorem
   below is therefore a sequential semantic soundness theorem for the concrete
   cache-update sequence shape.

   The explicit reachability-stability premise is needed because [SBS_Seq]
   threads the initial reachability set through the second statement, while
   primitive statement rules recompute reachability from their own input
   runtime environment. Assigning an integer temporary does not add reachable
   locations, so examples can discharge this premise directly. *)
Theorem derived_cache_update_sequence_sound :
  forall CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
         derived abs_vals old_cache_v n o,
    wf_r_config CT sΓ rΓ h ->
    stmt_typing CT sΓ mt (SVarAss tmp (EInt n)) sΓ ->
    stmt_typing CT sΓ mt (SFldWrite receiver cache_f tmp) sΓ ->
    rΓ_mid = set_vars rΓ (update tmp (Int n) (vars rΓ)) ->
    reachable_locations_from_initial_env CT h rΓ_mid =
      reachable_locations_from_initial_env CT h rΓ ->
    eval_stmt
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      CT rΓ h
      (SSeq (SVarAss tmp (EInt n)) (SFldWrite receiver cache_f tmp))
      OK
      (reachable_locations_from_initial_env CT h rΓ)
      rΓ_mid h' ->
    runtime_getVal rΓ_mid receiver = Some (Iot loc) ->
    runtime_getVal rΓ_mid tmp = Some (Int n) ->
    runtime_getObj h loc = Some o ->
    rctype (rt_type o) = C ->
    final_fields CT C abs_fields ->
    cache_field CT C cache_f ->
    field_reads h loc abs_fields abs_vals ->
    field_read h loc cache_f old_cache_v ->
    n = derived abs_vals ->
    n <> 0 ->
    field_reads h' loc abs_fields abs_vals /\
    derived_int_cache_protocol CT h' loc C abs_fields cache_f derived.
Proof.
  intros CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
         derived abs_vals old_cache_v n o
         Hwf Htype_compute Htype_write Hmid Hreach_stable Hseq
         Hreceiver_mid Htmp_mid Hobj HC Hfinals Hcache Hreads Hcache_read
         Hderived Hnz.
  subst rΓ_mid.
  inversion Hseq; subst; try discriminate.
  inversion Heval1; subst; try discriminate.
  inversion Heval; subst; try discriminate.
  rewrite <- Hreach_stable in Heval2.
  eapply derived_cache_update_sound
    with
      (sΓ := sΓ)
      (mt := mt)
      (old_cache_v := old_cache_v)
      (o := o); eauto.
Qed.

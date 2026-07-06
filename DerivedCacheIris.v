From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Require Import Syntax Helpers Typing Bigstep DerivedCache.

Section derived_cache_iris.
  Context {PROP : bi}.

  Definition derived_int_cache_protocolI
      (CT : class_table) (h : heap) (loc : Loc) (C : class_name)
      (abs_fields : list var) (cache_f : var)
      (derived : list value -> nat) : PROP :=
    ⌜derived_int_cache_protocol CT h loc C abs_fields cache_f derived⌝%I.

  Definition field_readsI
      (h : heap) (loc : Loc) (fields : list var) (vals : list value) : PROP :=
    ⌜field_reads h loc fields vals⌝%I.

  Lemma derived_int_cache_protocolI_intro :
    forall CT h loc C abs_fields cache_f derived,
      derived_int_cache_protocol CT h loc C abs_fields cache_f derived ->
      ⊢ derived_int_cache_protocolI CT h loc C abs_fields cache_f derived.
  Proof.
    intros CT h loc C abs_fields cache_f derived Hprotocol.
    iPureIntro.
    exact Hprotocol.
  Qed.

  Lemma field_readsI_intro :
    forall h loc fields vals,
      field_reads h loc fields vals ->
      ⊢ field_readsI h loc fields vals.
  Proof.
    intros h loc fields vals Hreads.
    iPureIntro.
    exact Hreads.
  Qed.

  Lemma eval_cache_field_write_establishes_protocolI :
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
      ⊢ derived_int_cache_protocolI CT h' loc C abs_fields cache_f derived.
  Proof.
    intros CT rΓ h h' x y loc C abs_fields cache_f derived
           abs_vals old_cache_v n o
           Heval Hx Hy Hobj HC Hfinals Hcache Hreads Hcache_read Hderived Hnz.
    iPureIntro.
    eapply eval_cache_field_write_establishes_protocol; eauto.
  Qed.

  Lemma eval_cache_field_write_preserves_final_readsI :
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
      ⊢ field_readsI h' loc abs_fields abs_vals.
  Proof.
    intros CT rΓ h h' x y loc C abs_fields cache_f abs_vals o
           Heval Hx Hobj HC Hfinals Hcache Hreads.
    iPureIntro.
    eapply eval_cache_field_write_preserves_final_reads; eauto.
  Qed.

  Lemma eval_int_compute_and_cache_write_soundI :
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
      ⊢ field_readsI h' loc abs_fields abs_vals ∧
        derived_int_cache_protocolI CT h' loc C abs_fields cache_f derived.
  Proof.
    intros CT rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f derived
           abs_vals old_cache_v n o
           Hcompute Hwrite Hreceiver_mid Htmp_mid Hobj HC Hfinals Hcache
           Hreads Hcache_read Hderived Hnz.
    iPureIntro.
    eapply eval_int_compute_and_cache_write_sound; eauto.
  Qed.

  Theorem derived_cache_update_immutabilityI :
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
      ⊢ field_readsI h' loc abs_fields abs_vals.
  Proof.
    intros CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
           abs_vals n o
           Hwf Htype_compute Htype_write Hcompute Hwrite Hreceiver_mid Hobj
           HC Hfinals Hcache Hreads.
    iPureIntro.
    eapply derived_cache_update_immutability; eauto.
  Qed.

  Theorem derived_cache_update_soundI :
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
      ⊢ field_readsI h' loc abs_fields abs_vals ∧
        derived_int_cache_protocolI CT h' loc C abs_fields cache_f derived.
  Proof.
    intros CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
           derived abs_vals old_cache_v n o
           Hwf Htype_compute Htype_write Hcompute Hwrite Hreceiver_mid Htmp_mid
           Hobj HC Hfinals Hcache Hreads Hcache_read Hderived Hnz.
    iPureIntro.
    eapply derived_cache_update_sound; eauto.
  Qed.

  Theorem derived_cache_update_sequence_soundI :
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
      ⊢ field_readsI h' loc abs_fields abs_vals ∧
        derived_int_cache_protocolI CT h' loc C abs_fields cache_f derived.
  Proof.
    intros CT sΓ mt rΓ rΓ_mid h h' receiver tmp loc C abs_fields cache_f
           derived abs_vals old_cache_v n o
           Hwf Htype_compute Htype_write Hmid Hreach_stable Hseq
           Hreceiver_mid Htmp_mid Hobj HC Hfinals Hcache Hreads Hcache_read
           Hderived Hnz.
    iPureIntro.
    eapply derived_cache_update_sequence_sound; eauto.
  Qed.
End derived_cache_iris.

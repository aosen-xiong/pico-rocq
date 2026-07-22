Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import Properties AbstractStatePreservation Reachability Preservation ReadonlyHelper ReadonlyNoMutation ReadonlyStatePreservation.
Require Import PotentialCapability ProtectedFieldPreservation.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

(** Transitive-state preservation is an instance of structural protected-field
    preservation in which every field is protected. *)
Lemma transitive_state_statement_preservation :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C anyrq vals vals' f
    (Hconfined : env_respects_protected_set
      (reachable_locations_from_initial_env h rΓ) sΓ rΓ)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ TransitiveState stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hlocalset : Ensembles.In Loc
      (reachable_locations_from_initial_env h rΓ) l)
    (Hobj : runtime_getObj h l =
      Some (mkObj (mkruntime_type anyrq C) vals))
    (Hobj' : runtime_getObj h' l =
      Some (mkObj (mkruntime_type anyrq C) vals')),
  nth_error vals f = nth_error vals' f.
Proof.
  intros.
  have Hinitial := initial_potential_live_history CT sΓ rΓ h
    Hwf Hconfined.
  eapply successful_stmt_preserves_protected_field with
    (authority := Imm_r) (stack := [])
    (Z := reachable_locations_from_initial_env h rΓ)
    (cutoff := dom h); eauto.
  - right. reflexivity.
  - right. right. right. reflexivity.
Qed.

Lemma transitive_state_preservation_with_end :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg vals_arg' f
    (Hstmt : stmt = (SCall x mindex y zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ TransitiveState stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Harg_obj' : runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg'))
    (Hall_readonly : signature_has_no_mutable_roots (msignature mdef)),
    nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
    loc_arg C anyrq vals_arg vals_arg' f Hstmt Hstatic_type Hmethod_lookup
    Hwf Htyping Heval Hget_y Hget_zs HinP Harg_obj Harg_obj' Hall_readonly.
  subst stmt.
  have Hcaller_scope : readonly_state_method_scope TransitiveState.
  { right. reflexivity. }
  destruct (successful_typed_safe_call_body CT sΓ TransitiveState rΓ h x
    mindex y zs sΓ' rΓ' h' Ty mdef vals ly Hstatic_type Hmethod_lookup
    Hwf Htyping Heval Hget_y Hget_zs Hall_readonly Hcaller_scope)
    as [runtime_mdef [body_sΓ' [body_rΓ'
      [Hsignature [Hbody_typed [Hframe_wf
        [Hbody_eval [Hbody_safe [Hbody_scope Hbody_subscope]]]]]]]]].
  inversion Hbody_subscope; subst.
  eapply transitive_state_statement_preservation with
    (sΓ := mreceiver (msignature runtime_mdef) ::
      mparams (msignature runtime_mdef))
    (rΓ := mkr_env (Iot ly :: vals))
    (stmt := mbody_stmt (mbody runtime_mdef))
    (sΓ' := body_sΓ') (rΓ' := body_rΓ').
  - eapply callee_frame_respects_protected_set; eauto.
  - exact Hframe_wf.
  - rewrite <- H1. exact Hbody_typed.
  - exact Hbody_eval.
  - have Hsubset := reachable_locations_subset_reachable_from_method_frame
      h ly vals.
    exact (Hsubset loc_arg HinP).
  - exact Harg_obj.
  - exact Harg_obj'.
Qed.

(** Public TS guarantee with final-object existence and runtime type derived
    from the successful call evaluation. *)
Theorem transitive_state_preservation :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
         loc_arg C anyrq vals_arg f
    (Hstmt : stmt = (SCall x mindex y zs))
    (Hstatic_type : static_getType sΓ y = Some Ty)
    (Hmethod_lookup : FindMethodWithName CT (sctype Ty) mindex mdef)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ TransitiveState stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hget_y : runtime_getVal rΓ y = Some (Iot ly))
    (Hget_zs : runtime_lookup_list rΓ zs = Some vals)
    (HinP: Ensembles.In Loc (reachable_locations_from_vals h (Iot ly :: vals)) loc_arg)
    (Harg_obj : runtime_getObj h loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg))
    (Hall_readonly : signature_has_no_mutable_roots (msignature mdef)),
    exists vals_arg',
      runtime_getObj h' loc_arg = Some (mkObj (mkruntime_type anyrq C) vals_arg') /\
      nth_error vals_arg f = nth_error vals_arg' f.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' x y mindex Ty mdef zs vals ly
    loc_arg C anyrq vals_arg f Hstmt Hstatic_type Hmethod_lookup Hwf Htyping
    Heval Hget_y Hget_zs HinP Harg_obj Hall_readonly.
  destruct (runtime_preserves_r_type_heap CT rΓ h loc_arg
    (mkruntime_type anyrq C) h' vals_arg stmt rΓ' Harg_obj Heval)
    as [vals_arg' Harg_obj'].
  exists vals_arg'. split; [exact Harg_obj'|].
  eapply transitive_state_preservation_with_end; eauto.
Qed.

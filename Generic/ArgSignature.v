From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases GhostOverride ArgClean ArgOverride GhostCall ArgCall GhostEntry ArgMain
  ArgEntry ArgRsf GhostSignature.

(** The final theorems.  They need no condition on the class table beyond
    its well-formedness: the method rule requires that the type parameters of
    a readonly-state or transitive-state method have bounds that reach no
    mutable position, and the same for the class's type parameters follows
    from the rule on the receiver type. *)

Corollary readonly_state_preservation_final_signature :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
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
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply readonly_state_preservation_final; auto.
  apply clean_bounds_of_signature; auto.
Qed.

Corollary transitive_state_preservation_final_signature :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
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
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply transitive_state_preservation_final; auto.
  apply clean_bounds_of_signature; auto.
Qed.

(** The same for a call that ends in any way. *)
Corollary readonly_state_preservation_final_signature_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
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
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply readonly_state_preservation_final_any; auto.
  apply clean_bounds_of_signature; auto.
Qed.

Corollary transitive_state_preservation_final_signature_any :
  forall CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
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
  intros CT Δ sΓ mt rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf.
  pose proof Hwf as (Hct & _).
  pose proof (clean_method_bounds_of_wf _ Hct) as Hcm.
  apply transitive_state_preservation_final_any; auto.
  apply clean_bounds_of_signature; auto.
Qed.

(* ------------------FROM A PROGRAM START------------------*)

(** A start state: a well-formed state with no type variable in scope whose
    objects are all of classes without type parameters.  The first state of
    a program, holding only the main object, is one. *)
Definition start_state (CT : class_table) (Δ : tv_env) (sΓ : s_env)
    (rΓ : r_env) (h : heap) : Prop :=
  wf_r_config CT Δ sΓ rΓ h /\
  class_bounds Δ = [] /\ method_bounds Δ = [] /\
  (forall l o def, runtime_getObj h l = Some o ->
     find_class CT (rctype (rt_type o)) = Some def ->
     ctparams (signature def) = []).

(** The whole statement, with no condition in the vocabulary of the proof:
    run any well-typed statement [s] from a start state, then a call that
    selects a readonly-state or transitive-state method.  However the call
    ends, the protected fields of every object that exists when the call
    starts are unchanged. *)
Theorem rs_ts_preservation_from_start :
  forall CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res,
    start_state CT Δ sΓ rΓ0 h0 ->
    stmt_typing CT Δ sΓ mt s sΓ1 ->
    eval_stmt CT rΓ0 h0 s OK rΓ h ->
    stmt_typing CT Δ sΓ1 mt (SCall x m y Us Qs zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
    runtime_getVal rΓ y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m D mdef ->
    forall l qr C Rs vals f,
      runtime_getObj h l = Some (mkObj (mkruntime_type qr C Rs) vals) ->
      (readonly_state_method_scope (mscope (msignature mdef)) /\
       (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)) \/
      mscope (msignature mdef) = TransitiveState ->
      exists vals',
        runtime_getObj h' l = Some (mkObj (mkruntime_type qr C Rs) vals') /\
        nth_error vals f = nth_error vals' f.
Proof.
  intros CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res
    (Hwf0 & Hc & Hm & Hobj) Hts Hes Htc Hec Hvy Hbase Hfind
    l qr C Rs vals f Hl Hcase.
  pose proof (preservation_pico _ _ _ _ _ _ _ Hes eq_refl _ _ _ _ Hwf0 Hts) as Hwf.
  pose proof (rsfp_preservation CT Δ sΓ mt s sΓ1 rΓ0 h0 rΓ h Hwf0 Hts Hes
                (RSFp_start_plain CT Δ rΓ0 h0 Hc Hm Hobj)) as HR.
  destruct Hcase as [[Hrs Hf] | Htsc].
  - exact (readonly_state_preservation_final_signature_any CT Δ sΓ1 mt rΓ h
             x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Hrs l qr C Rs vals f Hl Hf).
  - exact (transitive_state_preservation_final_signature_any CT Δ sΓ1 mt rΓ h
             x m y Us Qs zs sΓ' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Htsc l qr C Rs vals f Hl).
Qed.

Print Assumptions readonly_state_preservation_final_signature.
Print Assumptions transitive_state_preservation_final_signature.
Print Assumptions readonly_state_preservation_final_signature_any.
Print Assumptions transitive_state_preservation_final_signature_any.
Print Assumptions rs_ts_preservation_from_start.

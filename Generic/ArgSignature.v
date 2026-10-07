From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases GhostOverride ArgClean ArgOverride GhostCall ArgCall GhostEntry ArgMain
  ArgEntry ArgRsf GhostSignature.

(** The final theorems with the condition on the class table stated on
    method signatures only: the type parameters of a readonly-state or
    transitive-state method have bounds that reach no mutable position.  The
    same for the class's type parameters follows from the rule on the
    receiver type. *)

Corollary readonly_state_preservation_final_signature :
  forall CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef,
    clean_method_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us zs) OK rΓ' h' ->
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
  intros CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef Hcm Hwf.
  pose proof Hwf as (Hct & _).
  apply readonly_state_preservation_final; auto.
  apply clean_bounds_of_signature; auto.
Qed.

Corollary transitive_state_preservation_final_signature :
  forall CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef,
    clean_method_bounds_ct CT ->
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt (SCall x m y Us zs) sΓ' ->
    eval_stmt CT rΓ h (SCall x m y Us zs) OK rΓ' h' ->
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
  intros CT Δ sΓ mt rΓ h x m y Us zs sΓ' rΓ' h' ly cy D mdef Hcm Hwf.
  pose proof Hwf as (Hct & _).
  apply transitive_state_preservation_final; auto.
  apply clean_bounds_of_signature; auto.
Qed.

Print Assumptions readonly_state_preservation_final_signature.
Print Assumptions transitive_state_preservation_final_signature.

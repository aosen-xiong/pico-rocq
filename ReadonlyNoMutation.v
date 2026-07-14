Require Import Syntax Notations Helpers Typing Bigstep ViewpointAdaptation.
Require Import ReadonlyHelper PotentialCapability ProtectedFieldPreservation.
From Stdlib Require Import List.
Import ListNotations.

(** RS preserves every Final/RDA field of every object in the graph reachable
    from the initial call roots.  The structural history theorem supplies the
    call, nested-call, and sequence reasoning; only the paper-facing projection
    remains here. *)
Lemma deep_readonly_preservation :
  forall CT sΓ mt rΓ h stmt rΓ' h' sΓ' l C anyrq vals vals' f
    (Hconfined : env_respects_protected_set
      (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype : safe_readonly_method_type mt)
    (Heval : eval_stmt OK
      (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt
      OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hlocalset : Ensembles.In Loc
      (reachable_locations_from_initial_env CT h rΓ) l)
    (Hobj : runtime_getObj h l =
      Some (mkObj (mkruntime_type anyrq C) vals))
    (Hobj' : runtime_getObj h' l =
      Some (mkObj (mkruntime_type anyrq C) vals'))
    (Hassignability : sf_assignability_rel CT C f Final \/
      sf_assignability_rel CT C f RDA),
  nth_error vals f = nth_error vals' f.
Proof.
  intros.
  have Hinitial := initial_potential_live_history CT sΓ rΓ h
    Hwf Hconfined.
  eapply successful_stmt_preserves_protected_field with
    (authority := Imm_r) (stack := [])
    (Z := reachable_locations_from_initial_env CT h rΓ)
    (cutoff := dom h); eauto.
  destruct Hassignability as [Hfinal | Hrda].
  - left. exact Hfinal.
  - right. left. exact Hrda.
Qed.

Require Import Syntax Notations Helpers Typing Subtyping Bigstep.
Require Import ViewpointAdaptation Properties Preservation ReadonlyHelper.
Require Import Reachability MutableCapability AuthorityCapability.
Require Import ExecutionConfinement ProtectionHistory.
Require Import ComponentColoring ForwardCapabilityHistory AuthorityHistory.
From Stdlib Require Import List Sets.Ensembles.
Import ListNotations.

(** A proof-only snapshot of a suspended caller frame.  [frame_authority]
    records whether RDM denotes mutable authority in that frame; it is kept
    separate from the receiver object's runtime mutability. *)
Record watched_frame : Type := mk_watched_frame {
  frame_authority : q_r;
  frame_senv : s_env;
  frame_renv : r_env
}.

Definition rdm_roots_reflect_through_view
  (receiver_view : q)
  (callee_senv : s_env) (callee_renv : r_env)
  (caller_senv : s_env) (caller_renv : r_env) : Prop :=
  forall root,
    typed_root RDM callee_senv callee_renv root ->
    match receiver_view with
    | Mut => typed_root Mut caller_senv caller_renv root
    | Imm => typed_root Imm caller_senv caller_renv root
    | RDM => typed_root RDM caller_senv caller_renv root
    | RO => exists receiver,
        get_this_var_mapping (vars callee_renv) = Some receiver /\
        root = receiver /\
        typed_root RO caller_senv caller_renv root
    | Lost => False
    | Bot => False
    end.

(** Intraprocedural provenance is directional: a current RDM root either has
    an old RDM ancestor through RDM fields, or is a fresh allocation handled by
    the allocation case. *)
Definition rdm_roots_descend_from
  (CT : class_table) (h : heap)
  (old_senv : s_env) (old_renv : r_env)
  (new_senv : s_env) (new_renv : r_env) : Prop :=
  forall root,
    typed_root RDM new_senv new_renv root ->
    exists old_root,
      typed_root RDM old_senv old_renv old_root /\
      mutable_reachable CT h old_root root.

Record watched_boundary : Type := mk_watched_boundary {
  boundary_caller : watched_frame;
  boundary_callee_entry_senv : s_env;
  boundary_callee_entry_renv : r_env;
  boundary_receiver_view : q;
  boundary_rdm_origins :
    rdm_roots_reflect_through_view boundary_receiver_view
      boundary_callee_entry_senv boundary_callee_entry_renv
      boundary_caller.(frame_senv) boundary_caller.(frame_renv)
}.

(** This is the PICO call-boundary analogue of roDOT's call case for mutable
    reachability preservation: a capability-bearing callee formal is traced
    back to the caller actual selected by the receiver viewpoint.  The lemma
    deliberately exposes the stored directed fact instead of replacing it by
    an independent body-safety assumption. *)
Lemma boundary_entry_rdm_root_by_view :
  forall boundary root,
    typed_root RDM
      boundary.(boundary_callee_entry_senv)
      boundary.(boundary_callee_entry_renv) root ->
    match boundary.(boundary_receiver_view) with
    | Mut => typed_root Mut
        boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) root
    | Imm => typed_root Imm
        boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) root
    | RDM => typed_root RDM
        boundary.(boundary_caller).(frame_senv)
        boundary.(boundary_caller).(frame_renv) root
    | RO => exists receiver,
        get_this_var_mapping
          (vars boundary.(boundary_callee_entry_renv)) = Some receiver /\
        root = receiver /\
        typed_root RO
          boundary.(boundary_caller).(frame_senv)
          boundary.(boundary_caller).(frame_renv) root
    | Lost | Bot => False
    end.
Proof.
  intros boundary root Hroot.
  exact (boundary.(boundary_rdm_origins) root Hroot).
Qed.

Definition watched_frame_colors
  (CT : class_table) (h : heap) (M Z : Ensemble Loc)
  (frame : watched_frame) : Prop :=
  active_rdm_component_colors_separated CT h M Z
    frame.(frame_senv) frame.(frame_renv).

Lemma safe_call_rdm_roots_reflect_through_view :
  forall CT sGamma mt rGamma h x m y args sGamma'
    vals ly cy runtime_mdef Ty,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
    readonly_state_method_scope mt ->
    static_getType sGamma y = Some Ty ->
    runtime_getVal rGamma y = Some (Iot ly) ->
    r_basetype h ly = Some cy ->
    FindMethodWithName CT cy m runtime_mdef ->
    runtime_lookup_list rGamma args = Some vals ->
    rdm_roots_reflect_through_view (sqtype Ty)
      (mreceiver (msignature runtime_mdef) ::
        mparams (msignature runtime_mdef))
      (mkr_env (Iot ly :: vals)) sGamma rGamma.
Proof.
  intros CT sGamma mt rGamma h x m y args sGamma' vals ly cy runtime_mdef
    Ty Hwf Htyping Hscope Hreceiver_type Hreceiver_value Hbase Hfind Hargs
    root Hroot.
  destruct (safe_call_callee_rdm_root_origin CT sGamma mt rGamma h x m y
    args sGamma' vals ly cy runtime_mdef root Hwf Htyping Hscope
    Hreceiver_value Hbase Hfind Hargs Hroot) as
    [[Ty' [Hreceiver_type' [Hview Hcaller_root]]] |
     [Ty' [Hreceiver_type' [Hreadonly Hroot_receiver]]]].
  - rewrite Hreceiver_type in Hreceiver_type'.
    injection Hreceiver_type' as <-.
    destruct Hview as [Hmut | [Himm | Hrdm]].
    + rewrite Hmut in Hcaller_root |- *. exact Hcaller_root.
    + rewrite Himm in Hcaller_root |- *. exact Hcaller_root.
    + rewrite Hrdm in Hcaller_root |- *. exact Hcaller_root.
  - rewrite Hreceiver_type in Hreceiver_type'.
    injection Hreceiver_type' as <-.
    rewrite Hreadonly. exists ly. split; [reflexivity|]. split.
    + exact Hroot_receiver.
    + subst root. exists y, Ty. repeat split; assumption.
Qed.

Lemma rdm_roots_descend_after_assignment :
  forall CT sGamma mt rGamma h x e old value,
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SVarAss x e) sGamma ->
    readonly_state_method_scope mt ->
    runtime_getVal rGamma x = Some old ->
    eval_expr CT rGamma h e value OK rGamma h ->
    rdm_roots_descend_from CT h sGamma rGamma sGamma
      (update_r_env_value rGamma x value).
Proof.
  intros CT sGamma mt rGamma h x e old value Hwf Htyping Hscope Hx
    Heval root Hroot.
  eapply assignment_rdm_root_has_old_ancestor; eauto.
Qed.

Lemma rdm_roots_descend_after_local :
  forall CT sGamma mt rGamma h T x sGamma',
    wf_r_config CT sGamma rGamma h ->
    stmt_typing CT sGamma mt (SLocal T x) sGamma' ->
    runtime_getVal rGamma x = None ->
    rdm_roots_descend_from CT h sGamma rGamma sGamma'
      (set_vars rGamma (vars rGamma ++ [Null_a])).
Proof.
  intros CT sGamma mt rGamma h T x sGamma' Hwf Htyping Hnone root
    [y [Ty [Htype [Hval Hrdm]]]].
  inversion Htyping; subst.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
  destruct (appended_null_nonnull_lookup_is_old sGamma rGamma T y Ty root
    Hlength Htype Hval) as [Holdtype Holdval].
  exists root. split.
  - exists y, Ty. repeat split; assumption.
  - constructor.
Qed.

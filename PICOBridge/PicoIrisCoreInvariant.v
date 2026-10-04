From iris.program_logic Require Import language.

From Stdlib Require Import List Lia.
From Stdlib Require Import Program.Equality.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage.
Require Export PICOBridge.PicoCoreInvariant.

(** * Reducibility of Typed Core Steps

    Progress lemmas for the machine, stated with Iris's [reducible].  The
    typing invariants they use are in [PicoCoreInvariant]. *)

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

Theorem pico_core_typed_call_reducible :
  forall `{Hmem : CacheMemoryModel}
    CT sGamma sGamma' rGamma h sigma mt x y m args V K
    (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    @reducible
      (pico_core_language CT)
      (CoreRun rGamma (SCall x m y args) V K)
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

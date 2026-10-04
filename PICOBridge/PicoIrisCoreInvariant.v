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

(** Runtime cases for a statically known field write.  The location case uses
    the receiver's runtime subtype to transport the static field declaration
    to the concrete class. *)
Lemma pico_core_typed_fldwrite_runtime_cases_from_static :
  forall CT sGamma rGamma h x f y Tx C a
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hget_x : static_getType sGamma x = Some Tx)
    (Hget_y : exists Ty, static_getType sGamma y = Some Ty)
    (Href : sbase Tx = TRef C)
    (Hassign_static : sf_assignability_rel CT C f a),
    runtime_getVal rGamma x = Some Null_a \/
    exists loc o val_y,
      runtime_getVal rGamma x = Some (Iot loc) /\
      runtime_getObj h loc = Some o /\
      sf_assignability_rel CT (rctype (rt_type o)) f a /\
      runtime_getVal rGamma y = Some val_y /\
      (runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable \/
       runtime_vpa_assignability (rqtype (rt_type o)) a = Final).
Proof.
  intros CT sGamma rGamma h x f y Tx C a
    Henv Hget_x (Ty & Hget_y) Href Hassign_static.
  destruct
    (pico_core_typed_env_lookup
      CT sGamma rGamma h x Tx Henv Hget_x)
    as (qcontext_x & value_x & Hruntime_x & Htyped_x).
  destruct value_x as [|loc|n].
  - left.
    exact Hruntime_x.
  - right.
    unfold pico_core_typed_value in Htyped_x.
    unfold wf_r_typable, r_type in Htyped_x.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj.
    + destruct Htyped_x as [Hbase _Hqualifier].
      destruct
        (pico_core_typed_env_lookup
          CT sGamma rGamma h y Ty Henv Hget_y)
        as (qcontext_y & val_y & Hruntime_y & Htyped_y).
      exists loc, o, val_y.
      repeat split; try assumption.
      * destruct Hassign_static as
          (fdef & Hfield_static & Hassignability).
        exists fdef.
        split.
        -- destruct (base_subtype_from_ref CT (rctype (rt_type o)) (sbase Tx) Hbase)
             as [D0 [HbaseTx Hclass_sub]].
           rewrite HbaseTx in Href.
           inversion Href; subst D0.
           eapply field_inheritance_subtyping; eauto.
        -- exact Hassignability.
      * destruct (rqtype (rt_type o)), a; simpl; auto.
    + contradiction.
  - exfalso.
    unfold pico_core_typed_value in Htyped_x.
    rewrite Href in Htyped_x.
    discriminate.
Qed.

Lemma stmt_typing_fldwrite_static_components :
  forall CT sGamma sGamma' mt x f y
    (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma'),
    exists Tx Ty C a,
      static_getType sGamma x = Some Tx /\
      static_getType sGamma y = Some Ty /\
      sbase Tx = TRef C /\
      sf_assignability_rel CT C f a.
Proof.
  intros CT sGamma sGamma' mt x f y Htyping.
  inversion Htyping; subst;
    eexists _, _, _, _;
    repeat split; eauto.
Qed.

Theorem pico_core_typed_fldwrite_runtime_cases :
  forall CT sGamma sGamma' rGamma h mt x f y
    (Htyping : stmt_typing CT sGamma mt (SFldWrite x f y) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    runtime_getVal rGamma x = Some Null_a \/
    exists loc o a val_y,
      runtime_getVal rGamma x = Some (Iot loc) /\
      runtime_getObj h loc = Some o /\
      sf_assignability_rel CT (rctype (rt_type o)) f a /\
      runtime_getVal rGamma y = Some val_y /\
      (runtime_vpa_assignability (rqtype (rt_type o)) a = Assignable \/
       runtime_vpa_assignability (rqtype (rt_type o)) a = Final).
Proof.
  intros CT sGamma sGamma' rGamma h mt x f y Htyping Henv.
	  destruct
	    (stmt_typing_fldwrite_static_components
	      CT sGamma sGamma' mt x f y Htyping)
	    as (Tx & Ty & C & a & Hget_x & Hget_y & Href & Hassign_static).
	  destruct
	    (pico_core_typed_fldwrite_runtime_cases_from_static
	      CT sGamma rGamma h x f y Tx C a Henv Hget_x
	      (ex_intro _ Ty Hget_y) Href Hassign_static)
    as [Hnull |
      (loc & o & val_y & Hloc & Hobj & Hassign & Hy & Hcase)].
  - left.
    exact Hnull.
  - right.
    exists loc, o, a, val_y.
    auto.
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

Lemma pico_core_typed_env_lookup_list_exists :
  forall CT sGamma rGamma h args argtypes
    (Henv : pico_core_typed_env CT sGamma rGamma h)
    (Hstatic : static_getType_list sGamma args = Some argtypes),
    exists vals, runtime_lookup_list rGamma args = Some vals.
Proof.
  intros CT sGamma rGamma h args.
  induction args as [|arg args IH]; intros argtypes Henv Hstatic.
  - exists (@nil value).
    reflexivity.
  - unfold static_getType_list in Hstatic.
    simpl in Hstatic.
    destruct (static_getType sGamma arg) as [T |] eqn:Harg;
      try discriminate.
    destruct (mapM (static_getType sGamma) args) as [Ts |] eqn:Hargs;
      try discriminate.
    inversion Hstatic; subst argtypes.
    destruct
      (pico_core_typed_env_lookup
        CT sGamma rGamma h arg T Henv Harg)
      as (qcontext & value & Hruntime & Htyped).
    destruct (IH Ts Henv) as (values & Hruntime_args).
    {
      unfold static_getType_list.
      exact Hargs.
    }
    exists (value :: values).
    unfold runtime_lookup_list.
    simpl.
    rewrite Hruntime.
    unfold runtime_lookup_list in Hruntime_args.
    rewrite Hruntime_args.
    reflexivity.
Qed.

Lemma pico_core_typed_env_receiver_runtime :
  forall CT sGamma rGamma h
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    exists receiver qcontext,
      runtime_getVal rGamma 0 = Some (Iot receiver) /\
      r_muttype h receiver = Some qcontext.
Proof.
  intros CT sGamma rGamma h Henv.
  destruct
    (pico_core_typed_env_receiver CT sGamma rGamma h Henv)
    as (qcontext & receiver & Hthis & Hmut).
  exists receiver, qcontext.
  split; [| exact Hmut].
  unfold get_this_var_mapping in Hthis.
  unfold runtime_getVal.
  destruct (vars rGamma) as [|value values] eqn:Hvars;
    try discriminate.
  destruct value as [|loc|n]; try discriminate.
  inversion Hthis; subst loc.
  reflexivity.
Qed.

Lemma stmt_typing_new_static_args :
  forall CT sGamma sGamma' mt x qc C args
    (Htyping : stmt_typing CT sGamma mt (SNew x qc C args) sGamma'),
    exists argtypes,
      static_getType_list sGamma args = Some argtypes.
Proof.
  intros CT sGamma sGamma' mt x qc C args Htyping.
  inversion Htyping; subst.
  eexists.
  eauto.
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

Lemma stmt_typing_call_static_components :
  forall CT sGamma sGamma' mt x y m args
    (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma'),
    exists Ty C argtypes mdef,
      static_getType sGamma y = Some Ty /\
      sbase Ty = TRef C /\
      static_getType_list sGamma args = Some argtypes /\
      FindMethodWithName CT C m mdef.
Proof.
  intros CT sGamma sGamma' mt x y m args Htyping.
  inversion Htyping; subst;
    eexists _, _, _, _;
    repeat split; eauto.
Qed.

Lemma pico_core_typed_call_runtime_cases :
  forall CT sGamma sGamma' rGamma h mt x y m args
    (Htyping : stmt_typing CT sGamma mt (SCall x m y args) sGamma')
    (Henv : pico_core_typed_env CT sGamma rGamma h),
    runtime_getVal rGamma y = Some Null_a \/
    exists loc C mdef vals,
      runtime_getVal rGamma y = Some (Iot loc) /\
      r_basetype h loc = Some C /\
      FindMethodWithName CT C m mdef /\
      runtime_lookup_list rGamma args = Some vals.
Proof.
  intros CT sGamma sGamma' rGamma h mt x y m args Htyping Henv.
	  destruct
	    (stmt_typing_call_static_components
	      CT sGamma sGamma' mt x y m args Htyping)
	    as (Ty & Cstatic & argtypes & mdef_static
	        & Hget_y & Href & Hget_args & Hfind_static).
  destruct
    (pico_core_typed_env_lookup
      CT sGamma rGamma h y Ty Henv Hget_y)
    as (qcontext & receiver & Hruntime_y & Htyped_y).
  destruct receiver as [|loc|n].
  - left.
    exact Hruntime_y.
  - right.
    unfold pico_core_typed_value in Htyped_y.
    unfold wf_r_typable, r_type in Htyped_y.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj.
    + destruct Htyped_y as [Hbase _Hqualifier].
      pose proof
        (pico_core_typed_env_wf_config
          CT sGamma rGamma h Henv) as Hconfig.
      unfold wf_r_config in Hconfig.
      destruct Hconfig as (Hwf_CT & _).
	      destruct
	        (base_subtype_from_ref CT (rctype (rt_type o)) (sbase Ty) Hbase)
	        as [D0 [HbaseTy Hclass_sub]].
	      rewrite HbaseTy in Href.
	      inversion Href; subst D0.
	      destruct
	        (method_inheritance_exists
	          CT (rctype (rt_type o)) Cstatic m mdef_static
	          Hwf_CT Hclass_sub Hfind_static)
	        as (mdef & Hfind_runtime).
      destruct
        (pico_core_typed_env_lookup_list_exists
          CT sGamma rGamma h args argtypes Henv Hget_args)
        as (vals & Hargs).
      exists loc, (rctype (rt_type o)), mdef, vals.
      repeat split; try assumption.
      unfold r_basetype.
      rewrite Hobj.
      reflexivity.
    + contradiction.
	  - exfalso.
	    unfold pico_core_typed_value in Htyped_y.
	    rewrite Href in Htyped_y.
	    discriminate.
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

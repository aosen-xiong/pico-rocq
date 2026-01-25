Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties DeepImmutability.
Require Import List.
Import ListNotations.
Require Import String.
From RecordUpdate Require Import RecordUpdate.

Theorem readonly_pico_field_write:
    forall CT sΓ rΓ h stmt rΓ' h' sΓ' l C vals vals' f qt readonlyx anyf rhs anyrq,
      stmt = (SFldWrite readonlyx anyf rhs)-> 
      static_getType sΓ readonlyx = Some qt ->
      (sqtype qt) = Rd ->
      wf_r_config CT sΓ rΓ h ->
      stmt_typing CT sΓ stmt sΓ' -> 
      eval_stmt OK CT rΓ h stmt OK rΓ' h' -> 
      runtime_getVal rΓ readonlyx = Some (Iot l)  ->
      runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals) ->
      runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals') ->
      sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA ->
      nth_error vals f = nth_error vals' f.
Proof.
intros CT sΓ rΓ h stmt rΓ' h' sΓ' l C vals vals' f qt readonlyx anyf rhs anyrq.
intros Hstmt_form Hreceivermut Hstatic_type Hwf_config Htyping Heval Hruntime_val Hobj_before Hobj_after Hassign_rel.

(* Subst the statement form *)
subst stmt.

(* Invert the evaluation to get heap update details *)
inversion Heval; subst.

(* Invert typing to get field write constraints *)
inversion Htyping; subst.

unfold wf_r_config in Hwf_config.
  destruct Hwf_config as [_[_[Hrenv [_ [_ Htypable]]]]].
  assert (Hreadonly_dom : readonlyx < dom sΓ').
  {
    apply static_getType_dom in Hreceivermut.
    exact Hreceivermut.
  }
  rewrite Hruntime_val in H2.
  inversion H2.
  subst l.
  unfold wf_renv in Hrenv.
  destruct Hrenv as [_ [Hreceiver _]].
  destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
  assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
  {
    eapply receiver_mutability_exists_from_bound; eauto.
  }
  destruct HOutterReceiverMutability as [qcontext Hqcontext].
  (* Apply correspondence to get wf_r_typable *)
  specialize (Htypable iot qcontext Hget_iot Hqcontext readonlyx Hreadonly_dom qt Hreceivermut).
  rewrite Hruntime_val in Htypable.
  unfold wf_r_typable in Htypable.
  unfold r_type in Htypable.
  rewrite H3 in Htypable.
  destruct Htypable as [base qualifier].
  rewrite H3 in Hobj_before.
  inversion Hobj_before.
  rewrite H0 in base.
  simpl in base.

(* Use the fact that Final/RDA fields are protected from modification *)
destruct Hassign_rel as [Hfinal | Hrda].
-  
  rewrite Hreceivermut in H6.
  inversion H6.
  subst Tx.
  rewrite Hstatic_type in H15.
  unfold vpa_assignability in H15.
  destruct a eqn: Haeqn; try easy.
  assert (Hneq: anyf <> f).
  {
    intro Heq.
    subst anyf.
    unfold sf_assignability_rel in H13, Hfinal.
    destruct H13 as [fdef_assign [Hlookup_assign Hassign_assign]].
    destruct Hfinal as [fdef_final [Hlookup_final Hassign_final]].
    assert (fdef_final = fdef_assign).
    {
      eapply field_lookup_deterministic_rel; eauto.
      eapply field_inheritance_subtyping; eauto.
    }
    subst fdef_final.
    rewrite Hassign_final in Hassign_assign.
    discriminate.
  }
  injection Hobj_before as Hvals_eq.
  unfold update_field in Hobj_after.
  rewrite H3 in Hobj_after.
  simpl in Hobj_after.
  unfold update_field in Hobj_after.
  simpl in Hobj_after.
  assert (Hdom: loc_x < dom h).
  {
    apply runtime_getObj_dom in H3.
    exact H3.
  }
  rewrite runtime_getObj_update_same in Hobj_after; auto.
  inversion Hobj_after; subst.
  simpl.
  symmetry.
  apply update_diff.
  exact Hneq.
  unfold vpa_assignability in H16.
  rewrite Hstatic_type in H16; easy.
  rewrite Hstatic_type in H16; easy.
- (* RDA case: RDA fields cannot be written *)
  rewrite Hreceivermut in H6.
  inversion H6.
  subst Tx.
  rewrite Hstatic_type in H15.
  unfold vpa_assignability in H15.
  destruct a eqn: Haeqn; try easy.
  assert (Hneq: anyf <> f).
  {
    intro Heq.
    subst anyf.
    unfold sf_assignability_rel in H13, Hrda.
    destruct H13 as [fdef_assign [Hlookup_assign Hassign_assign]].
    destruct Hrda as [fdef_final [Hlookup_final Hassign_final]].
    assert (fdef_final = fdef_assign).
    {
      eapply field_lookup_deterministic_rel; eauto.
      eapply field_inheritance_subtyping; eauto.
    }
    subst fdef_final.
    rewrite Hassign_final in Hassign_assign.
    discriminate.
  }
  injection Hobj_before as Hvals_eq.
  unfold update_field in Hobj_after.
  rewrite H3 in Hobj_after.
  simpl in Hobj_after.
  unfold update_field in Hobj_after.
  simpl in Hobj_after.
  assert (Hdom: loc_x < dom h).
  {
    apply runtime_getObj_dom in H3.
    exact H3.
  }
  rewrite runtime_getObj_update_same in Hobj_after; auto.
  inversion Hobj_after; subst.
  simpl.
  symmetry.
  apply update_diff.
  exact Hneq.
  rewrite Hstatic_type in H16; easy.
  rewrite Hstatic_type in H16; easy.
Qed.

(* TODO: rename RD to RO *)
Inductive class_reachable (CT : class_table) : class_name -> class_name -> Prop :=
  (* Base Case: Reflexivity *)
  | cr_refl : 
      forall C, 
        class_reachable CT C C

  (* Inductive Step: Transitivity via Protected Fields *)
  | cr_step : 
      forall C f fDef C_next C_target,
        (* 1. Look up the field definition *)
        sf_def_rel CT C f fDef ->
        
        (* 2. CRITICAL: Only traverse if the field is part of the abstract state 
             (matches your reachable_abs condition) *)
        (fDef.(ftype).(mutability) = Imm_f \/ fDef.(ftype).(mutability) = RDM_f) ->
        
        (* 3. Get the static type of the field *)
        C_next = fDef.(ftype).(f_base_type) ->
        
        (* 4. Transitivity *)
        class_reachable CT C_next C_target ->
        
        class_reachable CT C C_target.

Inductive static_reachable (CT : class_table) (sΓ : s_env) : var -> class_name -> Prop :=
  | srch_entry : 
      forall x T C_target,
        (* 1. Look up x in the static environment *)
        static_getType sΓ x = Some T ->
        
        (* 2. Check if the class of x reaches C_target *)
        class_reachable CT (sctype T) C_target ->
        
        static_reachable CT sΓ x C_target.

Lemma vpa_mutabilty_stype_fld_rd_not_mut :
  forall q_recv q_field q_res
         (Hrd : q_recv = Rd)
         (Hvpa : vpa_mutabilty_stype_fld q_recv q_field = q_res),
    q_res <> Mut.
Proof.
  intros. subst.
  unfold vpa_mutabilty_stype_fld.
  destruct q_field; subst; try easy.
Qed.

(* Definition is_protected_root (T : qualified_type) : Prop :=
  sqtype T = Rd \/ sqtype T = Imm. *)

(* Safe means preserve shallow immutability *)
Definition is_safe_mode (m : q) : Prop :=
  (* m = Rd. *)
  m = Rd \/ m = Lost.
  (* Don't use bot because not interesting *)
  (* m = Rd \/ m = Imm \/ m = Lost \/ m = Bot. *)  

Definition protected_locset
  (CT : class_table) (h : heap) (l_root : Loc) : Ensembles.Ensemble Loc :=
  fun l_target => reachable_abs CT h l_root l_target.

(* Effectively require all variables *)
Definition env_respects_protected_set
  (P : Ensembles.Ensemble Loc) (sΓ : s_env) (rΓ : r_env) : Prop :=
  forall x l T,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot l) ->

    (* (exists l_intermediate,
      reachable_abs CT h l l_intermediate /\
      Ensembles.In Loc P l_intermediate) -> *)
    
    (* If the location is in the Protected Set... *)
    Ensembles.In Loc P l ->

    (* ...the variable must be ReadOnly, or Lost. *)
    is_safe_mode (sqtype T).

Definition heap_respects_protected_set
  (P : Ensembles.Ensemble Loc) (h_initial h_curr : heap) (CT : class_table) : Prop :=
  forall l_src C anyrq vals k l_dst,
    l_dst < dom h_initial ->  (* Only pre-existing objects *)
    l_src >= dom h_initial ->  (* Only newly allocated objects *)
    Ensembles.In Loc P l_dst ->
    runtime_getObj h_curr l_src = Some (mkObj (mkruntime_type anyrq C) vals) ->
    nth_error vals k = Some (Iot l_dst) ->
    exists fDef,
      sf_def_rel CT C k fDef /\
      (fDef.(ftype).(mutability) = Rd_f).

Definition confinement_invariant_precise
  (P : Ensembles.Ensemble Loc) 
  (CT : class_table) 
  (sΓ : s_env) 
  (rΓ : r_env) 
  (h_initial h_curr : heap) : Prop :=
  env_respects_protected_set P sΓ rΓ /\
  heap_respects_protected_set P h_initial h_curr CT.

Lemma mut_var_cannot_point_to_P :
  forall sΓ rΓ x T l P
         (Hlookup : static_getType sΓ x = Some T)
         (Hval : runtime_getVal rΓ x = Some (Iot l))
         (Henv_safe : env_respects_protected_set P sΓ rΓ)
         (Hin_P : Ensembles.In Loc P l),
    sqtype T <> Mut.
Proof.
  intros.
  (* Unfold the invariant *)
  unfold env_respects_protected_set in Henv_safe.
  specialize (Henv_safe x l T Hlookup Hval Hin_P).
  (* Henv_safe says T is Rd/Imm/Lost. Thus it is not Mut. *)
  unfold is_safe_mode in Henv_safe.
  intuition; subst; discriminate.
Qed.

(* Lemma step_preserves_confinement :
  forall CT sΓ rΓ h l_root stmt sΓ' rΓ' h' P
         (HP_def : P = protected_locset CT h l_root)
         (Hconfined : confinement_invariant_precise P CT sΓ rΓ h)
         (Hwf : wf_r_config CT sΓ rΓ h)
         (Htyping : stmt_typing CT sΓ stmt sΓ')
         (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h'),
    confinement_invariant_precise P CT sΓ' rΓ' h'.
Proof.
  intros.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  induction Heval; intros; subst; try discriminate.
  - (* Skip *) 
    inversion Htyping; subst.
    exact Hconfined.
  - (* Local *)
    inversion Htyping; subst.
    unfold confinement_invariant_precise in *.
    destruct Hconfined as [Henv_respects Hheap_respects].
    split.
    + (* Env respects *)
  (* Induction on eval_stmt. Use Lemma 2 for SAssignField. *)
  (* Use Lemma 1 to show we don't violate env_respects for SAssign. *)

Lemma step_preserves_protected_values :
  forall CT sΓ rΓ h l_root stmt sΓ' rΓ' h' P l C anyrq vals vals'
         (HP : P = protected_locset CT h l_root) (* P is fixed to PRE-state *)
         (Hconfined : confinement_invariant_precise P CT sΓ rΓ h)
         (Hwf : wf_r_config CT sΓ rΓ h)
         (Htyping : stmt_typing CT sΓ stmt sΓ')
         (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
         (* The object is in P *)
         (Hin : Ensembles.In Loc P l)
         (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
         (Hobj' : runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals')),
    (* Conclusion: Protected fields are equal *)
    forall f, (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA) ->
    nth_error vals f = nth_error vals' f.
Proof.
  intros.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  induction Heval; intros; subst; try discriminate.
  - (* Skip *) 
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* Local *)
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* VarAss *)
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* FldWrite *)
    {
    destruct (Nat.eq_dec loc_x l) as [Halias | Hno_alias].
    -
      subst loc_x.
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Same field case: contradiction *)
        subst f0.
        (* Now: x points to l, and l ∈ P *)
        (* Strategy: Show x must be Safe, but field write requires x to be Mut → contradiction *)
        
        (* Extract x's static type from typing *)
        inversion Htyping; subst.
        (* After inversion: static_getType sΓ x = Some Tx, and sqtype Tx should allow write *)
        
        (* Unfold confinement to get env_respects_protected_set *)
        unfold confinement_invariant_precise in Hconfined.
        destruct Hconfined as [Henv_respects _].
        
        (* Apply the lemma: if x points to l ∈ P, then x is Safe *)
        have Hx_safe := mut_var_cannot_point_to_P sΓ' rΓ x Tx l (protected_locset CT h l_root) H8 H0 Henv_respects Hin.
        
        (* But from ST_FldWrite typing, we need sqtype Tx to allow writes *)
        (* H15: vpa_assignability (sqtype Tx) a = Assignable *)
        
        (* Case on assignability *)
        apply vpa_assingability_assign_cases in H17.
        unfold wf_r_config in Hwf.
        destruct Hwf as [Hclasstable [_[Hrenv [_ [_ Htypable]]]]].
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qcontext Hqcontext].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qcontext Hget_iot Hqcontext x).
        have H8copy := H8.
        apply static_getType_dom in H8.
        unfold static_getType in H8copy.
        specialize (Htypable H8 Tx H8copy).
        rewrite H0 in Htypable.
        unfold wf_r_typable in Htypable.
        unfold r_type in Htypable.
        rewrite Hobj in Htypable.
        destruct Htypable as [base qualifier].
        simpl in base.
        destruct H17 as [Ha_assign | [Hx_mut Ha_rda]].
        
        ++ (* Case: a = Assignable *)
          destruct H as [HFinal | HRDA].
          * (* Case: sf_assignability_rel CT C f Final *)
          assert (Heq : Final = a).
          {
            eapply sf_assignability_consistent_subtype with (f := f) (C := C) (D := sctype Tx); eauto.
          }
          rewrite <- Heq in Ha_assign.
          discriminate Ha_assign.
          *
          assert (Heq : RDA = a).
          {
            eapply sf_assignability_consistent_subtype with (f := f) (C := C) (D := sctype Tx); eauto.
          }
          rewrite <- Heq in Ha_assign.
          discriminate Ha_assign.
        ++ (* Case: sqtype Tx = Mut ∧ a = RDA *)
          exfalso.
          apply Hx_safe.
          exact Hx_mut.
      + (* Different field case: trivial *)
        unfold update_field in Hobj'.
        rewrite H1 in Hobj'.
        simpl in Hobj'.

        (* Extract the domain bound for l *)
        assert (Hdom : l < dom h).
        {
          apply runtime_getObj_dom in H1.
          exact H1.
        }

        (* After update_field, the object at l has fields updated at f0 *)
        rewrite runtime_getObj_update_same in Hobj'; auto.

        (* Now Hobj' shows vals' = update f0 val_y (fields_map o) *)
        (* And Hobj shows vals = fields_map o *)
        injection Hobj' as _ Hvals'_eq.
        rewrite H1 in Hobj.
        injection Hobj as Hvals_eq.
        (* rewrite <- Hfields_eq in Hvals'_eq. *)

        (* vals' is just vals with f0 updated, so f is unchanged *)
        rewrite <- Hvals'_eq.
        rewrite update_diff.
        -- symmetry. exact Hneq_f.
        -- 
        assert (Hfields : fields_map o = vals).
        {
          rewrite Hvals_eq.
          reflexivity.
        }
        rewrite Hfields.
        reflexivity.
    -
      (* No aliasing case: trivial *)
      unfold update_field in Hobj'.
      have Heq : runtime_getObj 
        (match runtime_getObj h loc_x with
        | Some o => [loc_x ↦ o <| fields_map := update f0 val_y (fields_map o) |>] h
        | None => h
        end) l = runtime_getObj h l.
      {
        destruct (runtime_getObj h loc_x).
        - apply runtime_getObj_update_diff; auto.
        - reflexivity.
      }
      rewrite Heq in Hobj'.
      rewrite Hobj in Hobj'.
      inversion Hobj'.
      reflexivity.
  }
  - (* New *)
    unfold protected_locset in Hin.
  
    (* Extract l < dom h from reachable_abs *)
    assert(Hl_old : l < dom h).
    {
      apply runtime_getObj_dom in Hobj.
      exact Hobj.
    }
    
    rewrite runtime_getObj_last2 in Hobj'; auto.
  - (* Call *)
  - (* Seq *)
*)

Lemma extract_receiver_from_wf_config :
  forall CT sΓ rΓ h
    (Hwf : wf_r_config CT sΓ rΓ h),
    exists iot qcontext,
      get_this_var_mapping (vars rΓ) = Some iot /\
      iot < dom h /\
      r_muttype h iot = Some qcontext.
Proof.
  intros CT sΓ rΓ h Hwf.
  unfold wf_r_config in Hwf.
  destruct Hwf as [_ [_ [Hrenv _]]].
  destruct Hrenv as [_ [Hreceiver _]].
  destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
  exists iot.
  assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
  {
    eapply receiver_mutability_exists_from_bound; eauto.
  }
  destruct HOutterReceiverMutability as [qcontext Hqcontext].
  exists qcontext.
  (* TODO: is there better way to write this tactics? *)
  split. 
  exact Hget_iot.
  split.
  exact Hiot_dom.
  exact Hqcontext. 
Qed.

Lemma subtype_safe_implies_safe :
  forall CT T_sub T_super
         (Hsub : qualified_type_subtype CT T_sub T_super)
         (Hsafe_sub : is_safe_mode (sqtype T_sub)),
    is_safe_mode (sqtype T_super).
Proof.
  intros. unfold is_safe_mode in *.
  apply qualified_type_subtype_q_subtype in Hsub.
  inversion Hsub; subst; auto.
  rewrite <- H0 in Hsafe_sub.
  destruct Hsafe_sub as [Hrd | Hlost].
  inversion Hrd. 
  inversion Hlost.
Qed.

Lemma adapated_subtype_safe_implies_safe :
  forall CT T_sub T_Receiver T_super
         (Hsub : qualified_type_subtype CT T_sub (vpa_mutabilty_tt T_Receiver T_super))
         (Hsafe_sub : is_safe_mode (sqtype T_sub)),
    is_safe_mode (sqtype T_super).
Proof.
  intros.
  unfold is_safe_mode in *.
  apply qualified_type_subtype_q_subtype in Hsub.
  unfold vpa_mutabilty_tt in Hsub.
  destruct (sqtype T_Receiver) eqn: Hreceiver;
  destruct (sqtype T_super) eqn: HSuper;
  destruct Hsafe_sub as [Hrd | Hlost];
  try rewrite Hrd in Hsub;
  try rewrite Hlost in Hsub;
  try rewrite <- H in Hsub;
  inversion Hsub; subst; auto.
  all: try rewrite HSuper in H; try rewrite HSuper in H1; try discriminate.
  all: try easy.
Qed.

Lemma subtype_safe_implies_safe_adapted :
  forall CT T_sub T_Receiver T_super
         (Hsub : qualified_type_subtype CT (vpa_mutabilty_tt T_Receiver T_sub) T_super)
         (Hsafe_sub : is_safe_mode (sqtype T_sub)),
    is_safe_mode (sqtype T_super).
Proof.
  intros.
  unfold is_safe_mode in *.
  apply qualified_type_subtype_q_subtype in Hsub.
  unfold vpa_mutabilty_tt in Hsub.
  destruct (sqtype T_Receiver) eqn: Hreceiver;
  destruct (sqtype T_super) eqn: HSuper;
  destruct Hsafe_sub as [Hrd | Hlost];
  try rewrite Hrd in Hsub;
  try rewrite Hlost in Hsub;
  try rewrite <- H in Hsub;
  inversion Hsub; subst; auto.
  all: try rewrite HSuper in H; try rewrite Hrd in H0; try rewrite Hlost in H0; try discriminate.
Qed.

Lemma reachable_abs_dom :
  forall CT h l_src l_dst
    (Hreach : reachable_abs CT h l_src l_dst),
    l_dst < dom h.
Proof.
  intros CT h l_src l_dst Hreach.
  induction Hreach.
  - (* Base case: reachable_abs_heap *)
    exact H.
  - (* Step case: reachable_abs_step *)
    exact H.
  - (* Trans case *)
    exact IHHreach2.
Qed.

Lemma confinement_from_all_readonly_env :
  forall CT sΓ rΓ h x l_root
    (Hdom_root : l_root < dom h)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Hgetval : runtime_getVal rΓ x = Some (Iot l_root))
    (Hall_readonly : forall y T,
      static_getType sΓ y = Some T ->
      is_safe_mode (sqtype T)),
    confinement_invariant_precise (protected_locset CT h l_root) CT sΓ rΓ h h.
Proof.
  intros.
  unfold confinement_invariant_precise.
  split.
  - (* env_respects_protected_set *)
    unfold env_respects_protected_set.
    intros z l T Hlookup_s Hlookup_r Hin_P.
    exact (Hall_readonly z T Hlookup_s).
  - (* heap_respects_protected_set *)
    unfold heap_respects_protected_set.
    intros l_src C anyrq vals k l_dst Hdom_dst Hdom_src Hin_dst Hobj_src Hnth.
    (* For (h, h), we have h_initial = h_curr = h *)
    (* Therefore: l_src >= dom h *)
    (* But also: runtime_getObj h l_src = Some (...) requires l_src < dom h *)
    exfalso.
    apply runtime_getObj_dom in Hobj_src.
    lia.  (* This part depends on heap wellformedness properties *)
Qed.

(* Lemma expr_eval_to_protected_implies_safe_type :
  forall P CT sΓ rΓ h l_root e l_res Te
         (Hwf : wf_r_config CT sΓ rΓ h)
         (Hdom_root : l_root < dom h)
         (HP_def : P = protected_locset CT h l_root)
         (*  *)
         (Hconfined : confinement_invariant_precise P CT sΓ rΓ h h)
         (Heval : eval_expr OK CT rΓ h e (Iot l_res) OK rΓ h)
         (Htyp : expr_has_type CT sΓ e Te)
         (Hin : Ensembles.In Loc P l_res),
    is_safe_mode (sqtype Te).
Proof.
  intros.
  destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]].
  have htyp_copy := Htyp.
  eapply expr_eval_preservation with (v:= Iot l_res) (rΓ' := rΓ) (h' := h) in Htyp; eauto.
  unfold wf_r_typable in Htyp.
  unfold r_type in Htyp.
  destruct (runtime_getObj h l_res); try easy.
  (* remember OK as ok. *)
  inversion Heval; subst.
  - (* EVar case *)
  inversion htyp_copy; subst.
    (* Now Htyp should give us: expr_has_type CT sΓ (EVar x) Te *)
    (* which means static_getType sΓ x = Some Te *)
    
    unfold confinement_invariant_precise in Hconfined.
    destruct Hconfined as [Henv_respects Hheap_respects].
    
    (* Apply env_respects_protected_set *)
    unfold env_respects_protected_set in Henv_respects.
    specialize (Henv_respects x l_res Te).
    have H_static : static_getType sΓ x = Some Te.
    {
      auto.
    }
    
    specialize (Henv_respects H_static H Hin).
    exact Henv_respects.
  - (* EField case *)
    inversion htyp_copy; subst.
    (* unfold is_safe_mode; simpl. *)
    (* unfold vpa_mutabilty_stype_fld. *)
    (* unfold confinement_invariant_precise in Hconfined. *)
    destruct Hconfined as [Henv_respects Hheap_respects].
    set (P := protected_locset CT h l_root).
    destruct (classic (Ensembles.In Loc P v)) as [Hv_in | Hv_out].
    +
      specialize (Henv_respects x v T H7 H Hv_in).
      unfold is_safe_mode in Henv_respects.
      subst. simpl.
      destruct Henv_respects as [Hrd | Hlost].
      *
      rewrite Hrd.
      unfold vpa_mutabilty_stype_fld.
      unfold is_safe_mode.
      destruct (mutability (ftype fDef)); try easy.
      right; reflexivity.
      right; reflexivity.
      right; reflexivity.
      right; reflexivity.
      *
      rewrite Hlost.
      unfold vpa_mutabilty_stype_fld.
      unfold is_safe_mode.
      right; reflexivity.
    +
    assert (Hdom_v : v < dom h) by (apply runtime_getObj_dom in H0; exact H0).

    (* Extract C and vals from o0 *)
    destruct o0 as [[anyrq C] vals_v].
    simpl in H1.
    assert (Hdom_l_res : l_res < dom h) by (apply reachable_abs_dom in Hin; exact Hin).
    unfold env_respects_protected_set in Henv_respects.
    specialize (Henv_respects x v T H7 H)
    specialize (Hheap_respects v C anyrq vals_v f l_res
            Hdom_l_res Hin H0 H1).
    
      destruct Hheap_respects as [fDef' [Hlookup' Hmut_rd]].
      (* Align static/runtime field defs *)
      destruct Htyp as [Hbasetype Hqualifier].
      simpl in Hbasetype.
      eapply field_lookup_deterministic_rel in Hlookup';
        [| eapply field_inheritance_subtyping; eauto].
      subst fDef'.
      rewrite Hmut_rd.
      (* Now fDef.mutability = Rd_f *)
      
      unfold is_safe_mode.
      unfold vpa_mutabilty_stype_fld.
      destruct (sqtype T); simpl; try easy.
      left; reflexivity.
      left; reflexivity.
      left; reflexivity.
      right; reflexivity.
      right; reflexivity.
      left; reflexivity.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [_ Hcorr]]]]].
      assert (Hx_dom : x < dom sΓ) by (apply static_getType_dom in H7; exact H7).
      specialize (Hcorr iot qcontext Hget_iot Hqcontext x Hx_dom T H7).
      rewrite H in Hcorr.
      unfold wf_r_typable in Hcorr.
      unfold r_type in Hcorr.
      rewrite H0 in Hcorr.
      simpl in Hcorr.
      destruct Hcorr as [Hbaseruntime _].
      (* Hbaseruntime: base_subtype CT (rctype (rt_type o)) (sctype T) *)
      (* We have rctype (rt_type o) = C from H0 *)
      simpl in Hbaseruntime.
      exact Hbaseruntime.
Qed. *)

Lemma runtime_getObj_app_left_equal : forall h h_ext loc,
  loc < dom h ->
  runtime_getObj h loc = runtime_getObj (h ++ [h_ext]) loc.
Proof.
  intros h h_ext loc Hloc_dom.
  unfold runtime_getObj.
  rewrite nth_error_app1; auto.
Qed.

Lemma env_respects_weaken :
  forall CT sΓ rΓ h l_root l_intermediate
    (Hreach : reachable_abs CT h l_root l_intermediate)
    (Henv_respects : env_respects_protected_set (protected_locset CT h l_root) sΓ rΓ),
    env_respects_protected_set (protected_locset CT h l_intermediate) sΓ rΓ.
Proof.
  intros CT sΓ rΓ h l_root l_intermediate Hreach Henv_respects.
  intros x l T Hlookup Hval Hin_l_intermediate.
  unfold protected_locset in Hin_l_intermediate.
  have Hin_l_root : Ensembles.In Loc (protected_locset CT h l_root) l :=
    reachable_abs_trans CT h l_root l_intermediate l Hreach Hin_l_intermediate.
  exact (Henv_respects x l T Hlookup Hval Hin_l_root).
Qed.

Lemma heap_respects_weaken :
  forall CT h_initial h_curr l_root l_intermediate
    (Hreach : reachable_abs CT h_curr l_root l_intermediate)
    (Hheap : heap_respects_protected_set (protected_locset CT h_curr l_root) h_initial h_curr CT),
    heap_respects_protected_set (protected_locset CT h_curr l_intermediate) h_initial h_curr CT.
Proof.
  intros CT h_initial h_curr l_root l_intermediate Hreach Hheap.
  unfold heap_respects_protected_set in *.
  intros l_src C anyrq vals k l_dst Hdom_dst Hlsrc_new Hin_l_intermediate Hobj Hnth.
  (* The key: Hin_l_intermediate says l_dst ∈ protected_locset(l_intermediate)
     By transitivity: l_dst ∈ protected_locset(l_root) *)
  have Hin_l_root : Ensembles.In Loc (protected_locset CT h_curr l_root) l_dst :=
    reachable_abs_trans CT h_curr l_root l_intermediate l_dst Hreach Hin_l_intermediate.
  (* Now apply Hheap with all the same conditions *)
  exact (Hheap l_src C anyrq vals k l_dst Hdom_dst Hlsrc_new Hin_l_root Hobj Hnth).
Qed.

Lemma confinement_invariant_weaken :
  forall CT sΓ rΓ h_initial h_curr l_root l_intermediate
    (Hreach : reachable_abs CT h_curr l_root l_intermediate)
    (Hconf : confinement_invariant_precise (protected_locset CT h_curr l_root) CT sΓ rΓ h_initial h_curr),
    confinement_invariant_precise (protected_locset CT h_curr l_intermediate) CT sΓ rΓ h_initial h_curr.
Proof.
  intros CT sΓ rΓ h_initial h_curr l_root l_intermediate Hreach Hconf.
  unfold confinement_invariant_precise in *.
  destruct Hconf as [Henv_respects Hheap_respects].
  split.
  - (* env_respects_protected_set weakens *)
    eapply env_respects_weaken; eauto.
  - (* heap_respects_protected_set weakens *)
    eapply heap_respects_weaken; eauto.
Qed.

Lemma stmt_preserves_both :
  forall CT sΓ rΓ h l_root stmt sΓ' rΓ' h'
    (Hdom_root : l_root < dom h)
    (Hconfined : confinement_invariant_precise (protected_locset CT h l_root) CT sΓ rΓ h h)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ stmt sΓ')
    (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h'),
  protected_locset CT h l_root = protected_locset CT h' l_root /\
  confinement_invariant_precise (protected_locset CT h l_root) CT sΓ' rΓ' h h'.
Proof.
  intros.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  have Heval_copy := Heval.
  induction Heval; intros; subst; try discriminate.
  7:
  {
  inversion Htyping; subst.

  (* Apply IH1 *)
  pose proof (IHHeval1 Hdom_root eq_refl Heval1 sΓ'0 sΓ Hconfined Hwf H4) as [HeqP1 Hconf1].

  (* Get wellformedness for intermediate state *)
  pose proof (preservation_pico _ _ _ _ _ _ _ _ Hwf H4 Heval1) as Hwf'.

  assert (Hdom_root' : l_root < dom h').
  {
    apply eval_stmt_preserves_heap_domain_simple in Heval1; eauto.
    lia.
  }

  (* Convert Hconf1 from (h, h') to (h', h') parametrization *)
  assert (Hconf1_for_ih2 : confinement_invariant_precise (protected_locset CT h' l_root) CT sΓ'0 rΓ' h' h').
  {
    unfold confinement_invariant_precise in Hconf1.
    destruct Hconf1 as [Henv1 Hheap1].
    split.
    + rewrite <- HeqP1. exact Henv1.
    + unfold heap_respects_protected_set.
      intros l_src C anyrq vals k l_dst Hdom_dst Hlsrc_new Hin_dst Hobj_src Hnth.
      (* For (h', h'): l_src >= dom h' but also runtime_getObj h' l_src = Some(...) requires l_src < dom h' *)
      exfalso.
      apply runtime_getObj_dom in Hobj_src.
      lia.
  }

  (* Apply IH2 *)
  pose proof (IHHeval2 Hdom_root' eq_refl Heval2 sΓ' sΓ'0 Hconf1_for_ih2 Hwf' H6) as [HeqP2 Hconf2].

  (* Now chain the equalities via transitivity *)
  assert (HeqP : protected_locset CT h l_root = protected_locset CT h'' l_root).
  {
    (* By HeqP1 and HeqP2 *)
    rewrite HeqP1.
    exact HeqP2.
  }

  (* For the invariant part, convert Hconf2 back *)
  assert (Hconf_final : confinement_invariant_precise (protected_locset CT h l_root) CT sΓ' rΓ'' h h'').
  {
    unfold confinement_invariant_precise in Hconf1, Hconf2, Hconfined, Hconf1_for_ih2.
    destruct Hconf1 as [Henv1 Hheap1].
    destruct Hconf2 as [Henv2 Hheap2].
    destruct Hconfined as [Henv0 Hheap0].
    destruct Hconf1_for_ih2 as [Henv1' Hheap1'].
    split.
    + rewrite HeqP. rewrite <- HeqP2. exact Henv2.
    + unfold heap_respects_protected_set in *.
      intros l_src C anyrq vals k l_dst Hdom_dst_h Hlsrc_new_h Hin_dst Hobj_src Hnth.
      have Hdom_h_h' : dom h <= dom h' by
      (apply eval_stmt_preserves_heap_domain_simple in Heval1; lia).
      destruct (le_lt_dec (dom h') l_src) as [Hlsrc_new_h' | Hlsrc_old_h'].
    - (* Case: l_src >= dom h' (allocated during second statement) *)
      have Hin_dst' : Ensembles.In Loc (protected_locset CT h' l_root) l_dst by
        (rewrite <- HeqP1; exact Hin_dst).
      have Hdom_dst_h' : l_dst < dom h' by
        (apply reachable_abs_dom in Hin_dst'; exact Hin_dst').  
      exact (Hheap2 l_src C anyrq vals k l_dst Hdom_dst_h' Hlsrc_new_h' Hin_dst' Hobj_src Hnth).
    - (* Case: l_src < dom h' (allocated before or during first statement) *)
      unfold env_respects_protected_set in *.
      (* have Hh'some : exists C' vals', runtime_getObj h' l_src = Some (mkObj C' vals').
      {
        eapply runtime_getObj_Some; auto.
      }

      destruct Hh'some as [C' [vals' Hh'some]].

      have Hh''some: exists vals'', runtime_getObj h'' l_src = Some
      {| rt_type := C'; fields_map :=vals''|}.
      {
        eapply runtime_preserves_r_type_heap with (h := h') (h' := h'')(vals := vals'); eauto.
      }

      destruct Hh''some as [vals'' Hh''some].
      rewrite Hh''some in Hobj_src.
      inversion Hobj_src; subst C' vals''.
      eapply Hheap1 with (l_dst := l_dst) (l_src := l_src) (vals := vals'); eauto.
      rename vals into vals''. *)
      admit.
  }

  split.
  + exact HeqP.
  + exact Hconf_final.
  }
  - (* skip *)
    inversion Htyping; subst.
    split; [reflexivity | exact Hconfined].
  - (* local *)
    split.
    + reflexivity.
    + (* Invariant preserved *)
    inversion Htyping; subst.
    unfold confinement_invariant_precise in *.
    destruct Hconfined as [Henv_respects Hheap_respects].
    split.
    *
      unfold env_respects_protected_set.
      intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x y); subst.
      --
        assert (y = dom sΓ).
        {
          apply static_getType_dom in Hlookup_s.
          apply static_getType_not_dom in H4.
          rewrite length_app in Hlookup_s; simpl in Hlookup_s. (* dom (sΓ++[T]) = S (dom sΓ) *)
          lia.
        }
        rewrite H0 in Hlookup_s.
        destruct Hwf as [_ [_ [_ [_ [Hlen _]]]]]. (* gives dom sΓ = dom (vars rΓ) *)
        rewrite H0 in Hlookup_r.                  (* y = dom sΓ *)
        rewrite Hlen in Hlookup_r.                (* now y = dom (vars rΓ) *)
        rewrite runtime_getVal_last in Hlookup_r. (* yields Some Null_a *)
        discriminate.
      --

        assert (H_bound : y < dom sΓ).
        {
          (* Use the lookup success in the extended list *)
          apply static_getType_dom in Hlookup_s.
          rewrite length_app in Hlookup_s.
          simpl in Hlookup_s.
          assert (H_x_idx : x = dom sΓ). 
          {
            inversion Htyping; subst.
            apply static_getType_not_dom in H4.
            apply static_getType_dom in H9.
            rewrite length_app in H9; simpl in H9.
            lia.
          }
          
          (* With x = length sΓ and x <> y, we know y < length sΓ *)
          lia. 
        }

        assert (Hlookup_s_old : static_getType sΓ y = Some Ty).
        {
          unfold static_getType in *.
          rewrite nth_error_app1 in Hlookup_s; auto.
        }

        assert (Hlookup_r_old : runtime_getVal rΓ y = Some (Iot l_y)).
        {
          unfold runtime_getVal in *.
          rewrite nth_error_app1 in Hlookup_r; auto.
          destruct Hwf as [_ [_ [_ [_ [Hlen _]]]]]. (* gives dom sΓ = dom (vars rΓ) *)
          rewrite Hlen in H_bound.                (* now y = dom (vars rΓ) *)
          auto.
        }

        unfold env_respects_protected_set in Henv_respects.
        exact (Henv_respects y l_y Ty Hlookup_s_old Hlookup_r_old Hin_P).
    *
      unfold heap_respects_protected_set.
      intros l_src C anyrq vals k l_dst Hdom_src Hin_dst Hobj_src Hnth.
      unfold heap_respects_protected_set in Hheap_respects.
      exact (Hheap_respects l_src C anyrq vals k l_dst Hdom_src Hin_dst Hobj_src Hnth).
  - (* var assign *)
    split.
    + reflexivity.
    + (* Invariant preserved *)
      inversion Htyping; subst.
      have Hconfined_copy := Hconfined.
      unfold confinement_invariant_precise.
      unfold confinement_invariant_precise in Hconfined.
      destruct Hconfined as [Henv_respects Hheap_respects].
      rename sΓ' into sΓ.
      split.
      *
        unfold env_respects_protected_set.
        intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
        unfold runtime_getVal in Hlookup_r.
        simpl in Hlookup_r.
        destruct (Nat.eq_dec y x) as [Heq_y | Hneq_y].
        -- (* y = x *)
        subst y.
        rewrite H9 in Hlookup_s.
        inversion Hlookup_s; subst Ty.
        apply runtime_getVal_dom in H.
        rewrite update_same in Hlookup_r; auto.
        injection Hlookup_r as Heq_v2.
        subst v2.
        assert (Hsafe_e : is_safe_mode (sqtype Te)).
        {
          admit.
          (* eapply expr_eval_to_protected_implies_safe_type; eauto. *)
        }
        eapply subtype_safe_implies_safe; eauto.
        -- (* y <> x *)
        rewrite update_diff in Hlookup_r; auto.
        unfold env_respects_protected_set in Henv_respects.
        exact (Henv_respects y l_y Ty Hlookup_s Hlookup_r Hin_P).
      * 
        unfold heap_respects_protected_set.
        intros l_src C anyrq vals k l_dst Hdom_src Hin_dst Hobj_src Hnth.
        unfold heap_respects_protected_set in Hheap_respects.
        exact (Hheap_respects l_src C anyrq vals k l_dst Hdom_src Hin_dst Hobj_src Hnth).
  - (* field write *)
    split.
    +
    {
      unfold protected_locset.
      apply Ensembles.Extensionality_Ensembles.
      unfold Ensembles.Same_set, Ensembles.Included.
      split; intros l_target Hreach.
      - (* Forward direction: h → update_field h *)

        induction Hreach.
        + (* reachable_abs_heap *)
          apply reachable_abs_heap.
          rewrite update_field_length.
          exact H3.
        +
        {
          destruct (Nat.eq_dec l0 loc_x) as [Hl0 | Hl0].
          - subst l0.
            destruct (Nat.eq_dec k f) as [Hkf | Hkf].
            + (* k = f: you already proved this impossible; reuse that contradiction here *)
              exfalso. (* your existing contradiction proof *)
              subst k.
              (* From H6/H7: field f is RDM/Imm and RDA/Final (protected) *)
              (* But from typing: field f must be writable *)
              inversion Htyping; subst.
              (* H13: sf_assignability_rel CT C f a for some writable a *)
              unfold wf_r_config in Hwf.
              destruct Hwf as [_ [_ [Hrenv [_ [Hlen Htypable]]]]].

              (* Get receiver info *)
              destruct Hrenv as [_ [Hreceiver _]].
              destruct Hreceiver as [iot [Hget_iot Hiot_dom]].

              (* Get receiver mutability *)
              assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
              {
                eapply receiver_mutability_exists_from_bound; eauto.
              }
              destruct HOutterReceiverMutability as [qcontext Hqcontext].

              (* Apply typability correspondence *)
              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in H12.
                exact H12.
              }
              specialize (Htypable iot qcontext Hget_iot Hqcontext x Hx_dom Tx H12).
              rewrite H in Htypable.

              (* Htypable now gives us wf_r_typable for the location *)
              unfold wf_r_typable in Htypable.
              unfold r_type in Htypable.
              rewrite H0 in Htypable.
              rewrite H4 in H0.

              (* Htypable now contains: base_subtype CT (sctype Tx) C *)
              destruct Htypable as [Hbase Hqualifier].
              assert (rctype (rt_type o) = C).
              {
                inversion H0.
                easy.
              }
              rewrite H8 in Hbase.
              destruct H7 as [Hrda | Hfinal].
              ** (* RDA case *)
                unfold sf_assignability_rel in *.
                destruct H18 as [fdef_write [Hlookup_write Hassign_write]].
                destruct Hrda as [fdef_prot [Hlookup_prot Hassign_prot]].

                assert (fdef_prot = fdef_write).
                {
                  eapply field_lookup_deterministic_rel; eauto.
                  eapply field_inheritance_subtyping; eauto.
                }
                subst fdef_prot.
                rewrite Hassign_prot in Hassign_write.
                rewrite <- Hassign_write in H21.
                unfold vpa_assignability in H21.
                destruct (sqtype Tx) eqn: Hsqtypex; try discriminate.
                unfold confinement_invariant_precise in Hconfined.
                destruct Hconfined as [Henv_respects Hheap_respects].
                unfold env_respects_protected_set in Henv_respects.
                specialize (Henv_respects x loc_x Tx H12 H).
                assert (Hin_locx : Ensembles.In Loc (protected_locset CT h loc_x) loc_x).
                {
                  unfold protected_locset.
                  apply reachable_abs_heap.
                  apply runtime_getObj_dom in H4.
                  exact H4.
                }
                specialize (Henv_respects Hin_locx).
                unfold is_safe_mode in Henv_respects.
                destruct Henv_respects as [Hrd | Hlost].
                --- rewrite Hrd in Hsqtypex. discriminate.
                --- rewrite Hlost in Hsqtypex. discriminate.
              ** (* Final case *)
                unfold sf_assignability_rel in *.
                destruct H18 as [fdef_write [Hlookup_write Hassign_write]].
                destruct Hfinal as [fdef_prot [Hlookup_prot Hassign_prot]].
                assert (fdef_prot = fdef_write).
                {
                  eapply field_lookup_deterministic_rel; eauto.
                  eapply field_inheritance_subtyping; eauto.
                }
                subst fdef_prot.
                rewrite Hassign_prot in Hassign_write.
                rewrite <- Hassign_write in H21.
                unfold vpa_assignability in H21.
                destruct (sqtype Tx); try discriminate.
            + (* k ≠ f: protected field unchanged *)
              assert (Hloc_dom : loc_x < dom h) by (apply runtime_getObj_dom in H0; exact H0).
              apply reachable_abs_step with
                  (any := any) (C := C) (vals := update f val_y vals) (k := k).
              * rewrite update_field_length; exact H3.            (* dom unchanged *)
              * unfold update_field; rewrite H0; simpl.
                rewrite runtime_getObj_update_same. exact Hloc_dom.
                rewrite H0 in H4. inversion H4. easy.
              *  
                rewrite update_diff. symmetry. exact Hkf. exact H5. (* nth_error preserved *)
              * exact H6.
              * exact H7.

          - (* l0 ≠ loc_x: object untouched by the update *)
            apply reachable_abs_step with (any := any) (C := C) (vals := vals) (k := k).
            unfold update_field.
            destruct (runtime_getObj h loc_x); try exact H3.
            + rewrite update_length. exact H3.
            + 
              unfold update_field.
              destruct (runtime_getObj h loc_x).
              rewrite runtime_getObj_update_diff.
              symmetry. exact Hl0.
              exact H4.
              exact H4.
            + exact H5.
            + exact H6.
            + exact H7. 
        }
        + (* reachable_abs_trans *)
          eapply reachable_abs_trans.
          eapply reachable_abs_trans; eauto.
          * exact (IHHreach1 Hdom_root Hconfined).
          *
          apply IHHreach2.
          -- apply reachable_abs_dom in Hreach1. exact Hreach1.
          -- eapply confinement_invariant_weaken; eauto.
          * 
          apply reachable_abs_heap.
          apply reachable_abs_dom in Hreach2. 
          rewrite update_field_length.
          exact Hreach2.

      - (* Backward direction: update_field h → h *)
        induction Hreach.
        + (* reachable_abs_heap *)
          apply reachable_abs_heap.
          rewrite update_field_length in H3.
          exact H3.
        + (* reachable_abs_step *)
          destruct (Nat.eq_dec l0 loc_x) as [Heq | Hneq].
          *
            subst loc_x.
            inversion Htyping; subst.
            specialize (runtime_getObj_Some h l0 Hdom_root) as [C' [values' Hhsome]].
            remember (update_field h l0 f val_y) as h'.
            destruct (Nat.eq_dec k f) as [Heq_k | Hneq_k].
            --
              exfalso. (* your existing contradiction proof *)
              subst k.
              (* From H6/H7: field f is RDM/Imm and RDA/Final (protected) *)
              (* But from typing: field f must be writable *)
              (* H13: sf_assignability_rel CT C f a for some writable a *)
              unfold wf_r_config in Hwf.
              destruct Hwf as [_ [_ [Hrenv [_ [Hlen Htypable]]]]].

              (* Get receiver info *)
              destruct Hrenv as [_ [Hreceiver _]].
              destruct Hreceiver as [iot [Hget_iot Hiot_dom]].

              (* Get receiver mutability *)
              assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
              {
                eapply receiver_mutability_exists_from_bound; eauto.
              }
              destruct HOutterReceiverMutability as [qcontext Hqcontext].

              (* Apply typability correspondence *)
              assert (Hx_dom : x < dom sΓ').
              {
                apply static_getType_dom in H12.
                exact H12.
              }
              specialize (Htypable iot qcontext Hget_iot Hqcontext x Hx_dom Tx H12).
              rewrite H in Htypable.

              (* Htypable now gives us wf_r_typable for the location *)
              unfold wf_r_typable in Htypable.
              unfold r_type in Htypable.
              rewrite H0 in Htypable.
              (* rewrite H4 in H0. *)

              (* Htypable now contains: base_subtype CT (sctype Tx) C *)
              destruct Htypable as [Hbase Hqualifier].
              have Hh'some : exists vals', runtime_getObj h' l0 = Some {| rt_type := C'; fields_map := vals' |}.
              {
                eapply runtime_preserves_r_type_heap with (h := h) (h' := h')(vals := values'); eauto.
              }
              assert (rctype (rt_type o) = C).
              {
                clear - Hh'some H4 H0 Hhsome.
                rewrite H0 in Hhsome.
                destruct Hh'some as [vals'' Hh'some].
                rewrite H4 in Hh'some.
                inversion Hh'some; subst.
                inversion Hhsome; subst.
                easy.
              }
              rewrite H8 in Hbase.
              destruct H7 as [Hrda | Hfinal].
              ** (* RDA case *)
                unfold sf_assignability_rel in *.
                destruct H18 as [fdef_write [Hlookup_write Hassign_write]].
                destruct Hrda as [fdef_prot [Hlookup_prot Hassign_prot]].

                assert (fdef_prot = fdef_write).
                {
                  eapply field_lookup_deterministic_rel; eauto.
                  eapply field_inheritance_subtyping; eauto.
                }
                subst fdef_prot.
                rewrite Hassign_prot in Hassign_write.
                rewrite <- Hassign_write in H21.
                unfold vpa_assignability in H21.
                destruct (sqtype Tx) eqn: Hsqtypex; try discriminate.
                unfold confinement_invariant_precise in Hconfined.
                destruct Hconfined as [Henv_respects Hheap_respects].
                unfold env_respects_protected_set in Henv_respects.
                specialize (Henv_respects x l0 Tx H12 H).
                assert (Hin_locx : Ensembles.In Loc (protected_locset CT h l0) l0).
                {
                  unfold protected_locset.
                  apply reachable_abs_heap.
                  exact Hdom_root.
                }
                specialize (Henv_respects Hin_locx).
                unfold is_safe_mode in Henv_respects.
                destruct Henv_respects as [Hrd | Hlost].
                --- rewrite Hrd in Hsqtypex. discriminate.
                --- rewrite Hlost in Hsqtypex. discriminate.
              ** (* Final case *)
                unfold sf_assignability_rel in *.
                destruct H18 as [fdef_write [Hlookup_write Hassign_write]].
                destruct Hfinal as [fdef_prot [Hlookup_prot Hassign_prot]].
                assert (fdef_prot = fdef_write).
                {
                  eapply field_lookup_deterministic_rel; eauto.
                  eapply field_inheritance_subtyping; eauto.
                }
                subst fdef_prot.
                rewrite Hassign_prot in Hassign_write.
                rewrite <- Hassign_write in H21.
                unfold vpa_assignability in H21.
                destruct (sqtype Tx); try discriminate.
            --
              have Hl1_dom : l1 < dom h.
              {
                subst h'.
                rewrite update_field_length in H3.
                exact H3.
              }

              eapply reachable_abs_step with (vals := values')(any := any)(C := C)(k := k); auto.
              have Hh'some : exists vals', runtime_getObj h' l0 = Some {| rt_type := C'; fields_map := vals' |}.
              {
                eapply runtime_preserves_r_type_heap with (h := h) (h' := h')(vals := values'); eauto.
              }
              destruct Hh'some as [vals'' Hh'some].
              rewrite Hh'some in H4.
              inversion H4; subst; auto.
              have Hh'some : exists vals', runtime_getObj h' l0 = Some {| rt_type := C'; fields_map := vals' |}.
              {
                eapply runtime_preserves_r_type_heap with (h := h) (h' := h')(vals := values'); eauto.
              }
              destruct Hh'some as [vals'' Hh'some].
              rewrite Hh'some in H4.
              inversion H4; subst.
              clear - Hh'some Hhsome H5 Hneq_k Hdom_root.
              unfold update_field in Hh'some.
              rewrite Hhsome in Hh'some.
              simpl in Hh'some.
              rewrite <- H5.
              rewrite runtime_getObj_update_same in Hh'some; auto.
              injection Hh'some as H_vals_eq.
              rewrite <- H_vals_eq.
              rewrite nth_error_update_neq; auto.
          *
            apply reachable_abs_step with (any := any) (C := C) (vals := vals) (k := k).
            -- rewrite update_field_length in H3. exact H3.
            -- (* Show runtime_getObj preserved for different location *)
              unfold update_field in H4.
              destruct (runtime_getObj h loc_x) eqn:Hgetx.
              ++ rewrite runtime_getObj_update_diff in H4; auto.
              ++ exact H4.
            -- exact H5.
            -- exact H6.
            -- exact H7.
        + (* reachable_abs_trans *)
          eapply reachable_abs_trans with (l1:=l1).
          * exact (IHHreach1 Hdom_root Hconfined).
          *
            eapply IHHreach2.
            apply reachable_abs_dom in Hreach1.
            rewrite update_field_length in Hreach1; auto.
            eapply confinement_invariant_weaken; eauto.
            exact (IHHreach1 Hdom_root Hconfined).
    }
 
    + (* Invariant preserved *)
      inversion Htyping; subst sΓ'; subst.
      unfold confinement_invariant_precise in *.
      destruct Hconfined as [Henv_respects Hheap_respects].
      split.
      *
        exact Henv_respects.
      *
        unfold heap_respects_protected_set.
        intros l_src C anyrq vals k l_dst Hdom_dst Hlsrc_new Hin_dst Hobj_src Hnth.
        unfold update_field in Hobj_src.

        (* Case split on whether l_src = loc_x *)
        destruct (Nat.eq_dec l_src loc_x) as [Heq | Hneq].
        -- (* Case: l_src = loc_x (the written object) *)
          subst l_src.
          simpl in Hobj_src.
          destruct (runtime_getObj h loc_x) eqn:Hobj_locx; try easy.
          (* rewrite update_field_length in Hdom_src. *)
          rewrite runtime_getObj_update_same in Hobj_src; auto.
          apply runtime_getObj_dom in Hobj_locx; auto.
          (* Now Hobj_src says that the updated object at loc_x has fields_map = update f val_y vals *)
          (* injection Hobj_src as _ Hvals'_eq. *)
          unfold heap_respects_protected_set in Hheap_respects.
          apply runtime_getObj_dom in Hobj_locx; lia.
        -- (* Case: l_src ≠ loc_x (different object) *)
          have Heq : runtime_getObj (update_field h loc_x f val_y) l_src = runtime_getObj h l_src.
          {
            unfold update_field.
            destruct (runtime_getObj h loc_x); try easy.
            eapply runtime_getObj_update_diff; auto.
          }
          rewrite Heq in Hobj_src.
          assert (dom (update_field h loc_x f val_y) = dom h).
          {
            apply update_field_length.
          }
          (* rewrite <- H3 in Hdom_src. *)
          exact (Hheap_respects l_src C anyrq vals k l_dst Hdom_dst Hlsrc_new Hin_dst Hobj_src Hnth).
  - (* new *)
    split.
    +
    unfold protected_locset.
    apply Ensembles.Extensionality_Ensembles.
    unfold Ensembles.Same_set, Ensembles.Included.
    split; intros l_target Hreach.
    *
      induction Hreach.
      --
        apply reachable_abs_heap.
        rewrite length_app.
        lia.
      --
        eapply reachable_abs_step with (C := C) (k := k) (vals := vals0) (any := any); eauto.
        rewrite length_app. lia.
        eapply runtime_getObj_app_left.
        apply runtime_getObj_dom in H3; auto.
        exact H3.
      --
        eapply reachable_abs_trans.
        ---
           apply IHHreach1.
           +++ exact Hdom_root.
           +++ exact Hconfined.
        ---
           apply IHHreach2.
           +++ apply reachable_abs_dom in Hreach1. exact Hreach1.
           +++ eapply confinement_invariant_weaken. exact Hreach1. exact Hconfined.
    *
    induction Hreach.
    --
      apply reachable_abs_heap.
      exact Hdom_root.
    -- 
      eapply reachable_abs_step with (C := C) (k := k) (vals := vals0) (any := any); eauto.
      assert (Hobj_l0_h: runtime_getObj h l0 =
      Some
      {|
      rt_type :=
      {|
      rqtype := any; rctype :=
      C
      |};
      fields_map := vals0
      |}).
      {
        unfold runtime_getObj in *.
        rewrite nth_error_app1 in H3.
        --- exact Hdom_root.
        --- (* Prove l0 < length h *)
          exact H3.
      }
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [HwfHeap [_ [_ [_ Hcorr]]]]].
      unfold wf_heap in HwfHeap.
      specialize (HwfHeap l0 Hdom_root).
      unfold wf_obj in HwfHeap.
      rewrite Hobj_l0_h in HwfHeap.
      destruct HwfHeap as [Hwftype Hfields_wf].
      destruct Hfields_wf as [fieldsCollection Hfield_types].
      destruct Hfield_types as [HCollectFields Hfield_types].
      destruct Hfield_types as [Hlength Hfield_types].
      simpl in Hlength.
      have HfieldDef: exists fDef, nth_error fieldsCollection k = Some fDef.
      {
        apply nth_error_Some_exists.
        clear - H4 Hlength.
        rewrite <- Hlength.
        apply nth_error_Some.
        rewrite H4.
        discriminate.
      }
      destruct HfieldDef as [fDef HfieldDef].
      eapply Forall2_nth_error with (i := k) (a := Iot l2) (b := fDef) in Hfield_types; eauto.
      destruct (runtime_getObj h l2) eqn:Hobj_l2_h; try easy.
      apply runtime_getObj_dom in Hobj_l2_h; auto.
      unfold runtime_getObj in *.
      rewrite nth_error_app1 in H3.
      --- exact Hdom_root.
      --- (* Prove l0 < length h *)
        exact H3.
    --
      have Hreach1_orig : reachable_abs CT h l0 l2 := IHHreach1 Hdom_root Hconfined.
      have Hdom_l2 : l2 < dom h := reachable_abs_dom CT h l0 l2 Hreach1_orig.
      have Hconf_l2 : confinement_invariant_precise (protected_locset CT h l2) CT sΓ rΓ h h :=
        confinement_invariant_weaken CT sΓ rΓ h h l0 l2 Hreach1_orig Hconfined.
      have Hreach2_orig : reachable_abs CT h l2 l3 := IHHreach2 Hdom_l2 Hconf_l2.
      exact (reachable_abs_trans CT h l0 l2 l3 Hreach1_orig Hreach2_orig).   
    + (* Invariant preserved *)
      inversion Htyping; subst sΓ'; subst.
      unfold confinement_invariant_precise in *.
      destruct Hconfined as [Henv_respects Hheap_respects].
      split.
      *
        unfold env_respects_protected_set in *.
        intros y l_y Ty Hlookup_s Hlookup_r Hin_P.
        assert (rΓ <| vars := update x (Iot dom h) (vars rΓ) |> = update_r_env_value rΓ x (Iot (dom h))).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite H2 in Hlookup_r.
        destruct (Nat.eq_dec x y); subst.
        -- (* y = x *)
        rewrite runtime_getVal_update_same in Hlookup_r; auto.
        apply static_getType_dom in Hlookup_s.
        unfold wf_r_config in Hwf.
        destruct Hwf as [_ [_[_ [_ [Hlen _]]]]].
        rewrite Hlen in Hlookup_s.
        exact Hlookup_s.
        unfold protected_locset in Hin_P.
        apply reachable_abs_dom in Hin_P.
        inversion Hlookup_r; subst l_y.
        lia.
        -- (* y <> x *)
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Henv_respects; eauto.
      *
        unfold heap_respects_protected_set.
        intros l_src C anyrq vals0 k l_dst Hdom_dst Hlsrc_new Hin_dst Hobj_src Hnth.
        (* Split into cases: is l_src the new object or an old object? *)
        destruct (Nat.eq_dec l_src (dom h)) as [Heq_new | Hne_old].
        -- (* Case: l_src = dom h (the newly created object) *)
          (* subst l_src. *)
          (* The new object is at the end of the heap *)
          rewrite Heq_new in Hobj_src.
          have Hobj_src_copy := Hobj_src.
          rewrite runtime_getObj_last in Hobj_src; auto.
          injection Hobj_src as _ Hfields_eq.
          subst vals0.
          subst c.
          have hwf_constructor: wf_constructor CT C consig.
          {
            eapply constructor_lookup_wf; eauto.
            destruct Hwf as [Hclasstable [_ [_ [_ [Hlen Htypable]]]]]; auto.
            unfold constructor_sig_lookup in H10.
            unfold constructor_def_lookup in H10.
            destruct (find_class CT C) eqn: HfindC; try discriminate.
            apply find_class_dom in HfindC; auto.
          }
          remember (h ++
          [{|
          rt_type :=
          {| rqtype := vpa_mutabilty_object_creation qthisr (cqualifier consig);
          rctype := C |};
          fields_map := vals
          |}]) as h'.
          have hlsrc_domneq : l_src >= dom h by lia.
          unfold wf_constructor in hwf_constructor.
          destruct hwf_constructor as [Hbound [Hwf_constructor_params Hparam_count]].
          destruct Hparam_count as [HfieldCollection HparameterFieldSubtyping].
          destruct HparameterFieldSubtyping as [HCollectFields HparameterFieldSubtyping].
          destruct HparameterFieldSubtyping as [Hlength HparameterFieldSubtyping].
          unfold env_respects_protected_set in Henv_respects.
          assert (Hdomeq: dom vals = dom argtypes).
          {
            apply runtime_lookup_list_preserves_length in H0.
            apply static_getType_list_preserves_length in H8.
            rewrite <- H0 in H8.
            symmetry.
            exact H8.
          }
          assert (Hk_bound : k < List.length argtypes).
          {
            assert (k < List.length vals).
            apply nth_error_Some.
            rewrite Hnth.
            discriminate.
            rewrite <- Hdomeq.
            exact H2.
          }
          assert (Harg_type : exists argtype, nth_error argtypes k = Some argtype).
          {
            apply nth_error_Some_exists.
            exact Hk_bound.
          }
          destruct Harg_type as [argtype Hargtype].
          assert (HargtypeFromsEnv :
            exists iArgInSenv,
              nth_error sΓ iArgInSenv = Some argtype
          /\ nth_error ys k = Some iArgInSenv).
          {
            destruct (static_getType_list_nth_zs sΓ ys argtypes k argtype H8 Hargtype)
              as [j [Hzs_j Hst_j]].
            exists j.
            split.
            - (* from static_getType to nth_error sΓ' *)
              unfold static_getType in Hst_j; exact Hst_j.
            - (* keep the zs fact *)
              exact Hzs_j.
          }
          destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

          assert (Hi'dom : iArgInSenv < dom sΓ).
          {
            apply nth_error_Some.
            rewrite HargtypeFromsEnv; discriminate.
          }
          assert (HargtypeFromrEnv :
                    nth_error (vars rΓ) iArgInSenv = Some (Iot l_dst)).
          {
            destruct (runtime_lookup_list_nth_zs rΓ ys vals k (Iot l_dst) H0 Hnth)
              as [j [Hzs_j Hget_j]].
            assert (HiEq : iArgInSenv = j).
            {
              (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
              rewrite Hzs_iArg in Hzs_j.
              inversion Hzs_j; reflexivity.
            }
            subst iArgInSenv.
            unfold runtime_getVal in Hget_j.
            exact Hget_j.
          } 
          have Hnth_param : exists param_type, nth_error (cparams consig) k = Some param_type.
          {
            apply Forall2_length in H16.
            apply nth_error_Some_exists.
            rewrite <- H16.
            exact Hk_bound.
          }
          destruct Hnth_param as [param_type Hparam_type].
          specialize (Henv_respects iArgInSenv l_dst argtype HargtypeFromsEnv HargtypeFromrEnv Hin_dst).
          eapply Forall2_nth_error in H16; eauto.
          assert (is_safe_mode (sqtype param_type)).
          {
            eapply subtype_safe_implies_safe with (CT:= CT) (T_sub := argtype); eauto.
          }
          have [fdef Hfdef] : exists fdef, nth_error HfieldCollection k = Some fdef.
          {
            apply nth_error_Some_exists.
            apply nth_error_Some in Hk_bound.
            rewrite <- Hlength.
            apply nth_error_Some.
            rewrite Hparam_type; discriminate.
          }
          apply Forall2_nth_error with (i:=k) (a:=param_type) (b:=fdef) in HparameterFieldSubtyping; auto.
          unfold vpa_mutabilty_constructor_fld in HparameterFieldSubtyping.
          destruct (mutability (ftype fdef)) eqn:Hfld_mut;
          exists fdef;
          split;
          unfold sf_def_rel;
          try exact (FL_Found CT C HfieldCollection k fdef HCollectFields Hfdef).
          all: destruct (cqualifier consig) eqn: Hconsig_qual.
          all: unfold is_safe_mode in H2;
          apply qualified_type_subtype_q_subtype in HparameterFieldSubtyping;
          destruct H2 as [Hrd | Hlost].
          all: try rewrite Hrd in HparameterFieldSubtyping; try inversion HparameterFieldSubtyping; try discriminate.
          all: try rewrite Hlost in HparameterFieldSubtyping; try inversion HparameterFieldSubtyping; try discriminate.
          all: try exact Hfld_mut.
        -- (* Case: l_src < dom h (old object, not the new one) *)
          (* Heap grew but old objects unchanged *)
          remember ({| rt_type := {| rqtype := vpa_mutabilty_object_creation qthisr (cqualifier consig); rctype := c |}; fields_map := vals |}) as newobject.
          assert (l_src < dom h).
          {
            (* Extract l_src < dom (h ++ [new_obj]) from Hobj_src *)
            have Hdom_appended : l_src < dom (h ++ [newobject]).
            {
              eapply runtime_getObj_dom; exact Hobj_src.
            }
            (* Now simplify: dom (h ++ [obj]) = dom h + 1 *)
            rewrite length_app in Hdom_appended.
            simpl in Hdom_appended.
            (* l_src < dom h + 1 and l_src <> dom h imply l_src < dom h *)
            lia.
          }
          (* Now show that old objects weren't modified *)
          have Hobj_src_old : runtime_getObj h l_src = runtime_getObj (h ++ [newobject]) l_src.
          {
            eapply runtime_getObj_app_left_equal.
            exact H2.
          }
          rewrite <- Hobj_src_old in Hobj_src.
          exact (Hheap_respects l_src C anyrq vals0 k l_dst Hdom_dst Hlsrc_new Hin_dst Hobj_src Hnth).
  - (* call *)
    inversion Htyping; subst sΓ'; subst.
    have Hwfcopy := Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [Henv_len Htypable]]]]].
    unfold confinement_invariant_precise in *.
    destruct Hconfined as [Henv_respects Hheap_respects].
    specialize (IHHeval Hdom_root (eq_refl)).
    destruct H1 as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    inversion mdeflookup; revert getmbody; subst; intro getmbody.
    +
    assert (Hwfmethod: wf_method CT cy mdef).
    {
      eapply method_lookup_wf_class; eauto.
      eapply r_basetype_in_dom; eauto.
      unfold gget_method in H3.
      apply find_some in H3.
      destruct H3.
      exact H2.
    }
    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      (* Method inner config wellformed.*)
        have Hclass := Hclasstable.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobjexist [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobjexist.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed *)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values; eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.
        (* subst.
        assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        } *)

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom.
        (* assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        } *)
        eapply method_sig_wf_parameters_by_find; eauto.
        assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom.

        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H20.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.

        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H0.
        rewrite H4.
        rewrite <- H20.
        exact H11.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        destruct i as [|i'].

        (* Reciever index - 0 *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.

        rewrite Hobjy.
        simpl.
        split.

        (* Base type subtyping *)
        rewrite Hmsigeq.
        apply qualified_type_subtype_base_subtype in H19.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H19.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          apply qualified_type_subtype_q_subtype in H19.
          specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
          apply get_this_qualified_type_nth_error in H12.
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
          rewrite <- Hvars in HOutterReceiverAddr.
          apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
          rewrite HOutterReceiverAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
          destruct Hcorrcopy as [_ Houtter_qualifier_typable].

          assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
          {
            unfold r_muttype in HOutterReceiverMutabilityType.
            rewrite Houtterobj in HOutterReceiverMutabilityType.
            simpl in HOutterReceiverMutabilityType.
            inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
            reflexivity.
          }
          subst OutterReceiverMutability.

          assert (ly = ι). 
          {
            rewrite HeqrΓmethodinit in HreceiverAddr.
            unfold get_this_var_mapping in HreceiverAddr.
            simpl in HreceiverAddr.
            inversion HreceiverAddr; reflexivity.
          }
          subst ι.

          assert (r_muttype h ly = Some rq_obj).
          {
            unfold r_muttype.
            rewrite Hobjy.
            simpl.
            reflexivity.
          }

          assert (rq_obj = qinner).
          {
            rewrite H0 in Hqcontext.
            inversion Hqcontext; subst qinner.
            reflexivity.
          }
          subst rq_obj.

          unfold qualifier_typable_context.
          unfold qualifier_typable_context in HyQualifierTypablility.
          unfold qualifier_typable_context in Houtter_qualifier_typable.
          unfold vpa_mutabilty_rs.
          unfold vpa_mutabilty_rs in HyQualifierTypablility.
          unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
          unfold vpa_mutabilty_tt in H19.
          rewrite <- Hmsigeq in H19.

          destruct qinner eqn:HInnerReceiverMutability;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
          try trivial.
          all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          try trivial.
          all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
          try rewrite HTyStaticMutability in H19;
          simpl in H19;
          try rewrite HMethodReceiverDeclaredType in H19;
          try inversion H19; try trivial.
          all: try inversion H19; try easy.
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H18.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H20.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H20.
              apply nth_error_Some.
              intros Hnone.
              rewrite Hnth in Hnone.
              discriminate.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|contradiction].
              apply runtime_getObj_dom in Hargobjloc.
              exact Hargobjloc.
            }
            destruct Harg_type as [argtype Hargtype].
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|apply runtime_getObj_not_dom in Hargobjloc; lia].
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H11 Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ).
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }
            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            have Hcorrcopy_2 := Hcorrcopy.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy.
            rewrite HargtypeFromrEnv in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            rewrite Hargobjloc in Hcorrcopy.
            destruct Hcorrcopy as [Harg_basesubtype Harg_qualifiertypability].
            split.

            (* base subtype *)
            rewrite nth_error_cons_succ in Hnth.
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_base_subtype in H20.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H20.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_q_subtype in H20.
            rewrite sq_vpa_tt_eq_qq in H20.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H12.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H12).
            rewrite <- Hvars in Hget_iot.
            apply get_this_var_mapping_runtime_getVal in Hget_iot.
            rewrite Hget_iot in Hcorrcopy_2.
            unfold wf_r_typable in Hcorrcopy_2.
            unfold r_type in Hcorrcopy_2.
            destruct (runtime_getObj h iot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy_2 as [_ HOutterReceiverQualifierTypablility].
            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              clear - Houtterobj HOutterReceiverMutabilityType HOutterReceiverAddr Hget_iot Hvars.
              rewrite <- Hvars in HOutterReceiverAddr.
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
              rewrite Hget_iot in HOutterReceiverAddr.
              inversion HOutterReceiverAddr; subst lOutterReceiver.
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; reflexivity.
            }
            subst OutterReceiverMutability.
            assert (ι = ly).
            {
              unfold get_this_var_mapping in HreceiverAddr.
              rewrite HeqrΓmethodinit in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.
            assert(rq_obj = qinner).
            {
              unfold r_muttype in Hqcontext.
              rewrite Hobjy in Hqcontext.
              simpl in Hqcontext.
              inversion Hqcontext.
              easy.
            }
            subst rq_obj.
            clear - H20 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H20;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H20.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H20 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    specialize (IHHeval Heval sΓmethodend sΓmethodinit).
    assert (HenvInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z Tz Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      - simpl in Hlookup_s, Hlookup_r.
      injection Hlookup_s as <-. injection Hlookup_r as <-.
      unfold is_safe_mode.
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Henv_respects.
        specialize (Henv_respects y ly Ty H10 H Hin_P).
        exact Henv_respects.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutabilty_tt.
      apply qualified_type_subtype_q_subtype in H19.
      clear - Hty_safe H19.
      unfold vpa_mutabilty_tt in H19.
      destruct Hty_safe as [HRd | HLost].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in H19.
        simpl in H19.
        inversion H19; easy.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in H19.
        simpl in H19.
        inversion H19; easy.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        have Hnth_param_type : nth_error (mparams (msignature mdef)) z' = Some Tz.
        {
          simpl in Hlookup_s.
          easy.
        }

        have Hnth_param_val : nth_error vals z' = Some (Iot l_z).
        {
          simpl in Hlookup_r.
          easy.
        }
        assert (Hi'_bound : z' < List.length argtypes).
        {
          apply Forall2_length in H20.
          rewrite <- Hsigeq in H20.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H20 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H20; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Henv_respects.
        apply adapated_subtype_safe_implies_safe in H20; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg H11 Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) H4 Hnth_param_val)
            as [j [Hzs_j Hget_j]].
          assert (HzEq : z_outter = j) by (
            rewrite Hzs_z_outter in Hzs_j;
            inversion Hzs_j; reflexivity
          ).
          subst j.
          exact Hget_j.
        }
        specialize (Henv_respects z_outter l_z T_arg HgetZ_type HgetZ_val Hin_P); auto.
    }
    assert (HMethodInnerInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit /\ heap_respects_protected_set (protected_locset CT h l_root) h h CT).
    {
      split.
      exact HenvInvariant.
      exact Hheap_respects.
    }
    specialize (IHHeval HMethodInnerInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
    specialize (IHHeval Hmethodbody_typing).
    destruct IHHeval as [Htopology Hconfinement].
    destruct Hconfinement as [Henv_respects' Hheap_respects'].
    split.
    exact Htopology.
    split.
    assert (Henv_respects'': env_respects_protected_set (protected_locset CT h l_root) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      unfold env_respects_protected_set.
      intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x z); subst.
      -- (* CASE: z = x (New Variable) *)
        assert (T_z = Tx). 
        {
          rewrite H9 in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in Henv_respects'.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        have Hdom_z : z < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        have Hlookup_r_copy := Hlookup_r.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r. lia.   (* or by exact Hdom_x *)
        inversion Hlookup_r; subst.
        specialize (Henv_respects' (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType H6 Hin_P).
        rewrite <- Hsigeq in H18.
        apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
        apply subtype_safe_implies_safe_adapted in H18; auto.
      -- (* CASE: z <> x (Old Variables) *)
      (* Just use the original invariant *)
      assert (rΓ <| vars := update x retval (vars rΓ) |> = update_r_env_value rΓ x retval).
      {
        destruct rΓ.
        reflexivity.
      }
      rewrite H2 in Hlookup_r.
      rewrite runtime_getVal_update_diff in Hlookup_r; auto.
      eapply Henv_respects; eauto.
    }
    exact Henv_respects''.
    exact Hheap_respects'.
    +
    assert (Hwfmethod: exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
    {
      eapply method_lookup_in_wellformed_inherited; eauto.
      eapply r_basetype_in_dom; eauto.
    }
    destruct Hwfmethod as [D Hwfmethod].
    destruct Hwfmethod as [ddef Hwfmethod].
    destruct Hwfmethod as [Hbasecyd [HfindD [HmdefinD Hwfmethod]]].

    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      (* Method inner config wellformed.*)
        have Hclass := Hclasstable.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobjexist [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobjexist.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed *)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values; eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        (* assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom. *)
        assert (Hparentdom: parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        exact Hparentdom. 
        eapply method_sig_wf_parameters_by_find; eauto.
        assert (Hparentdom: parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        exact Hparentdom. 
        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H20.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.

        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H0.
        rewrite H4.
        rewrite <- H20.
        exact H11.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        destruct i as [|i'].

        (* Reciever index - 0 *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.

        rewrite Hobjy.
        simpl.
        split.

        (* Base type subtyping *)
        rewrite Hmsigeq.
        apply qualified_type_subtype_base_subtype in H19.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H19.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          apply qualified_type_subtype_q_subtype in H19.
          specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
          apply get_this_qualified_type_nth_error in H12.
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
          rewrite <- Hvars in HOutterReceiverAddr.
          apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
          rewrite HOutterReceiverAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
          destruct Hcorrcopy as [_ Houtter_qualifier_typable].

          assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
          {
            unfold r_muttype in HOutterReceiverMutabilityType.
            rewrite Houtterobj in HOutterReceiverMutabilityType.
            simpl in HOutterReceiverMutabilityType.
            inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
            reflexivity.
          }
          subst OutterReceiverMutability.

          assert (ly = ι). 
          {
            rewrite HeqrΓmethodinit in HreceiverAddr.
            unfold get_this_var_mapping in HreceiverAddr.
            simpl in HreceiverAddr.
            inversion HreceiverAddr; reflexivity.
          }
          subst ι.

          assert (r_muttype h ly = Some rq_obj).
          {
            unfold r_muttype.
            rewrite Hobjy.
            simpl.
            reflexivity.
          }

          assert (rq_obj = qinner).
          {
            rewrite H0 in Hqcontext.
            inversion Hqcontext; subst qinner.
            reflexivity.
          }
          subst rq_obj.

          unfold qualifier_typable_context.
          unfold qualifier_typable_context in HyQualifierTypablility.
          unfold qualifier_typable_context in Houtter_qualifier_typable.
          unfold vpa_mutabilty_rs.
          unfold vpa_mutabilty_rs in HyQualifierTypablility.
          unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
          unfold vpa_mutabilty_tt in H19.
          rewrite <- Hmsigeq in H19.

          destruct qinner eqn:HInnerReceiverMutability;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
          try trivial.
          all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          try trivial.
          all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
          try rewrite HTyStaticMutability in H19;
          simpl in H19;
          try rewrite HMethodReceiverDeclaredType in H19;
          try inversion H19; try trivial.
          all: try inversion H19; try easy.
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H18.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H20.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H20.
              apply nth_error_Some.
              intros Hnone.
              rewrite Hnth in Hnone.
              discriminate.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|contradiction].
              apply runtime_getObj_dom in Hargobjloc.
              exact Hargobjloc.
            }
            destruct Harg_type as [argtype Hargtype].
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|apply runtime_getObj_not_dom in Hargobjloc; lia].
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H11 Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ).
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }
            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            have Hcorrcopy_2 := Hcorrcopy.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy.
            rewrite HargtypeFromrEnv in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            rewrite Hargobjloc in Hcorrcopy.
            destruct Hcorrcopy as [Harg_basesubtype Harg_qualifiertypability].
            split.

            (* base subtype *)
            rewrite nth_error_cons_succ in Hnth.
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_base_subtype in H20.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H20.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_q_subtype in H20.
            rewrite sq_vpa_tt_eq_qq in H20.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H12.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H12).
            rewrite <- Hvars in Hget_iot.
            apply get_this_var_mapping_runtime_getVal in Hget_iot.
            rewrite Hget_iot in Hcorrcopy_2.
            unfold wf_r_typable in Hcorrcopy_2.
            unfold r_type in Hcorrcopy_2.
            destruct (runtime_getObj h iot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy_2 as [_ HOutterReceiverQualifierTypablility].
            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              clear - Houtterobj HOutterReceiverMutabilityType HOutterReceiverAddr Hget_iot Hvars.
              rewrite <- Hvars in HOutterReceiverAddr.
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
              rewrite Hget_iot in HOutterReceiverAddr.
              inversion HOutterReceiverAddr; subst lOutterReceiver.
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; reflexivity.
            }
            subst OutterReceiverMutability.
            assert (ι = ly).
            {
              unfold get_this_var_mapping in HreceiverAddr.
              rewrite HeqrΓmethodinit in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.
            assert(rq_obj = qinner).
            {
              unfold r_muttype in Hqcontext.
              rewrite Hobjy in Hqcontext.
              simpl in Hqcontext.
              inversion Hqcontext.
              easy.
            }
            subst rq_obj.
            clear - H20 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H20;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H20.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H20 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    specialize (IHHeval Heval sΓmethodend sΓmethodinit).
    assert (HenvInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z Tz Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      - simpl in Hlookup_s, Hlookup_r.
      injection Hlookup_s as <-. injection Hlookup_r as <-.
      unfold is_safe_mode.
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Henv_respects.
        specialize (Henv_respects y ly Ty H10 H Hin_P).
        exact Henv_respects.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutabilty_tt.
      apply qualified_type_subtype_q_subtype in H19.
      clear - Hty_safe H19.
      unfold vpa_mutabilty_tt in H19.
      destruct Hty_safe as [HRd | HLost].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in H19.
        simpl in H19.
        inversion H19; easy.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in H19.
        simpl in H19.
        inversion H19; easy.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        have Hnth_param_type : nth_error (mparams (msignature mdef)) z' = Some Tz.
        {
          simpl in Hlookup_s.
          easy.
        }

        have Hnth_param_val : nth_error vals z' = Some (Iot l_z).
        {
          simpl in Hlookup_r.
          easy.
        }
        assert (Hi'_bound : z' < List.length argtypes).
        {
          apply Forall2_length in H20.
          rewrite <- Hsigeq in H20.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H20 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H20; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Henv_respects.
        apply adapated_subtype_safe_implies_safe in H20; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg H11 Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) H4 Hnth_param_val)
            as [j [Hzs_j Hget_j]].
          assert (HzEq : z_outter = j) by (
            rewrite Hzs_z_outter in Hzs_j;
            inversion Hzs_j; reflexivity
          ).
          subst j.
          exact Hget_j.
        }
        specialize (Henv_respects z_outter l_z T_arg HgetZ_type HgetZ_val Hin_P); auto.
    }
    assert (HMethodInnerInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit /\ heap_respects_protected_set (protected_locset CT h l_root) h h CT).
    {
      split.
      exact HenvInvariant.
      exact Hheap_respects.
    }
    specialize (IHHeval HMethodInnerInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
    specialize (IHHeval Hmethodbody_typing).
    destruct IHHeval as [Htopology Hconfinement].
    destruct Hconfinement as [Henv_respects' Hheap_respects'].
    split.
    exact Htopology.
    split.
    assert (Henv_respects'': env_respects_protected_set (protected_locset CT h l_root) sΓ rΓ''' ).
    {
      rewrite HeqrΓ'''.
      unfold env_respects_protected_set.
      intros z l_z T_z Hlookup_s Hlookup_r Hin_P.
      destruct (Nat.eq_dec x z) eqn: Heqxz.
        --- (* CASE: z = x (New Variable) *)
        subst z.
        assert (T_z = Tx). 
        {
          rewrite H9 in Hlookup_s. 
          injection Hlookup_s as H_eq_T. subst T_z.
          reflexivity.
        }
        subst T_z.
        unfold env_respects_protected_set in Henv_respects'.
        have HGetMethodReturnType: static_getType sΓmethodend (mreturn (Syntax.mbody mdef)) = Some mbodyreturntype.
        {
          unfold static_getType; auto.
        }
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite getmbody in H6.
        have Hdom_x : x < dom (vars rΓ). 
        { 
          apply runtime_getVal_dom in Hlookup_r.
          rewrite update_length in Hlookup_r.
          exact Hlookup_r.
        }
        have Hlookup_r_copy := Hlookup_r.
        rewrite <- HeqrΓ''' in Hlookup_r_copy.
        unfold runtime_getVal in Hlookup_r.
        rewrite update_same in Hlookup_r. lia.   (* or by exact Hdom_x *)
        inversion Hlookup_r; subst.
        specialize (Henv_respects' (mreturn (Syntax.mbody mdef)) l_z mbodyreturntype HGetMethodReturnType H6 Hin_P).
        rewrite <- Hsigeq in H18.
        apply subtype_safe_implies_safe in HmethodReturnSubtype; auto.
        apply subtype_safe_implies_safe_adapted in H18; auto.
        --- (* CASE: z <> x (Old Variables) *)
        (* Just use the original invariant *)
        assert (rΓ <| vars := update x retval (vars rΓ) |> = update_r_env_value rΓ x retval).
        {
          destruct rΓ.
          reflexivity.
        }
        rewrite H2 in Hlookup_r.
        rewrite runtime_getVal_update_diff in Hlookup_r; auto.
        eapply Henv_respects; eauto.
    }
    exact Henv_respects''.
    exact Hheap_respects'.
Admitted.

Theorem deep_readonly_preservation :
  forall CT sΓ rΓ h l_root stmt rΓ' h' sΓ' l C anyrq vals vals' f
         (* 1. Initialize P based on the START state *)
         (* (HP_def : P = protected_locset CT h l_root) *)
         
         (* 2. Pre-condition: Invariant holds for P *)
         (* (Note: env_respects is trivial by def of P; heap_respects needs wf) *)
         (Hdom_root : l_root < dom h)
         (Hconfined : confinement_invariant_precise (protected_locset CT h l_root) CT sΓ rΓ h h)
         (Hwf : wf_r_config CT sΓ rΓ h)
         
         (* 3. Execution *)
         (Htyping : stmt_typing CT sΓ stmt sΓ')
         (Heval : eval_stmt OK CT rΓ h stmt OK rΓ' h')
         
    (* CONCLUSION: *)
    (* 1. The Invariant is preserved (Safety) *)
    (* confinement_invariant_precise P CT sΓ' rΓ' h' /\ *)
    
    (* 2. The Protected Set P is physically unmodified (Deep Immutability) *)
    (* (forall l C anyrq vals vals' f, *)
       (Hlocalset : Ensembles.In Loc (protected_locset CT h l_root) l)
       (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
       (Hobj' : runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals'))
       (* Only protected fields need to be equal, as discussed *)
       (* forall f,  *)
       (Hassignability : (sf_assignability_rel CT C f Final \/ sf_assignability_rel CT C f RDA)),
       nth_error vals f = nth_error vals' f.
Proof.
  intros.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent vals. 
  generalize dependent vals'.
  induction Heval; intros; subst; try discriminate.
  - (* Skip *) 
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* Local *)
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* VarAss *)
    rewrite Hobj in Hobj'.
    inversion Hobj'; subst.
    reflexivity.
  - (* FldWrite *)
    + (* Protected objects unchanged *)
    {
    (* intros l C anyrq vals vals' Hin Hobj Hobj' f0 Hprotected.   *)
    destruct (Nat.eq_dec loc_x l) as [Halias | Hno_alias].
    -
      subst loc_x.
      destruct (Nat.eq_dec f f0) as [Heq_f | Hneq_f].
      + (* Same field case: contradiction *)
        subst f0.
        (* Now: x points to l, and l ∈ P *)
        (* Strategy: Show x must be Safe, but field write requires x to be Mut → contradiction *)
        
        (* Extract x's static type from typing *)
        inversion Htyping; subst.
        (* After inversion: static_getType sΓ x = Some Tx, and sqtype Tx should allow write *)
        
        (* Unfold confinement to get env_respects_protected_set *)
        unfold confinement_invariant_precise in Hconfined.
        destruct Hconfined as [Henv_respects _].
        
        (* Apply the lemma: if x points to l ∈ P, then x is Safe *)
        have Hx_safe := mut_var_cannot_point_to_P sΓ' rΓ x Tx l (protected_locset CT h l_root) H7 H Henv_respects Hlocalset.
        
        (* But from ST_FldWrite typing, we need sqtype Tx to allow writes *)
        (* H15: vpa_assignability (sqtype Tx) a = Assignable *)
        
        (* Case on assignability *)
        apply vpa_assingability_assign_cases in H16.
        unfold wf_r_config in Hwf.
        destruct Hwf as [Hclasstable [_[Hrenv [_ [_ Htypable]]]]].
        unfold wf_renv in Hrenv.
        (* try destruct (extract_receiver_from_wf_config CT sΓ rΓ h Hwf) as [iot [qcontext [Hget_iot[Hiot_dom Hqcontext]]]]. *)
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qcontext Hqcontext].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qcontext Hget_iot Hqcontext x).
        have H7copy := H7.
        apply static_getType_dom in H7.
        unfold static_getType in H7copy.
        specialize (Htypable H7 Tx H7copy).
        rewrite H in Htypable.
        unfold wf_r_typable in Htypable.
        unfold r_type in Htypable.
        rewrite Hobj in Htypable.
        destruct Htypable as [base qualifier].
        simpl in base.
        destruct H16 as [Ha_assign | [Hx_mut Ha_rda]].
        
        ++ (* Case: a = Assignable *)
          destruct Hassignability as [HFinal | HRDA].
          * (* Case: sf_assignability_rel CT C f Final *)
          assert (Heq : Final = a).
          {
            eapply sf_assignability_consistent_subtype with (f := f) (C := C) (D := sctype Tx); eauto.
          }
          rewrite <- Heq in Ha_assign.
          discriminate Ha_assign.
          *
          assert (Heq : RDA = a).
          {
            eapply sf_assignability_consistent_subtype with (f := f) (C := C) (D := sctype Tx); eauto.
          }
          rewrite <- Heq in Ha_assign.
          discriminate Ha_assign.
        ++ (* Case: sqtype Tx = Mut ∧ a = RDA *)
          exfalso.
          apply Hx_safe.
          exact Hx_mut.
      + (* Different field case: trivial *)
        unfold update_field in Hobj'.
        rewrite H0 in Hobj'.
        simpl in Hobj'.

        (* Extract the domain bound for l *)
        assert (Hdom : l < dom h).
        {
          apply runtime_getObj_dom in H0.
          exact H0.
        }

        (* After update_field, the object at l has fields updated at f0 *)
        rewrite runtime_getObj_update_same in Hobj'; auto.

        injection Hobj' as _ Hvals'_eq.
        rewrite H0 in Hobj.
        injection Hobj as Hvals_eq.

        (* vals' is just vals with f0 updated, so f is unchanged *)
        rewrite <- Hvals'_eq.
        rewrite update_diff.
        --
         symmetry; exact Hneq_f.
        -- 
        assert (Hfields : fields_map o = vals).
        {
          rewrite Hvals_eq.
          reflexivity.
        }
        rewrite Hfields.
        reflexivity.
    -
      (* No aliasing case: trivial *)
      unfold update_field in Hobj'.
      have Heq : runtime_getObj 
        (match runtime_getObj h loc_x with
        | Some o => [loc_x ↦ o <| fields_map := update f0 val_y (fields_map o) |>] h
        | None => h
        end) l = runtime_getObj h l.
      {
        destruct (runtime_getObj h loc_x).
        - apply runtime_getObj_update_diff; auto.
        - reflexivity.
      }
      rewrite Heq in Hobj'.
      rewrite Hobj in Hobj'.
      inversion Hobj'.
      reflexivity.
    }
  - (* New *)
    (* intros l C anyrq vals0 vals' Hin Hobj Hobj' f Hprotected. *)
    unfold protected_locset in Hlocalset.

    (* Extract l < dom h from reachable_abs *)
    assert(Hl_old : l < dom h).
    {
      apply runtime_getObj_dom in Hobj.
      exact Hobj.
    }
    
    rewrite runtime_getObj_last2 in Hobj'; auto.
  - (* Call *)
    inversion Htyping; subst sΓ'; subst.
    have Hwfcopy := Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [_ Htypable]]]]].
    unfold confinement_invariant_precise in *.
    destruct Hconfined as [Henv_respects Hheap_respects].
    specialize (IHHeval Hdom_root (eq_refl)).
    destruct H1 as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    inversion mdeflookup; revert getmbody; subst; intro getmbody.
    assert (Hwfmethod: wf_method CT cy mdef).
    {
      eapply method_lookup_wf_class; eauto.
      eapply r_basetype_in_dom; eauto.
      unfold gget_method in H3.
      apply find_some in H3.
      destruct H3.
      exact H2.
    }
    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      (* Method inner config wellformed.*)
        have Hclass := Hclasstable.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobjexist [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobjexist.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed *)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values with (zs := zs) (vals0:=vals); eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom.
        (* assert (parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        } *)
        eapply method_sig_wf_parameters_by_find; eauto.
        assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom.

        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H20.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.

        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H0.
        rewrite H4.
        rewrite <- H20.
        exact H11.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        destruct i as [|i'].

        (* Reciever index - 0 *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.

        rewrite Hobjy.
        simpl.
        split.

        (* Base type subtyping *)
        rewrite Hmsigeq.
        apply qualified_type_subtype_base_subtype in H19.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H19.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          apply qualified_type_subtype_q_subtype in H19.
          specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
          apply get_this_qualified_type_nth_error in H12.
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
          rewrite <- Hvars in HOutterReceiverAddr.
          apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
          rewrite HOutterReceiverAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
          destruct Hcorrcopy as [_ Houtter_qualifier_typable].

          assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
          {
            unfold r_muttype in HOutterReceiverMutabilityType.
            rewrite Houtterobj in HOutterReceiverMutabilityType.
            simpl in HOutterReceiverMutabilityType.
            inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
            reflexivity.
          }
          subst OutterReceiverMutability.

          assert (ly = ι). 
          {
            rewrite HeqrΓmethodinit in HreceiverAddr.
            unfold get_this_var_mapping in HreceiverAddr.
            simpl in HreceiverAddr.
            inversion HreceiverAddr; reflexivity.
          }
          subst ι.

          assert (r_muttype h ly = Some rq_obj).
          {
            unfold r_muttype.
            rewrite Hobjy.
            simpl.
            reflexivity.
          }

          assert (rq_obj = qinner).
          {
            rewrite H0 in Hqcontext.
            inversion Hqcontext; subst qinner.
            reflexivity.
          }
          subst rq_obj.

          unfold qualifier_typable_context.
          unfold qualifier_typable_context in HyQualifierTypablility.
          unfold qualifier_typable_context in Houtter_qualifier_typable.
          unfold vpa_mutabilty_rs.
          unfold vpa_mutabilty_rs in HyQualifierTypablility.
          unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
          unfold vpa_mutabilty_tt in H19.
          rewrite <- Hmsigeq in H19.

          destruct qinner eqn:HInnerReceiverMutability;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
          try trivial.
          all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          try trivial.
          all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
          try rewrite HTyStaticMutability in H19;
          simpl in H19;
          try rewrite HMethodReceiverDeclaredType in H19;
          try inversion H19; try trivial.
          all: try inversion H19; try easy.
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H18.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H20.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H20.
              apply nth_error_Some.
              intros Hnone.
              rewrite Hnth in Hnone.
              discriminate.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|contradiction].
              apply runtime_getObj_dom in Hargobjloc.
              exact Hargobjloc.
            }
            destruct Harg_type as [argtype Hargtype].
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|apply runtime_getObj_not_dom in Hargobjloc; lia].
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H11 Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ).
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }
            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            have Hcorrcopy_2 := Hcorrcopy.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy.
            rewrite HargtypeFromrEnv in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            rewrite Hargobjloc in Hcorrcopy.
            destruct Hcorrcopy as [Harg_basesubtype Harg_qualifiertypability].
            split.

            (* base subtype *)
            rewrite nth_error_cons_succ in Hnth.
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_base_subtype in H20.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H20.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_q_subtype in H20.
            rewrite sq_vpa_tt_eq_qq in H20.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H12.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H12).
            rewrite <- Hvars in Hget_iot.
            apply get_this_var_mapping_runtime_getVal in Hget_iot.
            rewrite Hget_iot in Hcorrcopy_2.
            unfold wf_r_typable in Hcorrcopy_2.
            unfold r_type in Hcorrcopy_2.
            destruct (runtime_getObj h iot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy_2 as [_ HOutterReceiverQualifierTypablility].
            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              clear - Houtterobj HOutterReceiverMutabilityType HOutterReceiverAddr Hget_iot Hvars.
              rewrite <- Hvars in HOutterReceiverAddr.
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
              rewrite Hget_iot in HOutterReceiverAddr.
              inversion HOutterReceiverAddr; subst lOutterReceiver.
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; reflexivity.
            }
            subst OutterReceiverMutability.
            assert (ι = ly).
            {
              unfold get_this_var_mapping in HreceiverAddr.
              rewrite HeqrΓmethodinit in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.
            assert(rq_obj = qinner).
            {
              unfold r_muttype in Hqcontext.
              rewrite Hobjy in Hqcontext.
              simpl in Hqcontext.
              inversion Hqcontext.
              easy.
            }
            subst rq_obj.
            clear - H20 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H20;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H20.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H20 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    specialize (IHHeval Hlocalset Hassignability vals' Hobj' vals0 Hobj sΓmethodend sΓmethodinit).
    assert (HenvInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z Tz Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      - simpl in Hlookup_s, Hlookup_r.
      injection Hlookup_s as <-. injection Hlookup_r as <-.
      unfold is_safe_mode.
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Henv_respects.
        specialize (Henv_respects y ly Ty H10 H Hin_P).
        exact Henv_respects.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutabilty_tt.
      apply qualified_type_subtype_q_subtype in H19.
      clear - Hty_safe H19.
      unfold vpa_mutabilty_tt in H19.
      destruct Hty_safe as [HRd | HLost].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in H19.
        simpl in H19.
        inversion H19; easy.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in H19.
        simpl in H19.
        inversion H19; easy.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        have Hnth_param_type : nth_error (mparams (msignature mdef)) z' = Some Tz.
        {
          simpl in Hlookup_s.
          easy.
        }

        have Hnth_param_val : nth_error vals z' = Some (Iot l_z).
        {
          simpl in Hlookup_r.
          easy.
        }
        assert (Hi'_bound : z' < List.length argtypes).
        {
          apply Forall2_length in H20.
          rewrite <- Hsigeq in H20.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H20 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H20; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Henv_respects.
        apply adapated_subtype_safe_implies_safe in H20; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg H11 Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) H4 Hnth_param_val)
            as [j [Hzs_j Hget_j]].
          assert (HzEq : z_outter = j) by (
            rewrite Hzs_z_outter in Hzs_j;
            inversion Hzs_j; reflexivity
          ).
          subst j.
          exact Hget_j.
        }
        specialize (Henv_respects z_outter l_z T_arg HgetZ_type HgetZ_val Hin_P); auto.
    }
    assert (HMethodInnerInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit /\ heap_respects_protected_set (protected_locset CT h l_root) h h CT).
    {
      split.
      exact HenvInvariant.
      exact Hheap_respects.
    }
    specialize (IHHeval HMethodInnerInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
    specialize (IHHeval Hmethodbody_typing); auto.
    +
    assert (Hwfmethod: exists D ddef, base_subtype CT cy D /\ find_class CT D = Some ddef /\ In mdef (methods (body ddef)) /\ wf_method CT D mdef).
    {
      eapply method_lookup_in_wellformed_inherited; eauto.
      eapply r_basetype_in_dom; eauto.
    }
    destruct Hwfmethod as [D Hwfmethod].
    destruct Hwfmethod as [ddef Hwfmethod].
    destruct Hwfmethod as [Hbasecyd [HfindD [HmdefinD Hwfmethod]]].

    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
    remember (rΓ <| vars := update x retval (vars rΓ) |>) as rΓ'''.
    assert(Hwf_method_frame : wf_r_config CT sΓmethodinit rΓmethodinit h).
    {
      (* Method inner config wellformed.*)
        have Hclass := Hclasstable.
        unfold  wf_class_table in Hclass.
        destruct Hclass as [Hclass [Hobjexist [Hotherclasses Hcname_consistent]]].
        repeat split.
        exact Hclass.
        exact Hobjexist.
        exact Hotherclasses.
        apply Hcname_consistent.
        apply Hcname_consistent.
        exact Hheap.
        rewrite HeqrΓmethodinit.
        simpl.
        lia.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [HrEnvLen [Hreceiverval Hallvals]].
        exists ly.
        split.
        rewrite HeqrΓmethodinit.
        simpl.
        reflexivity.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjly; [|contradiction].
        apply runtime_getObj_dom in Hobjly.
        exact Hobjly.

        (* Inner runtime env is wellformed *)
        rewrite HeqrΓmethodinit.
        simpl.
        constructor.
        simpl.
        unfold runtime_getVal in H.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection H as H1_eq.
        subst v.
        unfold runtime_getVal in Hnth_y.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [_ Hallvals]].
        eapply Forall_nth_error in Hallvals; eauto.
        simpl in Hallvals.
        exact Hallvals.
        eapply runtime_lookup_list_preserves_wf_values with (zs:= zs) (vals0:=vals); eauto.

        (* Inner Static Environment's length is more than 0 *)
        rewrite HeqsΓmethodinit.
        simpl.
        lia.

        (* Inner static env's elements are wellformed typeuse *)
        rewrite HeqsΓmethodinit.
        constructor.

        (* Receiver type is well-formed *)
        eapply method_sig_wf_receiver_by_find; eauto.
        (* assert (Hcydom: cy < dom CT). {
            eapply find_class_dom; eauto.
        }
        exact Hcydom. *)
        assert (Hparentdom: parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        exact Hparentdom. 
        eapply method_sig_wf_parameters_by_find; eauto.
        assert (Hparentdom: parent < dom CT). {
          assert (cy < dom CT). {
            eapply find_class_dom; eauto.
          }
          assert (parent < cy). {
            eapply parent_implies_strict_ordering with (C:= cy) (D:=parent); eauto.
          }
          lia.
        }
        exact Hparentdom. 
        apply static_getType_list_preserves_length in H11.
        apply runtime_lookup_list_preserves_length in H4.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in H20.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.

        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        assert (msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        rewrite H0.
        rewrite H4.
        rewrite <- H20.
        exact H11.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }
        assert (HOutterReceiverAddr: exists lOutterReceiver, get_this_var_mapping (vars rΓ) = Some lOutterReceiver).
        {
          eapply get_this_exists_from_wf_r_config; eauto.
        }
        destruct HOutterReceiverAddr as [lOutterReceiver HOutterReceiverAddr].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h lOutterReceiver = Some qcontext).
        {
          eapply receiver_mutability_exists_wf_renv; eauto.
        }
        destruct HOutterReceiverMutability as [OutterReceiverMutability HOutterReceiverMutabilityType].
        have Hcorr := Htypable.
        have Hcorrcopy := Hcorr.
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty H10).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in H0.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection H0 as Hcy_eq.
        subst cy.
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        have Hrenvcopy := Hrenv.
        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot _]].
        unfold get_this_var_mapping.
        unfold gget in Hget_iot.
        destruct (vars rΓ) as [|v0 vs] eqn:Hvars; [discriminate|].

        unfold r_type in Hcorr.
        rewrite H in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
        
        assert (Hmsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        destruct i as [|i'].

        (* Reciever index - 0 *)
        simpl in Hnth.
        injection Hnth as Hsqt_eq.
        subst sqt.
        simpl.
        unfold wf_r_typable.
        unfold r_type.

        rewrite Hobjy.
        simpl.
        split.

        (* Base type subtyping *)
        rewrite Hmsigeq.
        apply qualified_type_subtype_base_subtype in H19.
        (* rewrite (vpa_mutabilty_tt_sctype Tthis Ty) in H23. *)
        rewrite (vpa_mutabilty_tt_sctype Ty (mreceiver (msignature mdef0))) in H19.
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          apply qualified_type_subtype_q_subtype in H19.
          specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
          apply get_this_qualified_type_nth_error in H12.
          unfold wf_senv in Hsenv.
          destruct Hsenv as [Hsenvdom _].
          specialize (Hcorrcopy 0 Hsenvdom Tthis H12).
          rewrite <- Hvars in HOutterReceiverAddr.
          apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
          rewrite HOutterReceiverAddr in Hcorrcopy.
          unfold wf_r_typable in Hcorrcopy.
          unfold r_type in Hcorrcopy.
          destruct (runtime_getObj h lOutterReceiver) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
          destruct Hcorrcopy as [_ Houtter_qualifier_typable].

          assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
          {
            unfold r_muttype in HOutterReceiverMutabilityType.
            rewrite Houtterobj in HOutterReceiverMutabilityType.
            simpl in HOutterReceiverMutabilityType.
            inversion HOutterReceiverMutabilityType; subst OutterReceiverMutability.
            reflexivity.
          }
          subst OutterReceiverMutability.

          assert (ly = ι). 
          {
            rewrite HeqrΓmethodinit in HreceiverAddr.
            unfold get_this_var_mapping in HreceiverAddr.
            simpl in HreceiverAddr.
            inversion HreceiverAddr; reflexivity.
          }
          subst ι.

          assert (r_muttype h ly = Some rq_obj).
          {
            unfold r_muttype.
            rewrite Hobjy.
            simpl.
            reflexivity.
          }

          assert (rq_obj = qinner).
          {
            rewrite H0 in Hqcontext.
            inversion Hqcontext; subst qinner.
            reflexivity.
          }
          subst rq_obj.

          unfold qualifier_typable_context.
          unfold qualifier_typable_context in HyQualifierTypablility.
          unfold qualifier_typable_context in Houtter_qualifier_typable.
          unfold vpa_mutabilty_rs.
          unfold vpa_mutabilty_rs in HyQualifierTypablility.
          unfold vpa_mutabilty_rs in Houtter_qualifier_typable.
          unfold vpa_mutabilty_tt in H19.
          rewrite <- Hmsigeq in H19.

          destruct qinner eqn:HInnerReceiverMutability;
          destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
          try trivial.
          all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
          destruct (sqtype Ty) eqn:HTyStaticMutability;
          try trivial.
          all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
          try rewrite HTyStaticMutability in H19;
          simpl in H19;
          try rewrite HMethodReceiverDeclaredType in H19;
          try inversion H19; try trivial.
          all: try inversion H19; try easy.
        }
        (* clear_dups. amazing.... *)

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        apply qualified_type_subtype_q_subtype in H18.
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc]; [trivial|].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in H20.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite H20.
              apply nth_error_Some.
              intros Hnone.
              rewrite Hnth in Hnone.
              discriminate.
            }
            assert (Harg_type : exists argtype, nth_error argtypes i' = Some argtype).
            {
              apply nth_error_Some_exists.
              exact Hi'_bound.
            }
            assert (loc < dom h).
            {
              assert (Hvals_wf :
              Forall
                (fun v =>
                  match v with
                  | Null_a => True
                  | Iot loc =>
                      match runtime_getObj h loc with
                      | Some _ => True
                      | None => False
                      end
                  end) vals).
              {
                eapply runtime_lookup_list_preserves_wf_values; eauto.
              }
              eapply Forall_nth_error in Hvals_wf; eauto.
              simpl in Hvals_wf.
              destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|contradiction].
              apply runtime_getObj_dom in Hargobjloc.
              exact Hargobjloc.
            }
            destruct Harg_type as [argtype Hargtype].
            unfold wf_r_typable.
            unfold r_type.
            destruct (runtime_getObj h loc) as [argobj|] eqn:Hargobjloc; [|apply runtime_getObj_not_dom in Hargobjloc; lia].
            assert (HargtypeFromsEnv :
              exists iArgInSenv,
                nth_error sΓ iArgInSenv = Some argtype
            /\ nth_error zs i' = Some iArgInSenv).
            {
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype H11 Hargtype)
                as [j [Hzs_j Hst_j]].
              exists j.
              split.
              - (* from static_getType to nth_error sΓ' *)
                unfold static_getType in Hst_j; exact Hst_j.
              - (* keep the zs fact *)
                exact Hzs_j.
            }
            destruct HargtypeFromsEnv as [iArgInSenv [HargtypeFromsEnv Hzs_iArg]].

            assert (Hi'dom : iArgInSenv < dom sΓ).
            {
              apply nth_error_Some.
              rewrite HargtypeFromsEnv; discriminate.
            }
            assert (HargtypeFromrEnv :
                      nth_error (vars rΓ) iArgInSenv = Some (Iot loc)).
            {
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) H4 Hval_i)
                as [j [Hzs_j Hget_j]].
              assert (HiEq : iArgInSenv = j).
              {
                (* zs[i'] = Some iArgInSenv and zs[i'] = Some j ⇒ iArgInSenv = j *)
                rewrite Hzs_iArg in Hzs_j.
                inversion Hzs_j; reflexivity.
              }
              subst iArgInSenv.
              unfold runtime_getVal in Hget_j.
              exact Hget_j.
            }
            have Hcorrcopy_2 := Hcorrcopy.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType iArgInSenv Hi'dom argtype HargtypeFromsEnv).
            unfold runtime_getVal in Hcorrcopy.
            rewrite HargtypeFromrEnv in Hcorrcopy.
            unfold wf_r_typable in Hcorrcopy.
            unfold r_type in Hcorrcopy.
            rewrite Hargobjloc in Hcorrcopy.
            destruct Hcorrcopy as [Harg_basesubtype Harg_qualifiertypability].
            split.

            (* base subtype *)
            rewrite nth_error_cons_succ in Hnth.
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_base_subtype in H20.
            rewrite (vpa_mutabilty_tt_sctype Ty sqt) in H20.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in H20; eauto.
            apply qualified_type_subtype_q_subtype in H20.
            rewrite sq_vpa_tt_eq_qq in H20.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in H12.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis H12).
            rewrite <- Hvars in Hget_iot.
            apply get_this_var_mapping_runtime_getVal in Hget_iot.
            rewrite Hget_iot in Hcorrcopy_2.
            unfold wf_r_typable in Hcorrcopy_2.
            unfold r_type in Hcorrcopy_2.
            destruct (runtime_getObj h iot) as [outterreceiverobj|] eqn:Houtterobj; [|easy].
            destruct Hcorrcopy_2 as [_ HOutterReceiverQualifierTypablility].
            assert (rqtype (rt_type outterreceiverobj) = OutterReceiverMutability).
            {
              clear - Houtterobj HOutterReceiverMutabilityType HOutterReceiverAddr Hget_iot Hvars.
              rewrite <- Hvars in HOutterReceiverAddr.
              apply get_this_var_mapping_runtime_getVal in HOutterReceiverAddr.
              rewrite Hget_iot in HOutterReceiverAddr.
              inversion HOutterReceiverAddr; subst lOutterReceiver.
              unfold r_muttype in HOutterReceiverMutabilityType.
              rewrite Houtterobj in HOutterReceiverMutabilityType.
              simpl in HOutterReceiverMutabilityType.
              inversion HOutterReceiverMutabilityType; reflexivity.
            }
            subst OutterReceiverMutability.
            assert (ι = ly).
            {
              unfold get_this_var_mapping in HreceiverAddr.
              rewrite HeqrΓmethodinit in HreceiverAddr.
              simpl in HreceiverAddr.
              inversion HreceiverAddr; reflexivity.
            }
            subst ι.
            assert(rq_obj = qinner).
            {
              unfold r_muttype in Hqcontext.
              rewrite Hobjy in Hqcontext.
              simpl in Hqcontext.
              inversion Hqcontext.
              easy.
            }
            subst rq_obj.
            clear - H20 Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in H20;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in H4.
            apply static_getType_list_preserves_length in H11.
            apply Forall2_length in H20.
            rewrite H4 in Hval_i.
            rewrite <- H11 in Hval_i.
            rewrite H20 in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    specialize (IHHeval Hlocalset Hassignability vals' Hobj' vals0 Hobj sΓmethodend sΓmethodinit).
    assert (HenvInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit).
    {
      unfold env_respects_protected_set.
      intros z l_z Tz Hlookup_s Hlookup_r Hin_P.
      rewrite HeqsΓmethodinit in Hlookup_s.
      rewrite HeqrΓmethodinit in Hlookup_r.
      unfold static_getType in Hlookup_s.
      unfold runtime_getVal in Hlookup_r.
      simpl in Hlookup_s, Hlookup_r.
      destruct z as [| z'].
      - simpl in Hlookup_s, Hlookup_r.
      injection Hlookup_s as <-. injection Hlookup_r as <-.
      unfold is_safe_mode.
      have Hty_safe : is_safe_mode (sqtype Ty).
      {
        unfold env_respects_protected_set in Henv_respects.
        specialize (Henv_respects y ly Ty H10 H Hin_P).
        exact Henv_respects.
      }
      unfold is_safe_mode in Hty_safe.
      unfold vpa_mutabilty_tt.
      apply qualified_type_subtype_q_subtype in H19.
      clear - Hty_safe H19.
      unfold vpa_mutabilty_tt in H19.
      destruct Hty_safe as [HRd | HLost].
      + (* Case: sqtype Ty = Rd *)
        rewrite HRd in H19.
        simpl in H19.
        inversion H19; easy.
      + (* Case: sqtype Ty = Lost *)
        rewrite HLost in H19.
        simpl in H19.
        inversion H19; easy.
      -
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in H10.
          exact H10.
        }

        unfold wf_renv in Hrenv.
        destruct Hrenv as [_ [Hreceiver _]].
        destruct Hreceiver as [iot [Hget_iot Hiot_dom]].
        assert (HOutterReceiverMutability: exists qcontext, r_muttype h iot = Some qcontext).
        {
          eapply receiver_mutability_exists_from_bound; eauto.
        }
        destruct HOutterReceiverMutability as [qoutter Hqoutter].
        (* Apply correspondence to get wf_r_typable *)
        specialize (Htypable iot qoutter Hget_iot Hqoutter y Hy_dom Ty H10).
        unfold wf_r_typable in Htypable.
        unfold r_basetype in H1.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy.
        2:{
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          discriminate.
        }
        destruct obj as [rt_obj fields_obj].
        destruct rt_obj as [rq_obj rc_obj].

        unfold r_type in Htypable.
        rewrite H in Htypable.
        rewrite Hobjy in Htypable.
        simpl in Htypable.
        destruct Htypable as [Hsubtype Hqualifier].
        simpl in Hobjy.

        simpl in H1.
        inversion H1.
        assert (Hrc_obj_eq: rc_obj = cy).
        {
          unfold r_basetype in H0.
          rewrite Hobjy in H0.
          inversion H0.
          easy.
        }
        subst rc_obj.
        assert (Hsigeq: msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
        have Hnth_param_type : nth_error (mparams (msignature mdef)) z' = Some Tz.
        {
          simpl in Hlookup_s.
          easy.
        }

        have Hnth_param_val : nth_error vals z' = Some (Iot l_z).
        {
          simpl in Hlookup_r.
          easy.
        }
        assert (Hi'_bound : z' < List.length argtypes).
        {
          apply Forall2_length in H20.
          rewrite <- Hsigeq in H20.
          assert (H_bound_params : z' < dom (mparams (msignature mdef))).
          {
            apply nth_error_Some. (* Converts "index < len" to "lookup <> None" *)
            rewrite Hnth_param_type.   (* lookup is Some Tz *)
            discriminate.         (* Some <> None *)
          }

          (* 2. Convert to bound for argtypes using the equality *)
          rewrite <- H20 in H_bound_params. (* Replace length of params with length of argtypes *)

          (* 3. Solve the goal *)
          exact H_bound_params.
        }

        have Hnth_arg: exists T_arg, nth_error argtypes z' = Some T_arg.
        {
          apply nth_error_Some_exists.
          exact Hi'_bound.
        }

        destruct Hnth_arg as [T_arg Hnth_arg].
        eapply Forall2_nth_error with (i := z') (a := T_arg) (b := Tz) in H20; [|auto|rewrite <- Hsigeq; exact Hnth_param_type].
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold env_respects_protected_set in Henv_respects.
        apply adapated_subtype_safe_implies_safe in H20; auto.

        have HargtypeFromsEnv :
          exists z_outter,
            static_getType sΓ z_outter = Some T_arg /\
            nth_error zs z' = Some z_outter.
        {
          destruct (static_getType_list_nth_zs sΓ zs argtypes z' T_arg H11 Hnth_arg)
            as [j [Hzs_j Hst_j]].
          exists j.
          split.
          - unfold static_getType. exact Hst_j.
          - exact Hzs_j.
        }

        destruct HargtypeFromsEnv as [z_outter [HgetZ_type Hzs_z_outter]].

        have HgetZ_val : runtime_getVal rΓ z_outter = Some (Iot l_z).
        {
          destruct (runtime_lookup_list_nth_zs rΓ zs vals z' (Iot l_z) H4 Hnth_param_val)
            as [j [Hzs_j Hget_j]].
          assert (HzEq : z_outter = j) by (
            rewrite Hzs_z_outter in Hzs_j;
            inversion Hzs_j; reflexivity
          ).
          subst j.
          exact Hget_j.
        }
        specialize (Henv_respects z_outter l_z T_arg HgetZ_type HgetZ_val Hin_P); auto.
    }
    assert (HMethodInnerInvariant: env_respects_protected_set (protected_locset CT h l_root)
    sΓmethodinit rΓmethodinit /\ heap_respects_protected_set (protected_locset CT h l_root) h h CT).
    {
      split.
      exact HenvInvariant.
      exact Hheap_respects.
    }
    specialize (IHHeval HMethodInnerInvariant Hwf_method_frame).
    rewrite <- getmbody in Hmethodbody_typing.
    specialize (IHHeval Hmethodbody_typing); auto.
  - (* Seq *)
    (* Invert typing for SSeq *)
    inversion Htyping; subst.
    rename sΓ' into  sΓ''.
    rename sΓ'0 into sΓ'.
    
    (* Extract wellformedness for intermediate state using preservation_pico *)
    have Hwf' : wf_r_config CT sΓ' rΓ' h'.
    {
      eapply preservation_pico; eauto.
    }

    assert (Heq_protected_set: protected_locset CT h l_root = protected_locset CT h' l_root /\ confinement_invariant_precise (protected_locset CT h l_root) CT sΓ' rΓ' h h').
    {
      eapply stmt_preserves_both; eauto.
    }
    destruct Heq_protected_set as [Heq_protected_set Hconfined_intermediate].

    specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1) as Hh'.
    assert (Hdom_root': l_root < dom h') by lia.
    assert (Hldomh': l < dom h') by (apply runtime_getObj_dom in Hobj; lia).
    specialize (runtime_getObj_Some h' l Hldomh') as [T [values' Hh'some]].
    specialize (runtime_preserves_r_type_heap CT rΓ h l ({| rqtype := anyrq; rctype := C |})
    h' vals s1 rΓ' Hobj Heval1) as [vals1 Hrtype].
    rewrite Hrtype in Hh'some; inversion Hh'some; subst.

    specialize (IHHeval1 Hdom_root eq_refl Hlocalset Hassignability values' Hrtype vals Hobj sΓ' sΓ Hconfined Hwf H4).

    have Hlocalset': Ensembles.In Loc (protected_locset CT h' l_root) l by (rewrite Heq_protected_set in Hlocalset; exact Hlocalset).
    rewrite Heq_protected_set in Hconfined_intermediate.

    assert (Hconf1_for_ih2 : confinement_invariant_precise (protected_locset CT h' l_root) CT sΓ' rΓ' h' h').
    {
      unfold confinement_invariant_precise in Hconfined_intermediate.
      destruct Hconfined_intermediate as [Henv1 Hheap1].
      split.
      + exact Henv1.
      + unfold heap_respects_protected_set in Hheap1.
        intros l_src C0 anyrq0 vals0 k l_dst Hdom_src_h' Hlsrc_new Hin_dst Hobj0 Hnth.
        (* l_dst < dom h' (from Hin_dst via reachable_abs_dom) *)
        have Hdom_src_h : l_dst < dom h.
        rewrite <- Heq_protected_set in Hin_dst.
        have Hin_dst_copy := Hin_dst.
        apply reachable_abs_dom in Hin_dst_copy.
        exact Hin_dst_copy.
        have hdom_src_h : l_src >= dom h by lia.
        exact (Hheap1 l_src C0 anyrq0 vals0 k l_dst Hdom_src_h hdom_src_h Hin_dst Hobj0 Hnth).
    }

    specialize (IHHeval2 Hdom_root' eq_refl Hlocalset' Hassignability vals' Hobj' values' Hrtype sΓ'' sΓ' Hconf1_for_ih2 Hwf' H6).
    rewrite IHHeval2 in IHHeval1; auto.
Qed.

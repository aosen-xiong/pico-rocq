Require Import Syntax Notations Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties DeepImmutability Reachability Preservation.
From Stdlib Require Import List.
From Stdlib Require String.
Import ListNotations.

(* Lemma vpa_mutability_stype_fld_ro_not_mut_abs_imm :
  forall q_recv q_field q_res
         (Hrd : q_recv = RO)
         (Hvpa : vpa_mutability_stype_fld_abs_imm q_recv q_field = q_res),
    q_res <> Mut.
Proof.
  intros. subst.
  unfold vpa_mutability_stype_fld_abs_imm.
  destruct q_field; subst; try easy.
Qed. *)

Lemma vpa_mutability_stype_fld_ro_not_mut_safe_ro :
  forall q_recv q_field q_res
         (Hrd : q_recv = RO)
         (Hvpa : vpa_mutability_stype_fld_safe_ro q_recv q_field = q_res),
    q_res <> Mut.
Proof.
  intros. subst.
  unfold vpa_mutability_stype_fld_safe_ro.
  destruct q_field; subst; try easy.
Qed.

(* Safe means preserve shallow immutability *)
Definition is_safe_mode (m : q) : Prop :=
  m = RO \/ m = Lost \/ m = RDM \/ m = Imm.

Ltac solve_safe_mode :=
  match goal with
  (* If the goal is a disjunction, try the left side. If that fails, try the right side. *)
  | |- ?A \/ ?B => (left; solve_safe_mode) || (right; solve_safe_mode)

  (* Base Case 1: The branch is a trivial equality (e.g., RO = RO) *)
  | |- ?X = ?X => reflexivity

  (* Base Case 2: The branch exactly matches a hypothesis in the current context *)
  | |- _ => assumption
  end.  

(* Effectively require all variables *)
Definition env_respects_protected_set
  (P : Ensembles.Ensemble Loc) (sΓ : s_env) (rΓ : r_env) : Prop :=
  forall x l T,
    static_getType sΓ x = Some T ->
    runtime_getVal rΓ x = Some (Iot l) ->

    (* If the location is in the Protected Set... *)
    Ensembles.In Loc P l ->

    (* ...the variable must be ReadOnly, or Lost. *)
    is_safe_mode (sqtype T).

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
  destruct Hsafe_sub as [Hrd | [Hlost| HRDM]].
  inversion Hrd. 
  inversion Hlost.
  inversion HRDM.
  discriminate.
  discriminate.
Qed.

Lemma adapated_subtype_safe_implies_safe :
  forall CT T_sub T_Receiver T_super
         (Hsub : qualified_type_subtype CT T_sub (vpa_mutability_tt_safe_ro T_Receiver T_super))
         (Hsafe_sub : is_safe_mode (sqtype T_sub)),
    is_safe_mode (sqtype T_super).
Proof.
  intros.
  unfold is_safe_mode in *.
  apply qualified_type_subtype_q_subtype in Hsub.
  unfold vpa_mutability_tt_safe_ro in Hsub.
  destruct (sqtype T_Receiver) eqn: Hreceiver;
  destruct (sqtype T_super) eqn: HSuper;
  destruct Hsafe_sub as [Hrd | [Hlost| [HRDM | HImm]]];
  try rewrite Hrd in Hsub;
  try rewrite Hlost in Hsub;
  try rewrite HRDM in Hsub;
  try rewrite HImm in Hsub;
  try rewrite <- H in Hsub;
  inversion Hsub; subst; auto.
  all: try rewrite HSuper in H; try rewrite HSuper in H1; try discriminate.
  all: try simpl in Hsub.
  all: try easy.
Qed.

(* TODO: after revise the setting, do I still need this? *)

Lemma subtype_safe_implies_safe_adapted :
  forall CT T_sub T_Receiver T_super
         (Hsub : qualified_type_subtype CT (vpa_mutability_tt_safe_ro T_Receiver T_sub) T_super)
         (Hsafe_sub : is_safe_mode (sqtype T_sub))
         (Hsafe_receiver: is_safe_mode (sqtype T_Receiver)),
    is_safe_mode (sqtype T_super).
Proof.
  intros.
  unfold is_safe_mode in *.
  apply qualified_type_subtype_q_subtype in Hsub.
  unfold vpa_mutability_tt_safe_ro in Hsub.
  destruct Hsafe_receiver as [Hrd_recv | [Hlost_recv| [HRDM_recv | HImm_recv]]];
  destruct (sqtype T_Receiver) eqn: Hreceiver;
  destruct (sqtype T_super) eqn: HSuper;
  destruct Hsafe_sub as [Hrd | [Hlost| [HRDM | HImm]]];
  try rewrite Hrd in Hsub;
  try rewrite Hlost in Hsub;
  try rewrite HRDM in Hsub;
  try rewrite HImm in Hsub;
  try rewrite <- H in Hsub;
  inversion Hsub; subst; auto.
  all: 
  try rewrite HSuper in H;
  try rewrite Hrd in H0;
  try rewrite Hlost in H0;
  try rewrite HRDM in H0;
  try rewrite HImm in H0;
  try discriminate.
Qed.

Lemma reachable_dom :
  forall h l_src l_dst
    (Hreach : reachable h l_src l_dst),
    l_dst < dom h.
Proof.
  intros.
  induction Hreach.
  - (* Base case: reachable_abs_heap *)
    exact Hdom.
  - (* Step case: reachable_abs_step *)
    exact Hdom.
  - (* Trans case *)
    exact IHHreach2.
Qed.

Lemma reachable_abs_dom :
  forall CT h l_src l_dst
    (Hreach : reachable_abs CT h l_src l_dst),
    l_dst < dom h.
Proof.
  intros CT h l_src l_dst Hreach.
  induction Hreach.
  - (* Base case: reachable_abs_heap *)
    exact Hdom.
  - (* Step case: reachable_abs_step *)
    exact Hdom.
  - (* Trans case *)
    exact IHHreach2.
Qed.

Lemma env_vars_in_protected_locset :
  forall CT h sΓ rΓ x l T
         (Hdom_root : l < dom h)
         (Hstatic : static_getType sΓ x = Some T)
         (Hruntime : runtime_getVal rΓ x = Some (Iot l)),
    Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) l.
Proof.
  intros CT h sΓ rΓ x l T Hstatic Hruntime.
  unfold reachable_locations_from_initial_env.
  eexists. eexists. eexists.
  repeat split; eauto.
  apply rch_heap; auto.
Qed.

Lemma confinement_from_all_readonly_env :
  forall CT sΓ rΓ h
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Hall_readonly : forall y T,
      static_getType sΓ y = Some T ->
      is_safe_mode (sqtype T)),
    env_respects_protected_set (reachable_locations_from_initial_env CT h rΓ) sΓ rΓ.
Proof.
  intros.
  unfold env_respects_protected_set.
  unfold env_respects_protected_set.
  intros z l T Hlookup_s Hlookup_r Hin_P.
  exact (Hall_readonly z T Hlookup_s).
Qed.

Lemma expr_eval_to_protected_implies_safe_type :
  forall P CT sΓ mt rΓ h e l_res Te
         (HP_def : P = reachable_locations_from_initial_env CT h rΓ)
         (Hwf : wf_r_config CT sΓ rΓ h)
         (Hconfined : env_respects_protected_set P sΓ rΓ)
         (Heval : eval_expr OK P CT rΓ h e (Iot l_res) OK P rΓ h)
         (Htyp : expr_has_type CT sΓ mt e Te)
         (Hmtype: mt <> AbstractImm)
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
  inversion Heval; subst.
  - (* EVar case *)
  inversion htyp_copy; subst.
    (* Now Htyp should give us: expr_has_type CT sΓ (EVar x) Te *)
    (* which means static_getType sΓ x = Some Te *)
    
    unfold env_respects_protected_set in Hconfined.
    (* destruct Hconfined as [Henv_respects Hheap_respects]. *)
    
    (* Apply env_respects_protected_set *)
    unfold env_respects_protected_set in Hconfined.
    specialize (Hconfined x l_res Te).
    have H_static : static_getType sΓ x = Some Te.
    {
      auto.
    }
    
	    specialize (Hconfined H_static Hval Hin).
    exact Hconfined.
  - (* EField case *)
    inversion htyp_copy; subst.
    exfalso; apply Hmtype; reflexivity.
    set (P := reachable_locations_from_initial_env CT h rΓ).
    destruct (classic (Ensembles.In Loc P v)) as [Hv_in | Hv_out].
    +
	      specialize (Hconfined x v T Hget_x Hval Hv_in).
      unfold is_safe_mode in Hconfined.
      subst. simpl.
      destruct Hconfined as [Hrd | [Hlost| [HRDM| HImm]]].
      *
      rewrite Hrd.
      unfold vpa_mutability_stype_fld_safe_ro.
      unfold is_safe_mode.
      destruct (mutability (ftype fDef));
      try solve solve_safe_mode.
      *
      rewrite Hlost.
      unfold vpa_mutability_stype_fld_safe_ro.
      unfold is_safe_mode.
      destruct (mutability (ftype fDef));
      try solve solve_safe_mode.
      *
      rewrite HRDM.
      unfold vpa_mutability_stype_fld_safe_ro.
      unfold is_safe_mode.
      destruct (mutability (ftype fDef));
      try solve solve_safe_mode.
      *
      rewrite HImm.
      unfold vpa_mutability_stype_fld_safe_ro.
      unfold is_safe_mode.
      destruct (mutability (ftype fDef));
      try solve solve_safe_mode.
    +
	    assert (Hdom_v : v < dom h) by (apply runtime_getObj_dom in Hobj; exact Hobj).
    unfold reachable_locations_from_initial_env in P.
    exfalso.
    apply Hv_out.
    exists x, v.
	    split; [exact Hval | apply rch_heap; apply runtime_getObj_dom in Hobj; exact Hobj].
Qed.

Lemma runtime_getObj_app_left_equal : forall h h_ext loc,
  loc < dom h ->
  runtime_getObj h loc = runtime_getObj (h ++ [h_ext]) loc.
Proof.
  intros h h_ext loc Hloc_dom.
  unfold runtime_getObj.
  rewrite nth_error_app1; auto.
Qed.

Lemma reachable_locations_from_initial_env_dom :
  forall CT h rΓ l_y
    (Hin : Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) l_y),
    l_y < dom h.
Proof.
  intros.
  unfold reachable_locations_from_initial_env in Hin.
  (* Hin is now: exists x l_root T, ... *)
  destruct Hin as [x [l_root [Hruntime_val]]].
  eapply reachable_dom; exact H.
Qed.

Lemma reachable_locations_from_initial_env_subset :
  forall CT h rΓ y ly zs vals,
    runtime_getVal rΓ y = Some (Iot ly) ->
    runtime_lookup_list rΓ zs = Some vals ->
    Ensembles.Included Loc 
      (reachable_locations_from_initial_env CT h {| vars := Iot ly :: vals |})
      (reachable_locations_from_initial_env CT h rΓ).
Proof.
  intros CT h rΓ y ly zs vals H Hlookup_list l Hin_method.
  unfold reachable_locations_from_initial_env in *.
  destruct Hin_method as [x_method [l_root [Hruntime_method Hreach]]].
  simpl in Hruntime_method.
  
  (* Now we case-split on x_method *)
  destruct x_method as [|x_method'].
  - (* Case: x_method = 0 (the receiver) *)
    (* At index 0, the method env has Iot ly *)
    simpl in Hruntime_method.
    inversion Hruntime_method; subst l_root.
    (* Now we need to show l is in the original environment's protected set *)
    exists y, ly.
    split.
    + exact H.
    + exact Hreach.
  - (* Case: x_method = S x_method' (a parameter) *)
    (* At index S x_method', the method env has vals[x_method'] *)
    simpl in Hruntime_method.
    (* By lemma runtime_lookup_list_nth_zs, there exists z : Loc such that *)
    (* zs[x_method'] = z and runtime_getVal rΓ z = Some l_root *)
    destruct (runtime_lookup_list_nth_zs rΓ zs vals x_method' (Iot l_root) Hlookup_list Hruntime_method)
      as [z [Hnth_zs Hruntime_z]].
    (* Now we can witness z in the original environment *)
    exists z, l_root.
    split.
    + exact Hruntime_z.
    + exact Hreach.
Qed.

Lemma stmt_preserves_unreachable_objects :
  forall CT rΓ h stmt rΓ' h' l C anyrq vals vals'
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hobj : runtime_getObj h l = Some (mkObj (mkruntime_type anyrq C) vals))
    (Hobj' : runtime_getObj h' l = Some (mkObj (mkruntime_type anyrq C) vals'))
    (Hnot_protected : ~ (Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) l)),
    vals = vals'.
Proof.
  intros CT rΓ h stmt rΓ' h' l C anyrq vals vals' Heval Hobj Hobj' Hnot_protected.
  remember OK as ok.
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
    destruct (Nat.eq_dec loc_x l) as [Halias | Hno_alias].
    -- (* Case: loc_x = l *)
      subst l.
      (* Now we have a contradiction: l is reachable from x, so it should be in protected_locset *)
      exfalso.
      apply Hnot_protected.
      unfold reachable_locations_from_initial_env.
      exists x, loc_x.
      split.
	      + exact Hval_x.  (* runtime_getVal rΓ x = Some (Iot loc_x) *)
	      + apply rch_heap.
	        apply runtime_getObj_dom in Hobj0.
	        exact Hobj0.
    -- (* Case: loc_x ≠ l *)
      (* update_field doesn't affect objects at other locations *)
      unfold update_field in Hobj'.
      simpl in Hobj'.
      destruct (runtime_getObj h loc_x) eqn:Hget_loc_x; try discriminate.
      simpl in Hobj'.
      rewrite runtime_getObj_update_diff in Hobj'; auto.
  - (* New *)
	    assert (Hl_old : l < dom h).
	    {
	      match goal with
	      | H : runtime_getObj h l = Some _ |- _ =>
	          apply runtime_getObj_dom in H; exact H
	      end.
	    }
    (* For objects in the old heap, New doesn't change them *)
    rewrite runtime_getObj_last2 in Hobj'; auto.
  - (* Call *)
    eapply IHHeval; eauto.
    intro Hin_method.
    apply Hnot_protected.
	    have Hsubset := reachable_locations_from_initial_env_subset CT h rΓ y ly zs vals Hval_y Hargs.
    unfold Ensembles.Included in Hsubset.
    exact (Hsubset l Hin_method).
  - (* Seq *)
    specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1) as Hh'.
    have Hlhdom: l < dom h by (apply runtime_getObj_dom in Hobj; exact Hobj). 
    assert (Hlh'dom: l < dom h') by lia. 
    specialize (runtime_getObj_Some h' l Hlh'dom) as [C' [values' Hh'some]].
    specialize (runtime_preserves_r_type_heap CT rΓ h l ({| rqtype := anyrq; rctype := C |})
    h' vals s1 rΓ' Hobj Heval1) as [vals1 Hrtype]. 
    rewrite Hrtype in Hh'some; inversion Hh'some; subst.
    specialize (IHHeval1 eq_refl Hnot_protected values' Hrtype vals Hobj).
    specialize (IHHeval2 eq_refl Hnot_protected vals' Hobj' values' Hrtype ).
    rewrite <- IHHeval1 in IHHeval2.
    auto.
Qed.

Lemma protected_locset_shrinks_with_null_binding :
  forall CT h rΓ,
    Ensembles.Included Loc 
      (reachable_locations_from_initial_env CT h (set_vars rΓ (vars rΓ ++ [Null_a])))
      (reachable_locations_from_initial_env CT h rΓ).
Proof.
  intros CT h rΓ l Hin.
  unfold reachable_locations_from_initial_env in *.
  destruct Hin as [x [l_root [Hruntime Hreach]]].
  (* Hruntime : runtime_getVal (set_vars rΓ (...)) x = Some (Iot l_root) *)
  (* Since new binding is Null_a (not Iot anything), x must be old *)
  (* So runtime_getVal rΓ x = Some (Iot l_root) *)
  exists x, l_root.
  split.
  - (* runtime_getVal on original env *)
    unfold runtime_getVal in Hruntime.
    simpl in Hruntime.
    destruct x as [|x'].
  -- (* Case: x = 0 (receiver) *)
    (* Receiver is unchanged by the update *)
    unfold runtime_getVal.
    simpl.
    destruct (vars rΓ).
    simpl in Hruntime.
    easy.
    simpl in Hruntime; auto.
  -- (* Case: x = S x' (a variable field) *)
    simpl in Hruntime.
    (* The new binding is at index (length (vars rΓ)) and has value Null_a *)
    destruct (Nat.eq_dec (S x') (List.length (vars rΓ))) as [Heq | Hneq].
    + (* x' = length (vars rΓ): this is the NEW binding *)
      change (nth_error (vars rΓ ++ [Null_a]) (S x') = Some (Iot l_root)) in Hruntime.
      rewrite Heq in Hruntime.
      rewrite nth_error_app2 in Hruntime; [lia| ].
      replace (dom (vars rΓ) - dom (vars rΓ)) with 0 in Hruntime by lia.
      simpl in Hruntime.
      easy.
    + (* x' < length (vars rΓ): OLD binding, unchanged *)
      unfold runtime_getVal.
      simpl.
      destruct (vars rΓ).
      simpl in Hruntime.
      exfalso.
      rewrite nth_error_nil in Hruntime.
      easy.
      simpl in Hruntime.
      assert (Hlen: x' < List.length v0).
      {
        assert (H_bound_extended : x' < dom (v0 ++ [Null_a])).
          {
            apply nth_error_Some. (* Now the goal becomes: list[x'] <> None *)
            rewrite Hruntime.     (* Becomes: Some ... <> None *)
            discriminate.         (* Trivial: Some is never None *)
          }
          rewrite length_app in H_bound_extended. (* len (v0 ++ [Null]) = len v0 + len [Null] *)
      simpl in H_bound_extended.              (* len v0 + 1 *)
      simpl in Hneq.                          (* S x' <> S (len v0) -> x' <> len v0 *)

      (* 3. Solve with arithmetic *)
      (* We have: x' < len v0 + 1   AND   x' <> len v0 *)
      (* Therefore: x' < len v0 *)
      lia.
      }

      (* have Hx'_bound : x' < List.length v0 by lia. *)
      rewrite List.nth_error_app1 in Hruntime; eauto.
  - exact Hreach.
Qed.

Lemma expr_eval_result_in_protected_set :
  forall CT sΓ mt rΓ h e Te v2 P
         (Hwf: wf_r_config CT sΓ rΓ h)
         (HP_def : P = reachable_locations_from_initial_env CT h rΓ)
         (Htyping : expr_has_type CT sΓ mt e Te)
        (Hmtype: mt <> AbstractImm)
         (Heval : eval_expr OK P CT rΓ h e v2 OK P rΓ h),
    (forall l, v2 = Iot l -> Ensembles.In Loc P l) \/
    (v2 = Null_a).
Proof.
  intros.
  remember OK as ok.
  induction Heval; intros; subst; try discriminate.
  - (* ENull *)
    right. reflexivity.
  - (* EVar case: variable evaluation *)
    inversion Htyping; subst.
    left. intros l Heq; subst.
    unfold reachable_locations_from_initial_env.
    exists x, l.
    split; auto.
    apply rch_heap.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [_ [Hwf_renv [_ [_ Hcorr]]]]].
    unfold wf_renv in Hwf_renv.
    destruct Hwf_renv as [_ [_ Hheap]].
    eapply Forall_nth_error with (x := (Iot l)) (n:=x)in Hheap.
    destruct (runtime_getObj h l) eqn :Hobj; try easy.
    apply runtime_getObj_dom in Hobj; auto.
	    unfold runtime_getVal in Hval; auto.
  - (* EInt case *)
    left. intros l Heq. discriminate.
  - (* EField case *)
    left. intros l Heq; subst.
    unfold reachable_locations_from_initial_env.
    exists x, v.
    split; auto.
    eapply rch_step; eauto.
    unfold wf_r_config in Hwf.
    destruct Hwf as [_ [Hheap [Hwf_renv [_ [_ Hcorr]]]]].
    unfold wf_heap in Hheap.
    have Hdom: v < dom h by
	    apply runtime_getObj_dom in Hobj; auto.
    specialize (Hheap v Hdom).
    unfold wf_obj in Hheap.
	    rewrite Hobj in Hheap.
    destruct Hheap as [_ Hfields].
    destruct Hfields as [fieldsCollection Hfields].
    destruct Hfields as [HfieldsCollection [Hfieldsdom HcorrFields]].
    have HfieldAtF: exists fDef, nth_error fieldsCollection f = Some fDef.
    {
      apply nth_error_Some_exists.
      rewrite <- Hfieldsdom.
	      apply getVal_dom in Hfield; auto.
    }
    destruct HfieldAtF as [fDef HfieldDef].
    eapply Forall2_nth_error in HcorrFields; eauto.
    destruct (Iot l) eqn:Heq; try easy.
    destruct (runtime_getObj h l0 ) eqn: Hobj_l0; try easy.
    inversion Heq; subst.
    apply runtime_getObj_dom in Hobj_l0; auto.
Qed.

Lemma protected_loc_has_safe_type :
  forall CT sΓ rΓ h z l_z T_z P
         (HP_def : P = reachable_locations_from_initial_env CT h rΓ)
         (Henv_respects : env_respects_protected_set P sΓ rΓ)
         (Hlookup_s : static_getType sΓ z = Some T_z)
         (Hlookup_r : runtime_getVal rΓ z = Some (Iot l_z))
         (Hin_P : Ensembles.In Loc P l_z),
    is_safe_mode (sqtype T_z).
Proof.
  intros CT sΓ rΓ h z l_z T_z P HP_def Henv_respects Hlookup_s Hlookup_r Hin_P.
  subst P.
  unfold env_respects_protected_set in Henv_respects.
  exact (Henv_respects z l_z T_z Hlookup_s Hlookup_r Hin_P).
Qed.

Lemma reachable_return_implies_reachable_args :
  forall CT sΓ mt rΓ h stmt sΓ' rΓ' h' ret_var l_z
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ mt stmt sΓ')
    (Hmtype: mt <> AbstractImm)
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ) CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (HgetVal: runtime_getVal rΓ' ret_var = Some (Iot l_z))
    (Hdom: l_z < dom h),
    (* CONCLUSION: l_z was reachable from the start *)
  Ensembles.In Loc (reachable_locations_from_initial_env CT h rΓ) l_z.
Proof.
  intros.
  remember OK as ok.
  generalize dependent sΓ.
  generalize dependent sΓ'.
  generalize dependent mt.
  (* generalize dependent l_z. *)
  generalize dependent ret_var.
  induction Heval; intros; subst; try discriminate.
  - (* skip *)
  unfold reachable_locations_from_initial_env.
  exists ret_var, l_z.
  split; auto.
  apply rch_heap; auto.
  - (* local *)
  destruct (Nat.eq_dec ret_var (dom rΓ.(vars))) as [Heq | Hneq].
  + (* Case: ret_var = dom rΓ.(vars) - this is the NEW variable *)
    (* But the new variable is bound to Null_a, not Iot l_z *)
    rewrite Heq in HgetVal.
    unfold runtime_getVal in HgetVal.
    simpl in HgetVal.
    rewrite nth_error_app2 in HgetVal.
    * lia.
    * replace (dom rΓ.(vars) - dom rΓ.(vars)) with 0 in HgetVal by lia.
      simpl in HgetVal.
      discriminate. (* Null_a <> Iot l_z *)
  + (* Case: ret_var < dom rΓ.(vars) - old variable, unchanged *)
    (* Show ret_var had the same value in original rΓ *)
    assert (ret_var < dom rΓ.(vars) + 1).
    {
      apply runtime_getVal_dom in HgetVal.
      simpl in HgetVal.
      rewrite length_app in HgetVal.
      simpl in HgetVal.
      exact HgetVal.
    }
    have Hret_var_old : runtime_getVal rΓ ret_var = Some (Iot l_z).
    {
      unfold runtime_getVal in HgetVal |- *.
      simpl in HgetVal |- *.
      rewrite nth_error_app1 in HgetVal; auto.
      lia.
    }
    (* Now apply the induction hypothesis with the original environment *)
    unfold reachable_locations_from_initial_env.
    exists ret_var, l_z.
    split; [exact Hret_var_old | ].
    apply rch_heap; auto.
	  - (* varass *)
	    inversion Htyping; subst.
	    rename sΓ' into sΓ.
	    have Hv2_cases := expr_eval_result_in_protected_set CT sΓ mt rΓ h e Te v2 
	    (reachable_locations_from_initial_env CT h rΓ) Hwf eq_refl Htype_e Hmtype Heval.
    destruct Hv2_cases as [Hv2_protected | Hv2_null].
    + (* Case: v2 = Iot l_z for some l_z in protected set *)
      destruct (Nat.eq_dec ret_var x) as [Heq_ret | Hne_ret].
      * (* ret_var = x: the updated variable *)
        subst ret_var.
	        assert (Hupdate_env : update_r_env_value rΓ x v2 = (set_vars rΓ (update x v2 (vars rΓ)))).
	        unfold update_r_env_value; simpl.
	        destruct rΓ.
	        easy.
	        rewrite <- Hupdate_env in HgetVal.
	        assert (Hget_update_same : runtime_getVal (update_r_env_value rΓ x v2) x = Some v2).
        {
          eapply runtime_getVal_update_same.
          apply runtime_getVal_dom in HgetVal.
	          rewrite Hupdate_env in HgetVal.
          have Hupdate_len : dom (vars (set_vars rΓ (update x v2 (vars rΓ)))) = dom (vars rΓ).
          {
            simpl.
            rewrite update_length.
            reflexivity.
          }
          rewrite <- Hupdate_len; auto.
	        }
	        rewrite Hget_update_same in HgetVal.
	        inversion HgetVal; subst.
	        specialize (Hv2_protected l_z eq_refl); auto.
      * (* ret_var ≠ x: unchanged variable *)
	        assert (Hupdate_env : update_r_env_value rΓ x v2 = (set_vars rΓ (update x v2 (vars rΓ)))).
        unfold update_r_env_value; simpl.
        destruct rΓ.
        easy.
	        rewrite <- Hupdate_env in HgetVal.
	        assert (Hget_update_diff : runtime_getVal (update_r_env_value rΓ x v2) ret_var = runtime_getVal rΓ ret_var).
        {
          eapply runtime_getVal_update_diff.
          easy.
        }
        unfold reachable_locations_from_initial_env.
        exists ret_var, l_z.
        split; auto.
        apply rch_heap; auto.
    + (* Case: v2 = Null_a *)
      subst v2.
      destruct (Nat.eq_dec ret_var x) as [Heq_ret | Hne_ret].
      * (* ret_var = x: the updated variable *)
        subst ret_var.
	        assert (Hupdate_env : update_r_env_value rΓ x Null_a = (set_vars rΓ (update x Null_a (vars rΓ)))).
        unfold update_r_env_value; simpl.
        destruct rΓ.
        easy.
	        rewrite <- Hupdate_env in HgetVal.
	        assert (Hget_update_same : runtime_getVal (update_r_env_value rΓ x Null_a) x = Some Null_a).
        {
          eapply runtime_getVal_update_same.
          apply runtime_getVal_dom in HgetVal.
	          rewrite Hupdate_env in HgetVal.
          have Hupdate_len : dom (vars (set_vars rΓ (update x Null_a (vars rΓ)))) = dom (vars rΓ).
          {
            simpl.
            rewrite update_length.
            reflexivity.
          }
          rewrite <- Hupdate_len; auto.
        }
	        rewrite Hget_update_same in HgetVal.
        discriminate. (* Null_a <> Iot l_z *)
      * (* ret_var ≠ x: unchanged variable *)
	        assert (Hupdate_env : update_r_env_value rΓ x Null_a = (set_vars rΓ (update x Null_a (vars rΓ)))).
        unfold update_r_env_value; simpl.
        destruct rΓ.
        easy.
	        rewrite <- Hupdate_env in HgetVal.
	        assert (Hget_update_diff : runtime_getVal (update_r_env_value rΓ x Null_a) ret_var = runtime_getVal rΓ ret_var).
        {
          eapply runtime_getVal_update_diff.
          easy.
        }
        unfold reachable_locations_from_initial_env.
        exists ret_var, l_z.
        split; auto.
        apply rch_heap; auto.
  - (* fldwrite *)
    unfold reachable_locations_from_initial_env.
    exists ret_var, l_z.
    split; auto.
    apply rch_heap; auto.
  - (* new *)
    destruct (Nat.eq_dec ret_var x) as [Heq | Hneq].
    +
      subst.
      (* TODO: all use update_r_env_value or the diamond syntax *)
	      assert (Hupdate_env : update_r_env_value rΓ x (Iot dom h) = (set_vars rΓ (update x (Iot dom h) (vars rΓ)))).
      unfold update_r_env_value; simpl.
      destruct rΓ.
      easy.
	      rewrite <- Hupdate_env in HgetVal.
	      assert (Hget_update_same : runtime_getVal (update_r_env_value rΓ x (Iot dom h)) x = Some (Iot dom h)).
      {
        eapply runtime_getVal_update_same.
        apply runtime_getVal_dom in HgetVal.
	        rewrite Hupdate_env in HgetVal.
        have Hupdate_len : dom (vars (set_vars rΓ (update x (Iot dom h) (vars rΓ)))) = dom (vars rΓ).
        {
          simpl.
          rewrite update_length.
          reflexivity.
        }
        rewrite <- Hupdate_len; auto.
      }
	      rewrite Hget_update_same in HgetVal.
      inversion HgetVal; subst l_z.
      lia.
   +  
	      assert (Hupdate_env : update_r_env_value rΓ x (Iot dom h) = (set_vars rΓ (update x (Iot dom h) (vars rΓ)))).
      unfold update_r_env_value; simpl.
      destruct rΓ.
      easy.
	      rewrite <- Hupdate_env in HgetVal.
	      assert (Hget_update_diff : runtime_getVal (update_r_env_value rΓ x (Iot dom h)) ret_var = runtime_getVal rΓ ret_var).
      eapply runtime_getVal_update_diff.
      easy.
	      rewrite Hget_update_diff in HgetVal.
      unfold reachable_locations_from_initial_env.
      exists ret_var, l_z.
      split; auto.
      apply rch_heap; auto.
  - (* call *)
    inversion Htyping; subst.
    exfalso; apply Hmtype; reflexivity.
    rename sΓ' into sΓ.
    remember (set_vars rΓ (update x retval (vars rΓ))) as rΓ'''.
    assert (HformatExchange: update_r_env_value rΓ x retval = (set_vars rΓ (update x retval (vars rΓ)))).
    unfold update_r_env_value; simpl.
    destruct rΓ.
    easy.
    destruct (Nat.eq_dec x ret_var) as [Heq_retval | Hneq_retval].
    2:{
	      assert (Hget_update_diff : runtime_getVal rΓ ret_var = runtime_getVal rΓ''' ret_var).
      {
        rewrite HeqrΓ'''.
        rewrite <- HformatExchange.
        symmetry.
        eapply runtime_getVal_update_diff.
        easy.
      }
	      rewrite <- Hget_update_diff in HgetVal.
      unfold reachable_locations_from_initial_env.
      exists ret_var, l_z.
      split; auto.
      apply rch_heap; auto.
    }
    subst x.
	    assert (Hget_update_same : runtime_getVal (update_r_env_value rΓ ret_var retval) ret_var = Some retval).
    {
      eapply runtime_getVal_update_same.
      unfold wf_r_config in Hwf.
      destruct Hwf as [_ [_ [_ [_ [Hlength _]]]]].
	      apply static_getType_dom in Hget_x.
	      rewrite Hlength in Hget_x; auto.
    }
    rewrite HeqrΓ''' in HgetVal.
    rewrite <- HformatExchange in HgetVal.
	    rewrite Hget_update_same in HgetVal.
    inversion HgetVal; subst retval.
    have Hwfcopy := Hwf.
    unfold wf_r_config in Hwf.
    destruct Hwf as [Hclasstable [Hheap [Hrenv [Hsenv [_ Htypable]]]]].
    unfold env_respects_protected_set in *.
	    destruct Hfind as [mdeflookup getmbody].
    remember (msignature mdef) as msig.
    inversion mdeflookup; revert getmbody; subst; intro getmbody.
    assert (Hwfmethod: wf_method CT cy mdef).
    {
      eapply method_lookup_wf_class; eauto.
      eapply r_basetype_in_dom; eauto.
	      unfold gget_method in Hget_method.
	      apply find_some in Hget_method.
	      destruct Hget_method as [Hmethod_in _].
	      exact Hmethod_in.
    }
    unfold wf_method in Hwfmethod;
    destruct Hwfmethod as [sΓmethodend [mbodyreturntype [Hmethodbody_typing [HmethodReturnBound [HmethodReturnType [HmethodReturnSubtype HMethodoverride]]]]]];
    remember (mreceiver (msignature mdef) :: mparams (msignature mdef)) as sΓmethodinit;
    remember {| vars := Iot ly :: vals |} as rΓmethodinit;
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
        unfold runtime_getVal in Hval_y.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection Hval_y as H1_eq.
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
        unfold runtime_getVal in Hval_y.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection Hval_y as H1_eq.
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

        apply static_getType_list_preserves_length in Hget_args.
        apply runtime_lookup_list_preserves_length in Hargs.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in Harg_sub.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
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
        rewrite Hval_y in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
	        assert (Hmsigeq : msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
	        rewrite Hmsigeq.
        rewrite Hargs.
        rewrite <- Harg_sub.
        exact Hget_args.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
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
        rewrite Hval_y in Hcorr.
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
        destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        rewrite (vpa_mutability_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in Hrcv_sub.
        eapply base_trans; eauto.
        destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
          1:{
            apply qualified_type_subtype_q_subtype in Hrcv_sub.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
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

	            assert (Hinner_mut_at_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
	              rewrite Hinner_mut_at_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
            rewrite <- Hmsigeq in Hrcv_sub.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in Hrcv_sub;
            simpl in Hrcv_sub;
            try rewrite HMethodReceiverDeclaredType in Hrcv_sub;
            try inversion Hrcv_sub; try trivial.
            all: try inversion Hrcv_sub; try easy.
          }
          1:{
            destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
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

	            assert (Hinner_mut_at_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
	              rewrite Hinner_mut_at_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try trivial.
            all: try easy.
          }
        }

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        (* apply qualified_type_subtype_q_subtype in H20. *)
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc|n]; [trivial| | trivial].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in Harg_sub.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite Harg_sub.
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
                  | Int _ => True
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
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype Hget_args Hargtype)
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
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) Hargs Hval_i)
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
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_base_subtype in Harg_sub.
            rewrite (vpa_mutability_tt_sctype_safe_ro Ty sqt) in Harg_sub.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_q_subtype in Harg_sub.
            rewrite sq_vpa_tt_eq_qq_safe_ro in Harg_sub.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in Hthis.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis Hthis).
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
            clear - Harg_sub Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in Harg_sub;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in Hargs.
            apply static_getType_list_preserves_length in Hget_args.
            apply Forall2_length in Harg_sub.
            rewrite Hargs in Hval_i.
            rewrite <- Hget_args in Hval_i.
            rewrite Harg_sub in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    rewrite <- getmbody in Hmethodbody_typing.
    assert (Hy_dom : y < dom sΓ).
    {
      apply static_getType_dom in Hget_y.
      exact Hget_y.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in Hbase.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection Hbase as Hcy_eq.
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
	    rewrite Hval_y in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
    
    assert (Hmsigeq: msignature mdef = msignature mdef0).
    {
      eapply method_signature_consistent_subtype; eauto.
    }
    {
      rewrite Hmsigeq in Hmethodbody_typing.
      destruct (mtype (msignature mdef0)).
      exfalso; apply Hmt_not_abs; reflexivity.
      all: destruct mt.
      exfalso; apply Hmtype; reflexivity.
      specialize (IHHeval eq_refl Hdom (mreturn mbody) Hretval SafeRO Hmtype sΓmethodend sΓmethodinit Hwf_method_frame Hmethodbody_typing).
      rewrite HeqrΓmethodinit in IHHeval.
      eapply reachable_locations_from_initial_env_subset; eauto.
      inversion Hmt_sub.
      exfalso; apply Hmt_not_abs2; reflexivity.
      specialize (IHHeval eq_refl Hdom (mreturn mbody) Hretval ConcreteImm Hmt_not_abs sΓmethodend sΓmethodinit Hwf_method_frame Hmethodbody_typing).
      rewrite HeqrΓmethodinit in IHHeval.
      eapply reachable_locations_from_initial_env_subset; eauto.
      specialize (IHHeval eq_refl Hdom (mreturn mbody) Hretval ConcreteImm Hmt_not_abs sΓmethodend sΓmethodinit Hwf_method_frame Hmethodbody_typing).
      rewrite HeqrΓmethodinit in IHHeval.
      eapply reachable_locations_from_initial_env_subset; eauto.
    }
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
    remember {| vars := Iot ly :: vals |} as rΓmethodinit.
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
        unfold runtime_getVal in Hval_y.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection Hval_y as H1_eq.
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
        unfold runtime_getVal in Hval_y.
        destruct (nth_error (vars rΓ) y) as [v|] eqn:Hnth_y; [|discriminate].
        injection Hval_y as H1_eq.
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
        apply static_getType_list_preserves_length in Hget_args.
        apply runtime_lookup_list_preserves_length in Hargs.
        rewrite HeqsΓmethodinit.
        rewrite HeqrΓmethodinit.
        simpl.
        f_equal.
        apply Forall2_length in Harg_sub.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
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
        rewrite Hval_y in Hcorr.
        rewrite Hobjy in Hcorr.
        simpl in Hcorr.
        destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
	        assert (Hmsigeq : msignature mdef = msignature mdef0).
        {
          eapply method_signature_consistent_subtype; eauto.
        }
	        rewrite Hmsigeq.
        rewrite Hargs.
        rewrite <- Harg_sub.
        exact Hget_args.

        (* Correspondence holds for inner environment *)
        intros ι qinner HreceiverAddr Hqcontext i Hi sqt Hnth.
        rewrite HeqsΓmethodinit in Hnth, Hi.
        rewrite HeqrΓmethodinit.
        simpl in *.
        assert (Hy_dom : y < dom sΓ).
        {
          apply static_getType_dom in Hget_y.
          exact Hget_y.
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
        specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
        unfold wf_r_typable in Hcorr.
        unfold r_basetype in Hbase.
        unfold r_type.
        destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
        injection Hbase as Hcy_eq.
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
        rewrite Hval_y in Hcorr.
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
        destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
        apply qualified_type_subtype_base_subtype in Hrcv_sub.
        rewrite (vpa_mutability_tt_sctype_safe_ro Ty (mreceiver (msignature mdef0))) in Hrcv_sub.
        eapply base_trans; eauto.
        destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
        eapply base_trans; eauto.

        (* Qualifier typbility *)
        1: 
        {
          destruct Hrcv_sub as [Hrcv_sub | Hrcv_sub].
          1:{
            apply qualified_type_subtype_q_subtype in Hrcv_sub.
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
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

	            assert (Hinner_mut_at_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
	              rewrite Hinner_mut_at_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            unfold vpa_mutability_tt_safe_ro in Hrcv_sub.
            rewrite <- Hmsigeq in Hrcv_sub.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            destruct (sqtype Ty) eqn:HTyStaticMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try rewrite HTyStaticMutability in Hrcv_sub;
            simpl in Hrcv_sub;
            try rewrite HMethodReceiverDeclaredType in Hrcv_sub;
            try inversion Hrcv_sub; try trivial.
            all: try inversion Hrcv_sub; try easy.
          }
          1:{
            destruct Hrcv_sub as [HTyqualifier [HReceiverDeclearedQualifier HBaseSubtype]].
            specialize (Hcorrcopy lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            apply get_this_qualified_type_nth_error in Hthis.
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            specialize (Hcorrcopy 0 Hsenvdom Tthis Hthis).
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

	            assert (Hinner_mut_at_ly : r_muttype h ly = Some rq_obj).
            {
              unfold r_muttype.
              rewrite Hobjy.
              simpl.
              reflexivity.
            }

            assert (rq_obj = qinner).
            {
	              rewrite Hinner_mut_at_ly in Hqcontext.
              inversion Hqcontext; subst qinner.
              reflexivity.
            }
            subst rq_obj.

            unfold qualifier_typable_context.
            unfold qualifier_typable_context in HyQualifierTypablility.
            unfold qualifier_typable_context in Houtter_qualifier_typable.
            unfold vpa_mutability_rs.
            unfold vpa_mutability_rs in HyQualifierTypablility.
            unfold vpa_mutability_rs in Houtter_qualifier_typable.
            rewrite <- Hmsigeq in HReceiverDeclearedQualifier.

            destruct qinner eqn:HInnerReceiverMutability;
            destruct (sqtype (mreceiver (msignature mdef))) eqn:HMethodReceiverDeclaredType;
            try trivial.
            all: destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try trivial.
            all: destruct (sqtype Tthis) eqn:HTthisStaticMutability;
            try easy.
          }
        }

  (* -------------------------------------------------- *)
  (* Other index - > 1 *)
        (* apply qualified_type_subtype_q_subtype in H1. *)
        unfold runtime_getVal.
        simpl.
        destruct (nth_error vals i') as [v|] eqn:Hval_i.
          - (* Parameter i' exists *)
            destruct v as [|loc|n]; [trivial| | trivial].
            (* Use H23 to get the subtyping relationship *)
            assert (Hi'_bound : i' < List.length argtypes).
            {
              apply Forall2_length in Harg_sub.
              simpl in Hi.
              simpl in Hnth.
              rewrite Hmsigeq in Hnth.
              rewrite Harg_sub.
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
                  | Int _ => True
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
              destruct (static_getType_list_nth_zs sΓ zs argtypes i' argtype Hget_args Hargtype)
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
              destruct (runtime_lookup_list_nth_zs rΓ zs vals i' (Iot loc) Hargs Hval_i)
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
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_base_subtype in Harg_sub.
            rewrite (vpa_mutability_tt_sctype_safe_ro Ty sqt) in Harg_sub.
            eapply base_trans; eauto.

            (* Qualifier Typability *)
            rewrite Hmsigeq in Hnth.
            eapply Forall2_nth_error in Harg_sub; eauto.
            apply qualified_type_subtype_q_subtype in Harg_sub.
            rewrite sq_vpa_tt_eq_qq_safe_ro in Harg_sub.
            specialize (Hcorrcopy_2 lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType).
            unfold wf_senv in Hsenv.
            destruct Hsenv as [Hsenvdom _].
            apply get_this_qualified_type_nth_error in Hthis.
            specialize (Hcorrcopy_2 0 Hsenvdom Tthis Hthis).
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
            clear - Harg_sub Harg_qualifiertypability HyQualifierTypablility HOutterReceiverQualifierTypablility.

            destruct (rqtype (rt_type argobj)) eqn:Hargobjmutability; move Hargobjmutability at bottom;
            destruct (sqtype sqt) eqn:HParameterStaticDeclearedMutability; move HParameterStaticDeclearedMutability at bottom;
            destruct qinner eqn:HInnerReceiverMutability; move HInnerReceiverMutability at bottom;
            try solve_qualifier_typable_correct_concrete.

            all: destruct (sqtype Ty) eqn:HTyStaticMutability;
            destruct (sqtype argtype) eqn:HArgTypeStaticMutability;
            simpl in Harg_sub;
            try solve_q_subtype_wrong.

            all: 
            destruct (rqtype (rt_type outterreceiverobj)) eqn:HOutterReceiverMutability;
            try solve_qualifier_typable_wrong_concrete.

          - (* Parameter i' doesn't exist - contradiction *)
            exfalso.
            apply nth_error_None in Hval_i.
            apply runtime_lookup_list_preserves_length in Hargs.
            apply static_getType_list_preserves_length in Hget_args.
            apply Forall2_length in Harg_sub.
            rewrite Hargs in Hval_i.
            rewrite <- Hget_args in Hval_i.
            rewrite Harg_sub in Hval_i.
            simpl in Hi.
            simpl in Hnth.
            rewrite <- Hmsigeq in Hval_i.
            lia.
    }
    rewrite <- getmbody in Hmethodbody_typing.
    assert (Hy_dom : y < dom sΓ).
    {
      apply static_getType_dom in Hget_y.
      exact Hget_y.
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
    specialize (Hcorr lOutterReceiver OutterReceiverMutability HOutterReceiverAddr HOutterReceiverMutabilityType y Hy_dom Ty Hget_y).
    unfold wf_r_typable in Hcorr.
    unfold r_basetype in Hbase.
    unfold r_type.
    destruct (runtime_getObj h ly) as [obj|] eqn:Hobjy; [|discriminate].
    injection Hbase as Hcy_eq.
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
    rewrite Hval_y in Hcorr.
    rewrite Hobjy in Hcorr.
    simpl in Hcorr.
    destruct Hcorr as [Hbasesubtype HyQualifierTypablility].
    
    assert (Hmsigeq: msignature mdef = msignature mdef0).
    {
      eapply method_signature_consistent_subtype; eauto.
    }
    {
      rewrite Hmsigeq in Hmethodbody_typing.
      destruct (mtype (msignature mdef0)).
      exfalso; apply Hmt_not_abs; reflexivity.
      all: destruct mt.
      exfalso; apply Hmtype; reflexivity.
      specialize (IHHeval eq_refl Hdom (mreturn mbody) Hretval SafeRO Hmtype sΓmethodend sΓmethodinit Hwf_method_frame Hmethodbody_typing).
      rewrite HeqrΓmethodinit in IHHeval.
      eapply reachable_locations_from_initial_env_subset; eauto.
      inversion Hmt_sub.
      exfalso; apply Hmt_not_abs2; reflexivity.
      specialize (IHHeval eq_refl Hdom (mreturn mbody) Hretval ConcreteImm Hmt_not_abs sΓmethodend sΓmethodinit Hwf_method_frame Hmethodbody_typing).
      rewrite HeqrΓmethodinit in IHHeval.
      eapply reachable_locations_from_initial_env_subset; eauto.
      specialize (IHHeval eq_refl Hdom (mreturn mbody) Hretval ConcreteImm Hmt_not_abs sΓmethodend sΓmethodinit Hwf_method_frame Hmethodbody_typing).
      rewrite HeqrΓmethodinit in IHHeval.
      eapply reachable_locations_from_initial_env_subset; eauto.
    }
  - (* seq *)
  inversion Htyping; subst.
	  specialize(preservation_pico _ _ _ _ _ _ _ _ _ Hwf Htype1 Heval1) as Hwf'.
  specialize (eval_stmt_preserves_heap_domain_simple CT rΓ h s1 rΓ' h' Heval1) as Hh'.
  assert (l_z < dom h') by lia.
  eapply IHHeval2; eauto.
Qed.

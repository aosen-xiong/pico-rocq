Require Import Syntax Helpers Typing Subtyping Bigstep ViewpointAdaptation Properties Preservation WatchedFrames PotentialCapabilityCore LiveCapabilityStack PotentialCapabilityRDMPop.
From Stdlib Require Import List Sets.Ensembles Relations.Relation_Operators
  Program.Equality.
Import ListNotations.

Lemma private_call_pop_state_preserved :
  forall CT P Z cutoff rGamma h statement rGamma' h',
    eval_stmt CT rGamma h statement OK rGamma' h' ->
    forall sGamma mt sGamma' authority stack incoming snapshots policies,
      private_call_pop_state CT P Z cutoff
        (mk_watched_frame authority sGamma rGamma) stack incoming snapshots
        policies h ->
      stmt_typing CT sGamma mt statement sGamma' ->
      readonly_state_method_scope mt ->
      exists final_snapshots,
        private_call_pop_state CT P Z cutoff
          (mk_watched_frame authority sGamma' rGamma') stack incoming
          final_snapshots policies h'.
Proof.
  intros CT P Z cutoff rGamma h statement rGamma' h' Heval.
  have Heval_copy := Heval.
  dependent induction Heval;
    intros sGamma mt sGamma' authority stack incoming snapshots policies
      Hstate Htyping Hscope.
  - (* skip *) inversion Htyping; subst. exists snapshots. exact Hstate.
  - (* local *) eexists. eapply private_call_pop_state_after_local; eauto.
  - (* varass *)
    inversion Htyping; subst.
    assert (Hupdate : set_vars rΓ (update x v2 (vars rΓ)) =
        update_r_env_value rΓ x v2).
    { destruct rΓ. reflexivity. }
    rewrite Hupdate.
    eexists. eapply private_call_pop_state_after_assignment; eauto.
  - (* fldwrite *) eexists.
    eapply private_call_pop_state_after_field_write; eauto.
  - (* new *) eexists. eapply private_call_pop_state_after_new; eauto.
  - (* call *)
    destruct Hfind as [Hfind_method Hbody_definition].
    subst mbody mstmt mret rΓ' rΓ'''.
    inversion Htyping; subst.
    all: destruct Hstate as [Hfrozen Hpolicies].
    all: edestruct private_fresh_frozen_statement_enter_call_untracked as
           [origins [destination_type [Hdest Hcallee_frozen]]]; eauto.
    all: have Hcallee_wf :=
           proj1 (proj1 (proj2 (proj2 (proj2 (proj2
             (proj1 (proj1 (proj1 Hcallee_frozen)))))))).
    all: have Hcallee_policies :=
           enter_private_frame_join_policies_valid CT h
             (mk_watched_frame authority sGamma' rΓ)
             (mk_watched_frame
                (MutableCapability.call_authority authority (sqtype Ty))
                (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mkr_env (Iot ly :: vals)))
             None
             (mk_watched_call_boundary
                (mk_watched_frame authority sGamma' rΓ)
                (mreceiver (msignature mdef) :: mparams (msignature mdef))
                (mkr_env (Iot ly :: vals)) (sqtype Ty)
                (mreturn (mbody mdef)) (sqtype destination_type)
                (sqtype (mret (msignature mdef))) (dom h) origins)
             stack policies eq_refl eq_refl Hcallee_wf Hpolicies.
    all: have Hcaller_wf :=
           proj1 (proj1 (proj2 (proj2 (proj2 (proj2
             (proj1 (proj1 (proj1 Hfrozen)))))))).
    all: have Hcallee_safe := safe_typed_call_target_method_safe CT sGamma'
           mt rΓ h x m y zs sGamma' ly cy mdef Hcaller_wf Htyping Hscope
           Hval_y Hbase Hfind_method.
    all: destruct (typed_call_target CT sGamma' mt rΓ h x m y zs sGamma'
           vals ly cy mdef Hcaller_wf Htyping Hval_y Hbase Hfind_method
           Hargs) as
           [declaring_class [declaring_def [body_end
             [Hruntime_sub [Hdeclaring_class [Hmethod_member
               [Hmethod_wf [Hbody_typing Hcallee_initial_wf]]]]]]]].
    all: unfold wf_method in Hmethod_wf; simpl in Hmethod_wf.
    all: destruct Hmethod_wf as
           [_ [method_end [body_return_type
             [Hmethod_body_typing [Hreturn_dom
               [Hreturn_type [Hbody_sub Hoverriding]]]]]]].
    all: edestruct (IHHeval eq_refl Heval _ _ _ _ _ _ _ _
           (conj Hcallee_frozen Hcallee_policies) Hmethod_body_typing
           Hcallee_safe) as [body_snapshots [Hbody_frozen Hbody_policies]].
    all: admit.
  - (* seq *)
    inversion Htyping; subst.
    destruct (IHHeval1 eq_refl Heval1 sGamma mt sΓ' authority stack incoming
      snapshots policies Hstate Htype1 Hscope) as [middle Hmiddle].
    destruct (IHHeval2 eq_refl Heval2 sΓ' mt sGamma' authority stack incoming
      middle policies Hmiddle Htype2 Hscope) as [final Hfinal].
    exists final. exact Hfinal.
Admitted.

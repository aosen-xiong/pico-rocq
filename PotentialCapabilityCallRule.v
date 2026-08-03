Require Import Syntax Helpers Typing Bigstep ReadonlyHelper WatchedFrames
  PotentialCapabilityStatement.
Require Export PotentialCapabilityRDMCall.

(** The structural recursive call rule is now reduced to exactly two
    result forms.  No third semantic case or compatibility premise is hidden
    here. *)
Lemma private_policy_successful_call_rule_from_result_cases :
  private_advancing_policy_successful_nonnull_call_rule ->
  private_advancing_policy_successful_call_rule.
Proof.
  intros Hnonnull.
  unfold private_advancing_policy_successful_call_rule.
  intros P CT rGamma h destination receiver method args vals
    receiver_location runtime_class runtime_mdef body statement return_var
    result h' entry_renv body_renv final_renv Hreceiver_value Hbase
    [Hfind Hbody] Hstatement Hreturn_var Hargs Hentry Heval Hresult Hfinal IH
    caller_senv caller_scope caller_final_senv caller_authority stack Z cutoff
    caller_incoming caller_snapshots caller_policies Hpotential Hprivate
    Htyping Hscope.
  subst body statement return_var entry_renv final_renv.
  destruct result as [|return_location].
  - assert (Hupdate :
        set_vars rGamma (update destination Null_a rGamma.(vars)) =
        update_r_env_value rGamma destination Null_a).
    { destruct rGamma. reflexivity. }
    rewrite Hupdate.
    eapply private_advancing_policy_successful_null_call_case; eauto.
  - assert (Hupdate :
        set_vars rGamma
          (update destination (Iot return_location) rGamma.(vars)) =
        update_r_env_value rGamma destination (Iot return_location)).
    { destruct rGamma. reflexivity. }
    rewrite Hupdate.
    eapply Hnonnull; eauto.
Qed.

(** Final structural assembly point.  The RDM-specific contract is private:
    it first completes the non-null rule, which is then combined with the
    already proved null result case. *)
Lemma private_policy_successful_call_rule_from_rdm_case :
  private_advancing_policy_successful_rdm_call_case ->
  private_advancing_policy_successful_call_rule.
Proof.
  intros Hrdm. eapply private_policy_successful_call_rule_from_result_cases.
  eapply private_advancing_policy_successful_nonnull_rule_from_rdm_case.
  exact Hrdm.
Qed.

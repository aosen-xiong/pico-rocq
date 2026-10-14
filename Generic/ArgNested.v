From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep DynLemmas RuntimeTyping ConfigLemmas PreservationCases PreservationCall
  Preservation ReadonlyFlat ReadonlyWorlds ReadonlyGeneric GhostLabels ArgViews
  GhostTyping GhostForget GhostFit ArgTyping GhostInvariant ArgFit ArgInvariant
  ArgCases GhostOverride ArgClean ArgOverride GhostCall ArgCall GhostEntry ArgMain
  ArgEntry ArgRsf GhostSignature ArgSignature.

(** Readonly-state and transitive-state preservation for every call of a run.

    [rs_ts_preservation_from_start] speaks about a call made by the statement
    that runs from the start state.  This file covers a call made anywhere
    during the run, at any depth of nested method bodies. *)

(* ------------------EVALUATIONS INSIDE AN EVALUATION------------------*)

(** [occurs CT rΓ h s rΓi hi si res rΓi' hi']: while [s] is evaluated from
    [rΓ] and [h], the statement [si] is evaluated from [rΓi] and [hi] and
    ends with [res] in [rΓi'] and [hi'].  The inner evaluation is the whole
    one, the first or the second part of a sequence, or lies in the body of
    a called method. *)
Inductive occurs (CT : class_table)
    : r_env -> heap -> stmt ->
      r_env -> heap -> stmt -> eval_result -> r_env -> heap -> Prop :=
  | occ_here : forall rΓ h s res rΓ' h'
      (Heval : eval_stmt CT rΓ h s res rΓ' h'),
      occurs CT rΓ h s rΓ h s res rΓ' h'
  | occ_seq_l : forall rΓ h s1 s2 rΓi hi si res rΓi' hi'
      (Hin : occurs CT rΓ h s1 rΓi hi si res rΓi' hi'),
      occurs CT rΓ h (SSeq s1 s2) rΓi hi si res rΓi' hi'
  | occ_seq_r : forall rΓ h s1 s2 rΓ1 h1 rΓi hi si res rΓi' hi'
      (Hfirst : eval_stmt CT rΓ h s1 OK rΓ1 h1)
      (Hin : occurs CT rΓ1 h1 s2 rΓi hi si res rΓi' hi'),
      occurs CT rΓ h (SSeq s1 s2) rΓi hi si res rΓi' hi'
  | occ_call : forall rΓ h x m y Us Qs zs ly cy D mdef vals rΓc
        rΓi hi si res rΓi' hi'
      (Hval_y : runtime_getVal rΓ y = Some (Iot ly))
      (Hbase  : r_basetype h ly = Some cy)
      (Hfind  : FindMethodWithName CT cy m D mdef)
      (Hargs  : runtime_lookup_list rΓ zs = Some vals)
      (Hframe : callee_env CT rΓ h ly D Us Qs vals rΓc)
      (Hin : occurs CT rΓc h (mbody_stmt (mbody mdef)) rΓi hi si res rΓi' hi'),
      occurs CT rΓ h (SCall x m y Us Qs zs) rΓi hi si res rΓi' hi'.

(** Every evaluation inside a well-typed evaluation from a well-formed state
    that satisfies the readonly-state invariant is itself a well-typed
    evaluation from such a state. *)
Lemma occurs_config : forall CT rΓ h s rΓi hi si res rΓi' hi',
  occurs CT rΓ h s rΓi hi si res rΓi' hi' ->
  forall Δ sΓ mt sΓ',
    wf_r_config CT Δ sΓ rΓ h ->
    RSFp CT Δ rΓ h ->
    stmt_typing CT Δ sΓ mt s sΓ' ->
    exists Δi sΓi mti sΓi',
      wf_r_config CT Δi sΓi rΓi hi /\
      RSFp CT Δi rΓi hi /\
      stmt_typing CT Δi sΓi mti si sΓi' /\
      eval_stmt CT rΓi hi si res rΓi' hi'.
Proof.
  intros CT rΓ h s rΓi hi si res rΓi' hi' H.
  induction H; intros Δ sΓ mt sΓ' Hwf HR Htype.
  - exists Δ, sΓ, mt, sΓ'. auto.
  - inversion Htype; subst. eapply IHoccurs; eauto.
  - inversion Htype; subst.
    eapply IHoccurs.
    + eapply preservation_pico; eauto.
    + eapply rsfp_preservation; eauto.
    + eauto.
  - destruct (call_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe)
      as (ι1 & o1 & oy1 & Tx1 & _ & _ & _ & _ & _ & _ &
          _ & Hwm & Hcfg & _).
    pose proof Hwm as (_ & _ & _ & (sΓb & Tb & Hbody & _) & _).
    destruct HR as (H1 & H2 & H3 & H4).
    eapply IHoccurs; [exact Hcfg | | exact Hbody].
    refine (conj (conj (proj1 H1) _) (conj H2 (conj _ _))).
    + exact (rsf_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1).
    + exact (rsfp_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
    + exact (rsfp_call_sb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hwf Htype Hval_y Hbase Hfind Hargs Hframe H1 H2 H3 H4).
Qed.

(* ------------------THE THEOREM------------------*)

(** Run any well-typed statement from a start state.  For every call that
    is evaluated during the run, at any depth, and that selects a
    readonly-state or transitive-state method: however the call ends, the
    protected fields of every object that exists when the call starts are
    unchanged. *)
Theorem rs_ts_preservation_all_calls :
  forall CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs res rΓ' h' ly cy D mdef,
    start_state CT Δ sΓ rΓ0 h0 ->
    stmt_typing CT Δ sΓ mt s sΓ1 ->
    occurs CT rΓ0 h0 s rΓ h (SCall x m y Us Qs zs) res rΓ' h' ->
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
  intros CT Δ sΓ mt rΓ0 h0 s sΓ1 rΓ h x m y Us Qs zs res rΓ' h' ly cy D mdef
    (Hwf0 & Hc & Hm & Hobj) Hts Hocc Hvy Hbase Hfind l qr C Rs vals f Hl Hcase.
  destruct (occurs_config _ _ _ _ _ _ _ _ _ _ Hocc Δ sΓ mt sΓ1 Hwf0
              (RSFp_start_plain CT Δ rΓ0 h0 Hc Hm Hobj) Hts)
    as (Δi & sΓi & mti & sΓi' & Hwf & HR & Htc & Hec).
  destruct Hcase as [[Hrs Hf] | Htsc].
  - exact (readonly_state_preservation_final_signature_any CT Δi sΓi mti rΓ h
             x m y Us Qs zs sΓi' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Hrs l qr C Rs vals f Hl Hf).
  - exact (transitive_state_preservation_final_signature_any CT Δi sΓi mti rΓ h
             x m y Us Qs zs sΓi' rΓ' h' ly cy D mdef res Hwf HR Htc Hec Hvy
             Hbase Hfind Htsc l qr C Rs vals f Hl).
Qed.

(** The relation is not empty where it matters: the body of a called method
    is evaluated inside the call. *)
Example occurs_in_body : forall CT rΓ h x m y Us Qs zs ly cy D mdef vals rΓc
    rb rΓb hb,
  runtime_getVal rΓ y = Some (Iot ly) ->
  r_basetype h ly = Some cy ->
  FindMethodWithName CT cy m D mdef ->
  runtime_lookup_list rΓ zs = Some vals ->
  callee_env CT rΓ h ly D Us Qs vals rΓc ->
  eval_stmt CT rΓc h (mbody_stmt (mbody mdef)) rb rΓb hb ->
  occurs CT rΓ h (SCall x m y Us Qs zs) rΓc h (mbody_stmt (mbody mdef)) rb rΓb hb.
Proof. intros. eapply occ_call; eauto. apply occ_here. assumption. Qed.

Print Assumptions rs_ts_preservation_all_calls.

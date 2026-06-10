From Stdlib Require Import List.
From Stdlib Require Import Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping ViewpointAdaptation.

Definition ex_type (q : q) : qualified_type :=
  Build_qualified_type q 0.

Definition ex_ctor_sig : constructor_sig :=
  {|
    cqualifier := RDM_c;
    cparams := [ex_type RDM]
  |}.

Definition ex_class : class_def :=
  {|
    signature :=
      {|
        class_qualifier := RDM_c;
        cname := 0;
        super := None
      |};
    body :=
      {|
        fields := [];
        constructor := {| csignature := ex_ctor_sig |};
        methods := []
      |}
  |}.

Definition ex_CT : class_table := [ex_class].

Definition ex_senv (qarg : q) : s_env :=
  [ex_type RDM; ex_type qarg; ex_type RO].

Example object_creation_rdm_constructor_rdm_instantiation :
  stmt_typing ex_CT (ex_senv RDM) SafeRO (SNew 2 RDM_c 0 [1]) (ex_senv RDM).
Proof.
  eapply S_New with
    (Tx := ex_type RO)
    (argtypes := [ex_type RDM])
    (Tthis := ex_type RDM)
    (consig := ex_ctor_sig).
  - unfold wf_senv, ex_senv, ex_type, wf_stypeuse, bound, find_class, gget,
      vpa_mutability_bound.
    simpl.
    repeat split; try lia; repeat constructor; discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - reflexivity.
  - repeat constructor; try discriminate.
  - repeat constructor; try discriminate.
Qed.

Example object_creation_rdm_constructor_imm_instantiation :
  stmt_typing ex_CT (ex_senv Imm) SafeRO (SNew 2 Imm_c 0 [1]) (ex_senv Imm).
Proof.
  eapply S_New with
    (Tx := ex_type RO)
    (argtypes := [ex_type Imm])
    (Tthis := ex_type RDM)
    (consig := ex_ctor_sig).
  - unfold wf_senv, ex_senv, ex_type, wf_stypeuse, bound, find_class, gget,
      vpa_mutability_bound.
    simpl.
    repeat split; try lia; repeat constructor; discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - reflexivity.
  - repeat constructor; try discriminate.
  - repeat constructor; try discriminate.
Qed.

Example object_creation_rdm_constructor_mut_instantiation :
  stmt_typing ex_CT (ex_senv Mut) SafeRO (SNew 2 Mut_c 0 [1]) (ex_senv Mut).
Proof.
  eapply S_New with
    (Tx := ex_type RO)
    (argtypes := [ex_type Mut])
    (Tthis := ex_type RDM)
    (consig := ex_ctor_sig).
  - unfold wf_senv, ex_senv, ex_type, wf_stypeuse, bound, find_class, gget,
      vpa_mutability_bound.
    simpl.
    repeat split; try lia; repeat constructor; discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - reflexivity.
  - repeat constructor; try discriminate.
  - repeat constructor; try discriminate.
Qed.

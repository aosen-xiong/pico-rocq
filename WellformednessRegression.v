From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers ViewpointAdaptation Subtyping Typing Bigstep.

Definition witness_type : qualified_type :=
  Build_qualified_type RDM (TRef 0).

Definition witness_constructor : constructor_def :=
  {| csignature := {| cqualifier := RDM_c; cparams := [] |} |}.

Definition witness_class : class_def :=
  {| signature :=
       {| class_qualifier := RDM_c; cname := 0; super := None |};
     body :=
       {| fields := []; constructor := witness_constructor; methods := [] |} |}.

Definition witness_CT : class_table := [witness_class].

Example witness_class_table_well_formed : wf_class_table witness_CT.
Proof.
  unfold wf_class_table, witness_CT.
  repeat split.
  - constructor.
    + eapply WFObjectDef with (class_name := 0).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * unfold wf_constructor_object, parent_lookup,
          constructor_def_lookup, bound.
        simpl.
        repeat split.
        eapply CF_Object with (def := witness_class); reflexivity.
      * constructor.
      * constructor.
    + constructor.
  - exists witness_class. simpl. auto.
  - intros i def Hi Hfind.
    exfalso. apply find_class_dom in Hfind. simpl in Hfind. lia.
  - intros i def Hfind.
    destruct i.
    + simpl in Hfind. injection Hfind as <-. reflexivity.
    + exfalso. apply find_class_dom in Hfind. simpl in Hfind. lia.
Qed.

Definition witness_heap : heap :=
  [mkObj (mkruntime_type Mut_r 0) []].

Definition witness_renv : r_env := mkr_env [Iot 0].

Definition witness_senv : s_env := [witness_type].

Example witness_runtime_configuration_well_formed :
  wf_r_config witness_CT witness_senv witness_renv witness_heap.
Proof.
  unfold wf_r_config.
  split.
  - exact witness_class_table_well_formed.
  - split.
    + unfold wf_heap.
      intros i Hi.
      destruct i; [|simpl in Hi; lia].
      unfold wf_obj, witness_heap, witness_CT, runtime_getObj, gget,
        wf_rtypeuse, bound.
      simpl.
      split.
      * split; [lia|reflexivity].
      * exists ([] : list field_def).
        split.
        -- eapply CF_Object with (def := witness_class); reflexivity.
        -- split; [reflexivity|constructor].
    + split.
      * unfold wf_renv.
        split.
        -- unfold witness_renv. simpl. lia.
        -- split.
           ++ exists 0. unfold witness_renv, witness_heap. simpl.
              split; [reflexivity|lia].
           ++ unfold witness_renv, witness_heap, runtime_getObj, gget.
              simpl. constructor; constructor.
      * split.
        -- unfold wf_senv.
           split.
           ++ unfold witness_senv. simpl. lia.
           ++ unfold witness_senv.
              constructor.
              ** unfold witness_type, wf_stypeuse, witness_CT, bound,
                   find_class, gget, vpa_mutability_bound.
                 simpl.
                 split.
                 --- constructor. discriminate.
                 --- lia.
              ** constructor.
        -- split.
           ++ reflexivity.
           ++ intros i qcontext Hthis Hmut n Hn sqt Hnth.
              destruct n; [|simpl in Hn; lia].
              simpl in Hthis, Hmut, Hnth.
              injection Hthis as <-.
              injection Hmut as <-.
              injection Hnth as <-.
              unfold wf_r_typable, r_type, witness_heap, runtime_getObj,
                gget, witness_type.
              simpl.
              split.
              ** apply Subtyping.base_ref.
                 apply Subtyping.class_refl. simpl. lia.
              ** exact I.
Qed.

From Stdlib Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers.
Require Import String.
Require Import Stdlib.Sets.Ensembles.
From RecordUpdate Require Import RecordUpdate.
Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Classes.RelationClasses.

Inductive reachable (h : heap): Loc -> Loc -> Prop :=

| rch_heap:
    forall l,
      l < dom h ->
      reachable h l l

| rch_step:
    forall l0 l1 obj f,
      l1 < dom h ->
      runtime_getObj h l0 = Some obj ->
      getVal obj.(fields_map) f = Some (Iot l1) ->
      reachable h l0 l1

| rch_trans:
    forall l0 l1 l2,
      reachable h l0 l1 ->
      reachable h l1 l2 ->
      reachable h l0 l2.


Inductive reachable_abs (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=

| reachable_abs_heap :
    forall l,
      l < dom h ->
      reachable_abs CT h l l

| reachable_abs_step :
    forall l0 l1 any C vals k,
      (* concrete step, as in [rch_step] *)
      l1 < dom h ->
      runtime_getObj h l0 = Some (mkObj (mkruntime_type any C) vals) ->
      (* field [f] corresponds to index [k] and is RDM/Imm in the abstract state *)
      nth_error vals k = Some (Iot l1) ->
      (sf_mutability_rel CT C k RDM_f \/
       sf_mutability_rel CT C k Imm_f) ->
      (sf_assignability_rel CT C k RDA \/
      sf_assignability_rel CT C k Final) ->
      reachable_abs CT h l0 l1

| reachable_abs_trans :
    forall l0 l1 l2,
      reachable_abs CT h l0 l1 ->
      reachable_abs CT h l1 l2 ->
      reachable_abs CT h l0 l2.

Definition reachable_locset
           (CT : class_table) (h : heap) (root : Loc) : Ensembles.Ensemble Loc :=
  fun l => reachable_abs CT h root l.

Definition protected_locset
  (CT : class_table) (h : heap) (l_root : Loc) : Ensembles.Ensemble Loc :=
  fun l_target => reachable_abs CT h l_root l_target.

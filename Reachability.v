From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require String.
Require Import Stdlib.Sets.Ensembles.
Require Import Stdlib.Classes.RelationClasses.
Require Import Stdlib.Logic.Classical_Prop.
Import ListNotations.
From RecordUpdate Require Import RecordUpdate.
Require Import Syntax Typing Subtyping ViewpointAdaptation Helpers.

Inductive reachable (h : heap) : Loc -> Loc -> Prop :=

  | rch_heap : forall l
      (Hdom : l < dom h),
      reachable h l l

  | rch_step : forall l0 l1 obj f
      (Hdom    : l1 < dom h)
      (Hobj    : runtime_getObj h l0 = Some obj)
      (Hfield  : getVal obj.(fields_map) f = Some (Iot l1)),
      reachable h l0 l1

  | rch_trans : forall l0 l1 l2
      (Hreach1 : reachable h l0 l1)
      (Hreach2 : reachable h l1 l2),
      reachable h l0 l2.


Inductive reachable_abs (CT : class_table) (h : heap) : Loc -> Loc -> Prop :=

  | reachable_abs_heap : forall l
      (Hdom : l < dom h),
      reachable_abs CT h l l

  | reachable_abs_step : forall l0 l1 any C vals k
      (Hdom        : l1 < dom h)
      (Hobj        : runtime_getObj h l0 = Some (mkObj (mkruntime_type any C) vals))
      (Hfield      : nth_error vals k = Some (Iot l1))
      (Hmut_abs    : sf_mutability_rel CT C k RDM_f \/ sf_mutability_rel CT C k Imm_f)
      (Hassign_abs : sf_assignability_rel CT C k RDA \/ sf_assignability_rel CT C k Final),
      reachable_abs CT h l0 l1

  | reachable_abs_trans : forall l0 l1 l2
      (Hreach1 : reachable_abs CT h l0 l1)
      (Hreach2 : reachable_abs CT h l1 l2),
      reachable_abs CT h l0 l2.

Definition protected_locset
  (CT : class_table) (h : heap) (l_root : Loc) : Ensembles.Ensemble Loc :=
  fun l_target => reachable_abs CT h l_root l_target.

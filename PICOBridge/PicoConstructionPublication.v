From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep DerivedCache ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoFinalFieldPublication.
Require Import MemoryModels.JMM.FinalFieldPublication.

(** * PICO Construction to Final-Snapshot Publication

    PICO constructors initialize an object's complete field vector at [SNew].
    This relation synchronizes that existing CESK allocation step with one
    [FinalFreeze] action for a selected list of final fields.  It does not make
    allocation itself a publication: [FinalPublish] and [FinalAcquire] remain
    separate actions of the publication interface. *)

Fixpoint select_field_values
    (values : list value) (fields : list var) : option (list value) :=
  match fields with
  | [] => Some []
  | field :: tail =>
      match nth_error values field, select_field_values values tail with
      | Some value, Some selected => Some (value :: selected)
      | _, _ => None
      end
  end.

Lemma select_field_values_sound :
  forall values fields selected
    (Hselect : select_field_values values fields = Some selected),
    Forall2 (fun field value => nth_error values field = Some value)
      fields selected.
Proof.
  intros values fields.
  induction fields as [|field fields IH]; intros selected Hselect.
  - simpl in Hselect. inversion Hselect. constructor.
  - simpl in Hselect.
    destruct (nth_error values field) as [value |] eqn:Hfield;
      [|discriminate].
    destruct (select_field_values values fields) as [tail |] eqn:Htail;
      [|discriminate].
    inversion Hselect; subst selected.
    constructor; [exact Hfield |].
    eapply IH. reflexivity.
Qed.

Lemma allocated_object_field_read :
  forall h runtime values field value
    (Hfield : nth_error values field = Some value),
    field_read (h ++ [mkObj runtime values]) (length h) field value.
Proof.
  intros h runtime values field value Hfield.
  exists (mkObj runtime values). split.
  - unfold runtime_getObj.
    rewrite nth_error_app2; [|lia].
    replace (length h - length h) with 0 by lia.
    reflexivity.
  - exact Hfield.
Qed.

Lemma allocated_object_field_reads :
  forall h runtime values fields selected
    (Hselect : select_field_values values fields = Some selected),
    field_reads (h ++ [mkObj runtime values]) (length h) fields selected.
Proof.
  intros h runtime values fields selected Hselect.
  pose proof (select_field_values_sound values fields selected Hselect)
    as Hselected.
  clear Hselect.
  induction Hselected.
  - constructor.
  - constructor.
    + eapply allocated_object_field_read. exact H.
    + exact IHHselected.
Qed.

Record pico_new_publication_config : Type := mkPicoNewPublicationConfig {
  pnpc_control : pico_core_expr;
  pnpc_state : pico_core_state;
  pnpc_publication : final_publication_state
}.

(** A source [SNew] transition paired with the freeze of the newly allocated
    object's selected final fields.  The selected fields are required to be
    final in the allocated class. *)
Inductive pico_new_freeze_step
    `{CacheMemoryModel} (CT : class_table) (abs_fields : list var) :
    pico_new_publication_config -> pico_new_publication_config -> Prop :=
  | PicoNewFreezeStep : forall
      rGamma x qc C args loc_this qthisr values qadapted V K
      h sigma publication snapshot,
      runtime_getVal rGamma 0 = Some (Iot loc_this) ->
      runtime_lookup_list rGamma args = Some values ->
      r_muttype h loc_this = Some qthisr ->
      vpa_mutability_object_creation qthisr qc = qadapted ->
      final_fields CT C abs_fields ->
      select_field_values values abs_fields = Some snapshot ->
      frozen_snapshot_lookup (length h) (fps_frozen publication) = None ->
      pico_new_freeze_step CT abs_fields
        (mkPicoNewPublicationConfig
          (CoreRun rGamma (SNew x qc C args) V K)
          (mkPicoCoreState h sigma)
          publication)
        (mkPicoNewPublicationConfig
          (CoreRun
            (set_vars rGamma (update x (Iot (length h)) (vars rGamma)))
            SSkip V K)
          (mkPicoCoreState
            (h ++ [mkObj (mkruntime_type qadapted C) values])
            (pico_core_alloc_weak sigma
              (mkObj (mkruntime_type qadapted C) values) V))
          (mkFinalPublicationState
            ((length h, snapshot) :: fps_frozen publication)
            (fps_published publication)
            (fps_observed publication))).

(** Erasing publication state yields precisely the existing CESK [PCS_New]
    transition. *)
Theorem pico_new_freeze_step_erases_to_core :
  forall `{CacheMemoryModel} CT abs_fields before after
    (Hstep : pico_new_freeze_step CT abs_fields before after),
    pico_core_step CT
      (pnpc_control before) (pnpc_state before)
      (pnpc_control after) (pnpc_state after).
Proof.
  intros Hmem CT abs_fields before after Hstep.
  inversion Hstep; subst; simpl.
  eapply PCS_New with
    (loc_this := loc_this)
    (qthisr := qthisr)
    (vals := values)
    (o := mkObj
      (mkruntime_type (vpa_mutability_object_creation qthisr qc) C) values)
    (qadapted := vpa_mutability_object_creation qthisr qc)
    (h' := h ++ [mkObj
      (mkruntime_type (vpa_mutability_object_creation qthisr qc) C) values])
    (sigma' := pico_core_alloc_weak sigma
      (mkObj
        (mkruntime_type (vpa_mutability_object_creation qthisr qc) C) values)
      V);
    eauto.
Qed.

(** The synchronized step contributes one legal [FinalFreeze] action. *)
Theorem pico_new_freeze_step_projects_to_publication :
  forall `{CacheMemoryModel} CT abs_fields before after
    (Hstep : pico_new_freeze_step CT abs_fields before after),
    final_publication_step
      (pnpc_publication before) (pnpc_publication after).
Proof.
  intros Hmem CT abs_fields before after Hstep.
  inversion Hstep; subst; simpl.
  constructor. assumption.
Qed.

(** The frozen snapshot is read from the actual post-allocation heap and
    consists only of fields declared final for the allocated class. *)
Theorem pico_new_freeze_step_establishes_final_heap_snapshot :
  forall `{CacheMemoryModel} CT abs_fields before after
    (Hstep : pico_new_freeze_step CT abs_fields before after),
    exists C loc snapshot,
      pico_final_heap_snapshot CT C abs_fields
        (pcs_heap (pnpc_state after)) loc snapshot /\
      final_snapshot_frozen (pnpc_publication after) loc snapshot.
Proof.
  intros Hmem CT abs_fields before after Hstep.
  inversion Hstep; subst; simpl.
  exists C, (length h), snapshot.
  split.
  - unfold pico_final_heap_snapshot.
    exists (mkObj
      (mkruntime_type (vpa_mutability_object_creation qthisr qc) C) values).
    split.
    + unfold runtime_getObj.
      rewrite nth_error_app2; [|lia].
      replace (length h - length h) with 0 by lia.
      reflexivity.
    + split; [reflexivity |].
      split.
      * assumption.
      * eapply allocated_object_field_reads. eassumption.
  - unfold final_snapshot_frozen. simpl.
    rewrite Nat.eqb_refl. reflexivity.
Qed.

From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation
  ViewpointAdaptation.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreInvariant PICOBridge.PicoCoreTypingSupport
  PICOBridge.PicoCoreTyping PICOBridge.PicoSemanticConcurrency.

(** * Type Safety of the Core Machine under Interleaving

    PICO's type soundness is proved for the big-step semantics, which
    describes one thread running alone.  This file proves it for the
    small-step machine with weak field histories and any number of
    interleaved threads.

    The one fact the big-step proof does not need is that a weak read returns
    a well-typed value: a read may return any value in the field's history,
    not only the current heap value.  The typed-histories invariant below
    states that every value ever written to a field is well typed for that
    field.  It is phrased with the runtime types of the heap alone, so it is
    stable under every step of every thread. *)

Section typed_histories.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).

  (** [v] is an admissible value of field [f] of the object at [ι]: the
      condition [wf_obj] imposes on a field value, strengthened so that
      [Null_a] inhabits only reference fields.  It mentions only runtime
      types, never field contents. *)
  Definition field_value_ok (h : heap) (ι : Loc) (f : var) (v : value) : Prop :=
    exists rt field_defs fdef,
      r_type h ι = Some rt /\
      CollectFields CT (rctype rt) field_defs /\
      nth_error field_defs f = Some fdef /\
      match v with
      | Null_a => exists C, f_base_type (ftype fdef) = TRef C
      | Int _ => f_base_type (ftype fdef) = TInt
      | Iot loc =>
          exists rqt,
            r_type h loc = Some rqt /\
            base_subtype CT (TRef (rctype rqt)) (f_base_type (ftype fdef)) /\
            qualifier_typable_heap (rqtype rqt)
              (vpa_mutability_rec_fld (rqtype rt) (mutability (ftype fdef)))
      end.

  (** Every value in every field history is admissible for its field. *)
  Definition histories_typed (S : pico_core_state) : Prop :=
    forall loc f v,
      List.In v (values_written_to (pcs_weak S) (loc, f)) ->
      field_value_ok (pcs_heap S) loc f v.

  Lemma field_value_ok_heap_types_extend :
    forall h h' ι f v,
      pico_core_heap_types_extend h h' ->
      field_value_ok h ι f v ->
      field_value_ok h' ι f v.
  Proof.
    intros h h' ι f v [_ Htypes] (rt & field_defs & fdef & Hrt & Hcf & Hnth & Hv).
    exists rt, field_defs, fdef.
    split; [exact (Htypes ι rt Hrt) |].
    split; [exact Hcf |].
    split; [exact Hnth |].
    destruct v as [| loc | n]; try exact Hv.
    destruct Hv as (rqt & Hrqt & Hbase & Hqual).
    exists rqt. split; [exact (Htypes loc rqt Hrqt) | split; assumption].
  Qed.
End typed_histories.

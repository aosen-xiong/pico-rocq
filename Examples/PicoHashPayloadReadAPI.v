From Stdlib Require Import List Lia.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import ownp.
Import ListNotations.

Require Import Syntax Helpers Subtyping Typing Bigstep.
Require Import Core.GenericCacheProtocol Core.GenericDerivedCache
  Examples.PicoIfZeroCacheExamples.
Require Import Iris.GenericCacheGhostState.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant PICOBridge.PicoIrisSemImmLogicalRelation
  PICOBridge.PicoIrisSemanticAPI.
Require Import Examples.PicoSemanticCacheAPIExamples
  Examples.PicoConcreteHashModel Examples.PicoSemanticConcurrencyExamples.

(** * The Concurrent Hash Method Through the Iris API

    The concurrent example's cached hash method computes its value by
    reading the receiver's final payload.  This file installs that exact
    method through the Iris hash API, with the concrete derivation-defined
    provider, and no separate computation premise. *)

(** In the concurrent class table, subclassing only goes to smaller class
    names. *)
Lemma pico_hash_concurrent_class_subtype_le : forall C D,
  class_subtype pico_hash_concurrent_CT C D -> D <= C.
Proof.
  intros C D Hsub.
  remember pico_hash_concurrent_CT as CT eqn:HCT.
  induction Hsub as [CT C Hdom | CT C D E Hsub1 IH1 Hsub2 IH2
    | CT C D Hdom_C Hdom_D Hparent]; subst CT.
  - lia.
  - specialize (IH1 eq_refl). specialize (IH2 eq_refl). lia.
  - destruct C as [| [| C]].
    + discriminate Hparent.
    + simpl in Hparent. inversion Hparent; subst.
      unfold pico_hash_witness_root. lia.
    + simpl in Hdom_C. lia.
Qed.

Lemma pico_hash_concurrent_cache_runtime_assignable
    `{CacheMemoryModel} :
  PicoHashCacheRuntimeAssignable pico_hash_concurrent_CT
    pico_hash_witness_receiver_type.
Proof.
  intros rGamma h loc (qcontext & this & Hwf & _ & _ & Htyped) Hreceiver.
  destruct (Htyped 0 pico_hash_witness_receiver_type eq_refl)
    as (v & Hv & Hvalue).
  change (runtime_getVal rGamma 0 = Some (Iot loc)) in Hreceiver.
  rewrite Hreceiver in Hv. injection Hv as <-.
  simpl in Hvalue. unfold wf_r_typable, r_type in Hvalue.
  destruct (runtime_getObj h loc) as [o |] eqn:Hobj; [| contradiction].
  destruct Hvalue as [Hbase _].
  have Hclass := base_ref_class_subtype pico_hash_concurrent_CT
    (rctype (rt_type o)) pico_hash_witness_receiver_type
    pico_hash_witness_class Hbase eq_refl.
  have Hle := pico_hash_concurrent_class_subtype_le _ _ Hclass.
  have [Hdom _] := class_subtype_domain _ _ _ Hclass.
  assert (HC : rctype (rt_type o) = pico_hash_witness_class).
  { unfold pico_hash_witness_class in *. simpl in Hdom. lia. }
  exists o, Assignable.
  split; [reflexivity |].
  split.
  - rewrite HC. exact pico_hash_concurrent_cache_assignable.
  - destruct (rqtype (rt_type o)); reflexivity.
Qed.

Section concurrent_hash_read_api.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : @CacheMemoryModelProgress Hmem}.
  Context `{!ownPGS (pico_core_language pico_hash_concurrent_CT) Sigma}.
  Context `{!genericCacheG hash_cache_protocol Sigma}.

  (** The concurrent example's own method, which reads its payload, is a
      callable and exported API method of the derivation-defined provider. *)
  Theorem pico_hash_concurrent_method_api_wfI :
    ⊢ pico_callable_method_wfI pico_hash_concurrent_CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        pico_hash_concurrent_value
        (pico_hash_cache_adapter pico_hash_concurrent_receiver)
        (pico_concrete_hash_semimm pico_hash_concurrent_CT
          pico_hash_concurrent_receiver pico_hash_derive_method
          pico_hash_concurrent_initial_heap pico_hash_concurrent_value))
      pico_hash_witness_class pico_hash_concurrent_method_def
      (pico_hash_method_contract_at pico_hash_concurrent_receiver
        pico_hash_concurrent_value) ∗
    pico_exported_methodI pico_hash_concurrent_CT
      (pico_core_semimm_worldI hash_cache_protocol pico_hash_stable_abs
        pico_hash_concurrent_value
        (pico_hash_cache_adapter pico_hash_concurrent_receiver)
        (pico_concrete_hash_semimm pico_hash_concurrent_CT
          pico_hash_concurrent_receiver pico_hash_derive_method
          pico_hash_concurrent_initial_heap pico_hash_concurrent_value))
      (pico_hash_method_contract_at pico_hash_concurrent_receiver
        pico_hash_concurrent_value)
      pico_hash_concurrent_method_def.
  Proof.
    iApply (pico_heap_hash_read_callable_api_wfI pico_hash_concurrent_CT
      pico_hash_concurrent_receiver pico_hash_derive_method
      pico_hash_concurrent_initial_heap pico_hash_concurrent_value
      pico_hash_witness_class pico_hash_witness_receiver_type
      pico_hash_concurrent_method).
    - exact pico_hash_concurrent_method_typing.
    - reflexivity.
    - intros parent_def parent mdef_parent qc Hclass Hsuper Hbound Hfind.
      simpl in Hclass. inversion Hclass; subst parent_def.
      simpl in Hsuper. inversion Hsuper; subst parent.
      inversion Hfind; subst.
      + simpl in Hfind0. inversion Hfind0; subst def.
        unfold pico_hash_witness_root_def in Hget_method.
        simpl in Hget_method. discriminate.
      + simpl in Hfind0. inversion Hfind0; subst def.
        unfold pico_hash_witness_root_def in Hsuper0.
        simpl in Hsuper0. discriminate.
    - exact pico_hash_concurrent_cache_runtime_assignable.
    - exact (pico_hash_payload_abstract pico_hash_concurrent_CT
        pico_hash_concurrent_payload_field_def).
    - exact pico_hash_concurrent_payload_footprint.
    - exists pico_hash_witness_object. split; reflexivity.
  Qed.
End concurrent_hash_read_api.

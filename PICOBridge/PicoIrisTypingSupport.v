From iris.program_logic Require Import weakestpre ownp adequacy.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import lib.excl_auth.
From iris.base_logic Require Import own.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation
  ViewpointAdaptation.
Require Export PICOBridge.PicoCoreTypingSupport.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreWP.
Require Import Core.GenericCacheProtocol Core.CacheLRVerticalSlice.
Require Import Iris.GenericCacheGhostState Iris.IrisSemanticBridge.


(** * PICO Iris Typing Support

    This file contains only pure typed-runtime value and environment facts
    shared by the typing-directed and SemImm developments.  It deliberately
    contains no statement, method, contract, or adequacy interpretation. *)

Section pico_typing_support.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).
  Context `{!irisGS_gen hlc (pico_core_language CT) Σ}.

  Local Notation pico_typed_runtime_value := (pico_typed_runtime_value CT) (only parsing).
  Local Notation pico_typed_runtime_env := (pico_typed_runtime_env CT) (only parsing).
  Local Notation pico_typed_runtime_env_wf_config := (pico_typed_runtime_env_wf_config CT) (only parsing).
  Local Notation pico_typed_runtime_env_receiver := (pico_typed_runtime_env_receiver CT) (only parsing).
  Local Notation pico_typed_runtime_env_runtime_lookup := (pico_typed_runtime_env_runtime_lookup CT) (only parsing).
  Local Notation pico_typed_runtime_env_local_runtime_absent := (pico_typed_runtime_env_local_runtime_absent CT) (only parsing).
  Local Notation pico_typed_runtime_env_after_local := (pico_typed_runtime_env_after_local CT) (only parsing).
  Local Notation pico_typed_runtime_env_after_varass_null := (pico_typed_runtime_env_after_varass_null CT) (only parsing).
  Local Notation pico_typed_runtime_env_after_varass_int := (pico_typed_runtime_env_after_varass_int CT) (only parsing).
  Local Notation pico_typed_runtime_env_after_varass_var := (pico_typed_runtime_env_after_varass_var CT) (only parsing).
  Local Notation pico_typed_runtime_env_update_value := (pico_typed_runtime_env_update_value CT) (only parsing).
  Local Notation pico_typed_runtime_value_from_updated_env := (pico_typed_runtime_value_from_updated_env CT) (only parsing).
  Local Notation pico_typed_runtime_field_value_exists := (pico_typed_runtime_field_value_exists CT) (only parsing).
  Local Notation pico_typed_runtime_env_after_fldwrite_success := (pico_typed_runtime_env_after_fldwrite_success CT) (only parsing).
  Local Notation stmt_typing_fldwrite_result_env := (stmt_typing_fldwrite_result_env CT) (only parsing).
  Local Notation pico_typed_runtime_env_after_new_success := (pico_typed_runtime_env_after_new_success CT) (only parsing).
  Local Notation wf_renv_preserved_by_eval_heap := (wf_renv_preserved_by_eval_heap CT) (only parsing).
  Local Notation wf_r_typable_preserved_by_eval_heap := (wf_r_typable_preserved_by_eval_heap CT) (only parsing).
  Local Notation pico_typed_runtime_env_preserved_by_eval_heap := (pico_typed_runtime_env_preserved_by_eval_heap CT) (only parsing).

(** Public state interpretation boundary for the new core language.  The
    concrete Iris [state_interp] remains abstract, but LR rules can name the
    pure agreement fact between the ordinary PICO heap and the weak
    field-history state. *)
  Definition pico_core_state_agreeI (sigma : pico_core_state) : iProp Σ :=
    ⌜heap_wm_type_agree (pcs_heap sigma) (pcs_weak sigma)⌝.


  Definition pico_typed_runtime_valueI
      (h : heap) (qcontext : q_r) (T : qualified_type)
      (v : Syntax.value) : iProp Σ :=
    ⌜pico_typed_runtime_value h qcontext T v⌝.


  Definition pico_typed_runtime_envI
      (sΓ : s_env) (rΓ : r_env) (h : heap) : iProp Σ :=
    ⌜pico_typed_runtime_env sΓ rΓ h⌝.
End pico_typing_support.

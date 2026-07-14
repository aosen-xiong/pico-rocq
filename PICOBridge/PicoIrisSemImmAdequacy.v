From iris.program_logic Require Import weakestpre ownp adequacy.
From iris.proofmode Require Import proofmode.

Require Import Syntax Typing.
Require Import Core.GenericCacheProtocol Iris.GenericCacheGhostState
  Iris.IrisSemanticBridge.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoIrisCoreLanguage
  PICOBridge.PicoIrisCoreInvariant
  PICOBridge.PicoIrisResourceLogicalRelation
  PICOBridge.PicoIrisSemImmOperations
  PICOBridge.PicoIrisSemImmLogicalRelation.

(** * Adequacy for the Ghost-Backed PICO Semantic Object LR

    This file is the final Iris execution boundary.  The initial cache-history
    snapshot allocates the authoritative ghost state.  The statement
    fundamental theorem, relative to an explicit protocol-preserving write
    rule, then proves [NotStuck] safety for the PICO core field-history machine.
    This is adequacy for that machine, not for the Java memory model. *)

Section pico_semimm_adequacy.
  Context `{Hmem : CacheMemoryModel}.
  Context `{Hprogress : CacheMemoryModelProgress}.
  Context (CT : class_table).
  Context {AbsVal Obj : Type}.
  Context (P : CacheProtocol AbsVal).
  Context (Stable : StableAbs Obj AbsVal).
  Context (a : AbsVal).
  Context (A : PicoCoreCacheAdapter P).
  Context (M : PicoCoreSemImmInstantiation CT P Stable a A).

  (** The only generic Iris adequacy bridge needed by the canonical SemImm
      endpoint.  It is kept here so this development does not depend on the
      retired contract-based LR adequacy layer. *)
  Theorem pico_core_ownP_adequacy :
    forall (Sigma : gFunctors)
      `{!ownPGpreS (pico_core_language CT) Sigma}
      stuck
      (e : language.expr (pico_core_language CT))
      (state : language.state (pico_core_language CT))
      (phi : language.val (pico_core_language CT) -> Prop),
      (forall `{!ownPGS (pico_core_language CT) Sigma},
        ownP state ⊢ WP e @ stuck; ⊤ {{ v, ⌜phi v⌝ }}) ->
      adequate stuck e state (fun v _ => phi v).
  Proof.
    intros Sigma Hpre stuck e state phi Hwp.
    exact
      (@ownP_adequacy
        Sigma (pico_core_language CT) Hpre stuck e state phi Hwp).
  Qed.

  (** Functional and safety adequacy are obtained by applying
      [pico_core_ownP_adequacy] to a method-specific semantic API WP.
      There is deliberately no ordinary-typing-to-[SemImmI] adequacy theorem:
      cache-write protocol validity is a semantic API obligation. *)
End pico_semimm_adequacy.

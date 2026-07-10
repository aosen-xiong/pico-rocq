From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep Reachability DeepImmutability.

(** Concrete-state preservation.

    Unlike transitive abstract immutability, this theorem has no premise that
    [f] is [Final] or [RDA].  CS uses concrete assignability adaptation, so all
    fields of immutable objects in the reachable abstract state—including
    fields declared [Assignable]—retain their entry values. *)
Theorem concrete_state_preservation :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals vals' f
    (Hroot_dom : root < dom h)
    (Hroot_imm : runtime_getObj h root =
      Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hreach : reachable_abs CT h root l)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteState stmt sΓ')
    (Heval : eval_stmt OK (reachable_locations_from_initial_env CT h rΓ)
      CT rΓ h stmt OK (reachable_locations_from_initial_env CT h rΓ) rΓ' h')
    (Hobj_start : runtime_getObj h l =
      Some (mkObj (mkruntime_type qr C) vals))
    (Hobj_end : runtime_getObj h' l =
      Some (mkObj (mkruntime_type qr C) vals')),
    nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals vals' f
    Hroot_dom Hroot_imm Hreach Hwf Htyping Heval Hobj_start Hobj_end.
  pose proof Hreach as Hreach_imm.
  eapply protected_locset_all_imm in Hreach_imm; eauto.
  destruct Hreach_imm as [C' [vals'' Himm_l]].
  rewrite Himm_l in Hobj_start.
  injection Hobj_start; intros; subst.
  eapply shallow_immutability_pico with (l := l); eauto.
  - apply runtime_getObj_dom in Himm_l. exact Himm_l.
  - right. right. left. reflexivity.
Qed.

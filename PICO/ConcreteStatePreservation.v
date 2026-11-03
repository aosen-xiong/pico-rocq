From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep Reachability AbstractStatePreservation.

(** Concrete-state preservation.

    Unlike abstract-state preservation, this theorem has no premise that
    [f] is [Final] or [RDA].  CS uses concrete assignability adaptation, so all
    fields of immutable objects in the reachable abstract state—including
    fields declared [Assignable]—retain their entry values. *)
Theorem concrete_state_preservation :
  forall CT sΓ rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    (Hroot_imm : runtime_getObj h root =
      Some (mkObj (mkruntime_type Imm_r C0) vals0))
    (Hreach : reachable_abs CT h root l)
    (Hwf : wf_r_config CT sΓ rΓ h)
    (Htyping : stmt_typing CT sΓ ConcreteState stmt sΓ')
    (Heval : eval_stmt CT rΓ h stmt OK rΓ' h')
    (Hobj_start : runtime_getObj h l =
      Some (mkObj (mkruntime_type qr C) vals)),
    exists vals',
      runtime_getObj h' l = Some (mkObj (mkruntime_type qr C) vals') /\
      nth_error vals f = nth_error vals' f.
Proof.
  intros CT sΓ rΓ h stmt rΓ' h' sΓ' root C0 vals0 l C qr vals f
    Hroot_imm Hreach Hwf Htyping Heval Hobj_start.
  destruct (runtime_preserves_r_type_heap CT rΓ h l
    (mkruntime_type qr C) h' vals stmt rΓ' Hobj_start Heval)
    as [vals' Hobj_end].
  exists vals'. split; [exact Hobj_end|].
  pose proof Hreach as Hreach_imm.
  eapply protected_locset_all_imm in Hreach_imm; eauto.
  destruct Hreach_imm as [C' [vals'' Himm_l]].
  rewrite Himm_l in Hobj_start.
  injection Hobj_start; intros; subst.
  eapply shallow_abstract_immutability_with_end with (l := l); eauto.
  right. right. left. reflexivity.
Qed.

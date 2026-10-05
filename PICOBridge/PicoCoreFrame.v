From Stdlib Require Import List.
Import ListNotations.

Require Import Syntax Helpers Typing Bigstep.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage.

(** * Steps Do Not Inspect the Rest of the Continuation

    A step of the core machine looks only at the top frame of the
    continuation.  A control therefore steps in the same way above any
    continuation [K], until it has finished and would pop a frame of [K]
    itself.  This lets a result about a control run with an empty
    continuation be reused when the control runs inside other code. *)

Definition append_cont (K : pico_core_cont) (e : pico_core_expr) :
    pico_core_expr :=
  match e with
  | CoreRun rGamma s V K1 => CoreRun rGamma s V (K1 ++ K)
  | CoreDone r rGamma V => CoreDone r rGamma V
  end.

Lemma step_under_cont :
  forall `{Hmem : CacheMemoryModel} CT K rGamma s V K1 S e' S',
    pico_core_step CT (CoreRun rGamma s V (K1 ++ K)) S e' S' ->
    ~ (s = SSkip /\ K1 = []) ->
    exists e1',
      pico_core_step CT (CoreRun rGamma s V K1) S e1' S' /\
      e' = append_cont K e1'.
Proof.
  intros Hmem CT K rGamma s V K1 S e' S' Hstep Hnot.
  destruct s.
  - destruct K1 as [| fr K1'];
      [exfalso; apply Hnot; split; reflexivity |].
    simpl in Hstep. inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
  - inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
  - inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
  - inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
  - inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
  - inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
  - inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
  - inversion Hstep; subst;
      eexists; (split; [econstructor; eauto | reflexivity]).
Qed.

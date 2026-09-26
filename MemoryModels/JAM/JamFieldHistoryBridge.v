From Stdlib Require Import List PeanoNat.
Import ListNotations.

Require Import MemoryModels.JAM.JamEvents MemoryModels.JAM.JamHistory
  MemoryModels.JAM.JamLegality.

(** * JAM to Field-History Bridge *)

Theorem jam_read_from_same_field_history :
  forall execution read
    (Hwf : jam_history_wf execution)
    (Hin : jam_event_in execution read)
    (Hread : jam_is_read read),
    exists write,
      jam_reads_from execution write read /\
      jam_is_write write /\
      jam_event_addr write = jam_event_addr read /\
      jam_event_value write = jam_event_value read /\
      In (jam_event_value read)
        (jam_field_history execution (jam_event_addr read)).
Proof.
  intros execution read Hwf Hin Hread.
  destruct (jam_reads_complete execution Hwf read Hin Hread) as
    [write Hrf].
  pose proof (jam_rf_events execution Hwf write read Hrf) as [Hwin _].
  pose proof (jam_rf_shapes execution Hwf write read Hrf) as
    [Hwrite [_ [Haddr Hvalue]]].
  exists write.
  repeat split; try assumption.
  rewrite <- Hvalue.
  rewrite <- Haddr.
  eapply jam_execution_write_in_field_history; eauto.
Qed.

Corollary jam_plain_read_from_same_field_history :
  forall execution read
    (Hlegal : jam_plain_legal execution)
    (Hin : jam_event_in execution read)
    (Hread : jam_is_read read),
    In (jam_event_value read)
      (jam_field_history execution (jam_event_addr read)).
Proof.
  intros execution read Hlegal Hin Hread.
  destruct (jam_read_from_same_field_history execution read
    (jam_plain_legal_history_wf execution Hlegal) Hin Hread) as
    [write [_ [_ [_ [_ HinHistory]]]]].
  exact HinHistory.
Qed.


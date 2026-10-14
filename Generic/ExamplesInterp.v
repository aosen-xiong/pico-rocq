From Stdlib Require Import List.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep Progress Interp.
Require Examples ExamplesOverride.

(** Running the example programs.

    The evaluations of the example programs were built rule by rule in their
    own files.  Here the interpreter computes the same final states. *)

(** The generic box program: allocation, a generic call, an upcast and a
    narrowing cast. *)
Example run_generic_main :
  run Examples.CT 5 Examples.rΓ0 Examples.h0 Examples.main =
  Some (FDone OK, Examples.rΓfinal, Examples.hfinal).
Proof. reflexivity. Qed.

(** The overriding program: the call is dispatched on the class of the
    receiver object. *)
Example run_override_main :
  run ExamplesOverride.CT 5 ExamplesOverride.rΓ0 ExamplesOverride.h0
    ExamplesOverride.main =
  Some (FDone OK, ExamplesOverride.rΓfinal, ExamplesOverride.hfinal).
Proof. reflexivity. Qed.

(** With no budget the same program stops at its first call. *)
Example run_override_main_timeout : exists rΓ' h',
  run ExamplesOverride.CT 0 ExamplesOverride.rΓ0 ExamplesOverride.h0
    ExamplesOverride.main = Some (FTimeout, rΓ', h').
Proof. do 2 eexists. reflexivity. Qed.

(** A larger budget gives the same result. *)
Example run_generic_main_more_fuel :
  run Examples.CT 50 Examples.rΓ0 Examples.h0 Examples.main =
  run Examples.CT 5 Examples.rΓ0 Examples.h0 Examples.main.
Proof. reflexivity. Qed.

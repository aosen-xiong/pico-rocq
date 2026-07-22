Require Import Syntax.

(* AS/CS mutability viewpoint adaptation *)
Definition vpa_mutability_qq_abstract_state (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | _, q2 => q2
  end.

Definition vpa_mutability_tt_abstract_state (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  Build_qualified_type
    (vpa_mutability_qq_abstract_state (sqtype t1) (sqtype t2))
    (sctype t2).

Definition vpa_mutability_stype_fld_abstract_state (q1: q)(q2 : q_f) : q :=
  match q1, q2 with
    | RO, RDM_f => Lost
    | q1, RDM_f => q1
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

(* RS/TS mutability viewpoint adaptation *)

Definition vpa_mutability_qq_readonly_state (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | Mut, Mut => Mut
    | _, Mut => Lost
    | _, q2 => q2
  end.

Definition vpa_mutability_tt_readonly_state (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  Build_qualified_type
    (vpa_mutability_qq_readonly_state (sqtype t1) (sqtype t2))
    (sctype t2).

Example vpa_mutability_readonly_state_mut_mut :
  vpa_mutability_qq_readonly_state Mut Mut = Mut.
Proof. reflexivity. Qed.

Example vpa_mutability_type_readonly_state_mut_mut :
  forall C,
    vpa_mutability_tt_readonly_state
      (Build_qualified_type Mut C) (Build_qualified_type Mut C) =
    Build_qualified_type Mut C.
Proof. reflexivity. Qed.

Definition vpa_mutability_stype_fld_readonly_state (q1: q)(q2 : q_f) : q :=
  match q1, q2 with
    | RO, RDM_f => Lost
    | q1, RDM_f => q1
    | _, Imm_f => Imm
    | Mut, Mut_f => Mut
    | _, Mut_f => Lost
    | _, RO_f => RO
    end.

Example vpa_mutability_field_readonly_state_mut_mut :
  vpa_mutability_stype_fld_readonly_state Mut Mut_f = Mut.
Proof. reflexivity. Qed.

(* Viewpoint adaptation of assignability qualifiers *)
Definition vpa_assignability (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | _, Assignable => Assignable
    | _, _ => Final
  end.

(* CS/TS assignability viewpoint adaptation *)
Definition vpa_assignability_cs_ts (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | Mut, Assignable => Assignable
    | _, _ => Final
  end.

Lemma concrete_assignable_implies_assignable : forall q1 a1,
  vpa_assignability_cs_ts q1 a1 = Assignable ->
  vpa_assignability q1 a1 = Assignable.
Proof.
  intros q1 a1 H.
  destruct q1, a1; simpl in *; try discriminate; reflexivity.
Qed.

(* Check whether a type respect its bound *)
Definition vpa_mutability_bound (q1: q)(q2 : q_c) : q :=
  match q1, q2 with
    | RO, RDM_c => Lost
    | q1, RDM_c => q1
    | _, Imm_c => Imm
    | _, Mut_c => Mut
    end.

(* Adapting field type from constructor *)
Definition vpa_mutability_constructor_fld (q1: q_c)(q2 : q_f) : q :=
  match q1, q2 with
    | Imm_c, RDM_f => Imm
    | Mut_c, RDM_f => Mut
    | RDM_c, RDM_f => RDM
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

(* Adapting field type from a runtime type *)
Definition vpa_mutability_rec_fld (q1: q_r)(q2 : q_f) : q :=
  match q1, q2 with
    | Imm_r, RDM_f => Imm
    | Mut_r, RDM_f => Mut
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

(** Runtime viewpoint adaptation used by runtime typability.  For example, in
    [m(Imm C this, RDM C c)], [c] may contain an immutable object because
    adapting [RDM] through an immutable runtime context yields [Imm]. *)
Definition vpa_mutability_runtime (q1: q_r)(q2 : q) : q :=
  match q1, q2 with
    | Imm_r, RDM => Imm
    | Mut_r, RDM => Mut
    | _, q2 => q2
  end.

(*  Adapted object creation for operational semantics *)
Definition vpa_mutability_object_creation (q1: q_r)(q2 : q_c) : q_r :=
  match q1, q2 with
    | Imm_r, RDM_c => Imm_r
    | Mut_r, RDM_c => Mut_r
    | _, Imm_c => Imm_r
    | _, Mut_c => Mut_r
    end.


(* ################################################################# *)

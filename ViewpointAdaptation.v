Require Import Syntax.

(* Abstract Immutability VPA *)
Definition vpa_mutability_qq_abs_imm (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | _, q2 => q2
  end.

Definition vpa_mutability_tt_abs_imm (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  match (sqtype t1), (sqtype t2) with
    | RO, RDM => Build_qualified_type Lost (sctype t2)
    | q1, RDM => Build_qualified_type q1 (sctype t2)
    | _, _ => t2
  end.

Definition vpa_mutability_stype_fld_abs_imm (q1: q)(q2 : q_f) : q :=
  match q1, q2 with
    | RO, RDM_f => Lost
    | q1, RDM_f => q1
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

(* Safe Readonly VPA *)

Definition vpa_mutability_qq_safe_ro (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | _, Mut => Lost
    | _, q2 => q2
  end.

Definition vpa_mutability_tt_safe_ro (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  match (sqtype t1), (sqtype t2) with
    | RO, RDM => Build_qualified_type Lost (sctype t2)
    | q1, RDM => Build_qualified_type q1 (sctype t2)
    | _, Mut => Build_qualified_type Lost (sctype t2)
    | _, _ => t2
  end.

Definition vpa_mutability_stype_fld_safe_ro (q1: q)(q2 : q_f) : q :=
  match q1, q2 with
    | RO, RDM_f => Lost
    | q1, RDM_f => q1
    | _, Imm_f => Imm
    | _, Mut_f => Lost
    | _, RO_f => RO
    end.

(* Viewpoint adaptation of assignability qualifiers *)
Definition vpa_assignability (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | _, Assignable => Assignable
    | _, _ => Final
  end.

(* Concrete Immutability *)
Definition vpa_assignability_concret_imm (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | Mut, Assignable => Assignable
    | _, _ => Final
  end.

Lemma concrete_assignable_implies_assignable : forall q1 a1,
  vpa_assignability_concret_imm q1 a1 = Assignable ->
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

(* Used to exam runtime typability based on its context, 
for example, m(Imm C this, RDM C c), 
the value of c is a Imm obj at runtime but is typable because Imm |> RDM = Imm *)
Definition vpa_mutability_rs (q1: q_r)(q2 : q) : q :=
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

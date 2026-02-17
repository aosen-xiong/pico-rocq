Require Import Syntax.

(* Viewpoint adaptation of mutability qualifiers *)
Definition vpa_mutabilty_qq (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | RO, RDM => Lost
    | q1, RDM => q1
    | _, q2 => q2
  end.

(* A wrapper around vpa_mutability by taking two full types *)
Definition vpa_mutabilty_tt (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  let qual_result :=
    match (sqtype t1), (sqtype t2) with
    | RO, RDM => Lost
    | q1, RDM => q1
    | _, _ => sqtype t2
    end
  in
  (* Do not adapt abs at method invocation *)
  Build_qualified_type (sabs t2) qual_result (sctype t2).

(* Check whether a type respect its bound *)
Definition vpa_mutabilty_bound (q1: q)(q2 : q_c) : q :=
  match q1, q2 with
    | RO, RDM_c => Lost
    | q1, RDM_c => q1
    | _, Imm_c => Imm
    | _, Mut_c => Mut
    end.

(* Check whether a field declaration respect its bound *)
Definition vpa_mutabilty_fld_bound (q1: q_f)(q2 : q_c) : q_f :=
  match q1, q2 with
    | Imm_f, RDM_c => Imm_f
    | Mut_f, RDM_c => Mut_f
    | RDM_f, RDM_c => RDM_f
    | RO_f, RDM_c => RO_f (* This is not the rule used to check assignability, use it for wellformedness only*)
    | _, Imm_c => Imm_f
    | _, Mut_c => Mut_f
    end.

(* Adapting field type from a type use *)
Definition vpa_mutabilty_stype_fld (q1: q)(q2 : q_f) : q :=
  match q1, q2 with
    | RO, RDM_f => Lost
    | q1, RDM_f => q1
    | _, Mut_f => Mut
    | _, RO_f => RO
    | _, Imm_f => Imm
    end.

(* Adapting field type from constructor *)
Definition vpa_mutabilty_constructor_fld (q1: q_c)(q2 : q_f) : q :=
  match q1, q2 with
    | Imm_c, RDM_f => Imm
    | Mut_c, RDM_f => Mut
    | RDM_c, RDM_f => RDM
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, RO_f => RO
    end.

(* Adapting field type from a runtime type *)
Definition vpa_mutabilty_rec_fld (q1: q_r)(q2 : q_f) : q :=
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
Definition vpa_mutabilty_rs (q1: q_r)(q2 : q) : q :=
  match q1, q2 with
    | Imm_r, RDM => Imm
    | Mut_r, RDM => Mut
    | _, q2 => q2
  end.

(*  Adapted object creation for operational semantics *)
Definition vpa_mutabilty_object_creation (q1: q_r)(q2 : q_c) : q_r :=
  match q1, q2 with
    | Imm_r, RDM_c => Imm_r
    | Mut_r, RDM_c => Mut_r
    | _, Imm_c => Imm_r
    | _, Mut_c => Mut_r
    end.


(* ################################################################# *)

(* Viewpoint adaptation of assignability qualifiers *)
Definition vpa_assignability (q1: q) (a1: a) : a :=
  match q1, a1 with
    | Mut, RDA => Assignable
    | _, Assignable => Assignable
    | _, _ => Final
  end.
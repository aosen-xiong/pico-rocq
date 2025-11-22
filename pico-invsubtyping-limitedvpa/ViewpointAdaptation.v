Require Import Syntax.

(* Viewpoint adaptation of mutability qualifiers *)
Definition vpa_mutabilty_qq (q1: q)(q2 : q) : q :=
  match q1, q2 with
    | Imm, RDM => Imm
    | Mut, RDM => Mut
    | Rd, RDM => Lost
    | Lost, RDM => Lost
    | Bot, RDM => Bot
    | _, _ => q2
  end.

(* A wrapper around vpa_mutability by taking two full types *)
Definition vpa_mutabilty_tt (t1: qualified_type)(t2 : qualified_type) : qualified_type :=
  match (sqtype t1), (sqtype t2) with
    | Imm, RDM => Build_qualified_type Imm (sctype t2)
    | Mut, RDM => Build_qualified_type Mut (sctype t2)
    | Rd, RDM => Build_qualified_type Lost (sctype t2)
    | Lost, RDM => Build_qualified_type Lost (sctype t2)
    | Bot, RDM => Build_qualified_type Bot (sctype t2)
    | _, _ => t2
  end.

(* Check whether a type respect its bound *)
Definition vpa_mutabilty_bound (q1: q)(q2 : q_c) : q :=
  match q1, q2 with
    | Rd, RDM_c => Lost
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
    | RD_f, RDM_c => RD_f (* This is not the rule used to check assignability, use it for wellformedness only*)
    | _, Imm_c => Imm_f
    | _, Mut_c => Mut_f
    end.

(* Adapting field type from a type use *)
Definition vpa_mutabilty_stype_fld (q1: q)(q2 : q_f) : q :=
  match q1, q2 with
    | Rd, RDM_f => Lost
    | Imm, RDM_f => Imm
    | Mut, RDM_f => Mut
    | RDM, RDM_f => RDM
    | Lost, RDM_f => Lost
    | Bot, RDM_f => Bot
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, Rd_f => Rd
    end.

(* Adapting field type from constructor *)
Definition vpa_mutabilty_constructor_fld (q1: q_c)(q2 : q_f) : q :=
  match q1, q2 with
    | Imm_c, RDM_f => Imm
    | Mut_c, RDM_f => Mut
    | RDM_c, RDM_f => RDM
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, Rd_f => Rd
    end.

(* Adapting field type from a runtime type *)
Definition vpa_mutabilty_rec_fld (q1: q_r)(q2 : q_f) : q :=
  match q1, q2 with
    | Imm_r, RDM_f => Imm
    | Mut_r, RDM_f => Mut
    | _, Imm_f => Imm
    | _, Mut_f => Mut
    | _, Rd_f => Rd
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
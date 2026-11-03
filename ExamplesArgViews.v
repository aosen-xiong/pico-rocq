From Stdlib Require Import List Lia Bool.
Import ListNotations.
Require Import Syntax Notations Helpers ViewpointAdaptation Subtyping Typing
  Bigstep GhostLabels ArgViews.

(** The payload rule on the programs that defeated the simpler rules.

    class Cell
    class D<X extends RO Object>
    class Base<A extends RO Object, A2 extends RO D<A>>
    class Sub<E extends RO D<Mut Cell>> extends Base<Mut Cell, E>
    class Q3 extends Sub<RO D<Mut Cell>>
    class Mid<E extends RO Object> extends Base<Mut Cell, RO D<Mut Cell>> *)

Definition tyVar (n : nat) : qualified_type := TVar TVSub ClassVar n.
Definition ROObject : qualified_type := TClass RO 0 [].
Definition MutCell : qualified_type := TClass Mut 1 [].
Definition RODMutCell : qualified_type := TClass RO 2 [MutCell].

Definition mkc (n : nat) (bs : list qualified_type)
    (sup : option (class_name * list qualified_type)) : class_def :=
  {| signature := {| class_qualifier := RDM_c; cname := n; ctparams := bs;
                     super := sup |};
     body := {| Syntax.fields := []; methods := [] |} |}.

Definition CT : class_table :=
  [ mkc 0 [] None;
    mkc 1 [] (Some (0, []));
    mkc 2 [ROObject] (Some (0, []));
    mkc 3 [ROObject; TClass RO 2 [tyVar 0]] (Some (0, []));
    mkc 4 [RODMutCell] (Some (3, [MutCell; tyVar 0]));
    mkc 5 [] (Some (4, [RODMutCell]));
    mkc 6 [ROObject] (Some (3, [MutCell; RODMutCell])) ].

(** A cell created by the running call, in world 7. *)
Definition newCell : ltype := LT Mut (LIn 7) 1 [].
Definition oldCell : ltype := LT Mut LOut 1 [].
Definition roD (c : ltype) : ltype := LT RO LOut 2 [c].

(** [Sub]: the bound writes a mutable position; the payload is what the
    argument holds there. *)
Example sub_payload :
  pclassf CT 4 [roD newCell] = Some (Mut, LIn 7).
Proof. reflexivity. Qed.

(** An object of [Sub] that is in no world, holding a new cell: its view at
    [Base] reads the written mutable position as the new cell's world, so
    the two arguments of [Base] agree as its bound demands. *)
Example sub_view_at_base :
  oview CT Mut_r LOut 4 [roD newCell] 3 [newCell; roD newCell].
Proof.
  unfold oview. eapply v_step; [reflexivity|]. simpl. apply v_refl.
Qed.

(** [Q3]: no type arguments and no bound, so its header is read through the
    object's own label; [Sub]'s payload is then that same label, and the
    view at [Base] is consistent without mentioning the running call. *)
Example q3_view_at_sub :
  oview CT Mut_r LOut 5 [] 4 [roD oldCell].
Proof.
  unfold oview. eapply v_step; [reflexivity|]. simpl. apply v_refl.
Qed.

Example q3_view_at_base :
  oview CT Mut_r LOut 5 [] 3 [oldCell; roD oldCell].
Proof.
  unfold oview. eapply v_step; [reflexivity|]. simpl.
  eapply v_step; [reflexivity|]. simpl. apply v_refl.
Qed.

(** [Mid]: its bound writes no mutable position, so even with a new cell as
    its argument, the header is read through the object's own label. *)
Example mid_payload : pclassf CT 6 [newCell] = None.
Proof. reflexivity. Qed.

Example mid_view_at_base :
  oview CT Mut_r LOut 6 [newCell] 3 [oldCell; roD oldCell].
Proof.
  unfold oview. eapply v_step; [reflexivity|]. simpl. apply v_refl.
Qed.

(** An object that is in world 7 reads everything as world 7. *)
Example sub_view_coloured :
  oview CT Mut_r (LIn 7) 4 [roD newCell] 3 [newCell; roD newCell].
Proof.
  unfold oview. eapply v_step; [reflexivity|]. simpl. apply v_refl.
Qed.

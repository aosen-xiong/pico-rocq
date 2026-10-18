From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation
  ViewpointAdaptation WFNOMutationEXP.
Require Import PICOBridge.PicoMemoryModel PICOBridge.PicoCoreLanguage
  PICOBridge.PicoCoreInvariant PICOBridge.PicoCoreTypingSupport
  PICOBridge.PicoCoreTyping PICOBridge.PicoSemanticConcurrency.

(** * Type Safety of the Core Machine under Interleaving

    PICO's type soundness is proved for the big-step semantics, which
    describes one thread running alone.  This file proves it for the
    small-step machine with weak field histories and any number of
    interleaved threads.

    The one fact the big-step proof does not need is that a weak read returns
    a well-typed value: a read may return any value in the field's history,
    not only the current heap value.  The typed-histories invariant below
    states that every value ever written to a field is well typed for that
    field.  It is phrased with the runtime types of the heap alone, so it is
    stable under every step of every thread. *)

Section typed_histories.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).

  (** [v] is an admissible value of field [f] of the object at [ι]: the
      condition [wf_obj] imposes on a field value, strengthened so that
      [Null_a] inhabits only reference fields.  It mentions only runtime
      types, never field contents. *)
  Definition field_value_ok (h : heap) (ι : Loc) (f : var) (v : value) : Prop :=
    exists rt field_defs fdef,
      r_type h ι = Some rt /\
      CollectFields CT (rctype rt) field_defs /\
      nth_error field_defs f = Some fdef /\
      match v with
      | Null_a => exists C, f_base_type (ftype fdef) = TRef C
      | Int _ => f_base_type (ftype fdef) = TInt
      | Iot loc =>
          exists rqt,
            r_type h loc = Some rqt /\
            base_subtype CT (TRef (rctype rqt)) (f_base_type (ftype fdef)) /\
            qualifier_typable_heap (rqtype rqt)
              (vpa_mutability_rec_fld (rqtype rt) (mutability (ftype fdef)))
      end.

  (** Every value in every field history is admissible for its field. *)
  Definition histories_typed (S : pico_core_state) : Prop :=
    forall loc f v,
      List.In v (values_written_to (pcs_weak S) (loc, f)) ->
      field_value_ok (pcs_heap S) loc f v.

  Lemma field_value_ok_heap_types_extend :
    forall h h' ι f v,
      pico_core_heap_types_extend h h' ->
      field_value_ok h ι f v ->
      field_value_ok h' ι f v.
  Proof.
    intros h h' ι f v [_ Htypes] (rt & field_defs & fdef & Hrt & Hcf & Hnth & Hv).
    exists rt, field_defs, fdef.
    split; [exact (Htypes ι rt Hrt) |].
    split; [exact Hcf |].
    split; [exact Hnth |].
    destruct v as [| loc | n]; try exact Hv.
    destruct Hv as (rqt & Hrqt & Hbase & Hqual).
    exists rqt. split; [exact (Htypes loc rqt Hrqt) | split; assumption].
  Qed.

  Lemma Forall2_nth_error_left :
    forall {A B : Type} (R : A -> B -> Prop) l1 l2 n a,
      Forall2 R l1 l2 ->
      nth_error l1 n = Some a ->
      exists b, nth_error l2 n = Some b /\ R a b.
  Proof.
    intros A B R l1 l2 n a HF2. revert n a.
    induction HF2 as [| x y l1 l2 Hxy _ IH]; intros [| n] a Hnth;
      simpl in Hnth; try discriminate.
    - injection Hnth as <-. exists y. split; [reflexivity | exact Hxy].
    - exact (IH n a Hnth).
  Qed.

  (** A field value of a well-formed heap is admissible for its field.  The
      heap's well-formedness says nothing about which fields may hold
      [Null_a], so that case is a premise. *)
  Lemma wf_heap_field_value_ok :
    forall h ι o f v,
      wf_heap CT h ->
      runtime_getObj h ι = Some o ->
      nth_error (fields_map o) f = Some v ->
      (v = Null_a ->
       forall field_defs fdef,
         CollectFields CT (rctype (rt_type o)) field_defs ->
         nth_error field_defs f = Some fdef ->
         exists C, f_base_type (ftype fdef) = TRef C) ->
      field_value_ok h ι f v.
  Proof.
    intros h ι o f v Hheap Hobj Hnth Hnull.
    have Hdom := runtime_getObj_dom ι o h Hobj.
    have Hwf := Hheap ι Hdom.
    unfold wf_obj in Hwf. rewrite Hobj in Hwf.
    destruct Hwf as [_ (field_defs & Hcf & Hlen & HF2)].
    destruct (Forall2_nth_error_left _ _ _ f v HF2 Hnth) as (fdef & Hfdef & Hv).
    exists (rt_type o), field_defs, fdef.
    split; [unfold r_type; rewrite Hobj; reflexivity |].
    split; [exact Hcf |].
    split; [exact Hfdef |].
    destruct v as [| loc | n].
    - exact (Hnull eq_refl field_defs fdef Hcf Hfdef).
    - destruct (runtime_getObj h loc) eqn:Hloc; [exact Hv | contradiction].
    - exact Hv.
  Qed.

  (** The static facts a typed field write provides: the written field is
      declared in the static class of the receiver, and the base type of the
      written variable is a subtype of the field's base type. *)
  Lemma stmt_typing_fldwrite_field :
    forall sGamma sGamma' mt x f y,
      stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
      exists Tx Ty C fieldT,
        static_getType sGamma x = Some Tx /\
        static_getType sGamma y = Some Ty /\
        sbase Tx = TRef C /\
        FieldLookup CT C f fieldT /\
        base_subtype CT (sbase Ty) (f_base_type (ftype fieldT)).
  Proof.
    intros sGamma sGamma' mt x f y Htyping.
    inversion Htyping; subst;
      match goal with
      | Hx : static_getType _ x = Some ?Tx,
        Hy : static_getType _ y = Some ?Ty,
        Hr : sbase ?Tx = TRef ?C,
        Hf : sf_def_rel CT ?C f ?fieldT,
        Hs : qualified_type_subtype CT ?Ty _ |- _ =>
          exists Tx, Ty, C, fieldT;
          repeat (split; [assumption |]);
          exact (qualified_type_subtype_base_subtype _ _ _ Hs)
      end.
  Qed.

  (** The field definition at index [f] of the runtime class of a typed
      receiver is the one declared in its static class. *)
  Lemma typed_receiver_field_def :
    forall h qcontext Tx C loc o f fieldT field_defs fdef,
      pico_core_typed_value CT h qcontext Tx (Iot loc) ->
      sbase Tx = TRef C ->
      runtime_getObj h loc = Some o ->
      FieldLookup CT C f fieldT ->
      CollectFields CT (rctype (rt_type o)) field_defs ->
      nth_error field_defs f = Some fdef ->
      fdef = fieldT.
  Proof.
    intros h qcontext Tx C loc o f fieldT field_defs fdef
      Htyped Href Hobj Hlookup Hcf Hnth.
    simpl in Htyped. unfold wf_r_typable in Htyped.
    unfold r_type in Htyped. rewrite Hobj in Htyped.
    destruct Htyped as [Hbase _]. rewrite Href in Hbase.
    destruct (base_subtype_from_ref CT _ _ Hbase) as (D & HD & Hsub).
    injection HD as <-.
    have Hlookup' := field_inheritance_subtyping CT _ C f fieldT Hsub Hlookup.
    inversion Hlookup' as [CT0 C0 fields0 f0 fdef0 Hcf0 Hget]; subst.
    have Heq := collect_fields_deterministic_rel CT _ _ _ Hcf Hcf0.
    subst fields0. unfold gget in Hget. congruence.
  Qed.

  (** A typed field write keeps the histories typed.  The appended value is
      the new heap value of the field, which the well-formed post-heap makes
      admissible; older history entries stay admissible because the write
      changes no runtime type. *)
  Lemma fldwrite_step_preserves_histories_typed :
    forall sGamma sGamma' rGamma h sigma mt x f y V K e' S',
      stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      pico_core_lr_state CT (mkPicoCoreState h sigma) ->
      histories_typed (mkPicoCoreState h sigma) ->
      pico_core_step CT (CoreRun rGamma (SFldWrite x f y) V K)
        (mkPicoCoreState h sigma) e' S' ->
      histories_typed S'.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x f y V K e' S'
      Htyping Henv Hlr Hhist Hstep.
    have Hpost := pico_core_typed_fldwrite_step_post CT _ _ _ _ _ _ _ _ _ _ _
      _ _ Htyping Henv Hlr Hstep.
    inversion Hstep; subst; try exact Hhist.
    match goal with
    | Hx : runtime_getVal rGamma x = Some (Iot ?l),
      Ho : runtime_getObj h ?l = Some ?ob,
      Hy : runtime_getVal rGamma y = Some ?w,
      Hw : wm_write sigma _ _ _ _ _,
      Ha : sf_assignability_rel CT _ f _ |- _ =>
        rename Hx into Hgetx; rename Ho into Hobj; rename Hy into Hgety;
        rename Hw into Hwrite; rename Ha into Hassign
    end.
    inversion Hpost as [rG V0 st Henv' _ | |]; subst. simpl in Henv'.
    have Hcfg' := pico_core_typed_env_wf_config CT _ _ _ Henv'.
    have Hheap' : wf_heap CT (update_field h loc_x f val_y)
      by (destruct Hcfg' as (_ & Hheap' & _); exact Hheap').
    have Hcfg := pico_core_typed_env_wf_config CT _ _ _ Henv.
    have Hheap : wf_heap CT h by (destruct Hcfg as (_ & Hh & _); exact Hh).
    have Hext := pico_core_heap_types_extend_write h loc_x f val_y o Hobj.
    have Hdom := runtime_getObj_dom loc_x o h Hobj.
    intros loc f0 v Hin. simpl in *.
    destruct (Nat.eq_dec loc loc_x) as [-> | Hloc];
      [destruct (Nat.eq_dec f0 f) as [-> | Hf] |].
    - (* the written address *)
      unfold values_written_to in Hin.
      rewrite (wm_write_history_same _ _ _ _ _ _ Hwrite) in Hin.
      rewrite map_app in Hin. apply in_app_or in Hin.
      destruct Hin as [Hold | Hnew].
      + eapply field_value_ok_heap_types_extend; [exact Hext |].
        exact (Hhist loc_x f v Hold).
      + simpl in Hnew. destruct Hnew as [<- | []].
        (* the field exists in the runtime class *)
        destruct Hassign as (fdef_a & Hlookup_a & _).
        inversion Hlookup_a as [CT0 C0 fields_a f1 fdef1 Hcf_a Hget_a]; subst.
        have Hwf := Hheap loc_x Hdom.
        unfold wf_obj in Hwf. rewrite Hobj in Hwf.
        destruct Hwf as [_ (field_defs & Hcf & Hlen & _)].
        have Heqf := collect_fields_deterministic_rel CT _ _ _ Hcf Hcf_a.
        subst fields_a.
        have Hf_lt : f < length (fields_map o).
        { rewrite Hlen. unfold gget in Hget_a.
          apply nth_error_Some. rewrite Hget_a. discriminate. }
        destruct o as [rt fs]. simpl in *.
        eapply (wf_heap_field_value_ok (update_field h loc_x f val_y) loc_x
          (mkObj rt (update f val_y fs)) f val_y Hheap').
        * unfold update_field. rewrite Hobj.
          apply runtime_getObj_update_same. exact Hdom.
        * simpl. apply update_same. exact Hf_lt.
        * intros -> field_defs' fdef' Hcf' Hnth'. simpl in Hcf'.
          destruct (stmt_typing_fldwrite_field _ _ _ _ _ _ Htyping)
            as (Tx & Ty & C & fieldT & Hsx & Hsy & Href & Hlookup & Hbase).
          destruct (pico_core_typed_env_lookup CT _ _ _ y Ty Henv Hsy)
            as (qy & vy & Hvy & Htyped_y).
          rewrite Hgety in Hvy. injection Hvy as <-.
          destruct Htyped_y as [Cy Hbase_y].
          rewrite Hbase_y in Hbase.
          destruct (base_subtype_from_ref CT _ _ Hbase) as (D & HD & _).
          destruct (pico_core_typed_env_lookup CT _ _ _ x Tx Henv Hsx)
            as (qx & vx & Hvx & Htyped_x).
          rewrite Hgetx in Hvx. injection Hvx as <-.
          have Heq := typed_receiver_field_def h qx Tx C loc_x (mkObj rt fs) f
            fieldT field_defs' fdef' Htyped_x Href Hobj Hlookup Hcf' Hnth'.
          subst fdef'. exists D. exact HD.
    - (* another field of the same object *)
      unfold values_written_to in *.
      destruct Hwrite as [-> _].
      rewrite history_of_append_write_other in Hin; [| congruence].
      eapply field_value_ok_heap_types_extend; [exact Hext |].
      exact (Hhist loc_x f0 v Hin).
    - (* another object *)
      unfold values_written_to in *.
      destruct Hwrite as [-> _].
      rewrite history_of_append_write_other in Hin; [| congruence].
      eapply field_value_ok_heap_types_extend; [exact Hext |].
      exact (Hhist loc f0 v Hin).
  Qed.

  Lemma mapM_nth_error_inv :
    forall {A B : Type} (g : A -> option B) l r n y,
      mapM g l = Some r ->
      nth_error r n = Some y ->
      exists x, nth_error l n = Some x /\ g x = Some y.
  Proof.
    intros A B g l. induction l as [| x l IH]; intros r n y Hmap Hnth.
    - simpl in Hmap. injection Hmap as <-. destruct n; discriminate.
    - simpl in Hmap.
      destruct (g x) as [y0 |] eqn:Hgx; [| discriminate].
      destruct (mapM g l) as [ys |] eqn:Hrest; [| discriminate].
      injection Hmap as <-.
      destruct n as [| n]; simpl in Hnth.
      + injection Hnth as <-. exists x. split; [reflexivity | exact Hgx].
      + destruct (IH ys n y eq_refl Hnth) as (x' & Hx' & Hg').
        exists x'. split; assumption.
  Qed.

  (** A [Null_a] constructor argument is passed only to a reference field:
      the argument's type is a reference type, a subtype of the adapted
      parameter type, which the well-formed constructor makes a subtype of
      the field's type. *)
  Lemma typed_new_null_argument_field :
    forall sGamma sGamma' rGamma h mt x qc C args vals f field_defs fdef,
      stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      runtime_lookup_list rGamma args = Some vals ->
      nth_error vals f = Some Null_a ->
      CollectFields CT C field_defs ->
      nth_error field_defs f = Some fdef ->
      exists D, f_base_type (ftype fdef) = TRef D.
  Proof.
    intros sGamma sGamma' rGamma h mt x qc C args vals f field_defs fdef
      Htyping Henv Hvals Hnull Hcf Hfdef.
    have Hcfg := pico_core_typed_env_wf_config CT _ _ _ Henv.
    have Hct : wf_class_table CT by (destruct Hcfg as (Hct & _); exact Hct).
    inversion Htyping; subst.
    match goal with
    | Hl : constructor_sig_lookup CT C = Some ?cs,
      Ha : static_getType_list _ args = Some ?ats,
      Hs : Forall2 _ ?ats _ |- _ =>
        rename Hl into Hconsig; rename Ha into Hargtypes; rename Hs into Harg_sub
    end.
    (* the argument at index f and its static type *)
    destruct (mapM_nth_error_inv _ _ _ _ _ Hvals Hnull) as (a_f & Ha_f & Hval_f).
    assert (Hlen_args : length argtypes = length args)
      by exact (static_getType_list_preserves_length _ _ _ Hargtypes).
    assert (Hf_args : f < length args)
      by (apply nth_error_Some; rewrite Ha_f; discriminate).
    destruct (nth_error argtypes f) as [T_f |] eqn:HT_f;
      [| apply nth_error_None in HT_f; lia].
    destruct (mapM_nth_error_inv _ _ _ _ _ Hargtypes HT_f) as (a_f' & Ha_f' & Hst_f).
    rewrite Ha_f in Ha_f'. injection Ha_f' as <-.
    destruct (pico_core_typed_env_lookup CT _ _ _ a_f T_f Henv Hst_f)
      as (q & v & Hv & Htyped).
    rewrite Hval_f in Hv. injection Hv as <-.
    (* the adapted parameter type at index f is a reference type *)
    destruct (Forall2_nth_error_left _ _ _ f T_f Harg_sub HT_f)
      as (P_f & HP_f & Hsub_arg).
    destruct (pico_core_subtype_preserves_reference CT T_f P_f Htyped Hsub_arg)
      as (D1 & HD1).
    rewrite nth_error_map in HP_f.
    destruct (nth_error (cparams consig) f) as [p_f |] eqn:Hp_f;
      [| discriminate].
    simpl in HP_f. injection HP_f as <-. simpl in HD1.
    (* the well-formed constructor relates the parameter to the field *)
    have Hdom := constructor_sig_lookup_dom CT C consig Hconsig.
    have Hwfc := constructor_lookup_wf CT C consig Hct Hdom Hconsig.
    destruct Hwfc as (_ & _ & field_defs0 & Hcf0 & _ & HF2).
    have Heq := collect_fields_deterministic_rel CT _ _ _ Hcf Hcf0.
    subst field_defs0.
    destruct (Forall2_nth_error_left _ _ _ f p_f HF2 Hp_f)
      as (fdef0 & Hfdef0 & Hsub_fld).
    rewrite Hfdef in Hfdef0. injection Hfdef0 as <-.
    assert (Href_p : exists D0,
      sbase (vpa_mutability_constructor_param (cqualifier consig) p_f) = TRef D0)
      by (exists D1; exact HD1).
    destruct (pico_core_subtype_preserves_reference CT _ _ Href_p Hsub_fld)
      as (D & HD).
    exists D. exact HD.
  Qed.

  (** A typed allocation keeps the histories typed.  The new object's
      histories hold its initial field values, which the well-formed
      post-heap makes admissible. *)
  Lemma new_step_preserves_histories_typed :
    forall sGamma sGamma' rGamma h sigma mt x qc C args V K e' S',
      stmt_typing CT sGamma mt (SNew x qc C args) sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      pico_core_lr_state CT (mkPicoCoreState h sigma) ->
      histories_typed (mkPicoCoreState h sigma) ->
      pico_core_step CT (CoreRun rGamma (SNew x qc C args) V K)
        (mkPicoCoreState h sigma) e' S' ->
      histories_typed S'.
  Proof.
    intros sGamma sGamma' rGamma h sigma mt x qc C args V K e' S'
      Htyping Henv Hlr Hhist Hstep.
    have Hpost := pico_core_typed_new_step_post CT _ _ _ _ _ _ _ _ _ _ _ _
      _ _ Htyping Henv Hlr Hstep.
    inversion Hstep; subst.
    match goal with
    | Hl : runtime_lookup_list rGamma args = Some ?vs |- _ =>
        rename Hl into Hvals
    end.
    inversion Hpost as [rG V0 st Henv' _ | |]; subst. simpl in Henv'.
    have Hcfg' := pico_core_typed_env_wf_config CT _ _ _ Henv'.
    have Hheap' : wf_heap CT
      (h ++ [mkObj (mkruntime_type (vpa_mutability_object_creation qthisr qc) C)
               vals])
      by (destruct Hcfg' as (_ & Hheap' & _); exact Hheap').
    set (o := mkObj (mkruntime_type (vpa_mutability_object_creation qthisr qc) C)
      vals) in *.
    have Hext := pico_core_heap_types_extend_alloc h o.
    have Hagree : length h = length (wm_objs sigma).
    { destruct Hlr as [[Hlen _] _]. exact Hlen. }
    have Hobj_new : runtime_getObj (h ++ [o]) (length h) = Some o.
    { unfold runtime_getObj. rewrite nth_error_app2; [| lia].
      rewrite Nat.sub_diag. reflexivity. }
    intros loc f v Hin. simpl in *.
    unfold values_written_to, history_of, pico_core_alloc_weak in Hin.
    simpl in Hin.
    destruct (Nat.eqb loc (length (wm_objs sigma))) eqn:Hloc.
    - apply Nat.eqb_eq in Hloc. rewrite <- Hagree in Hloc. subst loc.
      destruct (nth_error vals f) as [v0 |] eqn:Hv0.
      + simpl in Hin. destruct Hin as [<- | []].
        eapply (wf_heap_field_value_ok (h ++ [o]) (length h) o f v0 Hheap'
          Hobj_new Hv0).
        intros -> field_defs fdef Hcf Hfdef. simpl in Hcf.
        exact (typed_new_null_argument_field _ _ _ _ _ _ _ _ _ _ _ _ _
          Htyping Henv Hvals Hv0 Hcf Hfdef).
      + (* no history is recorded for a location that is not allocated *)
        exfalso.
        destruct (Hhist (length h) f v Hin) as (rt & _ & _ & Hrt & _).
        unfold r_type, runtime_getObj in Hrt.
        rewrite (proj2 (nth_error_None h (length h)) (le_n _)) in Hrt.
        discriminate.
    - eapply field_value_ok_heap_types_extend; [exact Hext |].
      exact (Hhist loc f v Hin).
  Qed.

  (** Viewpoint adaptation agrees between the heap and the reader: a value
      admissible for a field of the receiver's runtime type is typable at the
      field's type adapted through the receiver's static type. *)
  Lemma field_qualifier_typable_read :
    forall qv qrec qy fm qcontext,
      qualifier_typable_heap qv (vpa_mutability_rec_fld qrec fm) ->
      qualifier_typable_context qrec qy qcontext ->
      qualifier_typable_context qv
        (vpa_mutability_stype_fld_abstract_state qy fm) qcontext /\
      qualifier_typable_context qv
        (vpa_mutability_stype_fld_readonly_state qy fm) qcontext.
  Proof.
    intros qv qrec qy fm qcontext Hheap Hctx.
    destruct qv, qrec, qy, fm, qcontext; simpl in *; try contradiction;
      split; exact I.
  Qed.

  (** A value drawn from a typed history is well typed where it is read. *)
  Lemma histories_typed_typed_histories :
    forall h sigma,
      histories_typed (mkPicoCoreState h sigma) ->
      pico_core_typed_histories CT h sigma.
  Proof.
    intros h sigma Hhist sGamma mt rGamma x y f Tx Te loc v qcontext receiver
      Henv Hexpr Hx Hsub Hy Hthis Hmut Hin.
    destruct (Hhist loc f v Hin)
      as (rt & field_defs & fdef & Hrt & Hcf & Hnth & Hok).
    destruct Henv as (qc & rcv & Hcfg & Hthis' & Hmut' & Hvars).
    rewrite Hthis in Hthis'. injection Hthis' as <-.
    rewrite Hmut in Hmut'. injection Hmut' as <-.
    assert (Hwfheap : wf_heap CT h) by (destruct Hcfg as (_ & Hwf & _); exact Hwf).
    assert (Hfield : exists Ty C fDef,
      static_getType sGamma y = Some Ty /\ sbase Ty = TRef C /\
      sf_def_rel CT C f fDef /\
      (sqtype Te = vpa_mutability_stype_fld_abstract_state (sqtype Ty)
         (mutability (ftype fDef)) \/
       sqtype Te = vpa_mutability_stype_fld_readonly_state (sqtype Ty)
         (mutability (ftype fDef))) /\
      sbase Te = f_base_type (ftype fDef)).
    { inversion Hexpr; subst; do 3 eexists; repeat split; eauto. }
    destruct Hfield as (Ty & C & fDef & HTy & Href & Hfdef & Hq & Hbase).
    destruct (Hvars y Ty HTy) as (vy & Hvy & Htyped_y).
    rewrite Hy in Hvy. injection Hvy as <-.
    unfold r_type in Hrt.
    destruct (runtime_getObj h loc) as [o |] eqn:Hobj;
      [| rewrite Hobj in Hrt; discriminate].
    rewrite Hobj in Hrt.
    assert (Hrteq : rt = rt_type o) by congruence.
    subst rt. clear Hrt.
    have Heq := typed_receiver_field_def h qcontext Ty C loc o f fDef
      field_defs fdef Htyped_y Href Hobj Hfdef Hcf Hnth.
    subst fdef.
    simpl in Hok.
    destruct v as [| loc_v | n]; simpl.
    - eapply pico_core_subtype_preserves_reference; [| exact Hsub].
      destruct Hok as [D HD]. exists D. congruence.
    - destruct Hok as (rqt & Hrqt & Hbsub & Hqual).
      eapply wf_r_typable_subtype; [exact Hwfheap | | exact Hsub].
      unfold wf_r_typable. rewrite Hrqt. split; [congruence |].
      simpl in Htyped_y. unfold wf_r_typable, r_type in Htyped_y.
      rewrite Hobj in Htyped_y. destruct Htyped_y as [_ Hqy].
      destruct (field_qualifier_typable_read _ _ _ _ _ Hqual Hqy) as [Ha Hr].
      destruct Hq as [-> | ->]; assumption.
    - have Hbs := qualified_type_subtype_base_subtype CT _ _ Hsub.
      rewrite Hbase Hok in Hbs.
      exact (base_subtype_from_int _ _ Hbs).
  Qed.

  Lemma histories_typed_reads_typed :
    forall h sigma,
      histories_typed (mkPicoCoreState h sigma) ->
      pico_core_reads_typed CT h sigma.
  Proof.
    intros h sigma Hhist.
    apply pico_core_typed_histories_reads_typed.
    apply histories_typed_typed_histories. exact Hhist.
  Qed.
End typed_histories.

(** * Thread typing

    A running thread is typed when its statement is typed, its environment is
    typed in the current heap, and its continuation is typed.  A call frame
    remembers the typing facts of the call that pushed it, taken in the heap
    at the time of the call, because the return step needs them to adapt the
    returned value to the caller's viewpoint.  The heap may have grown since:
    the frame records only that runtime types were preserved, so it is stable
    under every step of every thread. *)

Section thread_typing.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).

  Inductive cont_typed (h : heap) :
      method_scope -> s_env -> Loc -> pico_core_cont -> Prop :=
    | ContTyped_Nil : forall mt sGamma this,
        cont_typed h mt sGamma this []
    | ContTyped_Seq : forall mt sGamma sGamma' this s2 K,
        stmt_typing CT sGamma mt s2 sGamma' ->
        cont_typed h mt sGamma' this K ->
        cont_typed h mt sGamma this (KSeq s2 :: K)
    | ContTyped_Call : forall mt_callee body_sGamma' loc caller x K
        h0 sGamma sGamma' mt y m args C mdef vals body_ret_type this_caller,
        stmt_typing CT sGamma mt (SCall x m y args) sGamma' ->
        pico_core_typed_env CT sGamma caller h0 ->
        pico_core_heap_types_extend h0 h ->
        runtime_getVal caller y = Some (Iot loc) ->
        r_basetype h0 loc = Some C ->
        FindMethodWithName CT C m mdef ->
        runtime_lookup_list caller args = Some vals ->
        static_getType body_sGamma' (mreturn (mbody mdef)) =
          Some body_ret_type ->
        qualified_type_subtype CT body_ret_type (mret (msignature mdef)) ->
        get_this_var_mapping (vars caller) = Some this_caller ->
        cont_typed h mt sGamma' this_caller K ->
        cont_typed h mt_callee body_sGamma' loc
          (KCall caller x (mreturn (mbody mdef)) :: K).

  Definition thread_typed (h : heap) (e : pico_core_expr) : Prop :=
    match e with
    | CoreRun rGamma s _ K =>
        exists sGamma mt sGamma' this,
          stmt_typing CT sGamma mt s sGamma' /\
          pico_core_typed_env CT sGamma rGamma h /\
          get_this_var_mapping (vars rGamma) = Some this /\
          cont_typed h mt sGamma' this K
    | CoreDone r _ _ => r <> MUTATIONEXP
    end.

  (** The shared-state invariant, and the guarantee of every typed step. *)
  Definition typed_state_inv (S : pico_core_state) : Prop :=
    histories_typed CT S /\
    pico_core_state_wf S /\
    wf_heap CT (pcs_heap S).

  Definition typed_guar (S S' : pico_core_state) : Prop :=
    pico_core_heap_types_extend (pcs_heap S) (pcs_heap S') /\
    typed_state_inv S'.

  Lemma typed_env_wf_heap :
    forall sGamma rGamma h,
      pico_core_typed_env CT sGamma rGamma h -> wf_heap CT h.
  Proof.
    intros sGamma rGamma h (qc & rcv & Hcfg & _).
    destruct Hcfg as (_ & Hwf & _). exact Hwf.
  Qed.

  Lemma typed_env_wf_senv :
    forall sGamma rGamma h,
      pico_core_typed_env CT sGamma rGamma h -> wf_senv CT sGamma.
  Proof.
    intros sGamma rGamma h (qc & rcv & Hcfg & _).
    destruct Hcfg as (_ & _ & _ & Hwf & _). exact Hwf.
  Qed.

  Lemma cont_typed_heap_types_extend :
    forall h h' mt sGamma this K,
      pico_core_heap_types_extend h h' ->
      cont_typed h mt sGamma this K ->
      cont_typed h' mt sGamma this K.
  Proof.
    intros h h' mt sGamma this K Hext Hcont.
    induction Hcont.
    - constructor.
    - econstructor; eauto.
    - econstructor; eauto.
      eapply pico_core_heap_types_extend_trans; eauto.
  Qed.

  (** Stability: a typed thread stays typed when another thread steps. *)
  Lemma thread_typed_stable :
    forall e S S',
      thread_typed (pcs_heap S) e ->
      typed_guar S S' ->
      thread_typed (pcs_heap S') e.
  Proof.
    intros e S S' Hthread [Hext (_ & _ & Hheap')].
    destruct e as [rGamma s V K | r rGamma V]; [| exact Hthread].
    destruct Hthread
      as (sGamma & mt & sGamma' & this & Htyping & Henv & Hthis & Hcont).
    exists sGamma, mt, sGamma', this.
    repeat split; try assumption.
    - eapply pico_core_typed_env_heap_types_extend; eauto.
    - eapply cont_typed_heap_types_extend; eauto.
  Qed.

  (** A typed field write never fails the run-time assignability check. *)
  Lemma typed_fldwrite_not_final :
    forall sGamma sGamma' mt rGamma h x f y loc_x o a val_y,
      stmt_typing CT sGamma mt (SFldWrite x f y) sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      runtime_getVal rGamma x = Some (Iot loc_x) ->
      runtime_getObj h loc_x = Some o ->
      sf_assignability_rel CT (rctype (rt_type o)) f a ->
      runtime_getVal rGamma y = Some val_y ->
      runtime_vpa_assignability (rqtype (rt_type o)) a = Final ->
      False.
  Proof.
    intros sGamma sGamma' mt rGamma h x f y loc_x o a val_y
      Htyping Henv Hx Hobj Hassign Hy Hfinal.
    assert (Hcfg : wf_r_config CT sGamma rGamma h).
    { destruct Henv as (qc & rcv & Hcfg & _). exact Hcfg. }
    assert (Hfield : exists vf, getVal (fields_map o) f = Some vf).
    { have Hwfobj := typed_env_wf_heap _ _ _ Henv loc_x
        (runtime_getObj_dom _ _ _ Hobj).
      unfold wf_obj in Hwfobj. rewrite Hobj in Hwfobj.
      destruct Hwfobj as (_ & field_defs & Hcf & Hlen & _).
      destruct Hassign as (fdef & Hlookup & _).
      inversion Hlookup as [CT0 C0 fields0 f0 fdef0 Hcf0 Hget]; subst.
      have Heq := collect_fields_deterministic_rel CT _ _ _ Hcf Hcf0.
      subst fields0.
      unfold getVal, gget in *.
      destruct (nth_error (fields_map o) f) as [vf |] eqn:Hnth;
        [eauto |].
      apply nth_error_None in Hnth.
      assert (Hlt : f < length field_defs)
        by (apply nth_error_Some; congruence).
      lia. }
    destruct Hfield as [vf Hvf].
    eapply well_typed_field_write_no_mutation_exp; eauto.
    eapply SBS_FldWrite_MUTATIONEXP; eauto.
  Qed.

  (** The primitive statements: declaration, assignment, field write and
      allocation. *)
  Definition primitive_stmt (s : stmt) : Prop :=
    match s with
    | SLocal _ _ | SVarAss _ _ | SFldWrite _ _ _ | SNew _ _ _ _ => True
    | _ => False
    end.

  Lemma primitive_step_post :
    forall sGamma sGamma' mt s rGamma h sigma V K e' S',
      primitive_stmt s ->
      stmt_typing CT sGamma mt s sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      pico_core_state_wf (mkPicoCoreState h sigma) ->
      histories_typed CT (mkPicoCoreState h sigma) ->
      pico_core_step CT (CoreRun rGamma s V K) (mkPicoCoreState h sigma)
        e' S' ->
      pico_core_stmt_post CT sGamma' K e' S'.
  Proof.
    intros sGamma sGamma' mt s rGamma h sigma V K e' S'
      Hprim Htyping Henv Hwf Hhist Hstep.
    assert (Hlr : pico_core_lr_state CT (mkPicoCoreState h sigma))
      by exact Hwf.
    destruct s; simpl in Hprim; try contradiction.
    - eapply pico_core_typed_local_step_post; eauto.
    - destruct e.
      + assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
        subst sGamma'.
        eapply pico_core_typed_assign_null_step_post; eauto.
      + assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
        subst sGamma'.
        eapply pico_core_typed_assign_var_step_post; eauto.
      + assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
        subst sGamma'.
        eapply pico_core_typed_assign_int_step_post; eauto.
      + eapply pico_core_typed_varass_field_step_post; eauto.
        intros loc_y val V' Hy Hread.
        eapply pico_core_typed_env_after_assign_field_read; eauto.
        apply histories_typed_reads_typed. exact Hhist.
      + assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
        subst sGamma'.
        eapply pico_core_typed_assign_bin_step_post; eauto.
    - eapply pico_core_typed_fldwrite_step_post; eauto.
    - eapply pico_core_typed_new_step_post; eauto.
  Qed.

  Lemma primitive_step_histories :
    forall sGamma sGamma' mt s rGamma h sigma V K e' S',
      primitive_stmt s ->
      stmt_typing CT sGamma mt s sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      pico_core_state_wf (mkPicoCoreState h sigma) ->
      histories_typed CT (mkPicoCoreState h sigma) ->
      pico_core_step CT (CoreRun rGamma s V K) (mkPicoCoreState h sigma)
        e' S' ->
      histories_typed CT S'.
  Proof.
    intros sGamma sGamma' mt s rGamma h sigma V K e' S'
      Hprim Htyping Henv Hwf Hhist Hstep.
    assert (Hlr : pico_core_lr_state CT (mkPicoCoreState h sigma))
      by exact Hwf.
    destruct s; simpl in Hprim; try contradiction.
    - inversion Hstep; subst; exact Hhist.
    - inversion Hstep; subst; exact Hhist.
    - eapply fldwrite_step_preserves_histories_typed; eauto.
    - eapply new_step_preserves_histories_typed; eauto.
  Qed.

  Lemma primitive_step_done :
    forall sGamma sGamma' mt s rGamma h sigma V K r rGamma' V' S',
      primitive_stmt s ->
      stmt_typing CT sGamma mt s sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      pico_core_step CT (CoreRun rGamma s V K) (mkPicoCoreState h sigma)
        (CoreDone r rGamma' V') S' ->
      S' = mkPicoCoreState h sigma /\ r <> MUTATIONEXP.
  Proof.
    intros sGamma sGamma' mt s rGamma h sigma V K r rGamma' V' S'
      Hprim Htyping Henv Hstep.
    inversion Hstep; subst; simpl in Hprim; try contradiction;
      try (split; [reflexivity | discriminate]).
    exfalso. eapply typed_fldwrite_not_final; eauto.
  Qed.

  Lemma primitive_step_receiver :
    forall sGamma sGamma' mt s rGamma h sigma V K rGamma' s' V' K' S' this,
      primitive_stmt s ->
      stmt_typing CT sGamma mt s sGamma' ->
      get_this_var_mapping (vars rGamma) = Some this ->
      pico_core_step CT (CoreRun rGamma s V K) (mkPicoCoreState h sigma)
        (CoreRun rGamma' s' V' K') S' ->
      get_this_var_mapping (vars rGamma') = Some this.
  Proof.
    intros sGamma sGamma' mt s rGamma h sigma V K rGamma' s' V' K' S' this
      Hprim Htyping Hthis Hstep.
    inversion Hstep; subst; simpl in Hprim; try contradiction;
      try exact Hthis.
    - change (get_this_var_mapping
        (vars (set_vars rGamma (vars rGamma ++ [default_value T]))) =
        Some this).
      rewrite get_this_var_mapping_update_vars_app_default. exact Hthis.
    - inversion Htyping; subst.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    - inversion Htyping; subst.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    - inversion Htyping; subst.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    - inversion Htyping; subst.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    - inversion Htyping; subst.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
    - inversion Htyping; subst.
      rewrite get_this_var_mapping_update_vars_nonzero; eauto.
  Qed.

  Lemma classic_primitive :
    forall s, primitive_stmt s \/ ~ primitive_stmt s.
  Proof. intros []; simpl; auto. Qed.

  (** ** Preservation

      One step of a typed thread, in a state satisfying the invariant, meets
      the guarantee and leaves the thread typed. *)
  Theorem typed_step :
    forall e S e' S',
      typed_state_inv S ->
      thread_typed (pcs_heap S) e ->
      pico_core_step CT e S e' S' ->
      typed_guar S S' /\ thread_typed (pcs_heap S') e'.
  Proof.
    intros e [h sigma] e' S' Hinv Hthread Hstep.
    pose proof Hinv as (Hhist & Hwf & Hheap).
    destruct e as [rGamma s V K | r rGamma V]; [| inversion Hstep].
    destruct Hthread
      as (sGamma & mt & sGamma' & this & Htyping & Henv & Hthis & Hcont).
    simpl in *.
    assert (Hsame : typed_guar (mkPicoCoreState h sigma)
      (mkPicoCoreState h sigma)).
    { split; [apply pico_core_heap_types_extend_refl | exact Hinv]. }
    destruct (classic_primitive s) as [Hprim | Hnonprim].
    - (* primitive statements *)
      have Hpost := primitive_step_post _ _ _ _ _ _ _ _ _ _ _
        Hprim Htyping Henv Hwf Hhist Hstep.
      have Hhist' := primitive_step_histories _ _ _ _ _ _ _ _ _ _ _
        Hprim Htyping Henv Hwf Hhist Hstep.
      have Hext := pico_core_step_preserves_heap_types CT _ _ _ _ Hstep.
      simpl in Hext.
      destruct e' as [rGamma' s' V' K' | r rGamma' V'].
      + inversion Hpost; subst.
        have Hthis' := primitive_step_receiver _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          Hprim Htyping Hthis Hstep.
        split.
        * split; [exact Hext |].
          split; [exact Hhist' |].
          split; [assumption |].
          eapply typed_env_wf_heap; eauto.
        * exists sGamma', mt, sGamma', this.
          split; [constructor; eapply typed_env_wf_senv; eauto |].
          split; [assumption |].
          split; [exact Hthis' |].
          eapply cont_typed_heap_types_extend; eauto.
      + destruct (primitive_step_done _ _ _ _ _ _ _ _ _ _ _ _ _
          Hprim Htyping Henv Hstep) as [-> Hr].
        split; [exact Hsame | exact Hr].
    - (* control statements *)
      destruct s; simpl in Hnonprim; try contradiction.
      + (* skip *)
        assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
        subst sGamma'.
        inversion Hstep; subst.
        * split; [exact Hsame | discriminate].
        * split; [exact Hsame |].
          inversion Hcont; subst.
          do 4 eexists.
          split; [eassumption |]. split; [eassumption |].
          split; eassumption.
        * split; [exact Hsame |].
          inversion Hcont; subst.
          match goal with
          | Hc : stmt_typing CT _ _ (SCall x _ _ _) _ |- _ =>
              rename Hc into Hcall
          end.
          match goal with
          | Hk : cont_typed h _ _ _ K0 |- _ => rename Hk into Hrest
          end.
          assert (Hshape : sGamma' = sGamma0 /\ x <> 0)
            by (inversion Hcall; subst; (split; [reflexivity | assumption])).
          destruct Hshape as [Heq Hx0]. subst sGamma'.
          assert (Henv' : pico_core_typed_env CT sGamma0
            (set_vars caller (update x retval (vars caller))) h)
            by (eapply pico_core_typed_resolved_method_return; eauto).
          exists sGamma0, mt0, sGamma0, this_caller.
          split; [constructor; eapply typed_env_wf_senv; eauto |].
          split; [exact Henv' |].
          split; [| assumption].
          rewrite get_this_var_mapping_update_vars_nonzero; assumption.
      + (* call *)
        assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
        subst sGamma'.
        inversion Hstep; subst.
        * split; [exact Hsame |].
          edestruct (pico_core_typed_resolved_method_body CT)
            as (body_sGamma' & body_ret_type & Hbody & Hret & Hretsub);
            [exact Htyping | exact Henv | eassumption | eassumption
            | eassumption | eassumption |].
          exists (mreceiver (msignature mdef) :: mparams (msignature mdef)),
            (mscope (msignature mdef)), body_sGamma', loc_y.
          split; [exact Hbody |].
          split; [eapply pico_core_typed_resolved_method_frame; eauto |].
          split; [reflexivity |].
          eapply ContTyped_Call; eauto.
          apply pico_core_heap_types_extend_refl.
        * split; [exact Hsame | discriminate].
      + (* sequence *)
        inversion Hstep; subst.
        split; [exact Hsame |].
        inversion Htyping; subst.
        do 4 eexists.
        split; [eassumption |]. split; [eassumption |].
        split; [eassumption |].
        econstructor; eauto.
      + (* zero test *)
        inversion Htyping; subst.
        inversion Hstep; subst.
        * split; [exact Hsame |].
          exists sGamma, mt, sGamma', this.
          split; [assumption |]. split; [assumption |]. split; assumption.
        * split; [exact Hsame |].
          exists sGamma, mt, sGamma', this.
          split; [assumption |]. split; [assumption |]. split; assumption.
        * split; [exact Hsame |].
          exists sGamma, mt, sGamma', this.
          split; [assumption |]. split; [assumption |]. split; assumption.
        * split; [exact Hsame |].
          exists sGamma, mt, sGamma', this.
          split; [assumption |]. split; [assumption |]. split; assumption.
  Qed.
  (** ** Progress

      A typed running thread can always take a step.  The step may end the
      thread with a null-pointer exception; by [typed_step] it never ends it
      with the mutation exception.  The memory model must let a read of a
      nonempty history return some value. *)
  Theorem typed_progress `{Hprogress : @CacheMemoryModelProgress Hmem} :
    forall rGamma s V K S,
      typed_state_inv S ->
      thread_typed (pcs_heap S) (CoreRun rGamma s V K) ->
      exists e' S', pico_core_step CT (CoreRun rGamma s V K) S e' S'.
  Proof.
    intros rGamma s V K [h sigma] (Hhist & Hwf & Hheap) Hthread.
    destruct Hthread
      as (sGamma & mt & sGamma' & this & Htyping & Henv & Hthis & Hcont).
    simpl in *.
    assert (Hlookup : forall x T, static_getType sGamma x = Some T ->
      exists v, runtime_getVal rGamma x = Some v).
    { intros x T Hx.
      destruct (pico_core_typed_env_lookup CT _ _ _ _ _ Henv Hx)
        as (qc & v & Hv & _).
      eauto. }
    destruct s.
    - (* skip *)
      assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
      subst sGamma'.
      inversion Hcont; subst.
      + do 2 eexists. apply PCS_SkipDone.
      + do 2 eexists. apply PCS_SkipSeq.
      + match goal with
        | Hret : static_getType sGamma _ = Some _ |- _ =>
            destruct (Hlookup _ _ Hret) as [retval Hretval]
        end.
        do 2 eexists. eapply PCS_SkipCall. exact Hretval.
    - (* local *)
      inversion Htyping; subst.
      do 2 eexists. apply PCS_Local.
      assert (Hlen : length sGamma = length (vars rGamma)).
      { destruct Henv as (qc & rcv & Hcfg & _).
        destruct Hcfg as (_ & _ & _ & _ & Hlen & _). exact Hlen. }
      unfold runtime_getVal, static_getType in *.
      apply nth_error_None. rewrite <- Hlen.
      apply nth_error_None. assumption.
    - (* assignment *)
      assert (sGamma' = sGamma) by (inversion Htyping; reflexivity).
      subst sGamma'.
      inversion Htyping; subst.
      match goal with
      | Hx : static_getType sGamma v = Some _ |- _ =>
          destruct (Hlookup _ _ Hx) as [old Hold]
      end.
      match goal with
      | He : expr_has_type CT sGamma mt e _ |- _ => rename He into Hexpr
      end.
      destruct e.
      + do 2 eexists. eapply PCS_AssignNull. exact Hold.
      + inversion Hexpr; subst.
        match goal with
        | Hy : static_getType sGamma v0 = Some _ |- _ =>
            destruct (Hlookup _ _ Hy) as [val_y Hval_y]
        end.
        do 2 eexists. eapply PCS_AssignVar; eassumption.
      + do 2 eexists. eapply PCS_AssignInt. exact Hold.
      + assert (Hfield : exists Ty C fDef,
          static_getType sGamma v0 = Some Ty /\ sbase Ty = TRef C /\
          sf_def_rel CT C v1 fDef).
        { inversion Hexpr; subst; do 3 eexists; repeat split; eauto. }
        destruct Hfield as (Ty & C & fDef & HTy & Href & Hfdef).
        destruct (pico_core_typed_env_field_receiver_cases CT _ _ _ _ _ _ _ _
          Henv HTy Href Hfdef) as [Hnull | (qc & loc & Hloc & Htyped)].
        * do 2 eexists. eapply PCS_AssignFieldNPE; eassumption.
        * destruct (pico_core_typed_receiver_field_exists CT _ _ _ _ _ _ _ _ _
            Henv Htyped Href Hfdef) as (o & current & Hobj & Hcur).
          destruct (pico_core_assign_field_step_exists CT rGamma v v0 v1 old
            loc o current V K h sigma Hold Hloc Hwf Hobj Hcur)
            as (val & V' & Hstep).
          eauto.
      + (* an integer operation: both operands hold integers *)
        assert (Hint : forall z T,
          static_getType sGamma z = Some T -> sbase T = TInt ->
          exists n, runtime_getVal rGamma z = Some (Int n)).
        { intros z T Hz HT.
          destruct (pico_core_typed_env_lookup CT _ _ _ _ _ Henv Hz)
            as (qc & v' & Hv' & Htv).
          destruct v' as [| loc | n]; simpl in Htv.
          - destruct Htv as [C HC]. congruence.
          - exfalso. unfold wf_r_typable in Htv.
            destruct (r_type h loc) as [rqt |]; [| contradiction].
            destruct Htv as [Hb _].
            destruct (base_subtype_from_ref CT _ _ Hb) as [C [HC _]].
            congruence.
          - eauto. }
        inversion Hexpr; subst.
        match goal with
        | Hy : static_getType sGamma v0 = Some ?T0, Hi : sbase ?T0 = TInt |- _ =>
            destruct (Hint _ _ Hy Hi) as [n1 Hn1]
        end.
        match goal with
        | Hz : static_getType sGamma v1 = Some ?T1, Hi : sbase ?T1 = TInt |- _ =>
            destruct (Hint _ _ Hz Hi) as [n2 Hn2]
        end.
        do 2 eexists. eapply PCS_AssignBin; eassumption.
    - (* field write *)
      destruct (pico_core_typed_fldwrite_runtime_cases CT _ _ _ _ _ _ _ _
        Htyping Henv)
        as [Hnull | (loc & o & a & val_y & Hloc & Hobj & Hassign & Hy & Hcase)].
      + do 2 eexists. eapply PCS_FldWriteNPE. exact Hnull.
      + destruct Hcase as [Hok | Hfinal].
        * do 2 eexists. eapply PCS_FldWrite; eauto.
          split; reflexivity.
        * do 2 eexists. eapply PCS_FldWriteMutation; eauto.
    - (* allocation *)
      destruct (pico_core_typed_env_receiver_runtime CT _ _ _ Henv)
        as (receiver & qthis & Hreceiver & Hmut).
      assert (Hargs : exists vals, runtime_lookup_list rGamma l = Some vals).
      { inversion Htyping; subst.
        eapply pico_core_typed_env_lookup_list_exists; eauto. }
      destruct Hargs as [vals Hvals].
      do 2 eexists. eapply PCS_New; eauto.
    - (* call *)
      destruct (pico_core_typed_call_runtime_cases CT _ _ _ _ _ _ _ _ _
        Htyping Henv)
        as [Hnull | (loc & C & mdef & vals & Hloc & Hbase & Hfind & Hvals)].
      + do 2 eexists. eapply PCS_CallNPE. exact Hnull.
      + do 2 eexists. eapply PCS_Call; eauto.
    - (* sequence *)
      do 2 eexists. apply PCS_Seq.
    - (* zero test *)
      inversion Htyping; subst.
      match goal with
      | Hx : static_getType _ v = Some ?Tx |- _ =>
          destruct (pico_core_typed_env_lookup CT _ _ _ _ _ Henv Hx)
            as (qc & val & Hval & Htyped)
      end.
      destruct val as [| loc | [| n]].
      + do 2 eexists. eapply PCS_IfNull. exact Hval.
      + do 2 eexists. eapply PCS_IfRef. exact Hval.
      + do 2 eexists. eapply PCS_IfZero. exact Hval.
      + do 2 eexists. eapply PCS_IfNonzero. exact Hval.
  Qed.
End thread_typing.

(** * Type safety under interleaving

    The parallel rule lifts single-step preservation to any number of threads
    under any interleaving.  Every thread relies on the others to preserve the
    typed-state invariant and to keep runtime types, and guarantees the
    same. *)

Section typed_pool.
  Context `{Hmem : CacheMemoryModel}.
  Context (CT : class_table).

  Definition typed_local (e : pico_core_expr) (S : pico_core_state) : Prop :=
    thread_typed CT (pcs_heap S) e.

  Definition typed_pool (cfg : pico_pool_config) : Prop :=
    pool_rg_inv (typed_state_inv CT) typed_local cfg.

  (** A typed statement started in a typed environment is a typed thread. *)
  Lemma thread_typed_start :
    forall sGamma mt s sGamma' rGamma h V,
      stmt_typing CT sGamma mt s sGamma' ->
      pico_core_typed_env CT sGamma rGamma h ->
      thread_typed CT h (CoreRun rGamma s V []).
  Proof.
    intros sGamma mt s sGamma' rGamma h V Htyping Henv.
    pose proof Henv as (qc & this & _ & Hthis & _).
    exists sGamma, mt, sGamma', this.
    split; [exact Htyping |]. split; [exact Henv |].
    split; [exact Hthis | constructor].
  Qed.

  (** Preservation: a typed pool stays typed. *)
  Theorem typed_pool_preservation :
    forall cfg cfg',
      typed_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      typed_pool cfg'.
  Proof.
    intros cfg cfg' Hpool Hsteps.
    eapply (pool_rely_guarantee CT (typed_state_inv CT) typed_local
      (typed_guar CT)); eauto.
    - intros e S e' S' Hinv Hlocal Hstep.
      exact (typed_step CT e S e' S' Hinv Hlocal Hstep).
    - intros S S' _ [_ Hinv']. exact Hinv'.
    - intros e S S' _ Hlocal Hguar.
      exact (thread_typed_stable CT e S S' Hlocal Hguar).
  Qed.

  (** No thread of a typed pool ever raises the mutation exception: typed
      code never fails the run-time assignability check, however the threads
      interleave and whichever values their weak reads return. *)
  Theorem typed_pool_no_mutation_exception :
    forall cfg cfg' r rGamma V,
      typed_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      List.In (CoreDone r rGamma V) (pool_threads cfg') ->
      r <> MUTATIONEXP.
  Proof.
    intros cfg cfg' r rGamma V Hpool Hsteps Hin.
    destruct (typed_pool_preservation cfg cfg' Hpool Hsteps) as [_ Hlocal].
    rewrite Forall_forall in Hlocal.
    exact (Hlocal _ Hin).
  Qed.

  (** Every value in every field history of a reachable state is well typed
      for its field. *)
  Theorem typed_pool_histories_typed :
    forall cfg cfg',
      typed_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      histories_typed CT (pool_state cfg').
  Proof.
    intros cfg cfg' Hpool Hsteps.
    destruct (typed_pool_preservation cfg cfg' Hpool Hsteps)
      as [(Hhist & _) _].
    exact Hhist.
  Qed.

  (** Progress for the pool: in every reachable pool, each thread has
      finished without the mutation exception or can take a step. *)
  Theorem typed_pool_progress
      `{Hprogress : @CacheMemoryModelProgress Hmem} :
    forall cfg cfg' e,
      typed_pool cfg ->
      pico_pool_steps CT cfg cfg' ->
      List.In e (pool_threads cfg') ->
      (exists r rGamma V, e = CoreDone r rGamma V /\ r <> MUTATIONEXP) \/
      (exists e' S', pico_core_step CT e (pool_state cfg') e' S').
  Proof.
    intros cfg cfg' e Hpool Hsteps Hin.
    destruct (typed_pool_preservation cfg cfg' Hpool Hsteps) as [Hinv Hlocal].
    rewrite Forall_forall in Hlocal.
    have Hthread := Hlocal _ Hin.
    destruct e as [rGamma s V K | r rGamma V].
    - right. eapply typed_progress; eauto.
    - left. exists r, rGamma, V. split; [reflexivity | exact Hthread].
  Qed.
End typed_pool.

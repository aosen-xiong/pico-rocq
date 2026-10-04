From Stdlib Require Import List Lia.
Import ListNotations.

Require Import Syntax Helpers Typing Subtyping Bigstep Properties Preservation
  ViewpointAdaptation.
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

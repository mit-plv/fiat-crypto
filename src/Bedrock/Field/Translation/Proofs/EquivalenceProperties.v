Require Import Coq.Strings.String.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Lists.List. (* after SeparationLogic *)
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Equivalence.
Require Import Crypto.Bedrock.Field.Translation.Proofs.UsedVarnames.
Require Import Crypto.Bedrock.Field.Translation.Proofs.VarnameSet.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.

Import API.Compilers.
Import ListNotations Types.Notations.

Section OnlyDiffer.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.
  Local Existing Instance Types.rep.Z.

  Lemma equiv_Z_only_differ_iff1
        {listZ : rep.rep base_listZ}
        locals1 locals2 vset (varname : base_ltype base_Z) s x :
    map.only_differ locals1 vset locals2 ->
    disjoint vset (varname_set_base varname) ->
    Lift1Prop.iff1
      (rep.equiv x (rep.rtype_of_ltype varname) s locals1)
      (rep.equiv x (rep.rtype_of_ltype varname) s locals2).
  Proof.
    cbn [varname_set_base
           rep.varname_set rep.equiv rep.rtype_of_ltype rep.Z].
    cbv [WeakestPrecondition.dexpr].
    rewrite <-disjoint_singleton_r_iff by eauto using string_dec.
    split; intros; sepsimpl; subst; eexists; sepsimpl; eauto;
      eapply expr_untouched; eauto using @only_differ_sym with typeclass_instances.
  Qed.

  Lemma equiv_Z_only_differ_undef {listZ:rep.rep base_listZ} :
    forall x y s locals locals' vset,
      map.only_differ locals vset locals' ->
      map.undef_on locals vset ->
      Lift1Prop.impl1
        (equivalent_base (t:=base_Z) x y s locals)
        (equivalent_base x y s locals').
  Proof.
    cbv [equivalent_base rep.equiv rep.Z WeakestPrecondition.dexpr].
    repeat intro; sepsimpl; subst; eexists; sepsimpl; eauto.
    eauto using expr_only_differ_undef.
  Qed.

  Section Local.
    Local Existing Instance rep.listZ_local.

    Lemma equiv_listZ_only_differ_local : forall
          locals1 locals2 vset (varnames : base_ltype base_listZ) s x (mem : mem),
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set_base varnames) ->
      rep.equiv x (rep.rtype_of_ltype varnames) s locals1 mem ->
      rep.equiv x (rep.rtype_of_ltype varnames) s locals2 mem.
    Proof.
      intros *.
      cbn [rep.equiv rep.rtype_of_ltype rep.listZ_local
                     varname_set rep.varname_set].
      rewrite !Forall.Forall2_map_r_iff.
      revert x; induction varnames; intros;
        match goal with H : Forall2 _ _ _ |- _ =>
                        inversion H; subst; clear H end;
        [ solve [eauto] | ].
      cbn [fold_right] in *; cbv [emp] in *. cleanup.
      constructor.
      { eapply equiv_Z_only_differ_iff1;
          cbn [rep.equiv rep.Z]; cbv [emp];
            destruct_head'_and;
            eauto using @only_differ_sym with typeclass_instances.
        cbv [varname_set rep.varname_set rep.Z] in *.
        match goal with H : disjoint _ _ |- _ =>
                        apply disjoint_union_r_iff in H;
                          cleanup
        end. eauto. }
      { apply IHvarnames; eauto.
        match goal with H : disjoint _ _ |- _ =>
                        apply disjoint_union_r_iff in H;
                          cleanup
        end. eauto. }
    Qed.

    Lemma equiv_listZ_only_differ_local_iff1
          locals1 locals2 vset (varnames : base_ltype base_listZ) s x :
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set_base varnames) ->
      Lift1Prop.iff1
        (rep.equiv x (rep.rtype_of_ltype varnames) s locals1)
        (rep.equiv x (rep.rtype_of_ltype varnames) s locals2).
    Proof.
      cbv [Lift1Prop.iff1]; split; intros;
        eapply equiv_listZ_only_differ_local;
        eauto using @only_differ_sym with typeclass_instances.
    Qed.

    Lemma equiv_listZ_only_differ_undef_local :
      forall x y s locals locals' vset,
        map.only_differ locals vset locals' ->
        map.undef_on locals vset ->
        Lift1Prop.impl1
          (equivalent_base (t:=base_listZ) x y s locals)
          (equivalent_base x y s locals').
    Proof.
      cbn [equivalent_base rep.equiv rep.listZ_local]; intros; sepsimpl.
      repeat intro; sepsimpl.
      eapply Forall.Forall2_Proper_impl;
        try eassumption; try reflexivity; repeat intro.
      eapply (equiv_Z_only_differ_undef (listZ:=rep.listZ_local)); eauto.
    Qed.
  End Local.

  Section InMemory.
    Local Existing Instance rep.listZ_mem.

    Lemma equiv_listZ_only_differ_mem
          locals1 locals2 vset (varnames : base_ltype base_listZ) s x :
          forall (mem : mem),
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set_base varnames) ->
      rep.equiv x (rep.rtype_of_ltype varnames) s locals1 mem ->
      rep.equiv x (rep.rtype_of_ltype varnames) s locals2 mem.
    Proof.
      intros *.
      cbn [rep.equiv rep.rtype_of_ltype rep.listZ_mem
                     varname_set rep.varname_set].
      intros.
      repeat match goal with
               H : Lift1Prop.ex1 _ _ |- Lift1Prop.ex1 _ _ =>
               let x := fresh in
               destruct H as [x ?]; exists x
             end.
      eapply Proper_sep_iff1; [ | reflexivity | eassumption ].
      cancel.
      eapply equiv_Z_only_differ_iff1; eauto using @only_differ_sym with typeclass_instances.
    Qed.

    Lemma equiv_listZ_only_differ_mem_iff1
          locals1 locals2 vset (varnames : base_ltype base_listZ) s x :
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set_base varnames) ->
      Lift1Prop.iff1
        (rep.equiv x (rep.rtype_of_ltype varnames) s locals1)
        (rep.equiv x (rep.rtype_of_ltype varnames) s locals2).
    Proof.
      cbv [Lift1Prop.iff1]; split; intros;
        eapply equiv_listZ_only_differ_mem;
        eauto using @only_differ_sym with typeclass_instances.
    Qed.

    Lemma equiv_listZ_only_differ_undef_mem :
      forall x y s locals locals' vset,
        map.only_differ locals vset locals' ->
        map.undef_on locals vset ->
        Lift1Prop.impl1
          (equivalent_base
             (t:=base_listZ) (listZ:=rep.listZ_mem)
             x y s locals)
          (equivalent_base x y s locals').
    Proof.
      cbn [equivalent_base rep.equiv rep.listZ_mem]; intros; sepsimpl.
      repeat intro; sepsimpl. eexists.
      repeat intro; sepsimpl. eexists.
      eapply Proper_sep_impl1; [ | reflexivity | eassumption ].
      repeat intro; sepsimpl; eauto.
      eapply (equiv_Z_only_differ_undef (listZ:=rep.listZ_mem)); eauto.
    Qed.

    Lemma equiv_nil_iff1 y s : forall (locals : locals),
      Lift1Prop.iff1
        (rep.equiv (rep:=rep.listZ_mem) [] y s locals)
        (Lift1Prop.ex1
           (fun x => rep.equiv (rep:=rep.Z) x y tt locals)).
    Proof.
      cbn [rep.equiv rep.listZ_mem rep.Z].
      intro; split; intros;
        repeat match goal with
               | _ => progress subst
               | _ => progress cbn [Array.array map] in *
               | _ => progress sepsimpl
               | H : map _ _ = [] |- _ =>
                 apply map_eq_nil in H
               | _ => rewrite word.of_Z_unsigned in *
               | |- _ /\ _ => split
               | |- Lift1Prop.ex1 _ _ => eexists
               | |- emp _ _ => cbv [emp]
               | _ => solve [apply word.unsigned_range]
               | _ => solve [eauto using map_nil]
               end.
    Qed.

    Lemma varname_set_listonly_listexcl {t} (names : _ t) :
      sameset
        (varname_set_base names)
        (union (varname_set_listonly names)
               (varname_set_listexcl names)).
    Proof.
      induction t;
        cbn [fst snd varname_set_base varname_set_listexcl
                 varname_set_listonly];
        break_match; intros;
          rewrite ?union_empty_l, ?union_empty_r;
          try reflexivity; [ ].
      rewrite IHt1, IHt2.
      clear. firstorder idtac.
    Qed.

    Lemma varname_set_listexcl_subset {t} (names : base_ltype t) :
      subset (varname_set_listexcl names) (varname_set_base names).
    Proof.
      rewrite varname_set_listonly_listexcl.
      clear. firstorder idtac.
    Qed.
  End InMemory.

  Section Generic.
    Context {listZ : rep.rep base_listZ}
            (equiv_listZ_only_differ_undef :
               forall x y s locals1 locals2 vset,
                 map.only_differ locals1 vset locals2 ->
                 map.undef_on locals1 vset ->
                 Lift1Prop.impl1
                   (rep.equiv (rep:=listZ) x y s locals1)
                   (rep.equiv x y s locals2))
            (equiv_listZ_only_differ :
               forall
                 locals1 locals2 vset
                 (varnames : base_ltype base_listZ) s x mem,
                 map.only_differ locals1 vset locals2 ->
                 disjoint vset (varname_set_base varnames) ->
                 rep.equiv x (rep.rtype_of_ltype varnames) s locals1 mem ->
                 rep.equiv x (rep.rtype_of_ltype varnames) s locals2 mem).

    Lemma equivalent_only_differ {t}
          locals1 locals2 vset (varnames : base_ltype t) s x :
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set_base varnames) ->
      forall mem,
        equivalent_base x (base_rtype_of_ltype varnames) s locals1 mem ->
        equivalent_base x (base_rtype_of_ltype varnames) s locals2 mem.
    Proof.
      intros Hdiffer Hexcl.
      induction t;
        cbn [fst snd rtype_of_ltype varname_set_base equivalent_base] in *;
        intros; break_match; destruct_head'_and; try tauto.
      { (* base case *)
        eapply equiv_Z_only_differ_iff1; eauto using @only_differ_sym with typeclass_instances. }
      { (* prod case *)
        match goal with H : disjoint _ (union _ _) |- _ =>
                        apply disjoint_union_r_iff in H
        end.
        cleanup.
        eapply Proper_sep_impl1; [ | | eassumption]; repeat intro; eauto.
        { apply IHt1; eauto. }
        { apply IHt2; eauto. } }
      { (* list case *)
        eapply equiv_listZ_only_differ; eauto. }
    Qed.

    Lemma equivalent_only_differ_iff1 {t}
          locals1 locals2 vset (varnames : base_ltype t) s x :
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set_base varnames) ->
      Lift1Prop.iff1
        (equivalent_base x (base_rtype_of_ltype varnames) s locals1)
        (equivalent_base x (base_rtype_of_ltype varnames) s locals2).
    Proof.
      repeat intro. split; intros.
      all:eapply equivalent_only_differ; eauto using @only_differ_sym with typeclass_instances.
    Qed.

    Lemma equivalent_args_only_differ {t}
          locals1 locals2 vset
          (argnames : type.for_each_lhs_of_arrow ltype t)
          s x :
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set_args argnames) ->
      let argvalues :=
          type.map_for_each_lhs_of_arrow
            rtype_of_ltype argnames in
      forall m,
        equivalent_args x argvalues s locals1 m ->
        equivalent_args x argvalues s locals2 m.
    Proof.
      induction t;
        cbv [Lift1Prop.iff1];
        cbn [fst snd rtype_of_ltype varname_set_args
                 type.map_for_each_lhs_of_arrow
                 equivalent_args];
        intros; break_match; cbn [fst snd] in *;
          try tauto; [ ].
      intros; cleanup; subst.
      repeat match goal with
             | |- _ /\ _ => split
             | |- exists _, _ => eexists
             | _ => solve [eauto]
             end;
        [ eapply Proper_sep_iff1;
          [ eapply equivalent_only_differ_iff1
          | reflexivity | eassumption ] | eapply IHt2 ];
        eauto using @only_differ_sym with typeclass_instances.
      all:match goal with
          | H : disjoint _ (union _ _) |- _ =>
            apply disjoint_union_r_iff in H;
              cleanup; eauto
          end.
    Qed.

    Lemma equivalent_only_differ_undef {t} :
      forall locals1 locals2 vset x y s,
        map.only_differ locals1 vset locals2 ->
        map.undef_on locals1 vset ->
        Lift1Prop.impl1
          (equivalent_base (t:=t) x y s locals1)
          (equivalent_base x y s locals2).
    Proof.
      induction t;
        cbn [equivalent_base];
        break_match; intros; try reflexivity; [ | | ].
      { eapply equiv_Z_only_differ_undef; eauto. }
      { apply Proper_sep_impl1; eauto. }
      { eapply equiv_listZ_only_differ_undef; eauto. }
    Qed.
  End Generic.
End OnlyDiffer.
Global Hint Resolve
     equiv_listZ_only_differ_undef_local
     equiv_listZ_only_differ_undef_mem
     equiv_listZ_only_differ_local
     equiv_listZ_only_differ_mem : equiv.

Section ContextEquivalence.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.
  Local Existing Instance Types.rep.Z.

  Section Local.
    Local Existing Instance Types.rep.listZ_local.

    (* 3-way equivalence (for single elements of the context list G
       from wf3 preconditions) *)
    Definition equiv3 {var1}
               (locals : Interface.map.rep (map:=locals))
               (x : {t : API.type
                         & (var1 t * API.interp_type t * ltype t)%type})
      : Prop :=
      match x with
      | existT (type.base b) (w, x, y) =>
        locally_equivalent x (base_rtype_of_ltype y) locals
      | existT (type.arrow _ _) _ => False (* no functions allowed *)
      end.

    Definition context_equiv {var1} G locals
      : Prop := Forall (equiv3 (var1:= var1) locals) G.

    Fixpoint context_varname_set {var1}
             (G : list {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
      : PropSet.set string :=
      match G with
      | (existT (type.base b) (w, x, y)) :: G' =>
        union (varname_set y) (context_varname_set G')
      |  _ => PropSet.empty_set (* no functions allowed *)
      end.

    Lemma varname_set_local x :
      sameset
        (rep.varname_set (rep:=rep.listZ_local) x)
        (of_list x).
    Proof.
      apply sameset_iff.
      cbn [rep.varname_set rep.listZ_local rep.Z].
      induction x; cbn [fold_right of_list In];
        [ solve [firstorder idtac] | ].
      intros. cbv [of_list] in *.
      rewrite <-IHx. firstorder idtac.
    Qed.
  End Local.

  Lemma equivalent_not_in_context {var1} locals1 locals2 vset x :
    map.only_differ locals1 vset locals2 ->
    disjoint vset (@context_varname_set var1 (x :: nil)) ->
    equiv3 locals1 x ->
    equiv3 locals2 x.
  Proof.
    intros; cbv [equiv3 context_varname_set locally_equivalent] in *.
    destruct x as [x [ [? ?] ?] ]; destruct x; [ | tauto ].
    eapply equivalent_only_differ; eauto with equiv.
    match goal with H : _ |- _ =>
                    apply disjoint_union_r_iff in H end.
    cleanup; eauto.
  Qed.

  Lemma equivalent_not_in_context_forall {var1} locals1 locals2 vset G :
    map.only_differ locals1 vset locals2 ->
    disjoint vset (@context_varname_set var1 G) ->
    Forall (equiv3 locals1) G ->
    Forall (equiv3 locals2) G.
  Proof.
    induction G; intros; constructor;
      repeat match goal with
             | _ => progress cbn [context_varname_set equiv3] in *
             | _ => progress break_match_hyps
             | H : disjoint _ (union _ _) |- _ =>
               apply disjoint_union_r_iff in H; cleanup
             | H : Forall _ (_ :: _) |- _ =>
               inversion H; subst; clear H
             | _ => tauto
             | _ => eapply equivalent_only_differ;
                      solve [eauto with equiv]
             end.
  Qed.
End ContextEquivalence.

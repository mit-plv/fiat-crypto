Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import Coq.Lists.List. (* after SeparationLogic *)
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Wf.Compilers.expr.
Import ListNotations.
Import Types.Notations Types.Types.

(* Reasoning about various collections of variable names *)
Section Varnames.
  Context {p : Types.parameters} {ok : @ok p}.
  Local Existing Instance Types.rep.Z.

  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.
  Local Notation varname := String.string.

  Section Equivalence.
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
        eapply expr_untouched; eauto using only_differ_sym.
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

      Lemma equiv_listZ_only_differ_local
            locals1 locals2 vset (varnames : base_ltype base_listZ) s x mem :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set_base varnames) ->
        rep.equiv x (rep.rtype_of_ltype varnames) s locals1 mem ->
        rep.equiv x (rep.rtype_of_ltype varnames) s locals2 mem.
      Proof.
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
              eauto using only_differ_sym.
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
          eauto using only_differ_sym.
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
            locals1 locals2 vset (varnames : base_ltype base_listZ) s x mem :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set_base varnames) ->
        rep.equiv x (rep.rtype_of_ltype varnames) s locals1 mem ->
        rep.equiv x (rep.rtype_of_ltype varnames) s locals2 mem.
      Proof.
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
        eapply equiv_Z_only_differ_iff1; eauto using only_differ_sym.
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
          eauto using only_differ_sym.
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

      Lemma equiv_nil_iff1 y s locals :
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
          eapply equiv_Z_only_differ_iff1; eauto using only_differ_sym. }
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
        all:eapply equivalent_only_differ; eauto using only_differ_sym.
      Qed.

      Lemma equivalent_args_only_differ_iff1 {t}
            locals1 locals2 vset
            (argnames : type.for_each_lhs_of_arrow ltype t)
            s x :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set_args argnames) ->
        let argvalues :=
            type.map_for_each_lhs_of_arrow
              rtype_of_ltype argnames in
        Lift1Prop.iff1
          (equivalent_args x argvalues s locals1)
          (equivalent_args x argvalues s locals2).
      Proof.
        induction t;
          cbv [Lift1Prop.iff1];
          cbn [fst snd rtype_of_ltype varname_set_args
                   type.map_for_each_lhs_of_arrow
                   equivalent_args];
          intros; break_match; cbn [fst snd] in *;
            try tauto.
        eapply Proper_sep_iff1;
          repeat match goal with
                 | _ => eapply equivalent_only_differ_iff1; eauto
                 | _ => eapply IHt2; eauto
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
  End Equivalence.
  Hint Resolve
       equiv_listZ_only_differ_undef_local
       equiv_listZ_only_differ_undef_mem
       equiv_listZ_only_differ_local
       equiv_listZ_only_differ_mem : equiv.

  Section UsedVarnames.
    Definition used_varnames nextn nvars : set varname :=
      of_list (map varname_gen (seq nextn nvars)).

    Lemma used_varnames_iff nextn nvars v :
      used_varnames nextn nvars v <->
      (exists n,
          v = varname_gen n /\ nextn <= n < nextn + nvars)%nat.
    Proof.
      cbv [used_varnames of_list]. revert nextn v.
      induction nvars; intros; cbn [seq map In];
        [ split; try tauto; intros; cleanup; lia | ].
      rewrite IHnvars.
      split; intros;
        repeat match goal with
               | _ => progress cleanup
               | _ => progress subst
               | H : _ \/ _ |- _ => destruct H
               | |- exists _, _ => eexists; solve [eauto with lia]
               end; [ ].
      match goal with H : _ <= _ |- _ =>
                      apply le_lt_or_eq in H; destruct H; [right | left]
      end.
      { eexists; eauto with lia. }
      { congruence. }
    Qed.

    Lemma used_varnames_disjoint n1 n2 l1 l2 :
      n1 + l1 <= n2 ->
      disjoint (used_varnames n1 l1) (used_varnames n2 l2).
    Proof.
      cbv [used_varnames].
      revert n1 n2 l2; induction l1; cbn [map seq]; intros;
        rewrite ?of_list_nil, ?of_list_cons;
          eauto using disjoint_empty_l.
      rewrite add_union_singleton.
      apply disjoint_union_l_iff; split; eauto with lia; [ ].
      apply disjoint_not_in. intro.
      repeat match goal with
             | _ => progress cleanup
             | H : In _ (map _ _) |- _ => rewrite in_map_iff in H
             | H : In _ (seq _ _) |- _ => rewrite in_seq in H
             | H : varname_gen _ = varname_gen _ |- _ =>
               apply varname_gen_unique in H
             | _ => lia
             end.
    Qed.

    Lemma used_varnames_succ_high n l :
      sameset (used_varnames n (S l))
              (add (used_varnames n l) (varname_gen (n + l))).
    Proof.
      intros. cbv [used_varnames].
      rewrite seq_snoc, map_app. cbn [map].
      rewrite of_list_app, of_list_cons.
      rewrite !add_union_singleton, of_list_nil, union_empty_r.
      apply union_comm.
    Qed.

    Lemma used_varnames_succ_low n m :
      PropSet.sameset (used_varnames n (S m))
                      (PropSet.add (used_varnames (S n) m)
                                   (varname_gen n)).
    Proof.
      apply sameset_iff. cbn. firstorder idtac.
    Qed.

    Lemma used_varnames_1 n :
      PropSet.sameset (used_varnames n 1)
                      (PropSet.singleton_set (varname_gen n)).
    Proof.
      apply sameset_iff. cbn. firstorder idtac.
    Qed.

    Lemma used_varnames_subset n1 n2 l1 l2 :
      (n2 <= n1)%nat ->
      (n1 + l1 <= n2 + l2)%nat ->
      PropSet.subset (used_varnames n1 l1)
                     (used_varnames n2 l2).
    Proof.
      cbv [PropSet.subset PropSet.elem_of];
        intros; rewrite !used_varnames_iff in *.
      cleanup; subst.
      eexists; split; [ reflexivity | lia ].
    Qed.

    Lemma used_varnames_union n m l :
      sameset (used_varnames n (m + l))
              (union (used_varnames n m) (used_varnames (n + m) l)).
    Proof.
      cbv [used_varnames].
      revert n m; induction l; cbn [map seq]; intros;
        rewrite ?Nat.add_0_r, ?of_list_nil, ?union_empty_r;
        try reflexivity; [ ].
      rewrite of_list_cons, add_union_singleton, union_assoc.
      rewrite <-Nat.add_succ_comm. rewrite IHl.
      rewrite seq_snoc, map_app. cbn [map].
      rewrite of_list_app, of_list_cons.
      rewrite !add_union_singleton, of_list_nil, union_empty_r.
      rewrite Nat.add_succ_r.
      reflexivity.
    Qed.

    Lemma used_varnames_shift n m l :
      subset (used_varnames (n + m) l)
             (used_varnames n (m + l)).
    Proof.
      cbv [subset]. intros.
      match goal with H : _ |- _ =>
                      apply used_varnames_iff in H end.
      apply used_varnames_iff.
      cleanup; subst. eexists; split; eauto.
      lia.
    Qed.

    Lemma used_varnames_subset_singleton n m l :
      n <= m < n + l ->
      subset (singleton_set (varname_gen m))
             (used_varnames n l).
    Proof.
      cbv [subset singleton_set elem_of]. intros.
      apply used_varnames_iff; subst.
      eexists; split; eauto; lia.
    Qed.
  End UsedVarnames.

  Section Local.
    Local Existing Instance Types.rep.listZ_local.
    (* 3-way equivalence (for single elements of the context list G
       from wf3 preconditions) *)
    Definition equiv3 {var1}
               (locals : Interface.map.rep (map:=Semantics.locals))
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
      : PropSet.set varname :=
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

  Lemma only_differ_zero nextn l :
    map.only_differ l (used_varnames nextn 0) l.
  Proof.
    cbv [map.only_differ used_varnames of_list elem_of].
    tauto.
  Qed.

  Lemma only_differ_succ nextn nvars l1 l2 v :
    map.only_differ (map.put l1 (varname_gen nextn) v)
                    (used_varnames (S nextn) nvars) l2 ->
    map.only_differ l1 (used_varnames nextn (S nvars)) l2.
  Proof.
    intros.
    eapply Proper_only_differ;
      [ reflexivity | | reflexivity
        | eapply only_differ_trans;
          solve [eauto using only_differ_sym, only_differ_put] ].
    eapply sameset_iff; intros.
    cbv [used_varnames of_list elem_of union singleton_set].
    cbn [seq map In].
    tauto.
  Qed.

  Lemma only_differ_step nvars nvars' nextn l1 l2 l3 :
    map.only_differ l1 (used_varnames nextn nvars) l2 ->
    map.only_differ l2 (used_varnames (nextn + nvars) nvars') l3 ->
    map.only_differ l1 (used_varnames nextn (nvars + nvars')) l3.
  Proof.

    (* if you want to change the definition of used_varnames:
    replace used_varnames with
        (fun nextn nvars v => 
           (exists n : nat, v = varname_gen n /\ nextn <= n < nextn + nvars)).
    2:admit.
    intros.
    pose proof (only_differ_trans _ _ _ _ _ H0 H).
    clear H0 H.
    eapply only_differ_sameset. 2:eassumption.
    clear H1.
    apply sameset_iff.
    intros. cbv [union elem_of].
    intuition (cleanup; subst; try lia).
    1-2:(exists x; split; [trivial | lia ]).
    
    destruct (le_dec (nextn + nvars) x);
      [ left | right].
    all:exists x; split; [trivial | lia ].
               
    firstorder lia. *)
    
    cbv [map.only_differ used_varnames of_list
                         elem_of].
    let H1 := fresh in
    let H2 := fresh in
    let x := fresh "x" in
    intros H1 H2 x; specialize (H1 x); specialize (H2 x).
    repeat match goal with
           | _ => progress cleanup
           | _ => progress subst
           | H : _ \/ _ |- _ => destruct H
           | |- context [In _ (map _ _)] => rewrite in_map_iff
           | H : In _ (map _ _) |- _ => apply in_map_iff in H
           | H : In _ (seq _ _) |- _ => apply in_seq in H
           | H : varname_gen _ = varname_gen _ |- _ =>
             apply varname_gen_unique in H
           | _ => solve [right; congruence]
           | _ => solve [left; eexists;
                         rewrite in_seq, varname_gen_unique; split;
                         eauto with lia ]
           end.
  Qed.

  Lemma disjoint_used_varnames_lt n nvars (vset : set varname) :
    (forall x, n <= x -> ~ vset (varname_gen x)) ->
    disjoint (used_varnames n nvars) vset.
  Proof.
    cbv [disjoint elem_of]; intros.
    apply Decidable.imp_simp.
    { cbv [used_varnames Decidable.decidable of_list ].
      match goal with
        |- In ?x ?l \/ ~ In ?x ?l =>
        destruct (in_dec string_dec x l); [left|right]
      end; tauto. }
    rewrite used_varnames_iff.
    intros; cleanup; subst.
    eauto with lia.
  Qed.

  Lemma disjoint_used_varnames_singleton n nvars m :
    m < n ->
    disjoint (used_varnames n nvars)
             (singleton_set (varname_gen m)).
  Proof.
    cbv [singleton_set elem_of]; intros.
    eapply disjoint_used_varnames_lt. intros.
    rewrite varname_gen_unique. lia.
  Qed.
End Varnames.
Hint Resolve
     equiv_listZ_only_differ_undef_local
     equiv_listZ_only_differ_undef_mem
     equiv_listZ_only_differ_local
     equiv_listZ_only_differ_mem : equiv.

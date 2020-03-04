Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface.
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

  (* TODO: are these all needed? *)
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Decidable.String.eqb_spec x y.
  Local Notation varname := String.string.

  Section Equivalence.
    Lemma equiv_Z_only_differ_iff1
          {listZ : rep.rep base_listZ}
          locals1 locals2 vset (varname : base_ltype base_Z) x :
      map.only_differ locals1 vset locals2 ->
      disjoint vset (varname_set varname) ->
      Lift1Prop.iff1
        (rep.equiv x (rep.rtype_of_ltype varname) locals1)
        (rep.equiv x (rep.rtype_of_ltype varname) locals2).
    Admitted.

    Section Local.
      Local Existing Instance rep.listZ_local.

      Lemma equiv_listZ_only_differ_local
            locals1 locals2 vset (varnames : base_ltype base_listZ) x mem :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set varnames) ->
        rep.equiv x (rep.rtype_of_ltype varnames) locals1 mem ->
        rep.equiv x (rep.rtype_of_ltype varnames) locals2 mem.
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
            locals1 locals2 vset (varnames : base_ltype base_listZ) x :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set varnames) ->
        Lift1Prop.iff1
          (rep.equiv x (rep.rtype_of_ltype varnames) locals1)
          (rep.equiv x (rep.rtype_of_ltype varnames) locals2).
      Proof.
        cbv [Lift1Prop.iff1]; split; intros;
          eapply equiv_listZ_only_differ_local;
          eauto using only_differ_sym.
      Qed.
    End Local.

    Section InMemory.
      Local Existing Instance rep.listZ_mem.

      Lemma equiv_listZ_only_differ_mem
            locals1 locals2 vset (varnames : base_ltype base_listZ) x mem :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set varnames) ->
        rep.equiv x (rep.rtype_of_ltype varnames) locals1 mem ->
        rep.equiv x (rep.rtype_of_ltype varnames) locals2 mem.
      Proof.
        cbn [rep.equiv rep.rtype_of_ltype rep.listZ_mem
                       varname_set rep.varname_set].
        intros.
        match goal with
          H : Lift1Prop.ex1 _ _ |- Lift1Prop.ex1 _ _ =>
          let x := fresh in
          destruct H as [x ?]; exists x
        end.
        eapply Proper_sep_iff1; [ | reflexivity | eassumption ].
        eapply equiv_Z_only_differ_iff1; eauto using only_differ_sym.
      Qed.

      Lemma equiv_listZ_only_differ_mem_iff1
            locals1 locals2 vset (varnames : base_ltype base_listZ) x :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set varnames) ->
        Lift1Prop.iff1
          (rep.equiv x (rep.rtype_of_ltype varnames) locals1)
          (rep.equiv x (rep.rtype_of_ltype varnames) locals2).
      Proof.
        cbv [Lift1Prop.iff1]; split; intros;
          eapply equiv_listZ_only_differ_mem;
          eauto using only_differ_sym.
      Qed.
    End InMemory.

    Section Generic.
      Context {listZ : rep.rep base_listZ}
              (equiv_listZ_only_differ :
                 forall
                   locals1 locals2 vset
                   (varnames : base_ltype base_listZ) x mem,
                   map.only_differ locals1 vset locals2 ->
                   disjoint vset (varname_set varnames) ->
                   rep.equiv x (rep.rtype_of_ltype varnames) locals1 mem ->
                   rep.equiv x (rep.rtype_of_ltype varnames) locals2 mem).

      Lemma equivalent_only_differ {t}
            locals1 locals2 vset (varnames : base_ltype t) x :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set varnames) ->
        forall mem,
          equivalent x (base_rtype_of_ltype varnames) locals1 mem ->
          equivalent x (base_rtype_of_ltype varnames) locals2 mem.
      Proof.
        intros Hdiffer Hexcl.
        induction t;
          cbn [fst snd rtype_of_ltype varname_set equivalent] in *; intros;
            BreakMatch.break_match; destruct_head'_and; try tauto.
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
            locals1 locals2 vset (varnames : base_ltype t) x :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set varnames) ->
        Lift1Prop.iff1
          (equivalent x (base_rtype_of_ltype varnames) locals1)
          (equivalent x (base_rtype_of_ltype varnames) locals2).
      Proof.
        repeat intro. split; intros.
        all:eapply equivalent_only_differ; eauto using only_differ_sym.
      Qed.

      Lemma equivalent_args_only_differ_iff1 {t}
            locals1 locals2 vset
            (argnames : type.for_each_lhs_of_arrow ltype t)
            x :
        map.only_differ locals1 vset locals2 ->
        disjoint vset (varname_set_args argnames) ->
        let argvalues :=
            type.map_for_each_lhs_of_arrow
              rtype_of_ltype argnames in
        Lift1Prop.iff1
          (equivalent_args x argvalues locals1)
          (equivalent_args x argvalues locals2).
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
    End Generic.
  End Equivalence.
  Hint Resolve equiv_listZ_only_differ_local
       equiv_listZ_only_differ_mem : equiv.

  Section UsedVarnames.
    Definition used_varnames nextn nvars : set varname :=
      of_list (map varname_gen (seq nextn nvars)).

    Lemma used_varnames_iff nextn nvars v :
      used_varnames nextn nvars v <->
      (exists n,
          v = varname_gen n /\ nextn <= n < nextn + nvars)%nat.
    Admitted.

    Lemma used_varnames_le nextn nvars n :
      (nextn + nvars <= n)%nat ->
      ~ used_varnames nextn nvars (varname_gen n).
    Admitted.
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

  (* if two maps only differ on some keys, and we get a key that
         is not in the differing set, then any proposition that holds
         on one result should hold on the other. *)
  Lemma get_untouched m1 m2 ks k P :
    map.only_differ m2 ks m1 ->
    ~ ks k ->
    WeakestPrecondition.get m1 k P <-> WeakestPrecondition.get m2 k P.
  Admitted.

  Lemma expr_untouched mem1 mem2 l1 l2 vars v P :
    map.only_differ l2 vars l1 ->
    ~ vars v ->
    WeakestPrecondition.expr mem1 l1 (expr.var v) P <->
    WeakestPrecondition.expr mem2 l2 (expr.var v) P.
  Proof.
    intros.
    cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body].
    rewrite get_untouched; eauto; reflexivity.
  Qed.
End Varnames.
Hint Resolve equiv_listZ_only_differ_local
     equiv_listZ_only_differ_mem : equiv.

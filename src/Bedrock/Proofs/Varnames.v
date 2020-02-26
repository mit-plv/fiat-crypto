Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.PropSet.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.DestructHead.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Wf.Compilers.expr.
Import Types.Notations Types.Types.

(* General-purpose lemmas about maps that should be later moved to coqutil *)
(* TODO: move *)
Section Sets.
  Context {E : Type}.

  Lemma disjoint_union_r_iff (s1 s2 s3 : set E) :
    disjoint s1 (union s2 s3) <-> disjoint s1 s2 /\ disjoint s1 s3.
  Proof.
    cbv [disjoint union elem_of];
      repeat match goal with
             | _ => progress intros
             | H : forall _, _ |- _ =>
               specialize (H ltac:(eassumption))
             | H : _ \/ _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | _ => split
             | _ => tauto
             end.
  Qed.

  Lemma disjoint_cons (s : set E) x l :
    disjoint s (of_list (x :: l)) ->
    disjoint s (of_list l) /\ disjoint s (singleton_set x).
  Proof.
    cbv [disjoint of_list elem_of]; cbn [In].
    repeat match goal with
           | _ => progress intros
           | H : _ \/ _ |- _ => destruct H
           | H : _ /\ _ |- _ => destruct H
           | _ => split
           | _ => tauto
           | H : forall _, _ |- context[s ?x] =>
             specialize (H x); tauto
           end.
  Qed.

  Lemma sameset_iff (s1 s2 : set E) :
    sameset s1 s2 <-> (forall e, s1 e <-> s2 e).
  Proof.
    cbv [sameset subset elem_of]. split.
    { destruct 1; split; eauto. }
    { intro Hiff; split; apply Hiff; eauto. }
  Qed.

  Lemma not_union_iff (s1 s2 : set E) x :
    ~ union s1 s2 x <-> ~ s1 x /\ ~ s2 x.
  Proof. cbv [union elem_of]. tauto. Qed.
End Sets.

(* General-purpose lemmas about maps that should be later moved to coqutil *)
(* TODO: move *)
Section Maps.
  Lemma only_differ_trans {key value} {map: map.map key value}
        m1 m2 m3 ks1 ks2 :
    map.only_differ m2 ks1 m1 ->
    map.only_differ m3 ks2 m2 ->
    map.only_differ m3 (union ks1 ks2) m1.
  Admitted.

  Lemma only_differ_sym {key value} {map: map.map key value}
        m1 m2 ks :
    map.only_differ m2 ks m1 ->
    map.only_differ m1 ks m2.
  Admitted.

  Lemma only_differ_sameset {key value} {map: map.map key value}
        m1 m2 ks1 ks2 :
    sameset ks1 ks2 ->
    map.only_differ m2 ks1 m1 ->
    map.only_differ m2 ks2 m1.
  Admitted.

  Lemma only_differ_put {key value} {map: map.map key value}
        m k v :
    map.only_differ (map.put m k v) (singleton_set k) m.
  Admitted.
End Maps.

(* General-purpose lemmas about lists that should be later moved to coqutil *)
(* TODO: move *)
Section Lists.
  Context {A : Type}.

  Lemma hd_map {B} (f : A -> B) x l :
    hd (f x) (map f l) = f (hd x l).
  Proof. destruct l; reflexivity. Qed.

  Lemma hd_skipn_nth_default (d:A) l i :
    nth_default d l i = hd d (skipn i l).
  Proof.
    revert i; induction l; destruct i; try reflexivity.
    rewrite nth_default_cons_S, skipn_cons_S. eauto.
  Qed.
End Lists.

(* General-purpose lemmas about sep that should be later moved to bedrock2 *)
(* TODO: move *)
Section Separation.
  Context `{map_ok : map.ok}
           {key_eqb : forall H H0 : key, bool}
           {key_eq_dec :
              forall x y : key,
                BoolSpec (x = y) (x <> y) (key_eqb x y)}.
  Lemma sep_empty_iff (q r : map.rep -> Prop) :
    sep q r map.empty <-> q map.empty /\ r map.empty.
  Proof.
    cbv [sep].
    repeat match goal with
           | _ => progress (intros; cleanup)
           | _ => progress subst
           | H : _ |- _ => apply map.split_empty in H
           | _ => rewrite map.split_empty
           | _ => exists map.empty
           | _ => tauto
           | _ => split
           end.
  Qed.
End Separation.

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
      (forall v, vset v -> ~ varname_set varname v) ->
      Lift1Prop.iff1
        (rep.equiv x (rep.rtype_of_ltype varname) locals1)
        (rep.equiv x (rep.rtype_of_ltype varname) locals2).
    Admitted.

    Section Local.
      Local Existing Instance rep.listZ_local.

      Lemma equiv_listZ_only_differ_local
            locals1 locals2 vset (varnames : base_ltype base_listZ) x mem :
        map.only_differ locals1 vset locals2 ->
        (forall v, vset v -> ~ varname_set varnames v) ->
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
              destruct_head'_and; eauto using only_differ_sym.
          cbv [varname_set rep.varname_set rep.Z] in *.
          match goal with H : _ |- _ =>
                   setoid_rewrite not_union_iff in H;
                     apply H; eauto
          end. }
        { apply IHvarnames; eauto.
          match goal with H : _ |- _ =>
                   setoid_rewrite not_union_iff in H;
                     apply H; eauto
          end. }
      Qed.

      Lemma equiv_listZ_only_differ_local_iff1
            locals1 locals2 vset (varnames : base_ltype base_listZ) x :
        map.only_differ locals1 vset locals2 ->
        (forall v, vset v -> ~ varname_set varnames v) ->
        Lift1Prop.iff1
          (rep.equiv x (rep.rtype_of_ltype varnames) locals1)
          (rep.equiv x (rep.rtype_of_ltype varnames) locals2).
      Proof.
        cbv [Lift1Prop.iff1]; split; intros;
          eapply equiv_listZ_only_differ_local; eauto using only_differ_sym.
      Qed.
    End Local.

    Section InMemory.
      Local Existing Instance rep.listZ_mem.

      Lemma equiv_listZ_only_differ_mem
            locals1 locals2 vset (varnames : base_ltype base_listZ) x mem :
        map.only_differ locals1 vset locals2 ->
        (forall v, vset v -> ~ varname_set varnames v) ->
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
        (forall v, vset v -> ~ varname_set varnames v) ->
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
                   (forall v, vset v -> ~ varname_set varnames v) ->
                   rep.equiv x (rep.rtype_of_ltype varnames) locals1 mem ->
                   rep.equiv x (rep.rtype_of_ltype varnames) locals2 mem).

      Lemma equivalent_only_differ {t}
            locals1 locals2 vset (varnames : base_ltype t) x :
        map.only_differ locals1 vset locals2 ->
        (forall v, vset v -> ~ varname_set varnames v) ->
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
          cbv [union elem_of] in *.
          eapply Proper_sep_impl1; [ | | eassumption]; repeat intro; eauto.
          { apply IHt1; eauto.
            match goal with H : _ |- _ =>
                            let x1 := fresh in
                            let x2 := fresh in
                            intros x1 x2; specialize (H x1 x2)
            end.
            tauto. }
          { apply IHt2; eauto.
            match goal with H : _ |- _ =>
                            let x1 := fresh in
                            let x2 := fresh in
                            intros x1 x2; specialize (H x1 x2)
            end.
            tauto. } }
        { (* list case *)
          eapply equiv_listZ_only_differ; eauto. }
      Qed.

      Lemma equivalent_only_differ_iff1 {t}
            locals1 locals2 vset (varnames : base_ltype t) x :
        map.only_differ locals1 vset locals2 ->
        (forall v, vset v -> ~ varname_set varnames v) ->
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
        (forall v, vset v -> ~ varname_set_args argnames v) ->
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
                 | H : _ |- _ =>
                   setoid_rewrite not_union_iff in H;
                     apply H; eauto
                 end.
      Qed.
    End Generic.
  End Equivalence.

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

    Definition varname_not_in_context {var1}
               (v : varname)
               (x : {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
      : Prop :=
      match x with
      | existT (type.base b) (w, x, y) =>
        ~ (varname_set y) v
      | existT (type.arrow _ _) _ => False (* no functions allowed *)
      end.
  End Local.

  Lemma equivalent_not_in_context {var1} locals1 locals2 vset x :
    map.only_differ locals1 vset locals2 ->
    (forall v, vset v -> varname_not_in_context v x) ->
    equiv3 (var1:=var1) locals1 x ->
    equiv3 locals2 x.
  Proof.
    intros; cbv [equiv3 varname_not_in_context locally_equivalent] in *.
    destruct x as [x [ [? ?] ?] ]; destruct x; [ | tauto ].
    eauto using equivalent_only_differ, equiv_listZ_only_differ_local.
  Qed.

  Lemma equivalent_not_in_context_forall {var1} locals1 locals2 vset G :
    map.only_differ locals1 vset locals2 ->
    (forall v, vset v -> Forall (varname_not_in_context v) G) ->
    Forall (equiv3 (var1:=var1) locals1) G ->
    Forall (equiv3 locals2) G.
  Proof.
    intros Hdiffer Hexcl; induction G; intros; constructor;
      match goal with
      | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H end.
    { eapply equivalent_not_in_context; eauto.
      intros x y; specialize (Hexcl x y); inversion Hexcl; auto. }
    { apply IHG; auto.
      intros x y; specialize (Hexcl x y); inversion Hexcl; auto. }
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
    eapply only_differ_sameset;
    [ | eapply only_differ_trans;
        eauto using only_differ_sym, only_differ_put ].
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

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.RelationClasses.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.PropSet.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.ListUtil.
Require Import Coq.Lists.List. (* after SeparationLogic *)
Import ListNotations.

(* This file contains general-purpose lemmas about other libraries that should
   eventually be moved to those libraries or to coqutil *)

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

  Lemma firstn_length_firstn n (l : list A) :
    firstn (length (firstn n l)) l = firstn n l.
  Proof.
    revert l; induction n; destruct l;
      cbn [firstn length]; rewrite ?IHn; reflexivity.
  Qed.

  Lemma skipn_length_firstn n (l : list A) :
    skipn (length (firstn n l)) l = skipn n l.
  Proof.
    revert l; induction n; destruct l;
      cbn [skipn firstn length]; rewrite ?IHn; reflexivity.
  Qed.

  Lemma NoDup_app_iff (l1 l2 : list A) :
    NoDup (l1 ++ l2) <-> (NoDup l1 /\ NoDup l2
                          /\ (forall x, In x l1 -> ~ In x l2)
                          /\ (forall x, In x l2 -> ~ In x l1)).
  Proof.
    revert l2; induction l1;
      repeat match goal with
             | _ => progress (intros; subst)
             | _ => progress cbn [In]
             | _ => rewrite app_nil_l
             | _ => rewrite <-app_comm_cons
             | _ => split
             | H : _ /\ _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H: ~ In _ (_ ++ _) |- _ =>
               rewrite in_app_iff in H;
                 apply Decidable.not_or in H
             | H: NoDup (_ ++ _) |- _ =>
               apply IHl1 in H
             | H: NoDup (_ :: _) |- _ =>
               inversion H; clear H; subst
             | |- ~ (_ \/ _) => intro
             | |- ~ In _ (_ ++_) =>
               rewrite in_app_iff
             | |- NoDup (_ ++ _) => apply IHl1
             | |- NoDup (_ :: _) => constructor
             | |- NoDup [] => constructor
             | H1 : (forall x (H:In x ?l), _),
                    H2 : In _ ?l |- _ => apply H1 in H2; tauto
             | H : forall x (_:?a = x \/ _), _ |- _ =>
               specialize (H a ltac:(tauto)); tauto
             | _ => solve [eauto]
             | _ => tauto
             end.
  Qed.

  Lemma Forall2_impl_strong {B} (R1 R2 : A -> B -> Prop) xs ys :
    (forall x y, R1 x y -> In x xs -> In y ys -> R2 x y) ->
    Forall2 R1 xs ys -> Forall2 R2 xs ys.
  Proof.
    revert ys; induction xs; destruct ys; intros;
      match goal with H : Forall2 _ _ _ |- _ =>
                      inversion H; subst; clear H end;
      constructor; eauto using in_eq, in_cons.
  Qed.

  Lemma Forall2_app_inv {B} (R : A -> B -> Prop)
        xs1 xs2 ys1 ys2 :
    length xs1 = length ys1 ->
    Forall2 R (xs1 ++ xs2) (ys1 ++ ys2) ->
    Forall2 R xs1 ys1 /\ Forall2 R xs2 ys2.
  Proof.
    revert xs2 ys1 ys2; induction xs1;
      destruct ys1; cbn [length]; intros; try lia.
    all:repeat match goal with
               | _ => rewrite app_nil_l in *
               | _ => rewrite <-app_comm_cons in *
               | H : Forall2 _ (_ :: _) _ |- _ =>
                 inversion H; subst; clear H
               | |- _ /\ _ => split
               | |- Forall2 _ _ _ => constructor
               | _ => solve [eauto]
               | H : Forall2 _ (_ ++ _) _ |- _ =>
                 apply IHxs1 in H; [ | lia .. ];
                   destruct H
               end.
  Qed.

  Lemma NoDup_combine_l {B} xs ys :
    NoDup xs -> NoDup (@combine A B xs ys).
  Proof.
    revert ys; induction xs; destruct ys; inversion 1;
      intros; subst; cbn [combine]; constructor; auto; [ ].
    let H := fresh in intro H; apply in_combine_l in H.
    contradiction.
  Qed.
End Lists.

Section Sets.
  Context {E : Type}.

  Lemma disjoint_union_l_iff (s1 s2 s3 : set E) :
    disjoint (union s1 s2) s3 <-> disjoint s1 s3 /\ disjoint s2 s3.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_union_r_iff (s1 s2 s3 : set E) :
    disjoint s1 (union s2 s3) <-> disjoint s1 s2 /\ disjoint s1 s3.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_cons (s : set E) x l :
    disjoint s (of_list (x :: l)) ->
    disjoint s (of_list l) /\ disjoint s (singleton_set x).
  Proof. firstorder idtac. Qed.

  Lemma disjoint_singleton_r_iff
        (x : E) (s : set E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}):
    ~ s x <->
    disjoint s (singleton_set x).
  Proof.
    intros. split; [|firstorder idtac].
    intros. intro y.
    destruct (eq_dec x y);
      subst; try firstorder idtac.
  Qed.

  Lemma disjoint_singleton_singleton
        (x y : E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}):
    y <> x ->
    disjoint (singleton_set x) (singleton_set y).
  Proof.
    intros.
    apply disjoint_singleton_r_iff;
      firstorder congruence.
  Qed.

  Lemma disjoint_sameset (s1 s2 s3 : set E) :
    sameset s3 s1 ->
    disjoint s1 s2 ->
    disjoint s3 s2.
  Proof. firstorder idtac. Qed.

  Global Instance disjoint_sym : Symmetric (@disjoint E).
  Proof. firstorder idtac. Defined.
  Global Instance disjoint_Proper
    : Proper (sameset ==> sameset ==> iff) (@disjoint E).
  Proof. firstorder idtac. Defined.

  Global Instance subset_trans : Transitive (@subset E).
  Proof. firstorder idtac. Defined.
  Global Instance subset_ref : Reflexive (@subset E).
  Proof. firstorder idtac. Defined.
  Global Instance subset_Proper
    : Proper (sameset ==> sameset ==> iff) (@subset E).
  Proof. firstorder idtac. Defined.

  Global Instance sameset_sym : Symmetric (@sameset E).
  Proof. firstorder idtac. Defined.
  Global Instance sameset_trans : Transitive (@sameset E).
  Proof. firstorder idtac. Defined.
  Global Instance sameset_ref : Reflexive (@sameset E).
  Proof. firstorder idtac. Defined.

  Lemma sameset_iff (s1 s2 : set E) :
    sameset s1 s2 <-> (forall e, s1 e <-> s2 e).
  Proof. firstorder idtac. Qed.

  Lemma not_union_iff (s1 s2 : set E) x :
    ~ union s1 s2 x <-> ~ s1 x /\ ~ s2 x.
  Proof. firstorder idtac. Qed.

  Lemma add_union_singleton (x : E) s :
    add s x = union (singleton_set x) s.
  Proof. reflexivity. Qed.

  Lemma subset_union_l (s1 s2 s3 : set E) :
    subset s1 s3 ->
    subset s2 s3 ->
    subset (union s1 s2) s3.
  Proof. firstorder idtac. Qed.

  Lemma subset_union_r (s1 s2 s3 : set E) :
    subset s1 s2 ->
    subset s1 s3 ->
    subset s1 (union s2 s3).
  Proof. firstorder idtac. Qed.

  Lemma subset_disjoint (s1 s2 s3 : set E) :
    subset s2 s3 ->
    disjoint s1 s3 ->
    disjoint s1 s2.
  Proof. firstorder idtac. Qed.

  Lemma subset_disjoint' (s1 s2 s3 : set E) :
    subset s1 s3 ->
    disjoint s2 s3 ->
    disjoint s1 s2.
  Proof. firstorder idtac. Qed.

  Lemma disjoint_not_in x (l : list E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}) :
    ~ In x l ->
    disjoint (singleton_set x) (of_list l).
  Proof.
    intros. symmetry. apply disjoint_singleton_r_iff; eauto.
  Qed.

  Lemma NoDup_disjoint (l1 l2 : list E)
        (eq_dec : forall a b : E, {a = b} + {a <> b}) :
    NoDup (l1 ++ l2) ->
    disjoint (of_list l1) (of_list l2).
  Proof.
    revert l2; induction l1; intros *;
      rewrite ?app_nil_l, <-?app_comm_cons;
      [ solve [firstorder idtac] | ].
    inversion 1; intros; subst.
    rewrite PropSet.of_list_cons.
    apply disjoint_union_l_iff; split; eauto.
    apply disjoint_not_in; eauto.
    rewrite in_app_iff in *. tauto.
  Qed.
End Sets.

Section Maps.
  Context {key value} {key_eqb}
          {map : map.map key value}
          {key_eq_dec :
             forall x y : key,
               BoolSpec (x = y) (x <> y) (key_eqb x y)}
          {map_ok : map.ok map}.

  Lemma only_differ_sym m1 m2 ks :
    map.only_differ m1 ks m2 ->
    map.only_differ m2 ks m1.
  Proof. firstorder congruence. Qed.

  Lemma only_differ_trans m1 m2 m3 ks1 ks2 :
    map.only_differ m2 ks1 m1 ->
    map.only_differ m3 ks2 m2 ->
    map.only_differ m3 (union ks1 ks2) m1.
  Proof. firstorder congruence. Qed.

  Global Instance Proper_only_differ :
    Proper (eq ==> sameset ==> eq ==> iff) map.only_differ.
  Proof. firstorder congruence. Qed.

  Lemma only_differ_put m k v :
    map.only_differ (map.put m k v) (singleton_set k) m.
  Proof.
    cbv [map.only_differ elem_of singleton_set].
    intro x; destr (key_eqb k x); subst;
      rewrite ?map.get_put_same, ?map.get_put_diff by congruence;
      tauto.
  Qed.

  Lemma putmany_of_list_zip_app_l m ks1 ks2 vs :
    map.putmany_of_list_zip (ks1 ++ ks2) vs m =
    Option.bind
      (map.putmany_of_list_zip
         ks1 (List.firstn (Datatypes.length ks1) vs) m)
      (map.putmany_of_list_zip
         ks2 (List.skipn (Datatypes.length ks1) vs)).
  Proof.
    revert m ks2 vs; induction ks1; destruct vs;
      rewrite ?app_nil_l, <-?app_comm_cons;
      try reflexivity; [ ].
    apply IHks1.
  Qed.

  Lemma putmany_of_list_zip_None ks vs m :
    map.putmany_of_list_zip ks vs m = None <->
    length ks <> length vs.
  Proof.
    revert m vs; induction ks; destruct vs;
      cbn [map.putmany_of_list_zip length];
      split; intros; try congruence;
        match goal with
        | H : _ |- _ => apply IHks in H; lia
        | _ => apply IHks; lia
        end.
  Qed.

  Lemma putmany_of_list_zip_combine m ks vs :
    length ks = length vs ->
    map.putmany_of_list_zip ks vs m =
    Some (map.putmany_of_list (combine ks vs) m).
  Proof.
    revert m vs; induction ks; destruct vs; intros;
      cbn [length] in *; try lia; try reflexivity; [ ].
    cbn [map.putmany_of_list_zip map.putmany_of_list combine].
    rewrite IHks; auto.
  Qed.

  Lemma put_put_comm k1 k2 v1 v2 m :
    k1 <> k2 ->
    map.put (map.put m k1 v1) k2 v2 =
    map.put (map.put m k2 v2) k1 v1.
  Proof.
    intros.
    apply map.map_ext; intro k;
      destruct (key_eq_dec k1 k);
      destruct (key_eq_dec k2 k);
      subst; try congruence;
        repeat first [ rewrite map.get_put_same
                     | rewrite map.get_put_diff by congruence
                     | reflexivity ].
  Qed.

  Lemma putmany_of_list_put_comm kv k v m :
    ~ In k (List.map fst kv) ->
    map.putmany_of_list kv (map.put m k v) =
    map.put (map.putmany_of_list kv m) k v.
  Proof.
    revert m k v; induction kv; intros;
      [ reflexivity | ].
    cbn [map.putmany_of_list]. break_match.
    cbn [List.map In fst] in *.
    match goal with H : _ |- _ =>
                    apply Decidable.not_or in H; destruct H end.
    rewrite <-IHkv by auto.
    rewrite put_put_comm by congruence.
    reflexivity.
  Qed.

  Lemma putmany_of_list_comm kv1 kv2 m :
    NoDup (List.map fst (kv1 ++ kv2)) ->
    map.putmany_of_list kv1 (map.putmany_of_list kv2 m) =
    map.putmany_of_list kv2 (map.putmany_of_list kv1 m).
  Proof.
    revert kv2 m; induction kv1; destruct kv2; intros;
      try reflexivity; [ ].
    rewrite map_app in *. cbn [List.map] in *.
    cbn [map.putmany_of_list]. break_match.
    repeat match goal with
           | H : NoDup (_ ++ _) |- _ =>
             apply NoDup_app_iff in H
           | H : _ /\ _ |- _ => destruct H
           | H : NoDup (_ :: _) |- _ => inversion H; subst; clear H
           end.
    cbn [In fst] in *.
    rewrite !putmany_of_list_put_comm by firstorder idtac.
    rewrite put_put_comm by firstorder idtac.
    rewrite IHkv1; [ reflexivity | ].
    rewrite map_app. apply NoDup_app_iff.
    firstorder idtac.
  Qed.

  Lemma putmany_of_list_zip_bind_comm ks1 ks2 vs1 vs2 m :
    NoDup (ks1 ++ ks2) ->
    Option.bind
      (map.putmany_of_list_zip ks1 vs1 m)
      (map.putmany_of_list_zip ks2 vs2) =
    Option.bind
      (map.putmany_of_list_zip ks2 vs2 m)
      (map.putmany_of_list_zip ks1 vs1).
  Proof.
    intros.
    destruct (Nat.eq_dec (length ks1) (length vs1));
      destruct (Nat.eq_dec (length ks2) (length vs2));
      try solve [
            cbv [Option.bind]; break_match; try reflexivity;
            repeat match goal with
                   | H : _ = Some _ |- _ =>
                     apply map.putmany_of_list_zip_sameLength in H
                   | H : _ = None |- _ =>
                     apply putmany_of_list_zip_None in H
                   | _ => apply putmany_of_list_zip_None
                   | _ => symmetry; apply putmany_of_list_zip_None
                   | _ => congruence
                   end ]; [ ].
    repeat match goal with
           | _ => rewrite putmany_of_list_zip_combine by auto
           | _ => progress cbn [Option.bind]
           end.
    rewrite <-putmany_of_list_comm; [ reflexivity | ].
    rewrite <-combine_app_samelength by congruence.
    rewrite map_fst_combine.
    rewrite firstn_all2 by (rewrite !app_length; lia).
    assumption.
  Qed.
End Maps.

(* These lemmas should be moved to bedrock2, not coqutil *)
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
           | _ => progress (intros; subst)
           | H : _ /\ _ |- _ => destruct H
           | H : exists _, _ |- _ => destruct H
           | H : _ |- _ => apply map.split_empty in H
           | _ => rewrite map.split_empty
           | _ => exists map.empty
           | _ => tauto
           | _ => split
           end.
  Qed.
End Separation.

(* These lemmas should be moved to bedrock2, not coqutil *)
Section WeakestPrecondition.
  Context {p : Semantics.parameters} {p_ok : Semantics.parameters_ok p}.

  Lemma expr_untouched mem1 mem2 l1 l2 vars v P :
    map.only_differ l2 vars l1 ->
    ~ vars v ->
    expr mem1 l1 (expr.var v) P <->
    expr mem2 l2 (expr.var v) P.
  Proof.
    cbv [map.only_differ
           elem_of
           expr
           expr_body
           get].
    let H := fresh in
    intro H; specialize (H v).
    split; intros;
      repeat match goal with
             | H : exists _, _ |- _ => destruct H
             | H : _ \/ _ |- _ => destruct H
             | H : _ /\ _ |- _ => destruct H
             | H : map.get _ _ = map.get _ _ |- _ =>
               rewrite H in *
             | |- exists _, _ => eexists
             | |- _ /\ _ => split
             | _ => eassumption
             | _ => tauto
             end.
  Qed.

  Section ListMap.
    Context {A B} (f : A -> (B -> Prop) -> Prop)
            (f_ext :
               forall a H1 H2,
                 (forall b, H1 b <-> H2 b) ->
                 f a H1 <-> f a H2).
    Lemma list_map_app_iff xs ys post :
      list_map f (xs ++ ys) post <->
      list_map
        f xs (fun xx =>
                list_map
                  f ys (fun yy => post (xx ++ yy))).
    Proof.
      revert ys post; induction xs;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [list_map
                                      list_map_body] in *
               | _ => rewrite app_nil_l
               | _ => rewrite <-app_comm_cons
               | |- f _ _ <-> f _ _ => apply f_ext
               | _ => reflexivity
               end.
      apply IHxs.
    Qed.

    Lemma list_map_cons_iff x xs post :
      list_map f (x :: xs) post <->
      f x (fun y => list_map f xs (fun ys => post (y :: ys))).
    Proof. reflexivity. Qed.
  End ListMap.

  Section Dexpr.
    Lemma dexpr_equiv m l n x1 x2 :
      dexpr m l (expr.var n) x1 ->
      dexpr m l (expr.var n) x2 ->
      x1 = x2.
    Proof.
      destruct 1; destruct 1; destruct_head'_and; congruence.
    Qed.

    Lemma dexpr_put_same m l n x :
      dexpr m (map.put l n x) (expr.var n) x.
    Proof. eexists; rewrite map.get_put_same; tauto. Qed.

    Lemma dexpr_put_diff m l n1 n2 x y :
      n1 <> n2 ->
      dexpr m l (expr.var n1) x ->
      dexpr m (map.put l n2 y) (expr.var n1) x.
    Proof.
      destruct 2; intros; eexists; rewrite map.get_put_diff; eauto.
    Qed.
  End Dexpr.

  (* TODO: some of these may be unused *)
  Section Dexprs.
    Local Ltac peel_expr :=
      progress (
          repeat
            progress match goal with
                     | H : expr ?m ?l ?e _ |- _ =>
                       match goal with
                       | |- expr m l e _ => idtac
                       | _ =>
                         apply expr_sound with (mc:=MetricLogging.EmptyMetricLog) in H;
                         destruct H as [? [_ [_ H] ] ]
                       end
                     end).

    Local Ltac propers_step :=
      match goal with
      | H : get ?l ?x _
        |- get ?l ?x _ =>
        eapply Proper_get
      | H : expr ?m ?l ?e _
        |- expr ?m ?l ?e _ =>
        eapply Proper_expr
      | H : list_map ?f ?xs _
        |- list_map ?f ?xs _ =>
        eapply Proper_list_map
      end; [ repeat intro .. | eassumption ]; cbv beta in *.

    Local Ltac propers :=
      propers_step;
      match goal with
      | _ => solve [propers]
      | H : _ |- _ => apply H; solve [eauto]
      | _ => congruence
      end.

    Lemma dexprs_cons_iff m l e es v vs :
      dexprs m l (e :: es) (v :: vs) <->
      (expr m l e (eq v)
       /\ dexprs m l es vs).
    Proof.
      cbv [dexprs].
      revert es v vs; induction es; split; intros;
        repeat match goal with
               | _ => progress cbn [list_map
                                      list_map_body] in *
               | _ => progress cbv beta in *
               | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
               | |- _ /\ _ => split
               | _ => progress destruct_head'_and
               | _ => solve [propers]
               | _ => reflexivity
               | _ => peel_expr
               end.
      eapply IHes with (vs := tl vs).
      propers_step. peel_expr.
      destruct vs; cbn [tl]; propers.
    Qed.

    Lemma dexprs_cons_nil m l e es :
      dexprs m l (e :: es) [] -> False.
    Proof.
      cbv [dexprs].
      induction es; intros;
        repeat match goal with
               | _ => progress cbn [list_map
                                      list_map_body] in *
               | _ => congruence
               | _ => solve [propers]
               | _ => apply IHes
               | _ => peel_expr
               end.
      propers_step. peel_expr. propers.
    Qed.

    Lemma dexprs_app_l m l es1 :
      forall es2 vs,
        dexprs m l (es1 ++ es2) vs ->
        (dexprs m l es1 (firstn (length es1) vs)) /\
        (dexprs m l es2 (skipn (length es1) vs)).
    Proof.
      induction es1; intros.
      { cbn [Datatypes.length skipn firstn]; rewrite app_nil_l in *.
        split; eauto; reflexivity. }
      { destruct vs; rewrite <-app_comm_cons in *;
          [ match goal with H : _ |- _ => apply dexprs_cons_nil in H; tauto end | ].
        cbn [Datatypes.length skipn firstn].
        rewrite !dexprs_cons_iff in *.
        destruct_head'_and.
        repeat split; try eapply IHes1; eauto. }
    Qed.

    Lemma dexprs_length m l :
      forall vs es,
        dexprs m l es vs ->
        length es = length vs.
    Proof.
      induction vs; destruct es; intros;
        repeat match goal with
               | _ => progress cbn [Datatypes.length]
               | _ => progress destruct_head'_and
               | H : _ |- _ => apply dexprs_cons_nil in H; tauto
               | H : _ |- _ => apply dexprs_cons_iff in H
               | _ => reflexivity
               | _ => congruence
               end.
      rewrite IHvs; auto.
    Qed.
  End Dexprs.
End WeakestPrecondition.

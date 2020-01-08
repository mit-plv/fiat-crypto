Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.PropSet.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Translation.Expr.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ListUtil.

(* for [eauto with lia] *)
Require Import Crypto.BoundsPipeline.

Import API.Compilers.
Import Types.Notations Types.Types.

(* General-purpose lemmas about maps that should be later moved to coqutil *)
(* TODO: move *)
Section Maps.
  Lemma only_differ_trans {key value} {map: map.map key value}
        m1 m2 m3 ks1 ks2 :
    map.only_differ m2 ks1 m1 ->
    map.only_differ m3 ks2 m2 ->
    map.only_differ m3 (union ks1 ks2) m1.
  Admitted.

  (* TODO: move *)
  Lemma only_differ_sameset {key value} {map: map.map key value}
        m1 m2 ks1 ks2 :
    sameset ks1 ks2 ->
    map.only_differ m2 ks1 m1 ->
    map.only_differ m2 ks2 m1.
  Admitted.

  Lemma sameset_iff {E} (s1 s2 : set E) :
    sameset s1 s2 <-> (forall e, s1 e <-> s2 e).
  Proof.
    cbv [sameset subset elem_of]. split.
    { destruct 1; split; eauto. }
    { intro Hiff; split; apply Hiff; eauto. }
  Qed.
End Maps.

(* Reasoning about various collections of variable names *)
Section Varnames.
  Context {p : Types.parameters} {ok : @ok p}.
  Existing Instance Types.rep.Z.
  Existing Instance Types.rep.listZ_local. (* local list representation *)

  (* TODO: are these all needed? *)
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.
  Local Instance mem_ok : map.ok Semantics.mem
    := Semantics.mem_ok.
  Local Instance varname_eqb_spec x y : BoolSpec _ _ _
    := Semantics.varname_eqb_spec x y.

  Fixpoint varname_set {t} : base_ltype t -> set varname :=
    match t with
    | base.type.prod a b =>
      fun x => union (varname_set (fst x)) (varname_set (snd x))
    | base.type.list (base.type.type_base base.type.Z) =>
      PropSet.of_list
    | _ => fun x => singleton_set x
    end.

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

  Definition varname_not_in_context {var1}
             (v : varname)
             (x : {t : API.type & (var1 t * API.interp_type t * ltype t)%type})
    : Prop :=
    match x with
    | existT (type.base b) (w, x, y) =>
      ~ (varname_set y) v
    | existT (type.arrow _ _) _ => False (* no functions allowed *)
    end.

  Lemma equivalent_not_varname_set {t}
        locals1 locals2 vset (varnames : base_ltype t) x :
    map.only_differ locals1 vset locals2 ->
    (forall v : varname, vset v -> ~ varname_set varnames v) ->
    forall mem,
      equivalent x (rtype_of_ltype varnames) locals1 mem ->
      equivalent x (rtype_of_ltype varnames) locals2 mem.
  Proof.
    (* TODO : clean up this proof *)
    intros Hdiffer Hexcl.
    induction t;
      cbn [fst snd rtype_of_ltype varname_set
               equivalent rep.Z rep.listZ_local rep.equiv]; intros;
        BreakMatch.break_match; DestructHead.destruct_head'_and; try tauto.
    { (* base case *)
      cbv [singleton_set
             elem_of
             varname_set
             WeakestPrecondition.expr
             WeakestPrecondition.expr_body
             WeakestPrecondition.get ] in *.
      specialize (Hexcl varnames); intros;
        destruct (Hdiffer varnames) as [? | Heq];
        [ tauto | rewrite <-Heq; eauto ]. }
    { (* prod case *)
      cbn [varname_set] in Hexcl; cbv [union elem_of] in Hexcl.
      eapply Proper_sep_impl1;
        cbv [Lift1Prop.impl1]; intros;
          [ | | eassumption ];
          [ apply IHt1 | apply IHt2]; auto;
            let x := fresh in
            let y := fresh in
            intros x y; specialize (Hexcl x y); tauto. }
    { (* list case *)
      split; [ assumption | ].
      cbn [varname_set] in Hexcl; cbv [union of_list] in Hexcl.
      cbn [Language.Compilers.base.interp Compilers.base_interp base_rtype] in *. (* simplify types *)
      cbn [rep.rtype rep.Z] in *.
      eapply Forall2_forall_iff with (d1:=0%Z) (d2:=expr.literal 0); auto.
      match goal with H : _ |- _ =>
                      intros i Hi;
                        rewrite Forall2_forall_iff
                          with (d1:=0%Z) (d2:=expr.literal 0) in H by auto;
                        specialize (H i Hi); revert H
      end.
      apply nth_default_preserves_properties_length_dep; try lia.
      cbn [equivalent base_ltype rep.Z rep.listZ_local rep.ltype rep.equiv
                      rep.rtype_of_ltype rtype_of_ltype] in *.
      intros *. rewrite in_map_iff. intros; cleanup. subst.
      apply IHt; intros; auto.
      match goal with H : vset _ |- _ => apply Hexcl in H end.
      congruence. }
  Qed.

  Lemma equivalent_not_in_context {var1} locals1 locals2 vset x :
    map.only_differ locals1 vset locals2 ->
    (forall v, vset v -> varname_not_in_context v x) ->
    equiv3 (var1:=var1) locals1 x ->
    equiv3 locals2 x.
  Proof.
    intros; cbv [equiv3 varname_not_in_context locally_equivalent] in *.
    destruct x as [x [ [? ?] ?] ]; destruct x; [ | tauto ].
    eauto using equivalent_not_varname_set.
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
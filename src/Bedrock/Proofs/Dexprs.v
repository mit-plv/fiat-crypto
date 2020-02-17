Require Import Coq.Lists.List.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import coqutil.Word.Interface.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Util.ListUtil.
Import ListNotations.

(* Proofs about [WeakestPrecondition.dexprs] *)
(* TODO: add to bedrock2? *)
(* TODO: some of these may be unused *)
Section Dexprs.
  Context {p : Semantics.parameters} {ok : @Semantics.parameters_ok p}.

  Lemma dexprs_cons_iff m l :
    forall e es v vs,
      WeakestPrecondition.dexprs m l (e :: es) (v :: vs) <->
      (WeakestPrecondition.expr m l e (eq v)
       /\ WeakestPrecondition.dexprs m l es vs).
  Proof.
    cbv [WeakestPrecondition.dexprs].
    induction es; split; intros;
      repeat match goal with
             | _ => progress cbn [WeakestPrecondition.list_map
                                    WeakestPrecondition.list_map_body] in *
             | _ => progress cbv beta in *
             | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
             | |- _ /\ _ => split
             | _ => progress destruct_head'_and
             | _ => reflexivity
             | _ => solve [propers]
             | _ => peel_expr
             end.
    eapply IHes with (vs := tl vs).
    propers_step. peel_expr.
    destruct vs; cbn [tl]; propers.
  Qed.

  Lemma dexprs_cons_nil m l e es :
    WeakestPrecondition.dexprs m l (e :: es) [] -> False.
  Proof.
    cbv [WeakestPrecondition.dexprs].
    induction es; intros;
      repeat match goal with
             | _ => progress cbn [WeakestPrecondition.list_map
                                    WeakestPrecondition.list_map_body] in *
             | _ => congruence
             | _ => solve [propers]
             | _ => apply IHes
             | _ => peel_expr
             end.
    propers_step. peel_expr. propers.
  Qed.

  Lemma dexprs_app_l m l es1 :
    forall es2 vs,
      WeakestPrecondition.dexprs m l (es1 ++ es2) vs ->
      (WeakestPrecondition.dexprs m l es1 (firstn (length es1) vs)) /\
      (WeakestPrecondition.dexprs m l es2 (skipn (length es1) vs)).
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
      WeakestPrecondition.dexprs m l es vs ->
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

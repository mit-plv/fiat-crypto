Require Import Coq.Lists.List Coq.Lists.SetoidList. Import ListNotations.
Require Import Crypto.Util.ListUtil.
Require Import Algebra. Import Monoid ScalarMult.
Require Import VerdiTactics.
Require Import Crypto.Util.Option.

Section AddChainExp.
  Function add_chain (is:list (nat*nat)) : list nat :=
    match is with
    | nil => nil
    | (i,j)::is' =>
      let chain' := add_chain is' in
      nth_default 1 chain' i + nth_default 1 chain' j::chain'
    end.

Example wikipedia_addition_chain : add_chain (rev [
(0, 0); (* 2 = 1 + 1 *) (* the indices say how far back the chain to look *)
(0, 1); (* 3 = 2 + 1 *)
(0, 0); (* 6 = 3 + 3 *)
(0, 0); (* 12 = 6 + 6 *)
(0, 0); (* 24 = 12 + 12 *)
(0, 2); (* 30 = 24 + 6 *)
(0, 6)] (* 31 = 30 + 1 *)
) = [31; 30; 24; 12; 6; 3; 2]. reflexivity. Qed.

  Context {G eq op id} {monoid:@Algebra.monoid G eq op id}.
  Local Infix "=" := eq : type_scope.

  Function add_chain_exp (is : list (nat*nat)) (x : G) : list G :=
    match is with
    | nil => nil
    | (i,j)::is' =>
      let chain' := add_chain_exp is' x in
      op (nth_default x chain' i) (nth_default x chain' j) ::chain'
    end.

  Fixpoint scalarmult n (x : G) : G := match n with
    | O    => id
    | S n' => op x (scalarmult n' x)
    end.

  Lemma add_chain_exp_step : forall i j is x,
    (forall n, nth_default x (add_chain_exp is x) n = scalarmult (nth_default 1 (add_chain is) n) x) ->
    (eqlistA eq)
    (add_chain_exp ((i,j) :: is) x)
      (op (scalarmult (nth_default 1 (add_chain is) i) x)
         (scalarmult (nth_default 1 (add_chain is) j) x) :: add_chain_exp is x).
  Proof.
    intros.
    unfold add_chain_exp; fold add_chain_exp.
    apply eqlistA_cons; [ | reflexivity].
    f_equiv; auto.
  Qed.

  Lemma scalarmult_same : forall c x y, eq x y -> eq (scalarmult c x) (scalarmult c y).
  Proof.
    induction c; intros.
    + reflexivity.
    + simpl. f_equiv; auto.
  Qed.

  Lemma scalarmult_pow_add : forall a b x, scalarmult (a + b) x = op (scalarmult a x) (scalarmult b x).
  Proof.
    intros; eapply scalarmult_add_l.
    Grab Existential Variables.
    2:eauto.
    econstructor; try reflexivity.
    repeat intro; subst.
    auto using scalarmult_same.
  Qed.

  Lemma add_chain_exp_spec : forall is x,
    (forall n, nth_default x (add_chain_exp is x) n = scalarmult (nth_default 1 (add_chain is) n) x).
  Proof.
    induction is; intros.
    + simpl; rewrite !nth_default_nil. cbv.
      symmetry; apply right_identity.
    + destruct a.
      rewrite add_chain_exp_step by auto.
      unfold add_chain; fold add_chain.
      destruct n.
      - rewrite !nth_default_cons, scalarmult_pow_add. reflexivity.
      - rewrite !nth_default_cons_S; auto.
  Qed.

  Lemma add_chain_exp_answer : forall is x n, Logic.eq (head (add_chain is)) (Some n) ->
    option_eq eq (Some (scalarmult n x)) (head (add_chain_exp is x)).
  Proof.
    intros.
    change head with (fun {T} (xs : list T) => nth_error xs 0) in *.
    cbv beta in *.
    cbv [option_eq].
    destruct is; [ discriminate | ].
    destruct p.
    simpl in *.
    injection H; clear H; intro H.
    subst n.
    rewrite !add_chain_exp_spec.
    apply scalarmult_pow_add.
  Qed.

End AddChainExp.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Algebra Crypto.Algebra.Monoid.

Module Import ModuloCoq8485.
  Import NPeano Nat.
  Infix "mod" := modulo.
End ModuloCoq8485.

Section ScalarMultProperties.
  Context {G eq add zero} `{monoidG:@monoid G eq add zero}.
  Context {mul:nat->G->G}.
  Local Infix "=" := eq : type_scope. Local Infix "=" := eq.
  Local Infix "+" := add. Local Infix "*" := mul.
  Class is_scalarmult :=
    {
      scalarmult_0_l : forall P, 0 * P = zero;
      scalarmult_S_l : forall n P, S n * P = P + n * P;

      scalarmult_Proper : Proper (Logic.eq==>eq==>eq) mul
    }.
  Global Existing Instance scalarmult_Proper.
  Context `{mul_is_scalarmult:is_scalarmult}.

  Fixpoint scalarmult_ref (n:nat) (P:G) {struct n} :=
    match n with
    | O => zero
    | S n' => add P (scalarmult_ref n' P)
    end.

  Global Instance Proper_scalarmult_ref : Proper (Logic.eq==>eq==>eq) scalarmult_ref.
  Proof.
    repeat intro; subst.
    match goal with [n:nat |- _ ] => induction n; simpl @scalarmult_ref; [reflexivity|] end.
    repeat match goal with [H:_ |- _ ] => rewrite H end; reflexivity.
  Qed.

  Lemma scalarmult_ext : forall n P, mul n P = scalarmult_ref n P.
    induction n; simpl @scalarmult_ref; intros; rewrite <-?IHn; (apply scalarmult_0_l || apply scalarmult_S_l).
  Qed.

  Lemma scalarmult_1_l : forall P, 1*P = P.
  Proof. intros. rewrite scalarmult_S_l, scalarmult_0_l, right_identity; reflexivity. Qed.

  Lemma scalarmult_add_l : forall (n m:nat) (P:G), ((n + m)%nat * P = n * P + m * P).
  Proof.
    induction n; intros;
      rewrite ?scalarmult_0_l, ?scalarmult_S_l, ?plus_Sn_m, ?plus_O_n, ?scalarmult_S_l, ?left_identity, <-?associative, <-?IHn; reflexivity.
  Qed.

  Lemma scalarmult_zero_r : forall m, m * zero = zero.
  Proof. induction m; rewrite ?scalarmult_S_l, ?scalarmult_0_l, ?left_identity, ?IHm; try reflexivity. Qed.

  Lemma scalarmult_assoc : forall (n m : nat) P, n * (m * P) = (m * n)%nat * P.
  Proof.
    induction n; intros.
    { rewrite <-mult_n_O, !scalarmult_0_l. reflexivity. }
    { rewrite scalarmult_S_l, <-mult_n_Sm, <-Plus.plus_comm, scalarmult_add_l.
      rewrite IHn. reflexivity. }
  Qed.

  Lemma scalarmult_times_order : forall l B, l*B = zero -> forall n, (l * n) * B = zero.
  Proof. intros ? ? Hl ?. rewrite <-scalarmult_assoc, Hl, scalarmult_zero_r. reflexivity. Qed.

  Lemma scalarmult_mod_order : forall l B, l <> 0%nat -> l*B = zero -> forall n, n mod l * B = n * B.
  Proof.
    intros ? ? Hnz Hmod ?.
    rewrite (NPeano.Nat.div_mod n l Hnz) at 2.
    rewrite scalarmult_add_l, scalarmult_times_order, left_identity by auto. reflexivity.
  Qed.
End ScalarMultProperties.

Section ScalarMultHomomorphism.
  Context {G EQ ADD ZERO} {monoidG:@monoid G EQ ADD ZERO}.
  Context {H eq add zero} {monoidH:@monoid H eq add zero}.
  Local Infix "=" := eq : type_scope. Local Infix "=" := eq : eq_scope.
  Context {MUL} {MUL_is_scalarmult:@is_scalarmult G EQ ADD ZERO MUL }.
  Context {mul} {mul_is_scalarmult:@is_scalarmult H eq add zero mul }.
  Context {phi} {homom:@Monoid.is_homomorphism G EQ ADD H eq add phi}.
  Context (phi_ZERO:phi ZERO = zero).

  Lemma homomorphism_scalarmult : forall n P, phi (MUL n P) = mul n (phi P).
  Proof.
    setoid_rewrite scalarmult_ext.
    induction n; intros; simpl; rewrite ?Monoid.homomorphism, ?IHn; easy.
  Qed.
End ScalarMultHomomorphism.

Global Instance scalarmult_ref_is_scalarmult {G eq add zero} `{@monoid G eq add zero}
  : @is_scalarmult G eq add zero (@scalarmult_ref G add zero).
Proof. split; try exact _; intros; reflexivity. Qed.
Require Import PArith BinInt ZArith.
From Coq Require Import Lia Zmod.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.


Section __.
  Context {m : Z}.

  Lemma solve_F_equality_via_Z lhs' rhs' (lhs rhs : Zmod m)
    : Zmod.unsigned lhs = lhs' mod m ->
      Zmod.unsigned rhs = rhs' mod m ->
      lhs' = rhs' ->
      lhs = rhs.
  Proof.
    intros.
    rewrite <- (Zmod.of_Z_unsigned lhs).
    rewrite <- (Zmod.of_Z_unsigned rhs).
    intuition congruence.
  Qed.


  (*TODO: add remaining homomorphisms.
    To support additional operations, prove a lemma like the ones below
    and then add it to the `F_convert_to_Z` tactic.
   *)

  Lemma F_mul_to_Z a a' b b'
    : Zmod.unsigned a = a' mod m ->
      Zmod.unsigned b = b' mod m ->
      @Zmod.unsigned m (a * b) = (a' * b') mod m.
  Proof.
    intros H H0.
    rewrite Zmod.unsigned_mul.
    rewrite H, H0.
    rewrite <- PullPush.Z.mul_mod_l.
    rewrite <- PullPush.Z.mul_mod_r.
    congruence.
  Qed.

  Lemma F_add_to_Z a a' b b'
    : Zmod.unsigned a = a' mod m ->
      Zmod.unsigned b = b' mod m ->
      @Zmod.unsigned m (a + b) = (a' + b') mod m.
  Proof.
    intros H H0.
    rewrite Zmod.unsigned_add.
    rewrite H, H0.
    rewrite <- PullPush.Z.add_mod_l.
    rewrite <- PullPush.Z.add_mod_r.
    congruence.
  Qed.


  Lemma F_pow_to_Z a a' c
    : Zmod.unsigned a = a' mod m ->
      0 <= c ->
      @Zmod.unsigned m (a ^ c) = (a' ^ c) mod m.
  Proof.
    intros H Hc.
    rewrite Zmod.unsigned_pow_nonneg_r by assumption.
    rewrite H.
    rewrite <- PullPush.Z.pow_mod_full.
    congruence.
  Qed.

End __.


Ltac F_convert_to_Z :=
  solve [repeat
           let e := lazymatch goal with |- Zmod.unsigned ?x = _ => x end in
           first [ simple eapply F_mul_to_Z
                 | simple eapply F_add_to_Z
                 | simple eapply Zmod.unsigned_1
                 | simple eapply F_pow_to_Z; [ | lia ]
                 | simple eapply Zmod.unsigned_of_Z
                 (* must be last *)
                 | symmetry; simple eapply Zmod.mod_unsigned ]].

(*TODO: doesn't prepare hypotheses.
  To support working with hypotheses will require a variation on `solve_F_equality_via_Z`
  that goes in the other direction.
  Since Z->F isn't injective, it will require some thinking.
 *)
Ltac F_zify :=
  intros;
  lazymatch goal with
  | [|- ?lhs = ?rhs] =>
      simple eapply solve_F_equality_via_Z;
      [F_convert_to_Z | F_convert_to_Z | ]
  end.

Ltac F_lia := F_zify; (lia || fail "F_lia failed; check that all necessary homomorphisms have been added").



Section Example.
  Context {m : Z}.

  Goal forall (x : Zmod m), (x + Zmod.of_Z  _ 4 * x)%Zmod = ( x * Zmod.of_Z  _ 2 + Zmod.of_Z  _ 2 * x + 1 * 1 * x)%Zmod.
  Proof.
    F_lia.
  Qed.
End Example.

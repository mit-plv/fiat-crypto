Require Import ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Local Open Scope Z_scope.


Section __.
  Context {M_pos : positive}.

  Lemma solve_F_equality_via_Z lhs' rhs' (lhs rhs : F M_pos)
    : F.to_Z lhs = lhs' mod Z.pos M_pos ->
      F.to_Z rhs = rhs' mod Z.pos M_pos ->
      lhs' = rhs' ->
      lhs = rhs.
  Proof.
    intros.
    rewrite <- (F.of_Z_to_Z lhs).
    rewrite <- (F.of_Z_to_Z rhs).
    intuition congruence.
  Qed.


  (*TODO: add remaining homomorphisms.
    To support additional operations, prove a lemma like the ones below
    and then add it to the `F_convert_to_Z` tactic.
   *)

  Lemma F_mul_to_Z a a' b b'
    : F.to_Z a = a' mod Z.pos M_pos ->
      F.to_Z b = b' mod Z.pos M_pos ->
      @F.to_Z M_pos (a * b) = (a' * b') mod Z.pos M_pos.
  Proof.
    intros H H0.
    rewrite F.to_Z_mul.
    rewrite H, H0.
    rewrite <- PullPush.Z.mul_mod_l.
    rewrite <- PullPush.Z.mul_mod_r.
    congruence.
  Qed.

  Lemma F_add_to_Z a a' b b'
    : F.to_Z a = a' mod Z.pos M_pos ->
      F.to_Z b = b' mod Z.pos M_pos ->
      @F.to_Z M_pos (a + b) = (a' + b') mod Z.pos M_pos.
  Proof.
    intros H H0.
    rewrite F.to_Z_add.
    rewrite H, H0.
    rewrite <- PullPush.Z.add_mod_l.
    rewrite <- PullPush.Z.add_mod_r.
    congruence.
  Qed.

  
  Lemma F_pow_to_Z a a' c
    : F.to_Z a = a' mod Z.pos M_pos ->
      @F.to_Z M_pos (a ^ c) = (a' ^ c) mod Z.pos M_pos.
  Proof.
    intros H.
    rewrite F.to_Z_pow.
    rewrite H.
    rewrite <- PullPush.Z.pow_mod_full.
    congruence.
  Qed.

  Lemma F_var_to_Z (x : F M_pos) : F.to_Z x = proj1_sig x mod Z.pos M_pos.
  Proof.
    destruct x; simpl; assumption.
  Qed.

  Lemma F_one_to_Z : @F.to_Z M_pos 1 = 1 mod Z.pos M_pos.
  Proof.
    reflexivity.
  Qed.


  Lemma F_const_to_Z c : F.to_Z (F.of_Z M_pos c) = c mod Z.pos M_pos.
  Proof.
    reflexivity.
  Qed.

End __.


Ltac F_convert_to_Z :=
  solve [repeat
           let e := lazymatch goal with |- F.to_Z ?x = _ => x end in
           first [ simple eapply F_mul_to_Z
                 | simple eapply F_add_to_Z
                 | simple eapply F_one_to_Z
                 | simple eapply F_pow_to_Z
                 | simple eapply F_const_to_Z
                 (* must be last *)
                 | simple eapply F_var_to_Z]].

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
  Context {M_pos : positive}.
  
  Goal forall (x : F M_pos), (x + F.of_Z  _ 4 * x)%F = ( x * F.of_Z  _ 2 + F.of_Z  _ 2 * x + 1 * 1 * x)%F.
  Proof.
    F_lia.
  Qed.
End Example.

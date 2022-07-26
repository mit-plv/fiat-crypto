Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.ZArith.Znumtheory Coq.ZArith.Zpow_facts.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma mod_r_distr_if (b : bool) x y z : z mod (if b then x else y) = if b then z mod x else z mod y.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite mod_r_distr_if : push_Zmod.
#[global]
  Hint Rewrite <- mod_r_distr_if : pull_Zmod.

  Lemma mod_l_distr_if (b : bool) x y z : (if b then x else y) mod z = if b then x mod z else y mod z.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite mod_l_distr_if : push_Zmod.
#[global]
  Hint Rewrite <- mod_l_distr_if : pull_Zmod.

  (** Version without the [n <> 0] assumption *)
  Lemma mul_mod_full a b n : (a * b) mod n = ((a mod n) * (b mod n)) mod n.
  Proof. auto using Zmult_mod. Qed.
#[global]
  Hint Rewrite <- mul_mod_full : pull_Zmod.
#[global]
  Hint Resolve mul_mod_full : zarith.

  Lemma mul_mod_l a b n : (a * b) mod n = ((a mod n) * b) mod n.
  Proof.
    intros; rewrite (mul_mod_full a b), (mul_mod_full (a mod n) b).
    autorewrite with zsimplify; reflexivity.
  Qed.
#[global]
  Hint Rewrite <- mul_mod_l : pull_Zmod.
#[global]
  Hint Resolve mul_mod_l : zarith.

  Lemma mul_mod_r a b n : (a * b) mod n = (a * (b mod n)) mod n.
  Proof.
    intros; rewrite (mul_mod_full a b), (mul_mod_full a (b mod n)).
    autorewrite with zsimplify; reflexivity.
  Qed.
#[global]
  Hint Rewrite <- mul_mod_r : pull_Zmod.
#[global]
  Hint Resolve mul_mod_r : zarith.

  Lemma add_mod_full a b n : (a + b) mod n = ((a mod n) + (b mod n)) mod n.
  Proof. auto using Zplus_mod. Qed.
#[global]
  Hint Rewrite <- add_mod_full : pull_Zmod.
#[global]
  Hint Resolve add_mod_full : zarith.

  Lemma add_mod_l a b n : (a + b) mod n = ((a mod n) + b) mod n.
  Proof.
    intros; rewrite (add_mod_full a b), (add_mod_full (a mod n) b).
    autorewrite with zsimplify; reflexivity.
  Qed.
#[global]
  Hint Rewrite <- add_mod_l : pull_Zmod.
#[global]
  Hint Resolve add_mod_l : zarith.

  Lemma add_mod_r a b n : (a + b) mod n = (a + (b mod n)) mod n.
  Proof.
    intros; rewrite (add_mod_full a b), (add_mod_full a (b mod n)).
    autorewrite with zsimplify; reflexivity.
  Qed.
#[global]
  Hint Rewrite <- add_mod_r : pull_Zmod.
#[global]
  Hint Resolve add_mod_r : zarith.

  Lemma opp_mod_mod a n : (-a) mod n = (-(a mod n)) mod n.
  Proof.
    intros; destruct (Z_zerop (a mod n)) as [H'|H']; [ rewrite H' | ];
      [ | rewrite !Z_mod_nz_opp_full ];
      autorewrite with zsimplify; lia.
  Qed.
#[global]
  Hint Rewrite <- opp_mod_mod : pull_Zmod.
#[global]
  Hint Resolve opp_mod_mod : zarith.

  (** Give alternate names for the next three lemmas, for consistency *)
  Lemma sub_mod_full a b n : (a - b) mod n = ((a mod n) - (b mod n)) mod n.
  Proof. auto using Zminus_mod. Qed.
#[global]
  Hint Rewrite <- sub_mod_full : pull_Zmod.
#[global]
  Hint Resolve sub_mod_full : zarith.

  Lemma sub_mod_l a b n : (a - b) mod n = ((a mod n) - b) mod n.
  Proof. auto using Zminus_mod_idemp_l. Qed.
#[global]
  Hint Rewrite <- sub_mod_l : pull_Zmod.
#[global]
  Hint Resolve sub_mod_l : zarith.

  Lemma sub_mod_r a b n : (a - b) mod n = (a - (b mod n)) mod n.
  Proof. auto using Zminus_mod_idemp_r. Qed.
#[global]
  Hint Rewrite <- sub_mod_r : pull_Zmod.
#[global]
  Hint Resolve sub_mod_r : zarith.

  Lemma lnot_mod_mod v m : (Z.lnot (v mod m) mod m) = (Z.lnot v) mod m.
  Proof.
    cbv [Z.lnot]; etransitivity; rewrite <- !Z.sub_1_r, Z.sub_mod_full, Z.opp_mod_mod, ?Zmod_mod; reflexivity.
  Qed.
#[global]
  Hint Rewrite lnot_mod_mod : pull_Zmod.
#[global]
  Hint Resolve lnot_mod_mod : zarith.

  Lemma mod_pow_full p q n : (p^q) mod n = ((p mod n)^q) mod n.
  Proof.
    destruct (Z_dec' n 0) as [ [H|H] | H]; subst;
      [
      | apply Zpower_mod; assumption
      | rewrite !Zmod_0_r; reflexivity ].
    { revert H.
      rewrite <- (Z.opp_involutive (p^q)),
      <- (Z.opp_involutive ((p mod n)^q)),
      <- (Z.opp_involutive p),
      <- (Z.opp_involutive n).
      generalize (-n); clear n; intros n H.
      rewrite !Zmod_opp_opp.
      rewrite !Z.opp_involutive.
      apply f_equal.
      destruct (Z.Even_or_Odd q).
      { rewrite !Z.pow_opp_even by (assumption || lia).
        destruct (Z.eq_dec (p^q mod n) 0) as [H'|H'], (Z.eq_dec ((-p mod n)^q mod n) 0) as [H''|H''];
          repeat first [ rewrite Z_mod_zero_opp_full by assumption
                       | rewrite Z_mod_nz_opp_full by assumption
                       | reflexivity
                       | rewrite <- Zpower_mod, Z.pow_opp_even in H'' by (assumption || lia); lia
                       | rewrite <- Zpower_mod, Z.pow_opp_even in H'' |- * by (assumption || lia); lia ]. }
      { rewrite Z.pow_opp_odd, !Z.opp_involutive, <- Zpower_mod, Z.pow_opp_odd, ?Z.opp_involutive by (assumption || lia).
        reflexivity. } }
  Qed.
#[global]
  Hint Rewrite <- mod_pow_full : pull_Zmod.
#[global]
  Hint Resolve mod_pow_full : zarith.
  Notation pow_mod_full := mod_pow_full.

  Definition NoZMod (x : Z) := True.
  Ltac NoZMod :=
    lazymatch goal with
    | [ |- NoZMod (?x mod ?y) ] => fail 0 "Goal has" x "mod" y
    | [ |- NoZMod _ ] => constructor
    end.

  Lemma mul_mod_push a b n : NoZMod a -> NoZMod b -> (a * b) mod n = ((a mod n) * (b mod n)) mod n.
  Proof. intros; apply mul_mod_full; assumption. Qed.
#[global]
  Hint Rewrite mul_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_push a b n : NoZMod a -> NoZMod b -> (a + b) mod n = ((a mod n) + (b mod n)) mod n.
  Proof. intros; apply add_mod_full; assumption. Qed.
#[global]
  Hint Rewrite add_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma mul_mod_l_push a b n : NoZMod a -> (a * b) mod n = ((a mod n) * b) mod n.
  Proof. intros; apply mul_mod_l; assumption. Qed.
#[global]
  Hint Rewrite mul_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma mul_mod_r_push a b n : NoZMod b -> (a * b) mod n = (a * (b mod n)) mod n.
  Proof. intros; apply mul_mod_r; assumption. Qed.
#[global]
  Hint Rewrite mul_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_l_push a b n : NoZMod a -> (a + b) mod n = ((a mod n) + b) mod n.
  Proof. intros; apply add_mod_l; assumption. Qed.
#[global]
  Hint Rewrite add_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_r_push a b n : NoZMod b -> (a + b) mod n = (a + (b mod n)) mod n.
  Proof. intros; apply add_mod_r; assumption. Qed.
#[global]
  Hint Rewrite add_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_push a b n : NoZMod a -> NoZMod b -> (a - b) mod n = ((a mod n) - (b mod n)) mod n.
  Proof. intros; apply Zminus_mod; assumption. Qed.
#[global]
  Hint Rewrite sub_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_l_push a b n : NoZMod a -> (a - b) mod n = ((a mod n) - b) mod n.
  Proof. intros; symmetry; apply Zminus_mod_idemp_l; assumption. Qed.
#[global]
  Hint Rewrite sub_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_r_push a b n : NoZMod b -> (a - b) mod n = (a - (b mod n)) mod n.
  Proof. intros; symmetry; apply Zminus_mod_idemp_r; assumption. Qed.
#[global]
  Hint Rewrite sub_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma opp_mod_mod_push a n : NoZMod a -> (-a) mod n = (-(a mod n)) mod n.
  Proof. intros; apply opp_mod_mod; assumption. Qed.
#[global]
  Hint Rewrite opp_mod_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma lnot_mod_mod_push v m : NoZMod v -> (Z.lnot v) mod m = (Z.lnot (v mod m) mod m).
  Proof. intros; symmetry; apply lnot_mod_mod. Qed.
#[global]
  Hint Rewrite lnot_mod_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma pow_mod_push p q n : NoZMod p -> (p^q) mod n = ((p mod n)^q) mod n.
  Proof. intros; apply pow_mod_full. Qed.
#[global]
  Hint Rewrite pow_mod_push using solve [ NoZMod ] : push_Zmod.
End Z.

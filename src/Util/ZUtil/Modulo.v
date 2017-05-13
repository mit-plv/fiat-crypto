Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.ZArith.Znumtheory.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Local Open Scope Z_scope.

Module Z.
  Lemma elim_mod : forall a b m, a = b -> a mod m = b mod m.
  Proof. intros; subst; auto. Qed.
  Hint Resolve elim_mod : zarith.

  Lemma mod_add_full : forall a b c, (a + b * c) mod c = a mod c.
  Proof. intros; destruct (Z_zerop c); try subst; autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_full : zsimplify.

  Lemma mod_add_l_full : forall a b c, (a * b + c) mod b = c mod b.
  Proof. intros; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_l_full : zsimplify.

  Lemma mod_add'_full : forall a b c, (a + b * c) mod b = a mod b.
  Proof. intros; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l'_full : forall a b c, (a * b + c) mod a = c mod a.
  Proof. intros; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add'_full mod_add_l'_full : zsimplify.

  Lemma mod_add_l : forall a b c, b <> 0 -> (a * b + c) mod b = c mod b.
  Proof. intros; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.

  Lemma mod_add' : forall a b c, b <> 0 -> (a + b * c) mod b = a mod b.
  Proof. intros; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l' : forall a b c, a <> 0 -> (a * b + c) mod a = c mod a.
  Proof. intros; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.

  Lemma add_pow_mod_l : forall a b c, a <> 0 -> 0 < b ->
                                      ((a ^ b) + c) mod a = c mod a.
  Proof.
    intros; replace b with (b - 1 + 1) by ring;
      rewrite Z.pow_add_r, Z.pow_1_r by omega; auto using Z.mod_add_l.
  Qed.

  Lemma mod_exp_0 : forall a x m, x > 0 -> m > 1 -> a mod m = 0 ->
    a ^ x mod m = 0.
  Proof.
    intros.
    replace x with (Z.of_nat (Z.to_nat x)) in * by (apply Z2Nat.id; omega).
    induction (Z.to_nat x). {
      simpl in *; omega.
    } {
      rewrite Nat2Z.inj_succ in *.
      rewrite Z.pow_succ_r by omega.
      rewrite Z.mul_mod by omega.
      case_eq n; intros. {
        subst. simpl.
        rewrite Zmod_1_l by omega.
        rewrite H1.
        apply Zmod_0_l.
      } {
        subst.
        rewrite IHn by (rewrite Nat2Z.inj_succ in *; omega).
        rewrite H1.
        auto.
      }
    }
  Qed.

  Lemma mod_pow : forall (a m b : Z), (0 <= b) -> (m <> 0) ->
      a ^ b mod m = (a mod m) ^ b mod m.
  Proof.
    intros; rewrite <- (Z2Nat.id b) by auto.
    induction (Z.to_nat b); auto.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite Z.mul_mod by auto.
    rewrite (Z.mul_mod (a mod m) ((a mod m) ^ Z.of_nat n) m) by auto.
    rewrite <- IHn by auto.
    rewrite Z.mod_mod by auto.
    reflexivity.
  Qed.

  Lemma mod_to_nat x m (Hm:(0 < m)%Z) (Hx:(0 <= x)%Z) : (Z.to_nat x mod Z.to_nat m = Z.to_nat (x mod m))%nat.
    pose proof Zdiv.mod_Zmod (Z.to_nat x) (Z.to_nat m) as H;
      rewrite !Z2Nat.id in H by omega.
    rewrite <-H by (change 0%nat with (Z.to_nat 0); rewrite Z2Nat.inj_iff; omega).
    rewrite !Nat2Z.id; reflexivity.
  Qed.
End Z.

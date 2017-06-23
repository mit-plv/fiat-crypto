Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.ZSimplify.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma mod_r_distr_if (b : bool) x y z : z mod (if b then x else y) = if b then z mod x else z mod y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mod_r_distr_if : push_Zmod.
  Hint Rewrite <- mod_r_distr_if : pull_Zmod.

  Lemma mod_l_distr_if (b : bool) x y z : (if b then x else y) mod z = if b then x mod z else y mod z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mod_l_distr_if : push_Zmod.
  Hint Rewrite <- mod_l_distr_if : pull_Zmod.

  (** Version without the [n <> 0] assumption *)
  Lemma mul_mod_full a b n : (a * b) mod n = ((a mod n) * (b mod n)) mod n.
  Proof. auto using Zmult_mod. Qed.
  Hint Rewrite <- mul_mod_full : pull_Zmod.
  Hint Resolve mul_mod_full : zarith.

  Lemma mul_mod_l a b n : (a * b) mod n = ((a mod n) * b) mod n.
  Proof.
    intros; rewrite (mul_mod_full a b), (mul_mod_full (a mod n) b).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- mul_mod_l : pull_Zmod.
  Hint Resolve mul_mod_l : zarith.

  Lemma mul_mod_r a b n : (a * b) mod n = (a * (b mod n)) mod n.
  Proof.
    intros; rewrite (mul_mod_full a b), (mul_mod_full a (b mod n)).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- mul_mod_r : pull_Zmod.
  Hint Resolve mul_mod_r : zarith.

  Lemma add_mod_full a b n : (a + b) mod n = ((a mod n) + (b mod n)) mod n.
  Proof. auto using Zplus_mod. Qed.
  Hint Rewrite <- add_mod_full : pull_Zmod.
  Hint Resolve add_mod_full : zarith.

  Lemma add_mod_l a b n : (a + b) mod n = ((a mod n) + b) mod n.
  Proof.
    intros; rewrite (add_mod_full a b), (add_mod_full (a mod n) b).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- add_mod_l : pull_Zmod.
  Hint Resolve add_mod_l : zarith.

  Lemma add_mod_r a b n : (a + b) mod n = (a + (b mod n)) mod n.
  Proof.
    intros; rewrite (add_mod_full a b), (add_mod_full a (b mod n)).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- add_mod_r : pull_Zmod.
  Hint Resolve add_mod_r : zarith.

  Lemma opp_mod_mod a n : (-a) mod n = (-(a mod n)) mod n.
  Proof.
    intros; destruct (Z_zerop (a mod n)) as [H'|H']; [ rewrite H' | ];
      [ | rewrite !Z_mod_nz_opp_full ];
      autorewrite with zsimplify; lia.
  Qed.
  Hint Rewrite <- opp_mod_mod : pull_Zmod.
  Hint Resolve opp_mod_mod : zarith.

  (** Give alternate names for the next three lemmas, for consistency *)
  Lemma sub_mod_full a b n : (a - b) mod n = ((a mod n) - (b mod n)) mod n.
  Proof. auto using Zminus_mod. Qed.
  Hint Rewrite <- sub_mod_full : pull_Zmod.
  Hint Resolve sub_mod_full : zarith.

  Lemma sub_mod_l a b n : (a - b) mod n = ((a mod n) - b) mod n.
  Proof. auto using Zminus_mod_idemp_l. Qed.
  Hint Rewrite <- sub_mod_l : pull_Zmod.
  Hint Resolve sub_mod_l : zarith.

  Lemma sub_mod_r a b n : (a - b) mod n = (a - (b mod n)) mod n.
  Proof. auto using Zminus_mod_idemp_r. Qed.
  Hint Rewrite <- sub_mod_r : pull_Zmod.
  Hint Resolve sub_mod_r : zarith.

  Definition NoZMod (x : Z) := True.
  Ltac NoZMod :=
    lazymatch goal with
    | [ |- NoZMod (?x mod ?y) ] => fail 0 "Goal has" x "mod" y
    | [ |- NoZMod _ ] => constructor
    end.

  Lemma mul_mod_push a b n : NoZMod a -> NoZMod b -> (a * b) mod n = ((a mod n) * (b mod n)) mod n.
  Proof. intros; apply mul_mod_full; assumption. Qed.
  Hint Rewrite mul_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_push a b n : NoZMod a -> NoZMod b -> (a + b) mod n = ((a mod n) + (b mod n)) mod n.
  Proof. intros; apply add_mod_full; assumption. Qed.
  Hint Rewrite add_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma mul_mod_l_push a b n : NoZMod a -> (a * b) mod n = ((a mod n) * b) mod n.
  Proof. intros; apply mul_mod_l; assumption. Qed.
  Hint Rewrite mul_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma mul_mod_r_push a b n : NoZMod b -> (a * b) mod n = (a * (b mod n)) mod n.
  Proof. intros; apply mul_mod_r; assumption. Qed.
  Hint Rewrite mul_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_l_push a b n : NoZMod a -> (a + b) mod n = ((a mod n) + b) mod n.
  Proof. intros; apply add_mod_l; assumption. Qed.
  Hint Rewrite add_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_r_push a b n : NoZMod b -> (a + b) mod n = (a + (b mod n)) mod n.
  Proof. intros; apply add_mod_r; assumption. Qed.
  Hint Rewrite add_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_push a b n : NoZMod a -> NoZMod b -> (a - b) mod n = ((a mod n) - (b mod n)) mod n.
  Proof. intros; apply Zminus_mod; assumption. Qed.
  Hint Rewrite sub_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_l_push a b n : NoZMod a -> (a - b) mod n = ((a mod n) - b) mod n.
  Proof. intros; symmetry; apply Zminus_mod_idemp_l; assumption. Qed.
  Hint Rewrite sub_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_r_push a b n : NoZMod b -> (a - b) mod n = (a - (b mod n)) mod n.
  Proof. intros; symmetry; apply Zminus_mod_idemp_r; assumption. Qed.
  Hint Rewrite sub_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma opp_mod_mod_push a n : NoZMod a -> (-a) mod n = (-(a mod n)) mod n.
  Proof. intros; apply opp_mod_mod; assumption. Qed.
  Hint Rewrite opp_mod_mod_push using solve [ NoZMod ] : push_Zmod.
End Z.

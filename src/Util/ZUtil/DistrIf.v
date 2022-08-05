Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Definition opp_distr_if (b : bool) x y : -(if b then x else y) = if b then -x else -y.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite opp_distr_if : push_Zopp.
#[global]
  Hint Rewrite <- opp_distr_if : pull_Zopp.

  Lemma mul_r_distr_if (b : bool) x y z : z * (if b then x else y) = if b then z * x else z * y.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite mul_r_distr_if : push_Zmul.
#[global]
  Hint Rewrite <- mul_r_distr_if : pull_Zmul.

  Lemma mul_l_distr_if (b : bool) x y z : (if b then x else y) * z = if b then x * z else y * z.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite mul_l_distr_if : push_Zmul.
#[global]
  Hint Rewrite <- mul_l_distr_if : pull_Zmul.

  Lemma add_r_distr_if (b : bool) x y z : z + (if b then x else y) = if b then z + x else z + y.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite add_r_distr_if : push_Zadd.
#[global]
  Hint Rewrite <- add_r_distr_if : pull_Zadd.

  Lemma add_l_distr_if (b : bool) x y z : (if b then x else y) + z = if b then x + z else y + z.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite add_l_distr_if : push_Zadd.
#[global]
  Hint Rewrite <- add_l_distr_if : pull_Zadd.

  Lemma sub_r_distr_if (b : bool) x y z : z - (if b then x else y) = if b then z - x else z - y.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite sub_r_distr_if : push_Zsub.
#[global]
  Hint Rewrite <- sub_r_distr_if : pull_Zsub.

  Lemma sub_l_distr_if (b : bool) x y z : (if b then x else y) - z = if b then x - z else y - z.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite sub_l_distr_if : push_Zsub.
#[global]
  Hint Rewrite <- sub_l_distr_if : pull_Zsub.

  Lemma div_r_distr_if (b : bool) x y z : z / (if b then x else y) = if b then z / x else z / y.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite div_r_distr_if : push_Zdiv.
#[global]
  Hint Rewrite <- div_r_distr_if : pull_Zdiv.

  Lemma div_l_distr_if (b : bool) x y z : (if b then x else y) / z = if b then x / z else y / z.
  Proof. destruct b; reflexivity. Qed.
#[global]
  Hint Rewrite div_l_distr_if : push_Zdiv.
#[global]
  Hint Rewrite <- div_l_distr_if : pull_Zdiv.
End Z.

Module Export Hints.
  Export Crypto.Util.FixCoqMistakes.
  Export Crypto.Util.ZUtil.Hints.Core.
#[global]
  Hint Rewrite Z.opp_distr_if : push_Zopp.
#[global]
  Hint Rewrite <- Z.opp_distr_if : pull_Zopp.
#[global]
  Hint Rewrite Z.mul_r_distr_if : push_Zmul.
#[global]
  Hint Rewrite <- Z.mul_r_distr_if : pull_Zmul.
#[global]
  Hint Rewrite Z.mul_l_distr_if : push_Zmul.
#[global]
  Hint Rewrite <- Z.mul_l_distr_if : pull_Zmul.
#[global]
  Hint Rewrite Z.add_r_distr_if : push_Zadd.
#[global]
  Hint Rewrite <- Z.add_r_distr_if : pull_Zadd.
#[global]
  Hint Rewrite Z.add_l_distr_if : push_Zadd.
#[global]
  Hint Rewrite <- Z.add_l_distr_if : pull_Zadd.
#[global]
  Hint Rewrite Z.sub_r_distr_if : push_Zsub.
#[global]
  Hint Rewrite <- Z.sub_r_distr_if : pull_Zsub.
#[global]
  Hint Rewrite Z.sub_l_distr_if : push_Zsub.
#[global]
  Hint Rewrite <- Z.sub_l_distr_if : pull_Zsub.
#[global]
  Hint Rewrite Z.div_r_distr_if : push_Zdiv.
#[global]
  Hint Rewrite <- Z.div_r_distr_if : pull_Zdiv.
#[global]
  Hint Rewrite Z.div_l_distr_if : push_Zdiv.
#[global]
  Hint Rewrite <- Z.div_l_distr_if : pull_Zdiv.
End Hints.

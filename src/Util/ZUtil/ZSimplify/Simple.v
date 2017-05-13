Require Import Coq.ZArith.ZArith Coq.micromega.Lia Coq.omega.Omega.
Require Import Crypto.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma sub_same_minus (x y : Z) : x - (x - y) = y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus : zsimplify.
  Lemma sub_same_plus (x y : Z) : x - (x + y) = -y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus : zsimplify.
  Lemma sub_same_minus_plus (x y z : Z) : x - (x - y + z) = y - z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_plus : zsimplify.
  Lemma sub_same_plus_plus (x y z : Z) : x - (x + y + z) = -y - z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_plus : zsimplify.
  Lemma sub_same_minus_minus (x y z : Z) : x - (x - y - z) = y + z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_minus : zsimplify.
  Lemma sub_same_plus_minus (x y z : Z) : x - (x + y - z) = z - y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_minus : zsimplify.
  Lemma sub_same_minus_then_plus (x y w : Z) : x - (x - y) + w = y + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_then_plus : zsimplify.
  Lemma sub_same_plus_then_plus (x y w : Z) : x - (x + y) + w = w - y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_then_plus : zsimplify.
  Lemma sub_same_minus_plus_then_plus (x y z w : Z) : x - (x - y + z) + w = y - z + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_plus_then_plus : zsimplify.
  Lemma sub_same_plus_plus_then_plus (x y z w : Z) : x - (x + y + z) + w = w - y - z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_plus_then_plus : zsimplify.
  Lemma sub_same_minus_minus_then_plus (x y z w : Z) : x - (x - y - z) + w = y + z + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_minus : zsimplify.
  Lemma sub_same_plus_minus_then_plus (x y z w : Z) : x - (x + y - z) + w = z - y + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_minus_then_plus : zsimplify.

  Lemma simplify_twice_sub_sub x y : 2 * x - (x - y) = x + y.
  Proof. lia. Qed.
  Hint Rewrite simplify_twice_sub_sub : zsimplify.

  Lemma simplify_twice_sub_add x y : 2 * x - (x + y) = x - y.
  Proof. lia. Qed.
  Hint Rewrite simplify_twice_sub_add : zsimplify.

  Lemma simplify_2XmX X : 2 * X - X = X.
  Proof. omega. Qed.
  Hint Rewrite simplify_2XmX : zsimplify.

  Lemma simplify_add_pos x y : Z.pos x + Z.pos y = Z.pos (x + y).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_add_pos : zsimplify_Z_to_pos.
  Lemma simplify_add_pos10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    : Z.pos x0 + (Z.pos x1 + (Z.pos x2 + (Z.pos x3 + (Z.pos x4 + (Z.pos x5 + (Z.pos x6 + (Z.pos x7 + (Z.pos x8 + Z.pos x9))))))))
      = Z.pos (x0 + (x1 + (x2 + (x3 + (x4 + (x5 + (x6 + (x7 + (x8 + x9))))))))).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_add_pos10 : zsimplify_Z_to_pos.
  Lemma simplify_mul_pos x y : Z.pos x * Z.pos y = Z.pos (x * y).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_mul_pos : zsimplify_Z_to_pos.
  Lemma simplify_mul_pos10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    : Z.pos x0 * (Z.pos x1 * (Z.pos x2 * (Z.pos x3 * (Z.pos x4 * (Z.pos x5 * (Z.pos x6 * (Z.pos x7 * (Z.pos x8 * Z.pos x9))))))))
      = Z.pos (x0 * (x1 * (x2 * (x3 * (x4 * (x5 * (x6 * (x7 * (x8 * x9))))))))).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_mul_pos10 : zsimplify_Z_to_pos.
  Lemma simplify_sub_pos x y : Z.pos x - Z.pos y = Z.pos_sub x y.
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_sub_pos : zsimplify_Z_to_pos.

  Lemma two_sub_sub_inner_sub x y z : 2 * x - y - (x - z) = x - y + z.
  Proof. clear; lia. Qed.
  Hint Rewrite two_sub_sub_inner_sub : zsimplify.

  Lemma minus_minus_one : - -1 = 1.
  Proof. reflexivity. Qed.
  Hint Rewrite minus_minus_one : zsimplify.
End Z.

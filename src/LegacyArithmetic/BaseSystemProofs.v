Require Import Coq.Lists.List Coq.micromega.Psatz.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.LegacyArithmetic.BaseSystem.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Notations.
Import Morphisms.
Local Open Scope Z.

Local Hint Extern 1 (@eq Z _ _) => ring.

Section BaseSystemProofs.
  Context `(base_vector : BaseVector).

  Lemma decode'_truncate : forall bs us, decode' bs us = decode' bs (firstn (length bs) us).
  Proof using Type.
    unfold decode'; intros; f_equal; apply combine_truncate_l.
  Qed.

  Lemma decode'_splice : forall xs ys bs,
    decode' bs (xs ++ ys) =
    decode' (firstn (length xs) bs) xs + decode'  (skipn (length xs) bs) ys.
  Proof using Type.
    unfold decode'.
    induction xs; destruct ys, bs; boring.
    + rewrite combine_truncate_r.
      do 2 rewrite Z.add_0_r; auto.
    + unfold accumulate.
      apply Z.add_assoc.
  Qed.

  Lemma decode_nil : forall bs, decode' bs nil = 0.
  Proof using Type.

    auto.
  Qed.
  Hint Rewrite decode_nil.

  Lemma decode_base_nil : forall us, decode' nil us = 0.
  Proof using Type.
    intros; rewrite decode'_truncate; auto.
  Qed.

  Lemma mul_each_rep : forall bs u vs,
    decode' bs (mul_each u vs) = u * decode' bs vs.
  Proof using Type.
    unfold decode', accumulate; induction bs; destruct vs; boring; ring.
  Qed.

  Lemma base_eq_1cons: base = 1 :: skipn 1 base.
  Proof using Type*.
    pose proof (b0_1 0) as H.
    destruct base; compute in H; try discriminate; boring.
  Qed.

  Lemma decode'_cons : forall x1 x2 xs1 xs2,
    decode' (x1 :: xs1) (x2 :: xs2) = x1 * x2 + decode' xs1 xs2.
  Proof using Type.
    unfold decode', accumulate; boring; ring.
  Qed.
  Hint Rewrite decode'_cons.

  Lemma decode_cons : forall x us,
    decode base (x :: us) = x + decode base (0 :: us).
  Proof using Type*.
    unfold decode; intros.
    rewrite base_eq_1cons.
    autorewrite with core; ring_simplify; auto.
  Qed.

  Lemma decode'_map_mul : forall v xs bs,
    decode' (map (Z.mul v) bs) xs =
    Z.mul v (decode' bs xs).
  Proof using Type.
    unfold decode'.
    induction xs; destruct bs; boring.
    unfold accumulate; simpl; nia.
  Qed.

  Lemma decode_map_mul : forall v xs,
    decode (map (Z.mul v) base) xs =
    Z.mul v (decode base xs).
  Proof using Type.
    unfold decode; intros; apply decode'_map_mul.
  Qed.

  Lemma mul_each_base : forall us bs c,
      decode' bs (mul_each c us) = decode' (mul_each c bs) us.
  Proof using Type.
    induction us; destruct bs; boring; ring.
  Qed.

  Hint Rewrite (@nth_default_nil Z).
  Hint Rewrite (@firstn_nil Z).
  Hint Rewrite (@skipn_nil Z).

  Lemma peel_decode : forall xs ys x y, decode' (x::xs) (y::ys) = x*y + decode' xs ys.
  Proof using Type.
    boring.
  Qed.
  Hint Rewrite peel_decode.

  Hint Rewrite plus_0_r.

  Lemma set_higher : forall bs vs x,
    decode' bs (vs++x::nil) = decode' bs vs + nth_default 0 bs (length vs) * x.
  Proof using Type.
    intros.
    rewrite !decode'_splice.
    cbv [decode' nth_default]; break_match; ring_simplify;
      match goal with
      | [H:_ |- _] => unique pose proof (nth_error_error_length _ _ _ H)
      | [H:_ |- _] => unique pose proof (nth_error_value_length _ _ _ _ H)
      end;
      repeat match goal with
             | _ => solve [simpl;ring_simplify; trivial]
             | _ => progress ring_simplify
             | _ => progress rewrite skipn_all by trivial
             | _ => progress rewrite combine_nil_r
             | _ => progress rewrite firstn_all2 by trivial
             end.
    rewrite (combine_truncate_r vs bs); apply (f_equal2 Z.add); trivial; [].
    unfold combine; break_match.
    { let Heql := match goal with H : _ = nil |- _ => H end in
      apply (f_equal (@length _)) in Heql; simpl length in Heql; rewrite skipn_length in Heql; omega. }
    { cbv -[Z.add Z.mul]; ring_simplify; f_equal.
      assert (HH: nth_error (z0 :: l) 0 = Some z) by
          (
            pose proof @nth_error_skipn _ (length vs) bs 0;
            rewrite plus_0_r in *;
            congruence); simpl in HH; congruence. }
  Qed.
End BaseSystemProofs.

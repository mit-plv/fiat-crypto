Require Import Crypto.NewBaseSystem.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.Algebra. Import Ring.
Require Import Crypto.Util.ZUtil Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Class Pow2Limbs :=
  {
    limb_widths : list Z;
    limb_widths_pos : forall w, In w limb_widths -> 0 < w;
    limb_widths_nonnil : limb_widths <> nil;
    base := base_from_limb_widths limb_widths
  }.

Class Modulus :=
  {
    m : Z;
    prime_modulus : Znumtheory.prime m;
    terms : list (Z * Z)
  }.

Class ModularBaseParams (limbs : Pow2Limbs) (modulus : Modulus) := {
  k := sum_firstn limb_widths (length limb_widths);
  terms_lt_k : forall t, In t terms -> snd t < k;
  terms_in_base : forall t, In t terms -> In (fst t) base;
  terms_correct : m = 2^k + B.eval terms
}.

Section ModularBaseSystem.
  Let B : Type := list (Z * Z).
  Context {R Req Rzero Rone Ropp Radd Rsub Rmul RToB BToR}
          {Rring : @ring R Req Rzero Rone Ropp Radd Rsub Rmul}
          {RBhomom : @is_homomorphism R Req Rone Radd Rmul
                                      B B.eq B.one B.add B.mul RToB}
          {BRhomom : @is_homomorphism B B.eq B.one B.add B.mul
                                      R Req Rone Radd Rmul BToR}.
  Context {BToR_RToB : forall b, B.eq (RToB (BToR b)) b}.
  Context `{mbp : ModularBaseParams}.

  
  Definition reduce' (a b : B) : B :=
    fold_right (fun cx state => B.sub state (B.mul (cx :: nil) b)) a terms.
  
  Definition reduce (r : R) : R :=
    let ab := B.split (2 ^ k) (RToB r) in
    BToR (reduce' (fst ab) (snd ab)).

  Definition eq_mod (x y : R) : Prop :=
    B.eval (RToB x) mod m = B.eval (RToB y) mod m.

  Lemma reduce'_correct a b :
    B.eval (reduce' a b) = B.eval a - B.eval (B.mul terms b).
  Proof.
    cbv [reduce']. rewrite B.mul_correct.
    induction terms; rewrite ?fold_right_cons, ?B.eval_nil.
    { simpl. ring. }
    { rewrite B.sub_correct, B.mul_single, B.eval_cons.
      rewrite IHl; ring. }
  Qed.


  Lemma reduction_rule : forall a b c d,
    (a - c * b) mod (d + c) = (a + d * b) mod (d + c).
  Proof.
    intros.
    replace (c * b) with (- (d * b) + (d + c) * b) by ring.
    rewrite Z.sub_add_distr.
    rewrite <-Z.add_opp_r, <-!Z.mul_opp_r.
    rewrite Z.mod_add'_full.
    f_equal; ring.
  Qed.

  Definition coefs_pow2 (b : B) : Prop :=
    forall cx, In cx b -> exists x, 2 ^ x = fst cx.

  Lemma k_nonneg : 0 <= k.
  Proof.
    unfold k; apply sum_firstn_nonnegative.
    intros; auto using Z.lt_le_incl, limb_widths_pos.
  Qed.

  Lemma reduce_correct r : coefs_pow2 (RToB r) ->
      eq_mod (reduce r) r.
  Proof.
    intros.
    cbv [eq_mod reduce]; rewrite BToR_RToB.
    rewrite reduce'_correct, B.mul_correct.
    rewrite terms_correct, reduction_rule, B.split_correct.
    auto.
    { apply Z.pow_nonzero; auto using k_nonneg; omega. }
    { intros.
      match goal with H : coefs_pow2 ?b, H1 : In _ ?b |- _ =>
      apply H in H1; destruct H1 as [? H1]; rewrite <-H1 end.
      auto using Z.pow2_lt_or_divides, k_nonneg. }
  Qed.

End ModularBaseSystem.
  

  
  
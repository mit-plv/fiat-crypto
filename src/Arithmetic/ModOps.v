Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.derive.Derive.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

Section mod_ops.
  Import Positional.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (len_c : nat)
          (idxs : list nat)
          (len_idxs : nat)
          (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
          (Hn_nz : n <> 0%nat)
          (Hc : length c = len_c)
          (Hidxs : length idxs = len_idxs).
  Definition weight (i : nat)
    := 2^(-(-(limbwidth_num * i) / limbwidth_den)).

  Local Ltac Q_cbv :=
    cbv [Qceiling inject_Z Qle Qfloor Qdiv Qnum Qden Qmult Qinv Qopp].

  Local Lemma weight_ZQ_correct i
        (limbwidth := (limbwidth_num / limbwidth_den)%Q)
    : weight i = 2^Qceiling(limbwidth*i).
  Proof using limbwidth_good.
    clear -limbwidth_good.
    cbv [limbwidth weight]; Q_cbv.
    destruct limbwidth_num, limbwidth_den, i; try reflexivity;
      repeat rewrite ?Pos.mul_1_l, ?Pos.mul_1_r, ?Z.mul_0_l, ?Zdiv_0_l, ?Zdiv_0_r, ?Z.mul_1_l, ?Z.mul_1_r, <- ?Z.opp_eq_mul_m1, ?Pos2Z.opp_pos;
      try reflexivity; try lia.
  Qed.

  Local Ltac t_weight_with lem :=
    clear -limbwidth_good;
    intros; rewrite !weight_ZQ_correct;
    apply lem;
    try omega; Q_cbv; destruct limbwidth_den; cbn; try lia.

  Definition wprops : @weight_properties weight.
  Proof using limbwidth_good.
    constructor.
    { cbv [weight Z.of_nat]; autorewrite with zsimplify_fast; reflexivity. }
    { intros; apply Z.gt_lt. t_weight_with (@pow_ceil_mul_nat_pos 2). }
    { t_weight_with (@pow_ceil_mul_nat_multiples 2). }
    { intros; apply Z.gt_lt. t_weight_with (@pow_ceil_mul_nat_divide 2). }
  Defined.
  Local Hint Immediate (weight_0 wprops).
  Local Hint Immediate (weight_positive wprops).
  Local Hint Immediate (weight_multiples wprops).
  Local Hint Immediate (weight_divides wprops).

  Local Lemma weight_1_gt_1 : weight 1 > 1.
  Proof using limbwidth_good.
    clear -limbwidth_good.
    cut (1 < weight 1); [ lia | ].
    cbv [weight Z.of_nat]; autorewrite with zsimplify_fast.
    apply Z.pow_gt_1; [ omega | ].
    Z.div_mod_to_quot_rem_in_goal; nia.
  Qed.

  Lemma weight_unique_iff : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j <-> i = j.
  Proof using limbwidth_good.
    clear Hn_nz; clear dependent c.
    cbv [weight]; split; intro H'; subst; trivial; [].
    apply (f_equal (fun x => limbwidth_den * (- Z.log2 x))) in H'.
    rewrite !Z.log2_pow2, !Z.opp_involutive in H' by (Z.div_mod_to_quot_rem; nia).
    Z.div_mod_to_quot_rem.
    destruct i as [|i], j as [|j]; autorewrite with zsimplify_const in *; [ reflexivity | exfalso; nia.. | ].
    nia.
  Qed.
  Lemma weight_unique : forall i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j -> i = j.
  Proof using limbwidth_good. apply weight_unique_iff. Qed.

  Derive carry_mulmod
         SuchThat (forall (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (carry_mulmod f g)) mod (s - Associational.eval c)
                      = (eval weight n f * eval weight n g) mod (s - Associational.eval c))
         As eval_carry_mulmod.
  Proof.
    intros.
    rewrite <-eval_mulmod with (s:=s) (c:=c) by auto with zarith.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto with zarith; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carry_mulmod; reflexivity.
  Qed.

  Derive carry_squaremod
         SuchThat (forall (f : list Z)
                          (Hf : length f = n),
                      (eval weight n (carry_squaremod f)) mod (s - Associational.eval c)
                      = (eval weight n f * eval weight n f) mod (s - Associational.eval c))
         As eval_carry_squaremod.
  Proof.
    intros.
    rewrite <-eval_squaremod with (s:=s) (c:=c) by auto with zarith.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto with zarith; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carry_squaremod; reflexivity.
  Qed.

  Derive carry_scmulmod
         SuchThat (forall (x : Z) (f : list Z)
                          (Hf : length f = n),
                      (eval weight n (carry_scmulmod x f)) mod (s - Associational.eval c)
                      = (x * eval weight n f) mod (s - Associational.eval c))
         As eval_carry_scmulmod.
  Proof.
    intros.
    push_Zmod.
    rewrite <-eval_encode with (s:=s) (c:=c) (x:=x) (weight:=weight) (n:=n) by auto with zarith.
    pull_Zmod.
    rewrite<-eval_mulmod with (s:=s) (c:=c) by (auto with zarith; distr_length).
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto with zarith; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carry_scmulmod; reflexivity.
  Qed.

  Derive carrymod
         SuchThat (forall (f : list Z)
                          (Hf : length f = n),
                      (eval weight n (carrymod f)) mod (s - Associational.eval c)
                      = (eval weight n f) mod (s - Associational.eval c))
         As eval_carrymod.
  Proof.
    intros.
    etransitivity;
      [ | rewrite <- @eval_chained_carries with (s:=s) (c:=c) (idxs:=idxs)
          by auto with zarith; reflexivity ].
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst carrymod; reflexivity.
  Qed.

  Derive addmod
         SuchThat (forall (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (addmod f g)) mod (s - Associational.eval c)
                      = (eval weight n f + eval weight n g) mod (s - Associational.eval c))
         As eval_addmod.
  Proof.
    intros.
    rewrite <-eval_add by auto with zarith.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst addmod; reflexivity.
  Qed.

  Derive submod
         SuchThat (forall (coef:Z)
                          (f g : list Z)
                          (Hf : length f = n)
                          (Hg : length g = n),
                      (eval weight n (submod coef f g)) mod (s - Associational.eval c)
                      = (eval weight n f - eval weight n g) mod (s - Associational.eval c))
         As eval_submod.
  Proof.
    intros.
    rewrite <-eval_sub with (coef:=coef) by auto with zarith.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst submod; reflexivity.
  Qed.

  Derive oppmod
         SuchThat (forall (coef:Z)
                          (f: list Z)
                          (Hf : length f = n),
                      (eval weight n (oppmod coef f)) mod (s - Associational.eval c)
                      = (- eval weight n f) mod (s - Associational.eval c))
         As eval_oppmod.
  Proof.
    intros.
    rewrite <-eval_opp with (coef:=coef) by auto with zarith.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst oppmod; reflexivity.
  Qed.

  Derive encodemod
         SuchThat (forall (f:Z),
                      (eval weight n (encodemod f)) mod (s - Associational.eval c)
                      = f mod (s - Associational.eval c))
         As eval_encodemod.
  Proof.
    intros.
    etransitivity.
    2:rewrite <-@eval_encode with (weight:=weight) (n:=n) by auto with zarith; reflexivity.
    eapply f_equal2; [|trivial]. eapply f_equal.
    subst encodemod; reflexivity.
  Qed.
End mod_ops.
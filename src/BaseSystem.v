Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.
Import Nat.

Local Open Scope Z.

Class BaseVector (base : list Z):= {
  base_positive : forall b, In b base -> b > 0; (* nonzero would probably work too... *)
  b0_1 : forall x, nth_default x base 0 = 1;
  base_good :
    forall i j, (i+j < length base)%nat ->
    let b := nth_default 0 base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat
}.

Section BaseSystem.
  Context (base : list Z).
  (** [BaseSystem] implements an constrained positional number system.
      A wide variety of bases are supported: the base coefficients are not
      required to be powers of 2, and it is NOT necessarily the case that
      $b_{i+j} = b_i b_j$. Implementations of addition and multiplication are
      provided, with focus on near-optimal multiplication performance on
      non-trivial but small operands: maybe 10 32-bit integers or so. This
      module does not handle carries automatically: if no restrictions are put
      on the use of a [BaseSystem], each digit is unbounded. This has nothing
      to do with modular arithmetic either.
  *)
  Definition digits : Type := list Z.

  Definition accumulate p acc := fst p * snd p + acc.
  Definition decode' bs u  := fold_right accumulate 0 (combine u bs).
  Definition decode := decode' base.
  (* Does not carry; z becomes the lowest and only digit. *)
  Definition encode (z : Z) := z :: nil.

  Lemma decode'_truncate : forall bs us, decode' bs us = decode' bs (firstn (length bs) us).
  Proof.
    unfold decode'; intros; f_equal; apply combine_truncate_l.
  Qed.

  Fixpoint add (us vs:digits) : digits :=
    match us,vs with
      | u::us', v::vs' => u+v :: add us' vs'
      | _, nil => us
      | _, _ => vs
    end.
  Infix ".+" := add.

  Hint Extern 1 (@eq Z _ _) => ring.

  Definition mul_each u := map (Z.mul u).
  Fixpoint sub (us vs:digits) : digits :=
    match us,vs with
      | u::us', v::vs' => u-v :: sub us' vs'
      | _, nil => us
      | nil, v::vs' => (0-v)::sub nil vs'
    end.

  Definition crosscoef i j : Z :=
    let b := nth_default 0 base in
    (b(i) * b(j)) / b(i+j)%nat.
  Hint Unfold crosscoef.

  Fixpoint zeros n := match n with O => nil | S n' => 0::zeros n' end.

  (* mul' is multiplication with the SECOND ARGUMENT REVERSED and OUTPUT REVERSED *)
  Fixpoint mul_bi' (i:nat) (vsr:digits) :=
    match vsr with
    | v::vsr' => v * crosscoef i (length vsr') :: mul_bi' i vsr'
    | nil => nil
    end.
  Definition mul_bi (i:nat) (vs:digits) : digits :=
    zeros i ++ rev (mul_bi' i (rev vs)).

  (* mul' is multiplication with the FIRST ARGUMENT REVERSED *)
  Fixpoint mul' (usr vs:digits) : digits :=
    match usr with
      | u::usr' =>
        mul_each u (mul_bi (length usr') vs) .+ mul' usr' vs
      | _ => nil
    end.
  Definition mul us := mul' (rev us).

End BaseSystem.

(* Example : polynomial base system *)
Section PolynomialBaseCoefs.
  Context (b1 : positive) (baseLength : nat) (baseLengthNonzero : ltb 0 baseLength = true).
  (** PolynomialBaseCoefs generates base vectors for [BaseSystem]. *)
  Definition bi i := (Zpos b1)^(Z.of_nat i).
  Definition poly_base := map bi (seq 0 baseLength).

  Lemma poly_b0_1 : forall x, nth_default x poly_base 0 = 1.
    unfold poly_base, bi, nth_default.
    case_eq baseLength; intros. {
      assert ((0 < baseLength)%nat) by
        (rewrite <-ltb_lt; apply baseLengthNonzero).
      subst; omega.
    }
    auto.
  Qed.

  Lemma poly_base_positive : forall b, In b poly_base -> b > 0.
  Proof.
    unfold poly_base.
    intros until 0; intro H.
    rewrite in_map_iff in *.
    destruct H; destruct H.
    subst.
    apply Z.pos_pow_nat_pos.
  Qed.

  Lemma poly_base_defn : forall i, (i < length poly_base)%nat ->
      nth_default 0 poly_base i = bi i.
  Proof.
    unfold poly_base, nth_default; nth_tac.
  Qed.

  Lemma poly_base_succ :
    forall i, ((S i) < length poly_base)%nat ->
    let b := nth_default 0 poly_base in
    let r := (b (S i) / b i) in
    b (S i) = r * b i.
  Proof.
    intros; subst b; subst r.
    repeat rewrite poly_base_defn in * by omega.
    unfold bi.
    replace (Z.pos b1 ^ Z.of_nat (S i))
      with (Z.pos b1 * (Z.pos b1 ^ Z.of_nat i)) by
      (rewrite Nat2Z.inj_succ; rewrite <- Z.pow_succ_r; intuition).
    replace (Z.pos b1 * Z.pos b1 ^ Z.of_nat i / Z.pos b1 ^ Z.of_nat i)
      with (Z.pos b1); auto.
    rewrite Z_div_mult_full; auto.
    apply Z.pow_nonzero; intuition.
  Qed.

  Lemma poly_base_good:
    forall i j, (i + j < length poly_base)%nat ->
    let b := nth_default 0 poly_base in
    let r := (b i * b j) / b (i+j)%nat in
    b i * b j = r * b (i+j)%nat.
  Proof.
    unfold poly_base, nth_default; nth_tac.

    clear.
    unfold bi.
    rewrite Nat2Z.inj_add, Zpower_exp by
      (replace 0 with (Z.of_nat 0) by auto; rewrite <- Nat2Z.inj_ge; omega).
    rewrite Z_div_same_full; try ring.
    rewrite <- Z.neq_mul_0.
    split; apply Z.pow_nonzero; try apply Zle_0_nat; try solve [intro H; inversion H].
  Qed.

  Instance PolyBaseVector : BaseVector poly_base := {
    base_positive := poly_base_positive;
    b0_1 := poly_b0_1;
    base_good := poly_base_good
  }.

End PolynomialBaseCoefs.

Import ListNotations.

Section BaseSystemExample.
  Definition baseLength := 32%nat.
  Lemma baseLengthNonzero : ltb 0 baseLength = true.
    compute; reflexivity.
  Qed.
  Definition base2 := poly_base 2 baseLength.

  Example three_times_two : mul base2 [1;1;0] [0;1;0] = [0;1;1;0;0].
  Proof.
    reflexivity.
  Qed.

  (* python -c "e = lambda x: '['+''.join(reversed(bin(x)[2:])).replace('1','1;').replace('0','0;')[:-1]+']'; print(e(19259)); print(e(41781))" *)
  Definition a := [1;1;0;1;1;1;0;0;1;1;0;1;0;0;1].
  Definition b := [1;0;1;0;1;1;0;0;1;1;0;0;0;1;0;1].
  Example da : decode base2 a = 19259.
  Proof.
    reflexivity.
  Qed.
  Example db : decode base2 b = 41781.
  Proof.
    reflexivity.
  Qed.
  Example encoded_ab :
    mul base2 a b =[1;1;1;2;2;4;2;2;4;5;3;3;3;6;4;2;5;3;4;3;2;1;2;2;2;0;1;1;0;1].
  Proof.
    reflexivity.
  Qed.
  Example dab : decode base2 (mul base2 a b) = 804660279.
  Proof.
    reflexivity.
  Qed.
End BaseSystemExample.

Require Import Coq.ZArith.ZArith Coq.micromega.Psatz.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.InterfaceProofs.
Require Import Crypto.BoundedArithmetic.Double.Core.
Require Import Crypto.BoundedArithmetic.Double.Proofs.Decode.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Prod.
Import Bug5107WorkAround.
Import BoundedRewriteNotations.

Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).

Local Open Scope Z_scope.
Local Opaque tuple_decoder.

Lemma ripple_carry_tuple_SS' {T} f k xss yss carry
  : @ripple_carry_tuple T f (S (S k)) xss yss carry
    = dlet xss := xss in
      dlet yss := yss in
      let '(xs, x) := eta xss in
      let '(ys, y) := eta yss in
      dlet addv := (@ripple_carry_tuple _ f (S k) xs ys carry) in
      let '(carry, zs) := eta addv in
      dlet fxy := (f x y carry) in
      let '(carry, z) := eta fxy in
      (carry, (zs, z)).
Proof. reflexivity. Qed.

Lemma ripple_carry_tuple_SS {T} f k xss yss carry
  : @ripple_carry_tuple T f (S (S k)) xss yss carry
    = let '(xs, x) := eta xss in
      let '(ys, y) := eta yss in
      let '(carry, zs) := eta (@ripple_carry_tuple _ f (S k) xs ys carry) in
      let '(carry, z) := eta (f x y carry) in
      (carry, (zs, z)).
Proof.
  rewrite ripple_carry_tuple_SS'.
  eta_expand.
  reflexivity.
Qed.

Lemma carry_is_good (n z0 z1 k : Z)
  : 0 <= n ->
    0 <= k ->
    (z1 + z0 >> k) >> n = (z0 + z1 << k) >> (k + n) /\
    (z0 mod 2 ^ k + ((z1 + z0 >> k) mod 2 ^ n) << k)%Z = (z0 + z1 << k) mod (2 ^ k * 2 ^ n).
Proof.
  intros.
  assert (0 < 2 ^ n) by auto with zarith.
  assert (0 < 2 ^ k) by auto with zarith.
  assert (0 < 2^n * 2^k) by nia.
  autorewrite with Zshift_to_pow push_Zpow.
  rewrite <- (Zmod_small ((z0 mod _) + _) (2^k * 2^n)) by (Z.div_mod_to_quot_rem; nia).
  rewrite <- !Z.mul_mod_distr_r by lia.
  rewrite !(Z.mul_comm (2^k)); pull_Zmod.
  split; [ | apply f_equal2 ];
    Z.div_mod_to_quot_rem; nia.
Qed.
Section carry_sub_is_good.
  Context (n k z0 z1 : Z)
          (Hn : 0 <= n)
          (Hk : 0 <= k)
          (Hz1 : -2^n < z1 < 2^n)
          (Hz0 : -2^k <= z0 < 2^k).

  Lemma carry_sub_is_good_carry
    : ((z1 - if z0 <? 0 then 1 else 0) <? 0) = ((z0 + z1 << k) <? 0).
  Proof.
    clear n Hn Hz1.
    assert (0 < 2 ^ k) by auto with zarith.
    autorewrite with Zshift_to_pow.
    repeat match goal with
           | _ => progress break_match
           | [ |- context[?x <? ?y] ] => destruct (x <? y) eqn:?
           | _ => reflexivity
           | _ => progress Z.ltb_to_lt
           | [ |- true = false ] => exfalso
           | [ |- false = true ] => exfalso
           | [ |- False ] => nia
           end.
  Qed.
  Lemma carry_sub_is_good_value
    : (z0 mod 2 ^ k + ((z1 - if z0 <? 0 then 1 else 0) mod 2 ^ n) << k)%Z
      = (z0 + z1 << k) mod (2 ^ k * 2 ^ n).
  Proof.
    assert (0 < 2 ^ n) by auto with zarith.
    assert (0 < 2 ^ k) by auto with zarith.
    assert (0 < 2^n * 2^k) by nia.
    autorewrite with Zshift_to_pow push_Zpow.
    rewrite <- (Zmod_small ((z0 mod _) + _) (2^k * 2^n)) by (Z.div_mod_to_quot_rem; nia).
    rewrite <- !Z.mul_mod_distr_r by lia.
    rewrite !(Z.mul_comm (2^k)); pull_Zmod.
    apply f_equal2; Z.div_mod_to_quot_rem; break_match; Z.ltb_to_lt; try reflexivity;
      match goal with
      | [ q : Z |- _ = _ :> Z ]
        => first [ cut (q = -1); [ intro; subst; ring | nia ]
                 | cut (q = 0); [ intro; subst; ring | nia ]
                 | cut (q = 1); [ intro; subst; ring | nia ] ]
      end.
  Qed.
End carry_sub_is_good.

Definition carry_is_good_carry n z0 z1 k H0 H1 := proj1 (@carry_is_good n z0 z1 k H0 H1).
Definition carry_is_good_value n z0 z1 k H0 H1 := proj2 (@carry_is_good n z0 z1 k H0 H1).

Section ripple_carry_adc.
  Context {n W} {decode : decoder n W} (adc : add_with_carry W).

  Lemma ripple_carry_adc_SS k xss yss carry
    : ripple_carry_adc (k := S (S k)) adc xss yss carry
      = let '(xs, x) := eta xss in
        let '(ys, y) := eta yss in
        let '(carry, zs) := eta (ripple_carry_adc (k := S k) adc xs ys carry) in
        let '(carry, z) := eta (adc x y carry) in
        (carry, (zs, z)).
  Proof. apply ripple_carry_tuple_SS. Qed.

  Local Opaque Z.of_nat.
  Global Instance ripple_carry_is_add_with_carry {k}
         {isdecode : is_decode decode}
         {is_adc : is_add_with_carry adc}
    : is_add_with_carry (ripple_carry_adc (k := k) adc).
  Proof.
    destruct k as [|k].
    { constructor; simpl; intros; autorewrite with zsimplify; reflexivity. }
    { induction k as [|k IHk].
      { cbv [ripple_carry_adc ripple_carry_tuple to_list].
        constructor; simpl @fst; simpl @snd; intros;
          simpl; pull_decode; reflexivity. }
      { apply Build_is_add_with_carry'; intros x y c.
        assert (0 <= n) by (destruct x; eauto using decode_exponent_nonnegative).
        assert (2^n <> 0) by auto with zarith.
        assert (0 <= S k * n) by nia.
        rewrite !tuple_decoder_S, !ripple_carry_adc_SS by assumption.
        simplify_projections; push_decode; generalize_decode.
        erewrite carry_is_good_carry, carry_is_good_value by lia.
        autorewrite with pull_Zpow push_Zof_nat zsimplify Zshift_to_pow.
        split; apply f_equal2; nia. } }
  Qed.

End ripple_carry_adc.

Hint Extern 2 (@is_add_with_carry _ (tuple ?W ?k) (@tuple_decoder ?n _ ?decode _) (@ripple_carry_adc _ ?adc _))
=> apply (@ripple_carry_is_add_with_carry n W decode adc k) : typeclass_instances.
Hint Resolve (fun n W decode adc isdecode isadc
              => @ripple_carry_is_add_with_carry n W decode adc 2 isdecode isadc
                 : @is_add_with_carry (Z.of_nat 2 * n) (W * W) (@tuple_decoder n W decode 2) (@ripple_carry_adc W adc 2))
  : typeclass_instances.

Section ripple_carry_subc.
  Context {n W} {decode : decoder n W} (subc : sub_with_carry W).

  Lemma ripple_carry_subc_SS k xss yss carry
    : ripple_carry_subc (k := S (S k)) subc xss yss carry
      = let '(xs, x) := eta xss in
        let '(ys, y) := eta yss in
        let '(carry, zs) := eta (ripple_carry_subc (k := S k) subc xs ys carry) in
        let '(carry, z) := eta (subc x y carry) in
        (carry, (zs, z)).
  Proof. apply ripple_carry_tuple_SS. Qed.

  Local Opaque Z.of_nat.
  Global Instance ripple_carry_is_sub_with_carry {k}
         {isdecode : is_decode decode}
         {is_subc : is_sub_with_carry subc}
    : is_sub_with_carry (ripple_carry_subc (k := k) subc).
  Proof.
    destruct k as [|k].
    { constructor; repeat (intros [] || intro); autorewrite with simpl_tuple_decoder zsimplify; reflexivity. }
    { induction k as [|k IHk].
      { cbv [ripple_carry_subc ripple_carry_tuple to_list].
        constructor; simpl @fst; simpl @snd; intros;
          simpl; push_decode; autorewrite with zsimplify; reflexivity. }
      { apply Build_is_sub_with_carry'; intros x y c.
        assert (0 <= n) by (destruct x; eauto using decode_exponent_nonnegative).
        assert (2^n <> 0) by auto with zarith.
        assert (0 <= S k * n) by nia.
        rewrite !tuple_decoder_S, !ripple_carry_subc_SS by assumption.
        simplify_projections; push_decode; generalize_decode.
        erewrite (carry_sub_is_good_carry (S k * n)), carry_sub_is_good_value by (break_match; lia).
        autorewrite with pull_Zpow push_Zof_nat zsimplify Zshift_to_pow.
        split; apply f_equal2; nia. } }
  Qed.

End ripple_carry_subc.

Hint Extern 2 (@is_sub_with_carry _ (tuple ?W ?k) (@tuple_decoder ?n _ ?decode _) (@ripple_carry_subc _ ?subc _))
=> apply (@ripple_carry_is_sub_with_carry n W decode subc k) : typeclass_instances.
Hint Resolve (fun n W decode subc isdecode issubc
              => @ripple_carry_is_sub_with_carry n W decode subc 2 isdecode issubc
                 : @is_sub_with_carry (Z.of_nat 2 * n) (W * W) (@tuple_decoder n W decode 2) (@ripple_carry_subc W subc 2))
  : typeclass_instances.

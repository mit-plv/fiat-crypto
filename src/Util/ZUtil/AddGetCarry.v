Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.BreakMatch.
Local Open Scope Z_scope.

Local Notation eta x := (fst x, snd x).

Module Z.
  Section with_bitwidth.
    Context (bitwidth : Z).

    Local Notation ADD := (Z.add_get_carry bitwidth).
    Local Notation ADC := (Z.add_with_get_carry bitwidth).

    Local Arguments Z.pow : simpl never.

    Lemma add_get_carry_to_add_with_get_carry_cps_gen {T} c a b (P : Z -> Z -> Z -> Z -> Z -> T)
      : (let '(a', c1) := ADD a b in
         let '(s, c2) := ADD c a' in
         dlet c := c1 + c2 in
         P a' c1 c2 s c)
        = let '(a', c1) := eta (ADD a b) in
          let '(s, c2) := eta (ADD c a') in
          let '(s, c) := ADC c a b in
          P a' c1 c2 s c.
    Proof.
      unfold Let_In, ADD, ADC, Z.get_carry, Z.add_with_carry; simpl.
      destruct (Z_dec bitwidth 0) as [ [?|?] | ? ].
      { rewrite Z.pow_neg_r by assumption.
        autorewrite with zsimplify.
        reflexivity. }
      { f_equal.
        { push_Zmod; pull_Zmod; apply f_equal2; omega. }
        { Z.div_mod_to_quot_rem; nia. } }
      { subst; autorewrite with zsimplify; f_equal; omega. }
    Qed.

    Lemma add_get_carry_to_add_with_get_carry_cps {T} c a b (P : Z -> Z -> T)
      : (let '(a', c1) := ADD a b in
         let '(s, c2) := ADD c a' in
         dlet c := c1 + c2 in
         P s c)
        = let '(s, c) := ADC c a b in
          P s c.
    Proof.
      apply add_get_carry_to_add_with_get_carry_cps_gen.
    Qed.
  End with_bitwidth.

  Local Ltac easypeasy :=
    repeat progress autounfold;
    break_match; autorewrite with cancel_pair zsimplify;
    solve [repeat (f_equal; try ring)].

  Local Hint Unfold Z.get_carry Z.get_borrow
        Z.add_get_carry_full Z.add_with_get_carry_full
        Z.add_get_carry Z.add_with_get_carry Z.add_with_carry
        Z.sub_get_borrow_full Z.sub_with_get_borrow_full
        Z.sub_get_borrow Z.sub_with_get_borrow Z.sub_with_borrow.

  Lemma add_get_carry_full_mod s x y :
    fst (Z.add_get_carry_full s x y)  = (x + y) mod s.
  Proof. easypeasy. Qed.

  Lemma add_get_carry_full_div s x y :
    snd (Z.add_get_carry_full s x y)  = (x + y) / s.
  Proof. easypeasy. Qed.

  Lemma add_with_get_carry_full_mod s c x y :
    fst (Z.add_with_get_carry_full s c x y)  = (c + x + y) mod s.
  Proof. easypeasy. Qed.

  Lemma add_with_get_carry_full_div s c x y :
    snd (Z.add_with_get_carry_full s c x y)  = (c + x + y) / s.
  Proof. easypeasy. Qed.

  Lemma sub_with_borrow_to_add_get_carry c x y
    : Z.sub_with_borrow c x y = Z.add_with_carry (-c) x (-y).
  Proof. reflexivity. Qed.

  Lemma sub_get_borrow_full_mod s x y :
    fst (Z.sub_get_borrow_full s x y)  = (x - y) mod s.
  Proof. easypeasy. Qed.

  Lemma sub_get_borrow_full_div s x y :
    snd (Z.sub_get_borrow_full s x y)  = - ((x - y) / s).
  Proof. easypeasy. Qed.

  Lemma sub_with_get_borrow_full_mod s c x y :
    fst (Z.sub_with_get_borrow_full s c x y)  = (x - y - c) mod s.
  Proof. easypeasy. Qed.

  Lemma sub_with_get_borrow_full_div s c x y :
    snd (Z.sub_with_get_borrow_full s c x y)  = - ((x - y - c) / s).
  Proof. easypeasy. Qed.

End Z.

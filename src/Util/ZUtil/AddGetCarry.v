Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Hints.ZArith.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.LetIn.
Local Open Scope Z_scope.

Local Notation eta x := (fst x, snd x).

Module Z.
  Section with_bitwidth.
    Context (bitwidth : Z).

    Local Notation ADD := (Z.add_get_carry bitwidth).
    Local Notation ADC := (Z.add_with_get_carry bitwidth).

    Local Arguments Z.pow : simpl never.

    Lemma add_get_carry_to_add_with_get_carry_cps_gen {T} c a b (P : Z -> Z -> Z -> Z -> Z -> T)
      : (let '(a', c1) := ADD c a in
         let '(s, c2) := ADD a' b in
         dlet c := c1 + c2 in
         P a' c1 c2 s c)
        = let '(a', c1) := eta (ADD c a) in
          let '(s, c2) := eta (ADD a' b) in
          let '(s, c) := ADC c a b in
          P a' c1 c2 s c.
    Proof.
      unfold Let_In, ADD, ADC, Z.get_carry, Z.add_with_carry; simpl.
      destruct (Z_dec bitwidth 0) as [ [?|?] | ? ].
      { rewrite Z.pow_neg_r by assumption.
        autorewrite with zsimplify.
        reflexivity. }
      { f_equal.
        { push_Zmod; reflexivity. }
        { Z.div_mod_to_quot_rem; nia. } }
      { subst; autorewrite with zsimplify; reflexivity. }
    Qed.

    Lemma add_get_carry_to_add_with_get_carry_cps {T} c a b (P : Z -> Z -> T)
      : (let '(a', c1) := ADD c a in
         let '(s, c2) := ADD a' b in
         dlet c := c1 + c2 in
         P s c)
        = let '(s, c) := ADC c a b in
          P s c.
    Proof.
      apply add_get_carry_to_add_with_get_carry_cps_gen.
    Qed.
  End with_bitwidth.
End Z.

Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil Crypto.Util.ZUtil Crypto.Util.NatUtil.
Require Import Crypto.BaseSystem Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.Pow2Base Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.omega.Omega Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.micromega.Psatz.
Require Coq.Arith.Arith.
Import Nat.
Local Open Scope Z.

Section Testbit.
  Context {width : Z} (limb_width_pos : 0 < width).
  Context (limb_widths : list Z) (limb_widths_nonnil : limb_widths <> nil)
    (limb_widths_uniform : forall w, In w limb_widths -> w = width).
  Local Notation "{base}" := (base_from_limb_widths limb_widths).

  Definition testbit (us : list Z) (n : nat) :=
    Z.testbit (nth_default 0 us (n / (Z.to_nat width))) (Z.of_nat (n mod Z.to_nat width)%nat).

  Local Hint Resolve (uniform_limb_widths_nonneg limb_width_pos _ limb_widths_uniform).

  Lemma testbit_spec' : forall a b us, (0 <= b < width) ->
    bounded limb_widths us -> (length us <= length limb_widths)%nat ->
    Z.testbit (nth_default 0 us a) b = Z.testbit (decode {base} us) (Z.of_nat a * width + b).
  Proof.
    induction a; destruct us; intros;
      match goal with H : bounded _ _ |- _ =>
        erewrite bounded_uniform in H by (omega || eauto) end;
      rewrite ?Z.mul_0_l, ?Z.add_0_l, ?nth_default_nil, ?decode_nil,
              ?nth_default_cons, ?decode_shift, ?Z.testbit_0_l by eauto;
      try reflexivity.
    + rewrite Z.testbit_add_shiftl_low by omega; reflexivity.
    + rewrite nth_default_cons_S, Nat2Z.inj_succ.
      rewrite Z.testbit_add_shiftl_high by (nia || auto using in_eq).
      replace (Z.succ (Z.of_nat a) * width + b - width) with (Z.of_nat a * width + b) by ring.
      apply IHa; erewrite ?bounded_uniform; eauto using in_cons;
        simpl in *; omega.
  Qed.

  Hint Rewrite div_add_l' mod_add_l mod_add_l' mod_div_eq0 add_0_r mod_mod : nat_mod_div.

  Lemma testbit_spec : forall n us, (length us = length limb_widths)%nat ->
    bounded limb_widths us ->
    testbit us n = Z.testbit (BaseSystem.decode {base} us) (Z.of_nat n).
  Proof.
    cbv [testbit]; intros.
    pose proof limb_width_pos as limb_width_pos_nat.
    rewrite Z2Nat.inj_lt in limb_width_pos_nat by omega.
    rewrite (Nat.div_mod n (Z.to_nat width)) by omega.
    autorewrite with nat_mod_div; try omega.
    rewrite testbit_spec' by (rewrite ?mod_Zmod, ?Z2Nat.id; try apply Z.mod_pos_bound; omega || auto).
    f_equal.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z2Nat.id; ring || omega.
  Qed.

End Testbit.
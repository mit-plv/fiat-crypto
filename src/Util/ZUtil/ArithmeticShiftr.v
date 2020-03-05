Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Div.
Local Open Scope Z_scope.

Section Z.
  (* note that this is only true since coq integer division rounds towards -infinity *)
  Lemma arithmetic_shiftr_small m a
        (Ha : - 2 ^ (m - 1) <= a < 2 ^ (m - 1))
        (Hm : 0 < m) :
    Z.arithmetic_shiftr m a = a / 2.
  Proof.
    unfold Z.arithmetic_shiftr. rewrite Z.shiftr_div_pow2, Z.pow_1_r; try lia.
    destruct (Z_dec 1 m) as [[]|]. 
    - destruct (Z.leb_spec 0 a) as [H|H].
      + now rewrite Z.land_pow2_small, Z.lor_0_l. 
      + rewrite Z.land_pow2_small_neg; try lia.
        rewrite Z.lor_small_neg; try lia. split.
        apply Zdiv_le_lower_bound; lia.
        apply Zdiv_lt_upper_bound; lia.  
    - lia.
    - subst; simpl in *.
      destruct (Z_dec a 0) as [[]|]; subst; try lia; try reflexivity.
      destruct (Z_dec a (-1)) as [[]|]; subst; try lia; reflexivity. Qed.

  Lemma arithmetic_shiftr_large m a
        (Ha : 2 ^ (m - 1) <= a < 2 ^ m)
        (Hm : 0 < m) :
    Z.arithmetic_shiftr m a = a / 2 + 2 ^ (m - 1).
  Proof.
    assert (0 < 2 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia).
    unfold Z.arithmetic_shiftr.
    rewrite Z.land_pow2_testbit, Z.testbit_large, <- Z.div2_spec, Z.div2_div, Z.lor_add; try lia.
    rewrite Z.land_comm, Z.land_div2; try lia. 
    rewrite Z.sub_simpl_r; lia. Qed.

  (* twos complement evaluation *)
  Local Notation twos_complement m a :=
    (if ((a mod 2 ^ m) <? 2 ^ (m - 1)) then a mod 2 ^ m else a mod 2 ^ m - 2 ^ m).

  Lemma arithmetic_shiftr_spec m a
        (Hm : 0 < m)
        (Ha : 0 <= a < 2 ^ m) :
    twos_complement m (Z.arithmetic_shiftr m a) = (twos_complement m a) / 2.
  Proof.
    rewrite (Z.mod_small a) by lia.
    assert (0 <= a / 2 < 2 ^ (m - 1)).
    { split.
      apply Zdiv_le_lower_bound; lia. 
      apply Zdiv_lt_upper_bound; try lia. rewrite Z.mul_comm, Pow.Z.pow_mul_base, Z.sub_simpl_r; lia. }
    
    destruct (a <? 2 ^ (m - 1)) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
    - rewrite arithmetic_shiftr_small, Z.mod_small; try lia.
      assert (a / 2 <? 2 ^ (m - 1) = true).
      { apply Z.ltb_lt; apply Zdiv_lt_upper_bound; lia. } 
      rewrite H0; lia.
      split.
      + apply Zdiv_le_lower_bound; lia. 
      + apply Zdiv_lt_upper_bound; lia. 
    - rewrite arithmetic_shiftr_large, Z.mod_small; try lia.
      assert (a / 2 + 2 ^ (m - 1) <? 2 ^ (m - 1) = false).
      { apply Z.ltb_ge; lia. }
      rewrite H0. unfold Z.sub at 3.
      replace (- 2 ^ m) with (2 ^ m * (-1)) by ring.
      rewrite Z.div2_split by lia. 
      replace (-1 mod 2) with 1 by reflexivity.
      replace (-1 / 2) with (-1) by reflexivity; lia. 
      
      replace (2 ^ m) with (2 * 2 ^ (m - 1)); try lia.
      rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia. Qed.
End Z.

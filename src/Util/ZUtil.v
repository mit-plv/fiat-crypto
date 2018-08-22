Require Import Coq.ZArith.Zpower Coq.ZArith.Znumtheory Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Coq.Structures.Equalities.
Require Import Coq.omega.Omega Coq.micromega.Psatz Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.Contains.
Require Import Crypto.Util.Tactics.Not.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Notations.
Require Import Coq.Lists.List.
Require Import Crypto.Util.NUtil.WithoutReferenceToZ.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.ZUtil.Definitions.
Require Export Crypto.Util.ZUtil.Div.
Require Export Crypto.Util.ZUtil.Divide.
Require Export Crypto.Util.ZUtil.DistrIf.
Require Export Crypto.Util.ZUtil.Le.
Require Export Crypto.Util.ZUtil.Log2.
Require Export Crypto.Util.ZUtil.EquivModulo.
Require Export Crypto.Util.ZUtil.Hints.
Require Export Crypto.Util.ZUtil.Land.
Require Export Crypto.Util.ZUtil.Lnot.
Require Export Crypto.Util.ZUtil.Modulo.
Require Export Crypto.Util.ZUtil.Modulo.PullPush.
Require Export Crypto.Util.ZUtil.Morphisms.
Require Export Crypto.Util.ZUtil.Mul.
Require Export Crypto.Util.ZUtil.N2Z.
Require Export Crypto.Util.ZUtil.Notations.
Require Export Crypto.Util.ZUtil.Odd.
Require Export Crypto.Util.ZUtil.Ones.
Require Export Crypto.Util.ZUtil.Pow.
Require Export Crypto.Util.ZUtil.Pow2.
Require Export Crypto.Util.ZUtil.Pow2Mod.
Require Export Crypto.Util.ZUtil.Quot.
Require Export Crypto.Util.ZUtil.Sgn.
Require Export Crypto.Util.ZUtil.Shift.
Require Export Crypto.Util.ZUtil.Tactics.
Require Export Crypto.Util.ZUtil.Testbit.
Require Export Crypto.Util.ZUtil.Z2Nat.
Require Export Crypto.Util.ZUtil.ZSimplify.
Import Nat.
Local Open Scope Z.

Module Z.
  Lemma mul_div_le x y z
        (Hx : 0 <= x) (Hy : 0 <= y) (Hz : 0 < z)
        (Hyz : y <= z)
    : x * y / z <= x.
  Proof.
    transitivity (x * z / z); [ | rewrite Z.div_mul by lia; lia ].
    apply Z_div_le; nia.
  Qed.
  Hint Resolve mul_div_le : zarith.

  Lemma div_mul_diff_exact a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : c * a / b = c * (a / b) + (c * (a mod b)) / b.
  Proof.
    rewrite (Z_div_mod_eq a b) at 1 by lia.
    rewrite Z.mul_add_distr_l.
    replace (c * (b * (a / b))) with ((c * (a / b)) * b) by lia.
    rewrite Z.div_add_l by lia.
    lia.
  Qed.

  Lemma div_mul_diff_exact' a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : c * (a / b) = c * a / b - (c * (a mod b)) / b.
  Proof.
    rewrite div_mul_diff_exact by assumption; lia.
  Qed.

  Lemma div_mul_diff_exact'' a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : a * c / b = (a / b) * c + (c * (a mod b)) / b.
  Proof.
    rewrite (Z.mul_comm a c), div_mul_diff_exact by lia; lia.
  Qed.

  Lemma div_mul_diff_exact''' a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : (a / b) * c = a * c / b - (c * (a mod b)) / b.
  Proof.
    rewrite (Z.mul_comm a c), div_mul_diff_exact by lia; lia.
  Qed.

  Lemma div_mul_diff a b c
        (Ha : 0 <= a) (Hb : 0 < b) (Hc : 0 <= c)
    : c * a / b - c * (a / b) <= c.
  Proof.
    rewrite div_mul_diff_exact by assumption.
    ring_simplify; auto with zarith.
  Qed.

  Lemma div_mul_le_le a b c
    :  0 <= a -> 0 < b -> 0 <= c -> c * (a / b) <= c * a / b <= c * (a / b) + c.
  Proof.
    pose proof (Z.div_mul_diff a b c); split; try apply Z.div_mul_le; lia.
  Qed.

  Lemma div_mul_le_le_offset a b c
    : 0 <= a -> 0 < b -> 0 <= c -> c * a / b - c <= c * (a / b).
  Proof.
    pose proof (Z.div_mul_le_le a b c); lia.
  Qed.

  Hint Resolve Zmult_le_compat_r Zmult_le_compat_l Z_div_le Z.div_mul_le_le_offset Z.add_le_mono Z.sub_le_mono : zarith.

  Lemma div_x_y_x x y : 0 < x -> 0 < y -> x / y / x = 1 / y.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm y x), <- Z.div_div, Z.div_same by lia.
    reflexivity.
  Qed.

  Hint Rewrite div_x_y_x using zutil_arith : zsimplify.

  Lemma mod_opp_l_z_iff a b (H : b <> 0) : a mod b = 0 <-> (-a) mod b = 0.
  Proof.
    split; intro H'; apply Z.mod_opp_l_z in H'; rewrite ?Z.opp_involutive in H'; assumption.
  Qed.

  Lemma opp_eq_0_iff a : -a = 0 <-> a = 0.
  Proof. omega. Qed.

  Hint Rewrite <- mod_opp_l_z_iff using zutil_arith : zsimplify.
  Hint Rewrite opp_eq_0_iff : zsimplify.

  Lemma sub_pos_bound a b X : 0 <= a < X -> 0 <= b < X -> -X < a - b < X.
  Proof. lia. Qed.

  Lemma shiftl_opp_l a n
    : Z.shiftl (-a) n = - Z.shiftl a n - (if Z_zerop (a mod 2 ^ (- n)) then 0 else 1).
  Proof.
    destruct (Z_dec 0 n) as [ [?|?] | ? ];
      subst;
      rewrite ?Z.pow_neg_r by omega;
      autorewrite with zsimplify_const;
      [ | | simpl; omega ].
    { rewrite !Z.shiftl_mul_pow2 by omega.
      nia. }
    { rewrite !Z.shiftl_div_pow2 by omega.
      rewrite Z.div_opp_l_complete by auto with zarith.
      reflexivity. }
  Qed.
  Hint Rewrite shiftl_opp_l : push_Zshift.
  Hint Rewrite <- shiftl_opp_l : pull_Zshift.

  Lemma shiftr_opp_l a n
    : Z.shiftr (-a) n = - Z.shiftr a n - (if Z_zerop (a mod 2 ^ n) then 0 else 1).
  Proof.
    unfold Z.shiftr; rewrite shiftl_opp_l at 1; rewrite Z.opp_involutive.
    reflexivity.
  Qed.
  Hint Rewrite shiftr_opp_l : push_Zshift.
  Hint Rewrite <- shiftr_opp_l : pull_Zshift.

  Lemma sub_pos_bound_div a b X : 0 <= a < X -> 0 <= b < X -> -1 <= (a - b) / X <= 0.
  Proof.
    intros H0 H1; pose proof (Z.sub_pos_bound a b X H0 H1).
    assert (Hn : -X <= a - b) by lia.
    assert (Hp : a - b <= X - 1) by lia.
    split; etransitivity; [ | apply Z_div_le, Hn; lia | apply Z_div_le, Hp; lia | ];
      instantiate; autorewrite with zsimplify; try reflexivity.
  Qed.

  Hint Resolve (fun a b X H0 H1 => proj1 (Z.sub_pos_bound_div a b X H0 H1))
       (fun a b X H0 H1 => proj1 (Z.sub_pos_bound_div a b X H0 H1)) : zarith.

  Lemma sub_pos_bound_div_eq a b X : 0 <= a < X -> 0 <= b < X -> (a - b) / X = if a <? b then -1 else 0.
  Proof.
    intros H0 H1; pose proof (Z.sub_pos_bound_div a b X H0 H1).
    destruct (a <? b) eqn:?; Z.ltb_to_lt.
    { cut ((a - b) / X <> 0); [ lia | ].
      autorewrite with zstrip_div; auto with zarith lia. }
    { autorewrite with zstrip_div; auto with zarith lia. }
  Qed.

  Lemma add_opp_pos_bound_div_eq a b X : 0 <= a < X -> 0 <= b < X -> (-b + a) / X = if a <? b then -1 else 0.
  Proof.
    rewrite !(Z.add_comm (-_)), !Z.add_opp_r.
    apply Z.sub_pos_bound_div_eq.
  Qed.

  Hint Rewrite Z.sub_pos_bound_div_eq Z.add_opp_pos_bound_div_eq using zutil_arith : zstrip_div.

  Lemma div_small_sym a b : 0 <= a < b -> 0 = a / b.
  Proof. intros; symmetry; apply Z.div_small; assumption. Qed.

  Lemma mod_small_sym a b : 0 <= a < b -> a = a mod b.
  Proof. intros; symmetry; apply Z.mod_small; assumption. Qed.

  Hint Resolve div_small_sym mod_small_sym : zarith.

  Lemma mod_eq_le_to_eq a b : 0 < a <= b -> a mod b = 0 -> a = b.
  Proof.
    intros H H'.
    assert (a = b * (a / b)) by auto with zarith lia.
    assert (a / b = 1) by nia.
    nia.
  Qed.
  Hint Resolve mod_eq_le_to_eq : zarith.

  Lemma mod_eq_le_div_1 a b : 0 < a <= b -> a mod b = 0 -> a / b = 1.
  Proof. auto with zarith. Qed.
  Hint Resolve mod_eq_le_div_1 : zarith.
  Hint Rewrite mod_eq_le_div_1 using zutil_arith : zsimplify.

  Lemma mod_neq_0_le_to_neq a b : a mod b <> 0 -> a <> b.
  Proof. repeat intro; subst; autorewrite with zsimplify in *; lia. Qed.
  Hint Resolve mod_neq_0_le_to_neq : zarith.

  Lemma div_small_neg x y : 0 < -x <= y -> x / y = -1.
  Proof.
    intro H; rewrite <- (Z.opp_involutive x).
    rewrite Z.div_opp_l_complete by lia.
    generalize dependent (-x); clear x; intros x H.
    pose proof (mod_neq_0_le_to_neq x y).
    autorewrite with zsimplify; edestruct Z_zerop; autorewrite with zsimplify in *; lia.
  Qed.
  Hint Rewrite div_small_neg using zutil_arith : zsimplify.

  Lemma div_sub_small x y z : 0 <= x < z -> 0 <= y <= z -> (x - y) / z = if x <? y then -1 else 0.
  Proof.
    pose proof (Zlt_cases x y).
    (destruct (x <? y) eqn:?);
      intros; autorewrite with zsimplify; try lia.
  Qed.
  Hint Rewrite div_sub_small using zutil_arith : zsimplify.

  Lemma mul_div_lt_by_le x y z b : 0 <= y < z -> 0 <= x < b -> x * y / z < b.
  Proof.
    intros [? ?] [? ?]; eapply Z.le_lt_trans; [ | eassumption ].
    auto with zarith.
  Qed.
  Hint Resolve mul_div_lt_by_le : zarith.

  Definition pow_sub_r'
    := fun a b c y H0 H1 => @Logic.eq_trans _ _ _ y (@Z.pow_sub_r a b c H0 H1).
  Definition pow_sub_r'_sym
    := fun a b c y p H0 H1 => Logic.eq_sym (@Logic.eq_trans _ y _ _ (Logic.eq_sym p) (@Z.pow_sub_r a b c H0 H1)).
  Hint Resolve pow_sub_r' pow_sub_r'_sym Z.eq_le_incl : zarith.
  Hint Resolve (fun b => f_equal (fun e => b ^ e)) (fun e => f_equal (fun b => b ^ e)) : zarith.
  Definition mul_div_le'
    := fun x y z w p H0 H1 H2 H3 => @Z.le_trans _ _ w (@Z.mul_div_le x y z H0 H1 H2 H3) p.
  Hint Resolve mul_div_le' : zarith.
  Lemma mul_div_le'' x y z w : y <= w -> 0 <= x -> 0 <= y -> 0 < z -> x <= z -> x * y / z <= w.
  Proof.
    rewrite (Z.mul_comm x y); intros; apply mul_div_le'; assumption.
  Qed.
  Hint Resolve mul_div_le'' : zarith.

  Lemma two_p_two_eq_four : 2^(2) = 4.
  Proof. reflexivity. Qed.
  Hint Rewrite <- two_p_two_eq_four : push_Zpow.

  Lemma div_mod' a b : b <> 0 -> a = (a / b) * b + a mod b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod' using zutil_arith : zsimplify.

  Lemma div_mod'' a b : b <> 0 -> a = a mod b + b * (a / b).
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod'' using zutil_arith : zsimplify.

  Lemma div_mod''' a b : b <> 0 -> a = a mod b + (a / b) * b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod''' using zutil_arith : zsimplify.

  Lemma sub_mod_mod_0 x d : (x - x mod d) mod d = 0.
  Proof.
    destruct (Z_zerop d); subst; autorewrite with push_Zmod zsimplify; reflexivity.
  Qed.
  Hint Resolve sub_mod_mod_0 : zarith.
  Hint Rewrite sub_mod_mod_0 : zsimplify.

  Lemma div_between n a b : 0 <= n -> b <> 0 -> n * b <= a < (1 + n) * b -> a / b = n.
  Proof. intros; Z.div_mod_to_quot_rem_in_goal; nia. Qed.
  Hint Rewrite div_between using zutil_arith : zsimplify.

  Lemma mod_small_n n a b : 0 <= n -> b <> 0 -> n * b <= a < (1 + n) * b -> a mod b = a - n * b.
  Proof. intros; erewrite Zmod_eq_full, div_between by eassumption. reflexivity. Qed.
  Hint Rewrite mod_small_n using zutil_arith : zsimplify.

  Lemma div_between_1 a b : b <> 0 -> b <= a < 2 * b -> a / b = 1.
  Proof. intros; rewrite (div_between 1) by lia; reflexivity. Qed.
  Hint Rewrite div_between_1 using zutil_arith : zsimplify.

  Lemma mod_small_1 a b : b <> 0 -> b <= a < 2 * b -> a mod b = a - b.
  Proof. intros; rewrite (mod_small_n 1) by lia; lia. Qed.
  Hint Rewrite mod_small_1 using zutil_arith : zsimplify.

  Lemma div_between_if n a b : 0 <= n -> b <> 0 -> n * b <= a < (2 + n) * b -> (a / b = if (1 + n) * b <=? a then 1 + n else n)%Z.
  Proof.
    intros.
    break_match; Z.ltb_to_lt;
      apply div_between; lia.
  Qed.

  Lemma mod_small_n_if n a b : 0 <= n -> b <> 0 -> n * b <= a < (2 + n) * b -> a mod b = a - (if (1 + n) * b <=? a then (1 + n) else n) * b.
  Proof. intros; erewrite Zmod_eq_full, div_between_if by eassumption; autorewrite with zsimplify_const. reflexivity. Qed.

  Lemma div_between_0_if a b : b <> 0 -> 0 <= a < 2 * b -> a / b = if b <=? a then 1 else 0.
  Proof. intros; rewrite (div_between_if 0) by lia; autorewrite with zsimplify_const; reflexivity. Qed.

  Lemma mod_small_0_if a b : b <> 0 -> 0 <= a < 2 * b -> a mod b = a - if b <=? a then b else 0.
  Proof. intros; rewrite (mod_small_n_if 0) by lia; autorewrite with zsimplify_const. break_match; lia. Qed.

  Lemma mul_mod_distr_r_full a b c : (a * c) mod (b * c) = (a mod b * c).
  Proof.
    destruct (Z_zerop b); [ | destruct (Z_zerop c) ]; subst;
      autorewrite with zsimplify; auto using Z.mul_mod_distr_r.
  Qed.

  Lemma mul_mod_distr_l_full a b c : (c * a) mod (c * b) = c * (a mod b).
  Proof.
    destruct (Z_zerop b); [ | destruct (Z_zerop c) ]; subst;
      autorewrite with zsimplify; auto using Z.mul_mod_distr_l.
  Qed.

  Lemma lt_mul_2_mod_sub : forall a b, b <> 0 -> b <= a < 2 * b -> a mod b = a - b.
  Proof.
    intros a b H H0.
    replace (a mod b) with ((1 * b + (a - b)) mod b) by (f_equal; ring).
    rewrite Z.mod_add_l by auto.
    apply Z.mod_small.
    omega.
  Qed.

  Lemma shl_shr_lt x y n m (Hx : 0 <= x < 2^n) (Hy : 0 <= y < 2^n) (Hm : 0 <= m <= n)
    : 0 <= (x >> (n - m)) + ((y << m) mod 2^n) < 2^n.
  Proof.
    cut (0 <= (x >> (n - m)) + ((y << m) mod 2^n) <= 2^n - 1); [ omega | ].
    assert (0 <= x <= 2^n - 1) by omega.
    assert (0 <= y <= 2^n - 1) by omega.
    assert (0 < 2 ^ (n - m)) by auto with zarith.
    assert (0 <= y mod 2 ^ (n - m) < 2^(n-m)) by auto with zarith.
    assert (0 <= y mod 2 ^ (n - m) <= 2 ^ (n - m) - 1) by omega.
    assert (0 <= (y mod 2 ^ (n - m)) * 2^m <= (2^(n-m) - 1)*2^m) by auto with zarith.
    assert (0 <= x / 2^(n-m) < 2^n / 2^(n-m)).
    { split; Z.zero_bounds.
      apply Z.div_lt_upper_bound; autorewrite with pull_Zpow zsimplify; nia. }
    autorewrite with Zshift_to_pow.
    split; Z.zero_bounds.
    replace (2^n) with (2^(n-m) * 2^m) by (autorewrite with pull_Zpow; f_equal; omega).
    rewrite Zmult_mod_distr_r.
    autorewrite with pull_Zpow zsimplify push_Zmul in * |- .
    nia.
  Qed.

  Lemma add_shift_mod x y n m
        (Hx : 0 <= x < 2^n) (Hy : 0 <= y)
        (Hn : 0 <= n) (Hm : 0 < m)
    : (x + y << n) mod (m * 2^n) = x + (y mod m) << n.
  Proof.
    pose proof (Z.mod_bound_pos y m).
    specialize_by omega.
    assert (0 < 2^n) by auto with zarith.
    autorewrite with Zshift_to_pow.
    rewrite Zplus_mod, !Zmult_mod_distr_r.
    rewrite Zplus_mod, !Zmod_mod, <- Zplus_mod.
    rewrite !(Zmod_eq (_ + _)) by nia.
    etransitivity; [ | apply Z.add_0_r ].
    rewrite <- !Z.add_opp_r, <- !Z.add_assoc.
    repeat apply f_equal.
    ring_simplify.
    cut (((x + y mod m * 2 ^ n) / (m * 2 ^ n)) = 0); [ nia | ].
    apply Z.div_small; split; nia.
  Qed.

  Lemma add_mul_mod x y n m
        (Hx : 0 <= x < 2^n) (Hy : 0 <= y)
        (Hn : 0 <= n) (Hm : 0 < m)
    : (x + y * 2^n) mod (m * 2^n) = x + (y mod m) * 2^n.
  Proof.
    generalize (add_shift_mod x y n m).
    autorewrite with Zshift_to_pow; auto.
  Qed.

  Lemma lt_pow_2_shiftr : forall a n, 0 <= a < 2 ^ n -> a >> n = 0.
  Proof.
    intros a n H.
    destruct (Z_le_dec 0 n).
    + rewrite Z.shiftr_div_pow2 by assumption.
      auto using Z.div_small.
    + assert (2 ^ n = 0) by (apply Z.pow_neg_r; omega).
      omega.
  Qed.

  Hint Rewrite Z.pow2_bits_eqb using zutil_arith : Ztestbit.
  Lemma pow_2_shiftr : forall n, 0 <= n -> (2 ^ n) >> n = 1.
  Proof.
    intros; apply Z.bits_inj'; intros.
    replace 1 with (2 ^ 0) by ring.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress rewrite ?Z.eqb_eq, ?Z.eqb_neq in *
           | |- _ => progress autorewrite with Ztestbit
           | |- context[Z.eqb ?a ?b] => case_eq (Z.eqb a b)
           | |- _ => reflexivity || omega
           end.
  Qed.

  Lemma lt_mul_2_pow_2_shiftr : forall a n, 0 <= a < 2 * 2 ^ n ->
                                            a >> n = if Z_lt_dec a (2 ^ n) then 0 else 1.
  Proof.
    intros a n H; break_match; [ apply lt_pow_2_shiftr; omega | ].
    destruct (Z_le_dec 0 n).
    + replace (2 * 2 ^ n) with (2 ^ (n + 1)) in *
        by (rewrite Z.pow_add_r; try omega; ring).
      pose proof (Z.shiftr_ones a (n + 1) n H).
      pose proof (Z.shiftr_le (2 ^ n) a n).
      specialize_by omega.
      replace (n + 1 - n) with 1 in * by ring.
      replace (Z.ones 1) with 1 in * by reflexivity.
      rewrite pow_2_shiftr in * by omega.
      omega.
    + assert (2 ^ n = 0) by (apply Z.pow_neg_r; omega).
      omega.
  Qed.

  Lemma shiftr_nonneg_le : forall a n, 0 <= a -> 0 <= n -> a >> n <= a.
  Proof.
    intros.
    repeat match goal with
           | [ H : _ <= _ |- _ ]
             => rewrite Z.lt_eq_cases in H
           | [ H : _ \/ _ |- _ ] => destruct H
           | _ => progress subst
           | _ => progress autorewrite with zsimplify Zshift_to_pow
           | _ => solve [ auto with zarith omega ]
           end.
  Qed.
  Hint Resolve shiftr_nonneg_le : zarith.

  Section ZInequalities.
    Lemma land_le : forall x y, (0 <= x)%Z -> (Z.land x y <= x)%Z.
    Proof.
      intros x y H; apply Z.ldiff_le; [assumption|].
      rewrite Z.ldiff_land, Z.land_comm, Z.land_assoc.
      rewrite <- Z.land_0_l with (a := y); f_equal.
      rewrite Z.land_comm, Z.land_lnot_diag.
      reflexivity.
    Qed.

    Lemma lor_lower : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (x <= Z.lor x y)%Z.
    Proof.
      intros x y H H0; apply Z.ldiff_le; [apply Z.lor_nonneg; auto|].
      rewrite Z.ldiff_land.
      apply Z.bits_inj_iff'; intros k Hpos; apply Z.le_ge in Hpos.
      rewrite Z.testbit_0_l, Z.land_spec, Z.lnot_spec, Z.lor_spec;
        [|apply Z.ge_le; assumption].
      induction (Z.testbit x k), (Z.testbit y k); cbv; reflexivity.
    Qed.

    Lemma lor_le : forall x y z,
        (0 <= x)%Z
        -> (x <= y)%Z
        -> (y <= z)%Z
        -> (Z.lor x y <= (2 ^ Z.log2_up (z+1)) - 1)%Z.
    Proof.
      intros x y z H H0 H1; apply Z.ldiff_le.

      - apply Z.le_add_le_sub_r.
        replace 1%Z with (2 ^ 0)%Z by (cbv; reflexivity).
        rewrite Z.add_0_l.
        apply Z.pow_le_mono_r; [cbv; reflexivity|].
        apply Z.log2_up_nonneg.

      - destruct (Z_lt_dec 0 z).

        + assert (forall a, a - 1 = Z.pred a)%Z as HP by (intro; omega);
            rewrite HP, <- Z.ones_equiv; clear HP.
          apply Z.ldiff_ones_r_low; [apply Z.lor_nonneg; split; omega|].
          rewrite Z.log2_up_eqn, Z.log2_lor; try omega.
          apply Z.lt_succ_r.
          apply Z.max_case_strong; intros; apply Z.log2_le_mono; omega.

        + replace z with 0%Z by omega.
          replace y with 0%Z by omega.
          replace x with 0%Z by omega.
          cbv; reflexivity.
    Qed.

    Local Ltac solve_pow2 :=
      repeat match goal with
             | [|- _ /\ _] => split
             | [|- (0 < 2 ^ _)%Z] => apply Z.pow2_gt_0
             | [|- (0 <= 2 ^ _)%Z] => apply Z.pow2_ge_0
             | [|- (2 ^ _ <= 2 ^ _)%Z] => apply Z.pow_le_mono_r
             | [|- (_ <= _)%Z] => omega
             | [|- (_ < _)%Z] => omega
             end.

    Lemma pow2_mod_range : forall a n m,
        (0 <= n) ->
        (n <= m) ->
        (0 <= Z.pow2_mod a n < 2 ^ m).
    Proof.
      intros; unfold Z.pow2_mod.
      rewrite Z.land_ones; [|assumption].
      split; [apply Z.mod_pos_bound, Z.pow2_gt_0; assumption|].
      eapply Z.lt_le_trans; [apply Z.mod_pos_bound, Z.pow2_gt_0; assumption|].
      apply Z.pow_le_mono; [|assumption].
      split; simpl; omega.
    Qed.

    Lemma shiftr_range : forall a n m,
        (0 <= n)%Z ->
        (0 <= m)%Z ->
        (0 <= a < 2 ^ (n + m))%Z ->
        (0 <= Z.shiftr a n < 2 ^ m)%Z.
    Proof.
      intros a n m H0 H1 H2; destruct H2.
      split; [apply Z.shiftr_nonneg; assumption|].
      rewrite Z.shiftr_div_pow2; [|assumption].
      apply Z.div_lt_upper_bound; [apply Z.pow2_gt_0; assumption|].
      eapply Z.lt_le_trans; [eassumption|apply Z.eq_le_incl].
      apply Z.pow_add_r; omega.
    Qed.


    Lemma shiftr_le_mono: forall a b c d,
        (0 <= a)%Z
        -> (0 <= d)%Z
        -> (a <= c)%Z
        -> (d <= b)%Z
        -> (Z.shiftr a b <= Z.shiftr c d)%Z.
    Proof.
      intros.
      repeat rewrite Z.shiftr_div_pow2; [|omega|omega].
      etransitivity; [apply Z.div_le_compat_l | apply Z.div_le_mono]; solve_pow2.
    Qed.

    Lemma shiftl_le_mono: forall a b c d,
        (0 <= a)%Z
        -> (0 <= b)%Z
        -> (a <= c)%Z
        -> (b <= d)%Z
        -> (Z.shiftl a b <= Z.shiftl c d)%Z.
    Proof.
      intros.
      repeat rewrite Z.shiftl_mul_pow2; [|omega|omega].
      etransitivity; [apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonneg_r]; solve_pow2.
    Qed.
  End ZInequalities.

  Lemma lor_bounds x y : 0 <= x -> 0 <= y
                         -> Z.max x y <= Z.lor x y <= 2^Z.log2_up (Z.max x y + 1) - 1.
  Proof.
    apply Z.max_case_strong; intros; split;
      try solve [ eauto using lor_lower, Z.le_trans, lor_le with omega
                | rewrite Z.lor_comm; eauto using lor_lower, Z.le_trans, lor_le with omega ].
  Qed.
  Lemma lor_bounds_lower x y : 0 <= x -> 0 <= y
                               -> Z.max x y <= Z.lor x y.
  Proof. intros; apply lor_bounds; assumption. Qed.
  Lemma lor_bounds_upper x y : Z.lor x y <= 2^Z.log2_up (Z.max x y + 1) - 1.
  Proof.
    pose proof (proj2 (Z.lor_neg x y)).
    destruct (Z_lt_le_dec x 0), (Z_lt_le_dec y 0);
      try solve [ intros; apply lor_bounds; assumption ];
      transitivity (2^0-1);
      try apply Z.sub_le_mono_r, Z.pow_le_mono_r, Z.log2_up_nonneg;
      simpl; omega.
  Qed.
  Lemma lor_bounds_gen_lower x y l : 0 <= x -> 0 <= y -> l <= Z.max x y
                                     -> l <= Z.lor x y.
  Proof.
    intros; etransitivity;
      solve [ apply lor_bounds; auto
            | eauto ].
  Qed.
  Lemma lor_bounds_gen_upper x y u : x <= u -> y <= u
                                     -> Z.lor x y <= 2^Z.log2_up (u + 1) - 1.
  Proof.
    intros; etransitivity; [ apply lor_bounds_upper | ].
    apply Z.sub_le_mono_r, Z.pow_le_mono_r, Z.log2_up_le_mono, Z.max_case_strong;
      omega.
  Qed.
  Lemma lor_bounds_gen x y l u : 0 <= x -> 0 <= y -> l <= Z.max x y -> x <= u -> y <= u
                                 -> l <= Z.lor x y <= 2^Z.log2_up (u + 1) - 1.
  Proof. auto using lor_bounds_gen_lower, lor_bounds_gen_upper. Qed.

  Lemma shiftl_le_Proper2 y
    : Proper (Z.le ==> Z.le) (fun x => Z.shiftl x y).
  Proof.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 y) as Hx.
    intros x x' H.
    pose proof (Zle_cases 0 x) as Hy.
    pose proof (Zle_cases 0 x') as Hy'.
    destruct (0 <=? y), (0 <=? x), (0 <=? x');
      autorewrite with Zshift_to_pow;
      Z.replace_all_neg_with_pos;
      autorewrite with pull_Zopp;
      rewrite ?Z.div_opp_l_complete;
      repeat destruct (Z_zerop _);
      autorewrite with zsimplify_const pull_Zopp;
      auto with zarith;
      repeat match goal with
             | [ |- context[-?x - ?y] ]
               => replace (-x - y) with (-(x + y)) by omega
             | _ => rewrite <- Z.opp_le_mono
             | _ => rewrite <- Z.add_le_mono_r
             | _ => solve [ auto with zarith ]
             | [ |- ?x <= ?y + 1 ]
               => cut (x <= y); [ omega | solve [ auto with zarith ] ]
             | [ |- -_ <= _ ]
               => solve [ transitivity (-0); auto with zarith ]
             end.
    { repeat match goal with H : context[_ mod _] |- _ => revert H end;
        Z.div_mod_to_quot_rem_in_goal; nia. }
  Qed.

  Lemma shiftl_le_Proper1 x
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
    : Proper (R (0 <=? x) ==> Z.le) (Z.shiftl x).
  Proof.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 x) as Hx.
    intros y y' H.
    pose proof (Zle_cases 0 y) as Hy.
    pose proof (Zle_cases 0 y') as Hy'.
    destruct (0 <=? x), (0 <=? y), (0 <=? y'); subst R; cbv beta iota in *;
      autorewrite with Zshift_to_pow;
      Z.replace_all_neg_with_pos;
      autorewrite with pull_Zopp;
      rewrite ?Z.div_opp_l_complete;
      repeat destruct (Z_zerop _);
      autorewrite with zsimplify_const pull_Zopp;
      auto with zarith;
      repeat match goal with
             | [ |- context[-?x - ?y] ]
               => replace (-x - y) with (-(x + y)) by omega
             | _ => rewrite <- Z.opp_le_mono
             | _ => rewrite <- Z.add_le_mono_r
             | _ => solve [ auto with zarith ]
             | [ |- ?x <= ?y + 1 ]
               => cut (x <= y); [ omega | solve [ auto with zarith ] ]
             | [ |- context[2^?x] ]
               => lazymatch goal with
                  | [ H : 1 < 2^x |- _ ] => fail
                  | [ H : 0 < 2^x |- _ ] => fail
                  | [ H : 0 <= 2^x |- _ ] => fail
                  | _ => first [ assert (1 < 2^x) by auto with zarith
                               | assert (0 < 2^x) by auto with zarith
                               | assert (0 <= 2^x) by auto with zarith ]
                  end
             | [ H : ?x <= ?y |- _ ]
               => is_var x; is_var y;
                    lazymatch goal with
                    | [ H : 2^x <= 2^y |- _ ] => fail
                    | [ H : 2^x < 2^y |- _ ] => fail
                    | _ => assert (2^x <= 2^y) by auto with zarith
                    end
             | [ H : ?x <= ?y, H' : ?f ?x = ?k, H'' : ?f ?y <> ?k |- _ ]
               => let Hn := fresh in
                  assert (Hn : x <> y) by congruence;
                    assert (x < y) by omega; clear H Hn
             | [ H : ?x <= ?y, H' : ?f ?x <> ?k, H'' : ?f ?y = ?k |- _ ]
               => let Hn := fresh in
                  assert (Hn : x <> y) by congruence;
                    assert (x < y) by omega; clear H Hn
             | _ => solve [ repeat match goal with H : context[_ mod _] |- _ => revert H end;
                            Z.div_mod_to_quot_rem_in_goal; subst;
                            lazymatch goal with
                            | [ |- _ <= (?a * ?q + ?r) * ?q' ]
                              => transitivity (q * (a * q') + r * q');
                                 [ assert (0 < a * q') by nia; nia
                                 | nia ]
                            end ]
             end.
    { replace y' with (y + (y' - y)) by omega.
      rewrite Z.pow_add_r, <- Zdiv_Zdiv by auto with zarith.
      assert (y < y') by (assert (y <> y') by congruence; omega).
      assert (1 < 2^(y'-y)) by auto with zarith.
      assert (0 < x / 2^y)
        by (repeat match goal with H : context[_ mod _] |- _ => revert H end;
            Z.div_mod_to_quot_rem_in_goal; nia).
      assert (2^y <= x)
        by (repeat match goal with H : context[_ / _] |- _ => revert H end;
            Z.div_mod_to_quot_rem_in_goal; nia).
      match goal with
      | [ |- ?x + 1 <= ?y ] => cut (x < y); [ omega | ]
      end.
      auto with zarith. }
  Qed.

  Lemma shiftr_le_Proper2 y
    : Proper (Z.le ==> Z.le) (fun x => Z.shiftr x y).
  Proof. apply shiftl_le_Proper2. Qed.

  Lemma shiftr_le_Proper1 x
        (R := fun b : bool => if b then Z.le else Basics.flip Z.le)
    : Proper (R (x <? 0) ==> Z.le) (Z.shiftr x).
  Proof.
    subst R; intros y y' H'; unfold Z.shiftr; apply shiftl_le_Proper1.
    unfold Basics.flip in *.
    pose proof (Zle_cases 0 x).
    pose proof (Zlt_cases x 0).
    destruct (0 <=? x), (x <? 0); try omega.
  Qed.
End Z.

Module Export BoundsTactics.
  Ltac prime_bound := Z.prime_bound.
  Ltac zero_bounds := Z.zero_bounds.
End BoundsTactics.

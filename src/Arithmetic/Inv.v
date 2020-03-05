Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.nsatz.Nsatz.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.WordByWordMontgomery.

Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.TruncatingShiftl.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Testbit.
Require Import Crypto.Util.ZUtil.Shift.
Require Import Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Lor.
Require Import Crypto.Util.ZUtil.Land.
Require Import Crypto.Util.ZUtil.ArithmeticShiftr.

Import Positional.
Import ListNotations.
Import Definitions.

(** An implementation of the divsteps2 algorithm from "Fast constant-time gcd computation and modular inversion."
   by D. J. Bernstein et al. See the file inversion-c/readme.txt for generation of C-code.
   For a C-implementation using this generated code to implement modular inversion, see inversion-c/test-inversion.c. **)

Local Coercion Z.of_nat : nat >-> Z.

Local Open Scope Z_scope.

(************* *)
(**Definitions *)
(************* *)

(*twos complement evaluation *)
Notation twosc m a :=
  (if ((a mod 2 ^ m) <? 2 ^ (m - 1)) then a mod 2 ^ m else a mod 2 ^ m - 2 ^ m).

(*Custom evaluation function for multi-limbg twos complement *)
Definition eval_twosc machine_wordsize n f :=
  twosc (machine_wordsize * Z.of_nat n) (eval (uweight machine_wordsize) n f).

(*Saturated addition of multi-limb integers *)
Local Definition sat_add machine_wordsize n f g :=
  fst (Rows.add (uweight machine_wordsize) n f g).

(*Saturated (logical) right shift *)
Definition sat_shiftr machine_wordsize n f :=
  (map
    (fun i =>
       Z.lor (Z.shiftr (nth_default 0 f i) 1)
             (Z.truncating_shiftl machine_wordsize
                           (nth_default 0 f (S i))
                           (machine_wordsize - 1)))
    (seq 0 (n - 1))) ++ [(nth_default 0 f (n - 1)) >> 1].

(* arithmetic right shift of saturated multi-limb integers *)
Definition sat_arithmetic_shiftr machine_wordsize n f :=
  (map
     (fun i =>
        ((nth_default 0 f i) >> 1) |' (Z.truncating_shiftl machine_wordsize
                                                    (nth_default 0 f (i + 1))
                                                    (machine_wordsize - 1)))
     (seq 0 (n - 1)))
    ++ [Z.arithmetic_shiftr machine_wordsize (nth_default 0 f (n - 1))].

(* Multi-limb parity check *)
Definition sat_mod2 f :=
  nth_default 0 f 0 mod 2.

Local Notation sat_one machine_wordsize n := (encode_no_reduce (uweight machine_wordsize) n 1).

Definition sat_opp machine_wordsize n f :=
  sat_add machine_wordsize n
          (sat_one machine_wordsize n)
          (map (fun i => Z.lnot_modulo i (2^machine_wordsize)) f).

Definition sat_zero n :=
  repeat 0 n.
  (* encode_no_reduce (uweight machine_wordsize) n 0. *)

(************************************************* *)
(**Lemmas about the twos complement representation *)
(************************************************* *)

Lemma twosc_one m (Hm : 1 < m) :
  twosc m 1 = 1.
Proof.
  assert (1 < 2 ^ m) by (apply Zpow_facts.Zpower_gt_1; lia).
  assert (1 < 2 ^ (m - 1)) by (apply Zpow_facts.Zpower_gt_1; lia).
  apply Z.ltb_lt in H0. rewrite Z.mod_small, H0; lia. Qed.

Lemma twosc_zero m (Hm : 0 < m):
  twosc m 0 = 0.
Proof.
  assert (0 <? 2 ^ (m - 1) = true).
  apply Z.ltb_lt; auto with zarith.
  rewrite Z.mod_0_l by auto with zarith.
  rewrite H; reflexivity. Qed.

Lemma twosc_mod a m (Hm : 0 < m) :
  twosc m (a mod 2 ^ m) = twosc m a.
Proof. rewrite Z.mod_mod; try apply Z.pow_nonzero; lia. Qed.

Lemma twosc_odd m a (Hm : 0 < m) : Z.odd (twosc m a) = Z.odd a.
Proof.
  destruct (a mod 2 ^m <? 2 ^ (m - 1));
    simpl;
    [ | unfold Z.sub; rewrite Z.odd_add_even];
    rewrite ?Zodd_mod, <- ?(Znumtheory.Zmod_div_mod);
    try (apply Z.pow_pos_nonneg; lia);
    try (apply Zpow_facts.Zpower_divide; lia);
    try reflexivity.
  apply Z.even_spec. rewrite Z.even_opp, Z.even_pow; try lia; reflexivity. Qed.

Lemma twosc_mod2 m a (Hm : 0 < m) : twosc m a mod 2 = a mod 2.
Proof. rewrite Zmod_odd, twosc_odd, <- Zmod_odd by lia. reflexivity. Qed.

Lemma twosc_bounds a m (Hm : 0 < m) :
  - 2 ^ (m - 1) <= twosc m a < 2 ^ (m - 1).
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ m = 2 * 2 ^ (m - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
  pose proof (Z.mod_pos_bound a (2 ^ m) H).
  destruct (a mod 2 ^ m <? 2 ^ (m - 1)) eqn:E.
  - rewrite Z.ltb_lt in E; lia.
  - apply Z.ltb_ge in E; lia. Qed.

(*********************************************************************** *)
(**Section for small independent lemmas which do not fit anywhere else   *)
(*********************************************************************** *)

Lemma app_split {A} (a b c d : list A) : a = c -> b = d -> a ++ b = c ++ d.
Proof. now intros; subst. Qed.

Lemma eval_bound machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n) :
  0 <= eval (uweight machine_wordsize) n f < 2 ^ (machine_wordsize * n).
Proof.
  generalize dependent n; induction f; intros; subst; simpl in *.
  - rewrite eval0, Z.mul_0_r, Z.pow_0_r; lia.
  - rewrite eval_cons, uweight_eval_shift, uweight_0, uweight_eq_alt' by lia.
    assert (0 <= 2 ^ machine_wordsize) by (apply Z.pow_nonneg; lia).
    specialize (IHf (fun z H => Hz z (or_intror H)) (length f) eq_refl).
    specialize (Hz a (or_introl eq_refl)).
    split; ring_simplify; rewrite Z.mul_1_r.
    + nia.
    + replace (machine_wordsize * Z.pos (Pos.of_succ_nat (length f))) with
        (machine_wordsize + machine_wordsize * Z.of_nat (length f)) by nia.
      rewrite Z.pow_add_r; nia. Qed.

Lemma mod_less_than_half_iff_not_neg_mod_less a m
        (Hm : 0 < m)
        (Ha1 : a mod 2 ^ m <> 2 ^ (m - 1))
        (Ha2 : a mod 2 ^ m <> 0) :
  (a mod 2 ^ m <? 2 ^ (m - 1)) = negb ((- a) mod 2 ^ m <? 2 ^ (m - 1)).
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (a mod 2 ^ m + (- a mod 2 ^ m) = 2 * 2 ^ (m - 1)) by
      (rewrite !Zmod_eq, Z_div_nz_opp_full, Pow.Z.pow_mul_base, Z.sub_simpl_r by lia; ring).
  destruct (a mod 2 ^ m <? 2 ^ (m - 1)) eqn:E1;
    destruct (- a mod 2 ^ m <? 2 ^ (m - 1)) eqn:E2;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *; try reflexivity; lia. Qed.

(****************************************************************************** *)
(**Section for lemma relating to bitwise operations and the Z.testbits function *)
(****************************************************************************** *)

Lemma eval_testbit machine_wordsize n f m
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hm : 0 <= m) :
  Z.testbit (eval (uweight machine_wordsize) n f) m =
  Z.testbit (nth_default 0 f (Z.abs_nat (m / machine_wordsize))) (m mod machine_wordsize).
Proof.
  generalize dependent n. generalize dependent m. induction f; intros; simpl in *; subst.
  - rewrite ListUtil.nth_default_nil, eval0, !Z.testbit_0_l; reflexivity.
  - rewrite eval_cons, uweight_eval_shift by lia.
    rewrite uweight_0, uweight_eq_alt', Z.mul_1_l, Z.mul_1_r, Z.mul_comm, <- Z.shiftl_mul_pow2, Shift.Z.testbit_add_shiftl_full; try lia.
    destruct (m <? machine_wordsize) eqn:E.
    + rewrite Z.ltb_lt in E; rewrite Z.div_small by lia.
      rewrite ListUtil.nth_default_cons, Z.mod_small by lia. reflexivity.
    + rewrite Z.ltb_ge in E; rewrite IHf; try lia.
      replace (Z.abs_nat (m / machine_wordsize)) with
          (S (Z.abs_nat ((m - machine_wordsize) / machine_wordsize))).
      rewrite ListUtil.nth_default_cons_S, PullPush.Z.sub_mod_r, Z_mod_same_full, Z.sub_0_r; reflexivity.
      rewrite <- Zabs2Nat.inj_succ_abs, Z.abs_eq.
      replace machine_wordsize with (1 * machine_wordsize) at 1 by ring.
      rewrite Div.Z.div_sub, Z.sub_1_r, Z.succ_pred; lia.
      apply Div.Z.div_nonneg; lia.
      intros; specialize (Hz z); tauto.
    + specialize (Hz a (or_introl eq_refl)); lia. Qed.

(**************************************************** *)
(**Functional correctness of multi-limb logical shift *)
(**************************************************** *)

Lemma eval_sat_shiftr machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  eval (uweight machine_wordsize) n (sat_shiftr machine_wordsize n f) =
  eval (uweight machine_wordsize) n f >> 1.
Proof.
  generalize dependent n. induction f; intros; subst.
  - unfold sat_shiftr; simpl; rewrite eval0; reflexivity.
  - unfold sat_shiftr; simpl.
    rewrite eval_cons, uweight_eval_shift; try lia.
    destruct f; simpl in *.
    + rewrite
        eval_cons, uweight_0, eval0, ListUtil.nth_default_cons, uweight_eq_alt',
        Z.mul_0_r, !Z.add_0_r, !Z.mul_1_l; reflexivity.
    + rewrite eval_cons, uweight_eval_shift;
        try (rewrite ?length_snoc, ?map_length, ?seq_length; lia).
      replace ((map _ _) ++ _) with (sat_shiftr machine_wordsize (S (length f)) (z :: f)).
      * rewrite IHf; try (intros; try apply Hz; tauto).
        rewrite uweight_0, ListUtil.nth_default_cons_S, uweight_eq_alt'.
        rewrite !ListUtil.nth_default_cons, !Z.mul_1_l, !Z.mul_1_r.
        rewrite <- !Z.div2_spec, !Z.div2_div, Z.div2_split by lia.
        rewrite eval_cons at 2 by reflexivity.
        rewrite uweight_eval_shift, uweight_0, uweight_eq_alt, Z.pow_1_r by lia.
        rewrite PullPush.Z.add_mod_r, PullPush.Z.mul_mod_l.
        replace 2 with (2 ^ 1) at 7 by trivial.
        rewrite Modulo.Z.mod_same_pow, Z.mul_0_l by lia. ring_simplify.
        rewrite Z.mul_1_l, Z.add_0_r, Z.truncating_shiftl_mod by lia. rewrite Z.lor_add; try ring.
        destruct (Z.odd z) eqn:E; rewrite Zmod_odd, E.
        ** specialize (Hz a (or_introl eq_refl)).
           rewrite Z.mul_1_r, Z.land_div2; rewrite ?Z.sub_simpl_r; lia.
        ** now rewrite Z.mul_0_r, Z.land_0_r.
      * unfold sat_shiftr. replace (S (length f) - 1)%nat with (length f) by omega.
        apply app_split.
        ** apply map_seq_ext; intros; try lia.
           rewrite Nat.sub_0_r, Nat.add_1_r.
           rewrite !(ListUtil.nth_default_cons_S _ a); reflexivity.
        ** now rewrite ListUtil.nth_default_cons_S. Qed.

(*********************************************************************************** *)
(**Section for properties of the multi-limb addtion including functional correctness *)
(*********************************************************************************** *)

Lemma eval_sat_add machine_wordsize n f g (mw0 : 0 < machine_wordsize) (Hf : length f = n) (Hg : length g = n) :
  eval (uweight machine_wordsize) n (sat_add machine_wordsize n f g) =
  (eval (uweight machine_wordsize) n f + eval (uweight machine_wordsize) n g) mod (2^(machine_wordsize * n)).
Proof.
  unfold sat_add.
  rewrite Rows.add_partitions;
    rewrite ?eval_partition; try assumption; try apply (uwprops machine_wordsize mw0).
  rewrite uweight_eq_alt'; reflexivity. Qed.

Lemma length_sat_add machine_wordsize n f g
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hg : length g = n) :
  length (sat_add machine_wordsize n f g) = n.
Proof.
  unfold sat_add, Rows.add.
  autorewrite with distr_length. reflexivity.
  apply (uwprops machine_wordsize mw0).
  intros row H; destruct H as [|[H|[]]]; subst; auto. Qed.

Hint Rewrite length_sat_add : length_distr.

Lemma sat_add_bounds machine_wordsize n f g
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hg : length g = n) :
  forall z, In z (sat_add machine_wordsize n f g) -> 0 <= z < 2 ^ machine_wordsize.
Proof.
  intros. unfold sat_add in *.
  rewrite Rows.add_partitions in *; auto.
  unfold Partition.partition in H.
  apply ListAux.in_map_inv in H.
  destruct H as [a [H]].
  rewrite H0, !uweight_eq_alt; try lia.
  split.
  - apply Z.div_le_lower_bound;
      ring_simplify; try apply Z.mod_pos_bound;
        apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
  - apply Z.div_lt_upper_bound.
    apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
    replace ((_ ^ _) ^ _ * _) with ((2 ^ machine_wordsize) ^ Z.of_nat (S a)).
    apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; try lia; apply Z.pow_pos_nonneg; lia.
    rewrite Z.mul_comm, Pow.Z.pow_mul_base; 
    try (replace (Z.of_nat (S a)) with ((Z.of_nat a + 1)) by lia; lia).
  - apply (uwprops machine_wordsize mw0). Qed.

(********************************************************* *)
(**Section on properties of sat_mod2 including correctness *)
(********************************************************* *)

Lemma sat_mod2_cons a f : sat_mod2 (a :: f) = a mod 2.
Proof. unfold sat_mod2. now rewrite ListUtil.nth_default_cons. Qed.

Lemma eval_sat_mod2 machine_wordsize n f
      (Hf : length f = n)
      (Hmw : 0 < machine_wordsize) :
  (eval (uweight machine_wordsize) n f) mod 2 = sat_mod2 f.
Proof.
  generalize dependent Hf. generalize dependent n.
  induction f; intros; simpl in *; subst.
  - unfold sat_mod2. rewrite eval0; reflexivity.
  - rewrite eval_cons by trivial. rewrite uweight_eval_shift by lia.
    rewrite <- Zplus_mod_idemp_r, <- Zmult_mod_idemp_r, IHf by reflexivity.
    unfold uweight, ModOps.weight; simpl.
    rewrite Z.mul_0_r, Z.mul_1_r, !Zdiv_1_r, !Z.opp_involutive, !Z.pow_0_r, Z.mul_1_l.
    rewrite <- Zmult_mod_idemp_l, PullPush.Z.mod_pow_full, Z_mod_same_full, Z.pow_0_l by assumption.
    rewrite Zmod_0_l, Z.add_0_r; reflexivity. Qed.

(*********************************************************************** *)
(**Section for properties of sat_arithmetic_shiftr including correctness *)
(*********************************************************************** *)

Lemma eval_sat_arithmetic_shiftr machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n) :
  eval (uweight machine_wordsize) n (sat_arithmetic_shiftr machine_wordsize n f) =
  Z.arithmetic_shiftr (machine_wordsize * n) (eval (uweight machine_wordsize) n f).
Proof.
  generalize dependent n.
  induction f as [|z f IHf]; intros; subst.
  - rewrite !eval0; reflexivity.
  - destruct f.
    + cbn; rewrite uweight_0, !Z.mul_1_r, !Z.mul_1_l, !Z.add_0_r; reflexivity.
    + unfold sat_arithmetic_shiftr; simpl.
      rewrite eval_cons, !uweight_eval_shift by (try lia; autorewrite with distr_length; reflexivity).
      replace (map _ _ ++ _) with (sat_arithmetic_shiftr machine_wordsize (S (length f)) (z0 :: f)).
      rewrite IHf; try reflexivity.

      unfold Z.arithmetic_shiftr; rewrite !Z.land_pow2_testbit, !eval_testbit; try tauto; try nia; simpl.
      replace (Z.abs_nat ((machine_wordsize * Z.pos (Pos.succ (Pos.of_succ_nat (length f))) - 1) / machine_wordsize)) with
          (S (Z.abs_nat ((machine_wordsize * Z.pos (Pos.of_succ_nat (length f)) - 1) / machine_wordsize))).
      rewrite !ListUtil.nth_default_cons_S, !ListUtil.nth_default_cons by lia.

      unfold Z.sub.
      rewrite !Modulo.Z.mod_add_l', uweight_0, uweight_eq_alt', !Z.mul_1_l, Z.mul_1_r, Z.truncating_shiftl_mod by lia.
      destruct (Z.testbit
      (nth_default 0 (z0 :: f)
         (Z.abs_nat
            ((machine_wordsize * Z.pos (Pos.of_succ_nat (length f)) + - (1)) /
             machine_wordsize)))
      ((- (1)) mod machine_wordsize)) eqn:E.
      * rewrite <- !Z.div2_spec, !Z.div2_div, !Z.lor_add; ring_simplify.
        rewrite (eval_cons _ (S _)), uweight_eval_shift by (try reflexivity; lia).
        rewrite uweight_0, uweight_eq_alt', !Z.mul_1_l, Z.mul_1_r, Z.div2_split, <- Z.pow_add_r by nia.
        rewrite eval_sat_mod2 by (try reflexivity; lia). unfold sat_mod2.
        rewrite ListUtil.nth_default_cons.
        replace (machine_wordsize + (_ + _)) with
            (machine_wordsize * Z.pos (Pos.succ (Pos.of_succ_nat (length f))) + - (1)) by lia; ring.

        rewrite Z.land_comm, Z.land_pow2_small; try lia.
        split.
        apply Div.Z.div_nonneg; try lia.
           assert (0 <= eval (uweight machine_wordsize) (S (S (length f))) (z :: z0 :: f)).
           { apply eval_bound; try lia. intros; apply Hz; simpl; tauto. reflexivity. }
           specialize (Hz z (or_introl eq_refl)); nia.
        apply Div.Z.div_lt_upper_bound'; try lia.
           rewrite Z.mul_comm, Pow.Z.pow_mul_base by nia.
        simpl; rewrite <- Z.add_assoc, Z.add_0_r.
        apply eval_bound; try lia; tauto.

        rewrite Z.land_comm, Z.land_pow2_small; try lia.
        split.
        apply Div.Z.div_nonneg; try lia.
        apply eval_bound; try lia. intros; apply Hz; simpl; tauto. reflexivity.

        apply Div.Z.div_lt_upper_bound'; try lia.
        rewrite Z.mul_comm, Pow.Z.pow_mul_base; try nia. rewrite <- Z.add_assoc, Z.add_0_r.
        apply eval_bound; try lia. intros; apply Hz; simpl; tauto. reflexivity.

        rewrite Zmod_odd.
        specialize (Hz z (or_introl eq_refl)).
        destruct (Z.odd z0).
        ** rewrite Z.mul_1_r, Z.land_pow2_small; try lia. split.
           apply Div.Z.div_nonneg; lia.
           apply Div.Z.div_lt_upper_bound'; try lia.
           rewrite Z.mul_comm, Pow.Z.pow_mul_base, Z.sub_simpl_r; lia.
        ** rewrite Z.mul_0_r, Z.land_0_r; reflexivity.
      * rewrite !Z.lor_0_l, (eval_cons _ (S _)), uweight_eval_shift; try lia; try reflexivity.
        rewrite uweight_0, uweight_eq_alt', Z.mul_1_l, Z.mul_1_r.
        rewrite <- !Z.div2_spec, !Z.div2_div, Z.div2_split by lia.
        rewrite eval_sat_mod2, sat_mod2_cons, Z.lor_add; try lia ; try reflexivity.
        rewrite Zmod_odd. specialize (Hz z (or_introl eq_refl)).
        destruct (Z.odd z0).
        ** rewrite Z.mul_1_r, Z.land_pow2_small; try lia.
           split.
           apply Div.Z.div_nonneg; lia.
           apply Div.Z.div_lt_upper_bound'; [lia|].
           rewrite Z.mul_comm, Pow.Z.pow_mul_base, Z.sub_simpl_r; lia.
        ** rewrite Z.mul_0_r, Z.land_0_r; reflexivity.
      * rewrite <- Zabs2Nat.inj_succ.
        apply f_equal.
        rewrite <- Z.add_1_r.
        unfold Z.sub.
        rewrite !Div.Z.div_add_l'; lia.
        set (x := Pos.of_succ_nat (length f)).
        set (a := machine_wordsize). apply Div.Z.div_nonneg; nia.
      * intros; apply Hz; simpl in *; tauto.
      * intros; apply Hz; simpl in *; tauto.
      * unfold sat_arithmetic_shiftr.
        replace (S (length f) - 1)%nat with (length f) by lia.
        rewrite ListUtil.nth_default_cons_S.
        apply f_equal2; [|reflexivity].
        apply map_seq_ext; [|lia].
        intros; simpl; rewrite !Nat.add_1_r, !(ListUtil.nth_default_cons_S _ z); reflexivity. Qed.

(************************************ *)
(**Properties of sat_one and sat_zero *)
(************************************ *)

Lemma length_sat_one machine_wordsize n :
  length (sat_one machine_wordsize n) = n.
Proof. auto with distr_length. Qed.

Lemma length_sat_zero n :
  length (sat_zero n) = n.
Proof. auto with distr_length. Qed.

Lemma eval_sat_zero machine_wordsize n (mw : 0 < machine_wordsize):
  eval (uweight machine_wordsize) n (sat_zero n) = 0.
Proof.
  unfold sat_zero; induction n.
  - reflexivity.
  - simpl; rewrite eval_cons, uweight_eval_shift, uweight_0, IHn;
      auto with distr_length; lia. Qed.

(******************************************************** *)
(**Properties of sat_opp including functional correctness *)
(******************************************************** *)

Lemma length_sat_opp machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n) :
  length (sat_opp machine_wordsize n f) = n.
Proof. unfold sat_opp; rewrite length_sat_add; auto with distr_length; lia. Qed.

Hint Rewrite length_sat_opp : distr_length.

Lemma eval_sat_opp machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n) :
  eval (uweight machine_wordsize) n (sat_opp machine_wordsize n f) =
  (- eval (uweight machine_wordsize) n f) mod (2^(machine_wordsize * n)).
Proof.
  assert (2 ^ machine_wordsize <> 0) by (apply Z.pow_nonzero; lia).
  assert (2 ^ (machine_wordsize * Z.of_nat (length f)) <> 0) by (apply Z.pow_nonzero; nia).

  symmetry. unfold sat_opp.
  rewrite eval_sat_add by distr_length.
  generalize dependent n. induction f; intros.
  - simpl in *; rewrite <- Hf; rewrite eval0; rewrite !Zmod_0_l; reflexivity.
  - simpl in *. subst.
    assert (2 ^ (machine_wordsize * Z.of_nat (length f)) <> 0) by (apply Z.pow_nonzero; nia).

    rewrite !eval_cons, uweight_0, !uweight_eval_shift, uweight_eq_alt' by distr_length.
    rewrite !Z.mul_1_l, !Z.mul_1_r, Z.opp_add_distr, Zopp_mult_distr_r, <- Z.add_mod_idemp_r by distr_length.
    symmetry. rewrite Z.add_assoc, <- Z.add_mod_idemp_r; try (rewrite Zpos_P_of_succ_nat in H0; rewrite Nat2Z.inj_succ; assumption). 
    replace (2 ^ (machine_wordsize * Z.of_nat (S (length f)))) with
        ((2 ^ machine_wordsize) * (2 ^ (machine_wordsize * Z.of_nat (length f)))).
    rewrite !Z.mul_mod_distr_l; try lia.
    unfold Z.lnot_modulo. rewrite Lnot.Z.lnot_equiv. unfold Z.pred.
    rewrite IHf; try lia.
    destruct (length f) eqn:E.
    + rewrite !eval0.
      rewrite !Z.mul_0_r, !Z.mul_1_r, !Z.add_0_r.
      replace (-a + -1) with (- (a + 1)) by ring.
      rewrite eval_encode_no_reduce.
      rewrite Z.mod_opp_small.
      replace (1 + (2 ^ machine_wordsize - (a + 1))) with
          (-a + 2 ^ machine_wordsize) by ring.
      rewrite <- Z.add_mod_idemp_r.
      rewrite Z_mod_same_full. rewrite Z.add_0_r. reflexivity.
      apply Z.pow_nonzero. omega. lia.
      specialize (Hz a (or_introl eq_refl)). lia.
      rewrite uweight_0. reflexivity.
      intro; symmetry; apply Z.lt_neq;
        apply (weight_positive (uwprops machine_wordsize mw0)). omega.
      intros; symmetry; apply Z.lt_neq;
        apply (weight_divides (uwprops machine_wordsize mw0)).
    + rewrite !eval_encode_no_reduce in *; try lia; try apply uweight_0.
      rewrite <- Z.mul_mod_distr_l, Z.add_mod_idemp_r; try nia.
      symmetry.
      rewrite <- Z.mul_mod_distr_l, Z.add_mod_idemp_r, Z.mul_add_distr_l, Z.mul_1_r; try nia.
      replace (-a + -1) with (- (a + 1)) by ring.
      rewrite Z.mod_opp_small.
      unfold Z.lnot_modulo.
      rewrite Z.add_assoc.
      replace (1 + (2 ^ machine_wordsize - (a + 1))) with
          (- a + 2 ^ machine_wordsize) by ring.
      reflexivity.
      specialize (Hz a (or_introl eq_refl)); lia.
      intro; symmetry; apply Z.lt_neq;
        eapply (weight_positive (uwprops machine_wordsize mw0)).
      intros; symmetry; apply Z.lt_neq;
      apply (weight_divides (uwprops machine_wordsize mw0)).
      intro; symmetry; apply Z.lt_neq;
        eapply (weight_positive (uwprops machine_wordsize mw0)).
      intros; symmetry; apply Z.lt_neq;
        apply (weight_divides (uwprops machine_wordsize mw0)).
    + intros; apply Hz; right; assumption.
    + rewrite <- Z.pow_add_r; try apply f_equal; nia. Qed.

Lemma sat_opp_mod2 machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = n)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  sat_mod2 (sat_opp machine_wordsize n f) = sat_mod2 f.
Proof.
  rewrite <- !(eval_sat_mod2 machine_wordsize n) by distr_length.
  rewrite eval_sat_opp; auto.
  set (x := eval (uweight machine_wordsize) n f).
  destruct f.
  - subst. reflexivity.
  - rewrite <- (Znumtheory.Zmod_div_mod _ (2 ^ (machine_wordsize * Z.of_nat n))).
    rewrite <- Z.opp_mod2; reflexivity. lia. apply Z.pow_pos_nonneg; nia.
    apply Zpow_facts.Zpower_divide. simpl in *. nia. Qed.

(*********************************** *)
(**Properties of twos_complement_opp *)
(*********************************** *)

Lemma twos_complement_opp_correct m a :
  (Z.twos_complement_opp m a) = - a mod 2 ^ m.
Proof.
  unfold Z.twos_complement_opp.
  unfold Z.lnot_modulo, Z.lnot.
  rewrite Zplus_mod_idemp_l.
  rewrite Z.add_1_r. rewrite Z.succ_pred. reflexivity. Qed.

Lemma twosc_Z_opp a m
      (Hm : 0 < m) (corner_case : twosc m a <> - 2 ^ (m - 1)) :
  - twosc m a = twosc m (- a).
Proof.
  pose proof twosc_bounds a m Hm.

  assert (0 < 2 ^ (m - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ m = 2 * 2 ^ (m - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
  assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).

  destruct (dec (a mod 2 ^ m = 2 ^ (m - 1)));
    destruct (dec (a mod 2 ^ m = 0)); rewrite ?e, ?e0; try lia.
  - rewrite e, Z.ltb_irrefl in *. lia.
  - rewrite PullPush.Z.opp_mod_mod, e, Z.mod_0_l by lia.
    replace (0 <? 2 ^ (m - 1)) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity.
  - pose proof (mod_less_than_half_iff_not_neg_mod_less _ _ Hm n n0). symmetry in H3.
    destruct (a mod 2 ^ m <? 2 ^ (m - 1)).
    + apply negb_true_iff in H3; rewrite H3.
      apply Z.ltb_ge in H3. rewrite PullPush.Z.opp_mod_mod, Z.mod_opp_small; lia.
    + apply negb_false_iff in H3; rewrite H3.
      apply Z.ltb_lt in H3. rewrite PullPush.Z.opp_mod_mod, Z.mod_opp_small; lia. Qed.

Lemma twos_complement_opp_spec m a
      (Hm : 0 < m)
      (corner_case : twosc m a <> - 2 ^ (m - 1)) :
  twosc m (Z.twos_complement_opp m a) = - (twosc m a).
Proof.
  unfold Z.twos_complement_opp, Z.lnot_modulo, Z.lnot.
  rewrite Zplus_mod_idemp_l, Z.add_1_r, Z.succ_pred, twosc_mod by lia. symmetry; apply twosc_Z_opp; lia. Qed.

(************************* *)
(**Properties of twos_complement_pos *)
(************************* *)

Lemma twos_complement_pos_spec m a
      (mw0 : 0 < m)
      (corner_case : twosc m a <> - 2 ^ (m - 1)) : (* note that this has to be true for Z.twos_complement_pos to work *)
  Z.twos_complement_pos m a = Z.b2z (0 <? twosc m a).
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (2 ^ m = 2 * 2 ^ (m - 1)) by (rewrite Pow.Z.pow_mul_base; ring_simplify (m - 1 + 1); lia).

  unfold Z.twos_complement_pos; cbv [Let_In]; rewrite twos_complement_opp_correct.
  destruct (a mod 2 ^ m <? 2 ^ (m - 1)) eqn:E; destruct (dec (a mod 2 ^ m = 0)).
  - rewrite PullPush.Z.opp_mod_mod, e; simpl; rewrite Z.mod_0_l, Z.shiftr_0_l; auto.
    apply Z.pow_nonzero; lia.
  - rewrite mod_less_than_half_iff_not_neg_mod_less in E; auto.
    assert (0 <? a mod 2 ^ m = true) by (apply Z.ltb_lt; lia).
    rewrite H2, Z.shiftr_div_pow2, Div.Z.div_between_1; try lia; auto.
    rewrite negb_true_iff, Z.ltb_ge in E.
    split; try lia.
    rewrite H1. apply Z.mod_pos_bound; lia. rewrite Z.ltb_lt in E; lia.
  - rewrite PullPush.Z.opp_mod_mod, e, !Z.mod_0_l, Z.shiftr_0_l; try lia.
    assert (0 <? 0 - 2 ^ m = false) by (apply Z.ltb_ge; lia). rewrite H2; reflexivity.
  - rewrite mod_less_than_half_iff_not_neg_mod_less in E; try lia; auto.
    assert (0 <? a mod 2 ^ m - 2 ^ m = false) by (apply Z.ltb_ge; lia).
    rewrite H2, Z.shiftr_div_pow2, Z.div_small; try lia; auto.
    rewrite negb_false_iff, Z.ltb_lt in E. split; try apply Z.mod_pos_bound; lia. Qed.

(****************************************************************************** *)
(**This section is for the interaction between twosc and integer addition       *)
(**There are some badly named lemmas. These are just casing on some inequalites *)
(**of the sum of to numbers under modular reduction.                            *)
(****************************************************************************** *)

Lemma mod_add a b m
      (Hm : 0 < m)
      (Ha : a mod 2 ^ m < (2 ^ (m - 1)))
      (Hb : b mod 2 ^ m < (2 ^ (m - 1))) :
  (a + b) mod 2 ^ m = a mod 2 ^ m + b mod 2 ^ m.
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= a mod 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= b mod 2 ^ m) by (apply Z.mod_pos_bound; lia).

  rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r.
  rewrite Z.mod_small. lia. replace (2 ^ m) with (2 * 2 ^ (m - 1)) at 5. lia.
  rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia. Qed.

Lemma mod_add2 a b m
      (Hm : 0 < m)
      (Ha : a mod 2 ^ m < (2 ^ (m - 1)))
      (Hb : 2 ^ (m - 1) <= b mod 2 ^ m)
      (Hsum : (a + b) mod 2 ^ m < 2 ^ (m - 1)) :
  (a + b) mod 2 ^ m = a mod 2 ^ m + b mod 2 ^ m - 2 ^ m.
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= b mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (2 ^ m <= a mod 2 ^ m + b mod 2 ^ m < 2 * 2 ^ m).
  { split; try lia.
    destruct (dec (2 ^ m <= a mod 2 ^ m + b mod 2 ^ m)); try lia.
    apply Znot_le_gt in n. rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Z.mod_small in Hsum; lia. }
  rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Modulo.Z.mod_small_1; lia. Qed.

Lemma mod_add3 a b m
      (Hm : 0 < m)
      (Ha : a mod 2 ^ m < (2 ^ (m - 1)))
      (Hb : 2 ^ (m - 1) <= b mod 2 ^ m)
      (Hsum : 2 ^ (m - 1) <= (a + b) mod 2 ^ m) :
  (a + b) mod 2 ^ m = a mod 2 ^ m + b mod 2 ^ m.
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= b mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).

  assert (0 <= a mod 2 ^ m + b mod 2 ^ m < 2 ^ m).
  split; try lia.
  destruct (dec (a mod 2 ^ m + b mod 2 ^ m < 2 ^ m)); try lia.
  apply Znot_lt_ge in n.
  rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Modulo.Z.mod_small_1 in Hsum; lia.
  rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Z.mod_small; lia. Qed.

Lemma mod_add4 a b m
      (Hm : 0 < m)
      (Ha : 2 ^ (m - 1) <= a mod 2 ^ m)
      (Hb : 2 ^ (m - 1) <= b mod 2 ^ m) :
  (a + b) mod 2 ^ m = a mod 2 ^ m + b mod 2 ^ m - 2 ^ m.
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= b mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).

  assert (2 ^ m = 2 * 2 ^ (m - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).

  rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Modulo.Z.mod_small_1; lia. Qed.

Lemma twosc_add a b m
      (Hm : 0 < m)
      (Ha : - 2 ^ (m - 2) < twosc m a < 2 ^ (m - 2))
      (Hb : - 2 ^ (m - 2) < twosc m b < 2 ^ (m - 2)) :
  twosc m (a + b) = twosc m a + twosc m b.
Proof.
  destruct (dec (m = 1)).
  rewrite e in *; replace (2 ^ (1 - 2)) with 0 in * by reflexivity; lia.

  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ m = 2 * 2 ^ (m - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
  assert (2 ^ m = 2 * (2 * 2 ^ (m - 2)))
    by (rewrite !Pow.Z.pow_mul_base; replace (m - 2 + 1 + 1) with m by ring; lia).

  assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= b mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).

  destruct ((a + b) mod 2 ^ m <? 2 ^ (m - 1)) eqn:Hsum;
    destruct (a mod 2 ^ m <? 2 ^ (m - 1)) eqn:Hamod;
    destruct (b mod 2 ^ m <? 2 ^ (m - 1)) eqn:Hbmod;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
  - apply mod_add; lia.
  - rewrite Z.add_sub_assoc. apply mod_add2; lia.
  - rewrite Z.add_comm, <- Z.add_sub_swap.
    rewrite (Z.add_comm (a mod _)). apply mod_add2; try lia. rewrite Z.add_comm; lia.
  - assert (2 ^ m <= a mod 2 ^ m + b mod 2 ^ m < 2 * 2 ^ m) by (split; lia).
    rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Modulo.Z.mod_small_1 in Hsum; lia.
  - rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Z.mod_small in Hsum; lia.
  - rewrite mod_add3; lia.
  - rewrite Z.add_comm, mod_add3; try lia. rewrite Z.add_comm; lia.
  - rewrite mod_add4; lia. Qed.

Lemma mod_add_full a b m
      (Hm : 0 < m)
      (Hsum : a mod m + b mod m < m) :
  (a + b) mod m = a mod m + b mod m.
Proof.
  assert (0 <= a mod m < m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= b mod m < m) by (apply Z.mod_pos_bound; lia).
  rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Z.mod_small; lia. Qed.

Lemma twosc_add_full a b m
      (Hm : 0 < m)
      (Ha : - 2 ^ (m - 1) <= twosc m a + twosc m b < 2 ^ (m - 1)) :
  twosc m (a + b) = twosc m a + twosc m b.
Proof.
  assert (0 < 2 ^ m) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ m = 2 * 2 ^ (m - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).

  assert (0 <= a mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).
  assert (0 <= b mod 2 ^ m < 2 ^ m) by (apply Z.mod_pos_bound; lia).

  destruct ((a + b) mod 2 ^ m <? 2 ^ (m - 1)) eqn:Hsum;
    destruct (a mod 2 ^ m <? 2 ^ (m - 1)) eqn:Hamod;
    destruct (b mod 2 ^ m <? 2 ^ (m - 1)) eqn:Hbmod;
    rewrite ?Z.ltb_lt, ?Z.ltb_ge in *.
  - rewrite mod_add_full; lia.
  - rewrite mod_add2; lia.
  - rewrite Z.add_comm. rewrite <- Z.add_sub_swap.
    rewrite (Z.add_comm (a mod _)). apply mod_add2. lia. lia. lia.
    rewrite Z.add_comm; lia.
  - assert (2 ^ m <= a mod 2 ^ m + b mod 2 ^ m < 2 * 2 ^ m) by (split; lia).
    rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Modulo.Z.mod_small_1 in Hsum; lia.
  - rewrite <- Zplus_mod_idemp_l, <- Zplus_mod_idemp_r, Z.mod_small in Hsum; lia.
  - rewrite mod_add3; lia.
  - rewrite Z.add_comm, mod_add3; try lia. rewrite Z.add_comm; lia.
  - rewrite mod_add4; lia. Qed.

(********************************************************************* *)
(**Section for interaction between eval_twosc and saturated operations *)
(********************************************************************* *)

Lemma eval_twosc_sat_arithmetic_shiftr machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n) :
  eval_twosc machine_wordsize n (sat_arithmetic_shiftr machine_wordsize n f) =
  (eval_twosc machine_wordsize n f) / 2.
Proof.
  assert (0 < Z.of_nat n) by omega. unfold eval_twosc. rewrite eval_sat_arithmetic_shiftr, arithmetic_shiftr_spec; auto; try nia.
  apply eval_bound; auto. Qed.

Lemma eval_twosc_sat_add machine_wordsize n f g
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hf : length f = n)
      (Hg : length g = n)
      (overflow_f : - 2 ^ (machine_wordsize * n - 2) <
                    twosc (machine_wordsize * n) (eval (uweight machine_wordsize) n f) <
                    2 ^ (machine_wordsize * n - 2))
      (overflow_g : - 2 ^ (machine_wordsize * n - 2) <
                    twosc (machine_wordsize * n) (eval (uweight machine_wordsize) n g) <
                    2 ^ (machine_wordsize * n - 2)) :
  eval_twosc machine_wordsize n (sat_add machine_wordsize n f g) =
  eval_twosc machine_wordsize n f + eval_twosc machine_wordsize n g.
Proof. assert (0 < Z.of_nat n) by omega. unfold eval_twosc. rewrite eval_sat_add, twosc_mod, twosc_add; nia. Qed.

Lemma eval_twosc_select machine_wordsize n cond f g
      (Hf : length f = n)
      (Hg : length g = n) :
  eval_twosc machine_wordsize n (select cond f g) = if dec (cond = 0)
                                                    then (eval_twosc machine_wordsize n f)
                                                    else (eval_twosc machine_wordsize n g).
Proof. unfold eval_twosc; rewrite eval_select; auto; destruct (dec (cond = 0)); auto. Qed.

Lemma eval_twosc_sat_opp machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hz : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hf : length f = n)
      (corner_case : eval_twosc machine_wordsize n f <> - 2 ^ (machine_wordsize * n - 1)):
  eval_twosc machine_wordsize n (sat_opp machine_wordsize n f) =
  - eval_twosc machine_wordsize n f.
Proof. assert (0 < Z.of_nat n) by omega; unfold eval_twosc in *; rewrite eval_sat_opp, twosc_mod, twosc_Z_opp; try nia; tauto. Qed.

Lemma eval_twosc_sat_zero machine_wordsize n
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat) :
  eval_twosc machine_wordsize n (sat_zero n) = 0.
Proof.
  unfold eval_twosc; rewrite eval_sat_zero; auto.
  rewrite Z.mod_0_l by (apply Z.pow_nonzero; nia).
  assert (0 <? 2 ^ (machine_wordsize * Z.of_nat n - 1) = true) by (apply Z.ltb_lt; apply Z.pow_pos_nonneg; nia).
  now rewrite H. Qed.

Lemma eval_twosc_sat_mod2 machine_wordsize n f
      (mw0 : 0 < machine_wordsize)
      (n0 : (0 < n)%nat)
      (Hf : length f = n) :
  (eval_twosc machine_wordsize n f) mod 2 = sat_mod2 f.
Proof.
  assert (0 < Z.of_nat n) by omega. unfold eval_twosc. rewrite twosc_mod2, eval_sat_mod2; nia. Qed.

(** ******************************************************************************* *)
(** This section is for the implementation and correctness of the divstep algorithm *)
(** ******************************************************************************* *)

Import WordByWordMontgomery.
Import Positional.

Definition divstep_aux machine_wordsize sat_limbs mont_limbs m (data : Z * (list Z) * (list Z) * (list Z) * (list Z)) :=
  let r := snd data in
  let v := snd (fst data) in
  let g := snd (fst (fst data)) in
  let f := snd (fst (fst (fst data))) in
  let d := fst (fst (fst (fst data))) in
  dlet cond := Z.land (Z.twos_complement_pos machine_wordsize d) (sat_mod2 g) in
  dlet d' := Z.zselect cond d (Z.twos_complement_opp machine_wordsize d) in
  dlet f' := select cond f g in
  dlet g' := select cond g (sat_opp machine_wordsize sat_limbs f) in
  dlet v' := select cond v r in
  let v'':= addmod machine_wordsize mont_limbs m v' v' in
  dlet r' := select cond r (oppmod machine_wordsize mont_limbs m v) in
  dlet g0 := sat_mod2 g' in
  let d'' := (d' + 1) mod 2^machine_wordsize in
  dlet f'' := select g0 (sat_zero sat_limbs) f' in
  let g'' := sat_arithmetic_shiftr machine_wordsize sat_limbs (sat_add machine_wordsize sat_limbs g' f'') in
  dlet v''' := select g0 (sat_zero mont_limbs) v' in
  let r'' := addmod machine_wordsize mont_limbs m r' v''' in
    (d'',f',g'',v'',r'').

Definition divstep machine_wordsize sat_limbs mont_limbs m d f g v r :=
  divstep_aux machine_wordsize sat_limbs mont_limbs m (d, f, g, v, r).
Definition divstep_safe machine_wordsize n :=
  let sat_limbs := (n + 1)%nat in
  divstep machine_wordsize sat_limbs n.

Definition divstep_spec d f g :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2)
  else (1 + d, f, (g + (g mod 2) * f) / 2 ).

Definition divstep_spec2 m d g v r :=
  if (0 <? d) && Z.odd g
  then (2 * r mod m, (r - v) mod m)
  else (2 * v mod m, (r + (g mod 2) * v) mod m).

Definition divstep_spec_full m d f g v r :=
  if (0 <? d) && Z.odd g
  then (1 - d, g, (g - f) / 2, 2 * r mod m, (r - v) mod m)
  else (1 + d, f, (g + (g mod 2) * f) / 2, 2 * v mod m, (r + (g mod 2) * v) mod m).

Lemma divstep_g machine_wordsize sat_limbs mont_limbs m d f g v r
      (mw0 : 0 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (fodd : Z.odd (eval_twosc machine_wordsize sat_limbs f) = true)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (corner_case : twosc machine_wordsize d <> - 2 ^ (machine_wordsize - 1))
      (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twosc machine_wordsize sat_limbs f <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twosc machine_wordsize sat_limbs g <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  eval_twosc machine_wordsize sat_limbs g1 =
  snd (divstep_spec
         (twosc machine_wordsize d)
         (eval_twosc machine_wordsize sat_limbs f)
         (eval_twosc machine_wordsize sat_limbs g)).
Proof.
  set (bw := machine_wordsize * Z.of_nat sat_limbs) in *.

  simpl.
  assert (0 < Z.of_nat sat_limbs) by omega.
  assert (bw0 : 0 < bw) by nia.
  assert (bw1 : 1 < bw) by (destruct (dec (bw = 1)); rewrite ?e in *; simpl in *; lia).
  assert (2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).
  assert (0 < 2 ^ bw) by (apply Z.pow_pos_nonneg; lia).
  assert (2 ^ (bw - 2) <= 2 ^ (bw - 1)) by (apply Z.pow_le_mono; lia).

  Hint Rewrite length_sat_add length_sat_opp length_select : distr_length.

  rewrite eval_twosc_sat_arithmetic_shiftr; distr_length; autorewrite with distr_length; try nia.
  rewrite eval_twosc_sat_add; auto; try (autorewrite with distr_length; lia).
  rewrite !eval_twosc_select; auto; try (autorewrite with distr_length; lia).
  rewrite eval_twosc_sat_opp; auto; try (autorewrite with distr_length; lia).
  rewrite select_push; try (autorewrite with distr_length; lia).

  rewrite sat_opp_mod2; auto.
  unfold divstep_spec.
  rewrite twos_complement_pos_spec; auto.
  rewrite <- !(eval_twosc_sat_mod2 machine_wordsize sat_limbs); auto.
  rewrite !Zmod_odd; auto.

  set (g' := eval_twosc machine_wordsize sat_limbs g) in *.
  set (f' := eval_twosc machine_wordsize sat_limbs f) in *.
  assert (corner_case_f : f' <> - 2 ^ (bw - 1)) by
      (replace (- _) with (- (2 * 2 ^ (bw - 2))); rewrite ?Pow.Z.pow_mul_base; ring_simplify (bw - 2 + 1); nia).

  destruct (0 <? twosc machine_wordsize d);
    destruct (Z.odd g') eqn:g'_odd; rewrite ?fodd, ?eval_sat_zero; auto.
  - simpl. rewrite Z.add_comm; reflexivity.
  - simpl. rewrite eval_twosc_sat_zero; auto.
  - rewrite Z.mul_1_l. simpl. reflexivity.
  - simpl. rewrite eval_twosc_sat_zero; auto.
  - replace (_ * _) with bw by reflexivity. lia.
  - fold (eval_twosc machine_wordsize sat_limbs
                     (select (Z.twos_complement_pos machine_wordsize d &' sat_mod2 g) g (sat_opp machine_wordsize sat_limbs f))).
    rewrite eval_twosc_select; try apply length_sat_opp; auto.
    destruct (dec (_)); replace (machine_wordsize * _) with bw by reflexivity;
    try rewrite eval_twosc_sat_opp; auto; replace (machine_wordsize * _) with bw by reflexivity; lia.
  - fold (eval_twosc machine_wordsize sat_limbs
                     (select (sat_mod2 (select (Z.twos_complement_pos machine_wordsize d &' sat_mod2 g) g (sat_opp machine_wordsize sat_limbs f)))
                             (sat_zero sat_limbs) (select (Z.twos_complement_pos machine_wordsize d &' sat_mod2 g) f g))).
    rewrite eval_twosc_select; try apply length_sat_zero; try apply length_select; auto.
    destruct (dec (_)); try rewrite eval_twosc_sat_zero; try rewrite eval_twosc_select;
      replace (machine_wordsize * _) with bw by reflexivity; try lia; destruct (dec (_)); lia.
  - apply sat_add_bounds; try lia; repeat (rewrite ?length_sat_opp, ?(length_select sat_limbs), ?length_sat_zero; auto). Qed.

Lemma divstep_d machine_wordsize sat_limbs mont_limbs m d f g v r
      (mw1 : 1 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    twosc machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  twosc machine_wordsize d1 =
  fst (fst (divstep_spec (twosc machine_wordsize d)
                           (eval_twosc machine_wordsize sat_limbs f)
                           (eval_twosc machine_wordsize sat_limbs g))).
Proof.
  assert (helper0 : 0 < Z.of_nat sat_limbs) by omega.
  assert (mw0 : 0 < machine_wordsize) by lia.
  assert (helper : 1 < 2 ^ machine_wordsize) by (apply Zpow_facts.Zpower_gt_1; lia).
  assert (helper2 : 1 < 2 ^ (machine_wordsize - 1)) by (apply Zpow_facts.Zpower_gt_1; lia).
  assert (helper3 : 2 ^ machine_wordsize = 2 * 2 ^ (machine_wordsize - 1))
    by (rewrite Pow.Z.pow_mul_base, Z.sub_simpl_r; lia).

  simpl; unfold divstep_spec.
  rewrite twos_complement_pos_spec, <- (eval_twosc_sat_mod2 machine_wordsize sat_limbs), Zmod_odd; auto; try nia.
  fold (eval_twosc machine_wordsize sat_limbs g); set (g' := eval_twosc machine_wordsize sat_limbs g) in *.
  destruct ((0 <? twosc machine_wordsize d) && (Z.odd g')) eqn:E.
  - apply andb_prop in E. destruct E; rewrite H, H0. simpl Z.b2z; simpl Z.land; cbv [fst].
    unfold Z.zselect. simpl (if _ =? _ then _ else _).
    rewrite twos_complement_opp_correct, twosc_mod, twosc_add_full, twosc_mod, <- twosc_Z_opp, twosc_one; try lia.
    rewrite twosc_mod, <- twosc_Z_opp, twosc_one; lia.
  - apply andb_false_iff in E.
    destruct E; rewrite H;
      unfold Z.zselect; cbv [fst]; simpl (if _ =? _ then _ else _);
        [destruct (Z.odd g') | rewrite Z.land_0_r; simpl (if _ =? _ then _ else _)];
        rewrite twosc_mod, twosc_add_full, twosc_one; try rewrite ?twosc_one; lia. Qed.

Lemma divstep_f machine_wordsize sat_limbs mont_limbs m d f g v r
      (mw0 : 0 < machine_wordsize)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (corner_case : twosc machine_wordsize d <> - 2 ^ (machine_wordsize - 1)) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  eval_twosc machine_wordsize sat_limbs f1 =
  snd (fst (divstep_spec (twosc machine_wordsize d)
                           (eval_twosc machine_wordsize sat_limbs f)
                           (eval_twosc machine_wordsize sat_limbs g))).
Proof.
  destruct sat_limbs. subst.
  unfold eval_twosc.
  rewrite !eval0; rewrite Z.mul_0_r.
  replace (twosc 0 0) with (-1). unfold divstep_spec.
  destruct (0 <? twosc machine_wordsize d); reflexivity. reflexivity.

  unfold divstep_spec.
  simpl.

  set (n' := S sat_limbs) in *.
  assert (0 < n')%nat by apply Nat.lt_0_succ.
  rewrite eval_twosc_select, twos_complement_pos_spec, <- (eval_twosc_sat_mod2 machine_wordsize n'), Zmod_odd; auto.
  fold (eval_twosc machine_wordsize n' g).
  destruct (0 <? twosc machine_wordsize d); destruct (Z.odd (eval_twosc machine_wordsize n' g));
    try reflexivity; lia. Qed.

Theorem divstep_correct machine_wordsize sat_limbs mont_limbs m d f g v r
        (mw1 : 1 < machine_wordsize)
        (sat_limbs0 : (0 < sat_limbs)%nat)
        (fodd : Z.odd (eval_twosc machine_wordsize sat_limbs f) = true)
        (Hf : length f = sat_limbs)
        (Hg : length g = sat_limbs)
        (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    twosc machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1)
        (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                      eval_twosc machine_wordsize sat_limbs f <
                      2 ^ (machine_wordsize * sat_limbs - 2))
        (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                      eval_twosc machine_wordsize sat_limbs g <
                      2 ^ (machine_wordsize * sat_limbs - 2))
        (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
        (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  (twosc machine_wordsize d1,
   eval_twosc machine_wordsize sat_limbs f1,
   eval_twosc machine_wordsize sat_limbs g1) =
  divstep_spec (twosc machine_wordsize d)
               (eval_twosc machine_wordsize sat_limbs f)
               (eval_twosc machine_wordsize sat_limbs g).
Proof.
  assert (0 < machine_wordsize) by lia.
  apply injective_projections.
  apply injective_projections.
  rewrite <- (divstep_d _ _ mont_limbs m _ _ _ v r); auto.
  rewrite <- (divstep_f _ _ mont_limbs m _ _ _ v r); auto; lia.
  rewrite <- (divstep_g _ _ mont_limbs m _ _ _ v r); auto; lia. Qed.

Lemma divstep_v machine_wordsize sat_limbs mont_limbs m (r' : Z) m' d f g v r
      (fodd : Z.odd (eval_twosc machine_wordsize sat_limbs f) = true)

      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (m_big : 1 < m)
      (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
      (Hv2 : valid machine_wordsize mont_limbs m v)
      (Hr2 : valid machine_wordsize mont_limbs m r)
      (mw0 : 0 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat)
      (Hv : length v = mont_limbs)
      (Hr : length r = mont_limbs)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    twosc machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  @WordByWordMontgomery.eval machine_wordsize mont_limbs
                        (from_montgomerymod machine_wordsize mont_limbs m m' v1) mod m =
  fst (divstep_spec2 m (twosc machine_wordsize d)
                (eval_twosc machine_wordsize sat_limbs g)
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' v))
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' r))).
Proof.
  assert (sat_limbs <> 0%nat) by lia.
  assert (mont_limbs <> 0%nat) by lia.
  simpl.
  rewrite twos_complement_pos_spec, <- (eval_twosc_sat_mod2 machine_wordsize sat_limbs) by lia.
  rewrite Zmod_odd, (select_eq (uweight machine_wordsize) _ mont_limbs); auto.
  unfold divstep_spec2.
  destruct (0 <? twosc machine_wordsize d);
    destruct (Z.odd (eval_twosc machine_wordsize sat_limbs g));
    rewrite ?(eval_addmod _ _ _ r'), ?Z.add_diag; auto. Qed.

Lemma nonzero_zero n :
  nonzeromod (sat_zero n) = 0.
Proof. unfold nonzero, sat_zero; induction n; auto. Qed.

Lemma zero_valid machine_wordsize n m
      (mw0 : 0 < machine_wordsize)
      (m0 : 0 < m) :
  valid machine_wordsize n m (sat_zero n).
Proof.
  unfold valid, small, WordByWordMontgomery.eval.
  rewrite eval_sat_zero, partition_0; try split; auto; try lia. Qed.

Lemma divstep_r machine_wordsize sat_limbs mont_limbs m (r' : Z) m' d f g v r
      (fodd : Z.odd (eval_twosc machine_wordsize sat_limbs f) = true)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (m_big : 1 < m)
      (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
      (Hv2 : valid machine_wordsize mont_limbs m v)
      (Hr2 : valid machine_wordsize mont_limbs m r)
      (mw0 : 0 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat)
      (Hv : length v = mont_limbs)
      (Hr : length r = mont_limbs)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    twosc machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1)
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
  @WordByWordMontgomery.eval machine_wordsize mont_limbs
                        (from_montgomerymod machine_wordsize mont_limbs m m' r1) mod m =
  snd (divstep_spec2 m (twosc machine_wordsize d)
                (eval_twosc machine_wordsize sat_limbs g)
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' v))
                (@WordByWordMontgomery.eval machine_wordsize mont_limbs
                                       (from_montgomerymod machine_wordsize mont_limbs m m' r))).
Proof.
  Arguments Z.mul : simpl never.
  assert (sat_limbs0' : (sat_limbs <> 0%nat)) by lia.
  assert (mont_limbs0' : mont_limbs <> 0%nat) by lia.
  unfold divstep_spec2.
  pose proof (oppmod_correct machine_wordsize mont_limbs m r' m' r'_correct m'_correct mw0 m_big (ltac:(lia)) m_small) as H.
  destruct H as [H1 H2].
  assert (zero_valid : valid machine_wordsize mont_limbs m (sat_zero mont_limbs)) by (apply zero_valid; lia).
  pose proof (nonzero_zero mont_limbs) as H3.
  rewrite (nonzeromod_correct machine_wordsize mont_limbs m r' m') in H3; try apply zero_valid; try lia; auto.

  simpl.
  rewrite select_push; rewrite ?length_sat_opp; auto.
  rewrite sat_opp_mod2; auto.
  rewrite twos_complement_pos_spec, <- !(eval_twosc_sat_mod2 machine_wordsize sat_limbs); try lia.
  rewrite !Zmod_odd, !(select_eq (uweight machine_wordsize) _ mont_limbs), fodd;
    try apply length_select; auto.
  destruct (0 <? twosc machine_wordsize d);
    destruct (Z.odd (eval_twosc machine_wordsize sat_limbs g)); simpl.
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite <- Zplus_mod_idemp_l; auto.
    rewrite (eval_oppmod _ _ _ r'); auto.
    rewrite Zplus_mod_idemp_l; auto.
    rewrite Z.add_comm; unfold Z.sub; auto.
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite <- Zplus_mod_idemp_r; auto.
    rewrite H3.
    rewrite Z.mul_0_l, Z.add_0_r; auto.
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite Z.mul_1_l; auto.
  - rewrite (eval_addmod _ _ _ r'); auto.
    rewrite <- Zplus_mod_idemp_r; auto.
    rewrite H3.
    rewrite Z.mul_0_l, Z.add_0_r; auto.
  - apply length_sat_zero.
  - unfold oppmod, WordByWordMontgomery.opp,
    WordByWordMontgomery.sub, Rows.sub_then_maybe_add, Rows.add.
    destruct (Rows.sub (uweight machine_wordsize) mont_limbs (zeros mont_limbs)) eqn:E.
    destruct (Rows.flatten (uweight machine_wordsize) mont_limbs
                           [l; zselect (2 ^ machine_wordsize - 1) (- z) (Partition.partition (uweight machine_wordsize) mont_limbs m)]) eqn:E2.
    simpl.
    inversion E; subst.
    inversion E2.
    apply Rows.length_sum_rows.
    apply (uwprops machine_wordsize mw0).
    apply Rows.length_sum_rows.
    apply (uwprops machine_wordsize mw0).
    apply length_zeros.
    apply map_length.
    rewrite length_zselect.
    apply length_partition. Qed.

Lemma divstep_spec_divstep_spec_full_d m d f g v r :
  fst (fst (divstep_spec d f g)) = fst (fst (fst (fst (divstep_spec_full m d f g v r)))).
Proof. unfold divstep_spec, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

Lemma divstep_spec_divstep_spec_full_f m d f g v r :
  snd (fst (divstep_spec d f g)) = snd (fst (fst (fst (divstep_spec_full m d f g v r)))).
Proof. unfold divstep_spec, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

Lemma divstep_spec_divstep_spec_full_g m d f g v r :
  snd (divstep_spec d f g) = snd (fst (fst (divstep_spec_full m d f g v r))).
Proof. unfold divstep_spec, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

Lemma divstep_spec2_divstep_spec_full_v m d f g v r :
  fst (divstep_spec2 m d g v r) = snd (fst (divstep_spec_full m d f g v r)).
Proof. unfold divstep_spec2, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

Lemma divstep_spec2_divstep_spec_full_r m d f g v r :
  snd (divstep_spec2 m d g v r) = snd (divstep_spec_full m d f g v r).
Proof. unfold divstep_spec2, divstep_spec_full.
       destruct ((0 <? d) && Z.odd g); reflexivity. Qed.

Theorem divstep_correct_full machine_wordsize sat_limbs mont_limbs m r' m' d f g v r
      (fodd : Z.odd (eval_twosc machine_wordsize sat_limbs f) = true)
      (r'_correct : (2 ^ machine_wordsize * r') mod m = 1)
      (m'_correct : (m * m') mod 2 ^ machine_wordsize = -1 mod 2 ^ machine_wordsize)
      (m_big : 1 < m)
      (m_small : m < (2 ^ machine_wordsize) ^ Z.of_nat mont_limbs)
      (mw1 : 1 < machine_wordsize)
      (sat_limbs0 : (0 < sat_limbs)%nat)
      (mont_limbs0 : (0 < mont_limbs)%nat)
      (Hv : length v = mont_limbs)
      (Hr : length r = mont_limbs)
      (Hf : length f = sat_limbs)
      (Hg : length g = sat_limbs)
      (overflow_d : - 2 ^ (machine_wordsize - 1) + 1 <
                    twosc machine_wordsize d <
                    2 ^ (machine_wordsize - 1) - 1)
      (overflow_f : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twosc machine_wordsize sat_limbs f <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (overflow_g : - 2 ^ (machine_wordsize * sat_limbs - 2) <
                    eval_twosc machine_wordsize sat_limbs g <
                    2 ^ (machine_wordsize * sat_limbs - 2))
      (Hf2 : forall z, In z f -> 0 <= z < 2^machine_wordsize)
      (Hg2 : forall z, In z g -> 0 <= z < 2^machine_wordsize)
      (Hv2 : valid machine_wordsize mont_limbs m v)
      (Hr2 : valid machine_wordsize mont_limbs m r) :
  let '(d1,f1,g1,v1,r1) := (divstep machine_wordsize sat_limbs mont_limbs m d f g v r) in
    (twosc machine_wordsize d1,
     eval_twosc machine_wordsize sat_limbs f1,
     eval_twosc machine_wordsize sat_limbs g1,
     @WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' v1) mod m,
     @WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' r1) mod m) =
    divstep_spec_full m (twosc machine_wordsize d)
                      (eval_twosc machine_wordsize sat_limbs f)
                      (eval_twosc machine_wordsize sat_limbs g)
                      (@WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' v))
                      (@WordByWordMontgomery.eval machine_wordsize mont_limbs (from_montgomerymod machine_wordsize mont_limbs m m' r)).
Proof.
  assert (0 < machine_wordsize) by lia.
  repeat apply injective_projections.
  rewrite <- divstep_spec_divstep_spec_full_d, <- (divstep_d _ _ mont_limbs m _ _ _ v r); auto.
  rewrite <- divstep_spec_divstep_spec_full_f, <- (divstep_f _ _ mont_limbs m _ _ _ v r); auto; lia.
  rewrite <- divstep_spec_divstep_spec_full_g, <- (divstep_g _ _ mont_limbs m _ _ _ v r); auto; lia.
  rewrite <- divstep_spec2_divstep_spec_full_v;
    rewrite <- (divstep_v _ _ _ _ r' _ _ f _ _ _); auto.
  rewrite <- divstep_spec2_divstep_spec_full_r;
    rewrite <- (divstep_r _ _ _ _ r' _ _ f _ _ _); auto. Qed.

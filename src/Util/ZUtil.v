Require Import Coq.ZArith.Zpower Coq.ZArith.Znumtheory Coq.ZArith.ZArith Coq.ZArith.Zdiv.
Require Import Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Coq.Structures.Equalities.
Require Import Coq.omega.Omega Coq.micromega.Psatz Coq.Numbers.Natural.Peano.NPeano Coq.Arith.Arith.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Notations.
Require Import Coq.Lists.List.
Require Export Crypto.Util.FixCoqMistakes.
Import Nat.
Local Open Scope Z.

Infix ">>" := Z.shiftr : Z_scope.
Infix "<<" := Z.shiftl : Z_scope.
Infix "&" := Z.land : Z_scope.

Hint Extern 1 => lia : lia.
Hint Extern 1 => lra : lra.
Hint Extern 1 => nia : nia.
Hint Extern 1 => omega : omega.
Hint Resolve Z.log2_nonneg Z.div_small Z.mod_small Z.pow_neg_r Z.pow_0_l Z.pow_pos_nonneg Z.lt_le_incl Z.pow_nonzero Z.div_le_upper_bound Z_div_exact_full_2 Z.div_same Z.div_lt_upper_bound Z.div_le_lower_bound Zplus_minus Zplus_gt_compat_l Zplus_gt_compat_r Zmult_gt_compat_l Zmult_gt_compat_r : zarith.
Hint Resolve (fun a b H => proj1 (Z.mod_pos_bound a b H)) (fun a b H => proj2 (Z.mod_pos_bound a b H)) : zarith.

Ltac zutil_arith := solve [ omega | lia ].

(** Only hints that are always safe to apply (i.e., reversible), and
    which can reasonably be said to "simplify" the goal, should go in
    this database. *)
Create HintDb zsimplify discriminated.
Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r Z_mod_same_full Z.sub_simpl_r Z.sub_simpl_l Z.add_opp_diag_r Z.add_opp_diag_l Zmod_0_l Z.add_simpl_r Z.add_simpl_l Z.opp_0 Zmod_0_r Zmod_mod Z.mul_succ_l Z.mul_succ_r Z.shiftr_0_r Z.shiftr_0_l Z.mod_1_r Zmod_0_l Zmod_0_r Z.shiftl_0_r Z.shiftl_0_l Z.shiftr_0_r Z.shiftr_0_l : zsimplify.
Hint Rewrite Z.div_mul Z.div_1_l Z.div_same Z.mod_same Z.div_small Z.mod_small Z.div_add Z.div_add_l Z.mod_add Z.div_0_l Z.mod_mod Z.mod_small Z_mod_zero_opp_full Z.mod_1_l using zutil_arith : zsimplify.
Hint Rewrite <- Z.opp_eq_mul_m1 Z.one_succ Z.two_succ : zsimplify.
Hint Rewrite <- Z.div_mod using zutil_arith : zsimplify.

(** "push" means transform [-f x] to [f (-x)]; "pull" means go the other way *)
Create HintDb push_Zopp discriminated.
Create HintDb pull_Zopp discriminated.
Create HintDb push_Zpow discriminated.
Create HintDb pull_Zpow discriminated.
Create HintDb push_Zmul discriminated.
Create HintDb pull_Zmul discriminated.
Create HintDb push_Zdiv discriminated.
Create HintDb pull_Zdiv discriminated.
Create HintDb push_Zadd discriminated.
Create HintDb pull_Zadd discriminated.
Create HintDb push_Zsub discriminated.
Create HintDb pull_Zsub discriminated.
Create HintDb pull_Zmod discriminated.
Create HintDb push_Zmod discriminated.
Create HintDb pull_Zof_nat discriminated.
Create HintDb push_Zof_nat discriminated.
Create HintDb pull_Zshift discriminated.
Create HintDb push_Zshift discriminated.
Create HintDb Zshift_to_pow discriminated.
Create HintDb Zpow_to_shift discriminated.
Hint Extern 1 => autorewrite with push_Zopp in * : push_Zopp.
Hint Extern 1 => autorewrite with pull_Zopp in * : pull_Zopp.
Hint Extern 1 => autorewrite with push_Zpow in * : push_Zpow.
Hint Extern 1 => autorewrite with pull_Zpow in * : pull_Zpow.
Hint Extern 1 => autorewrite with push_Zmul in * : push_Zmul.
Hint Extern 1 => autorewrite with pull_Zmul in * : pull_Zmul.
Hint Extern 1 => autorewrite with push_Zadd in * : push_Zadd.
Hint Extern 1 => autorewrite with pull_Zadd in * : pull_Zadd.
Hint Extern 1 => autorewrite with push_Zsub in * : push_Zsub.
Hint Extern 1 => autorewrite with pull_Zsub in * : pull_Zsub.
Hint Extern 1 => autorewrite with push_Zdiv in * : push_Zmul.
Hint Extern 1 => autorewrite with pull_Zdiv in * : pull_Zmul.
Hint Extern 1 => autorewrite with pull_Zmod in * : pull_Zmod.
Hint Extern 1 => autorewrite with push_Zmod in * : push_Zmod.
Hint Extern 1 => autorewrite with pull_Zof_nat in * : pull_Zof_nat.
Hint Extern 1 => autorewrite with push_Zof_nat in * : push_Zof_nat.
Hint Extern 1 => autorewrite with pull_Zshift in * : pull_Zshift.
Hint Extern 1 => autorewrite with push_Zshift in * : push_Zshift.
Hint Extern 1 => autorewrite with Zshift_to_pow in * : Zshift_to_pow.
Hint Extern 1 => autorewrite with Zpow_to_shift in * : Zpow_to_shift.
Hint Rewrite Z.div_opp_l_nz Z.div_opp_l_z using zutil_arith : pull_Zopp.
Hint Rewrite Z.mul_opp_l : pull_Zopp.
Hint Rewrite <- Z.opp_add_distr : pull_Zopp.
Hint Rewrite <- Z.div_opp_l_nz Z.div_opp_l_z using zutil_arith : push_Zopp.
Hint Rewrite <- Z.mul_opp_l : push_Zopp.
Hint Rewrite Z.opp_add_distr : push_Zopp.
Hint Rewrite Z.pow_sub_r Z.pow_div_l Z.pow_twice_r Z.pow_mul_l Z.pow_add_r using zutil_arith : push_Zpow.
Hint Rewrite <- Z.pow_sub_r Z.pow_div_l Z.pow_mul_l Z.pow_add_r Z.pow_twice_r using zutil_arith : pull_Zpow.
Hint Rewrite Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : push_Zmul.
Hint Rewrite <- Z.mul_add_distr_l Z.mul_add_distr_r Z.mul_sub_distr_l Z.mul_sub_distr_r : pull_Zmul.
Hint Rewrite Z.div_div using zutil_arith : pull_Zdiv.
Hint Rewrite <- Z.div_div using zutil_arith : push_Zdiv.
Hint Rewrite <- Z.mul_mod Z.add_mod Zminus_mod using zutil_arith : pull_Zmod.
Hint Rewrite Zminus_mod_idemp_l Zminus_mod_idemp_r : pull_Zmod.
Hint Rewrite Z_mod_nz_opp_full using zutil_arith : push_Zmod.
Hint Rewrite Nat2Z.id : zsimplify.
Hint Rewrite Nat2Z.id : push_Zof_nat.
Hint Rewrite Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : push_Zof_nat.
Hint Rewrite <- Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : pull_Zof_nat.
Hint Rewrite Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : pull_Zshift.
Hint Rewrite <- Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : pull_Zshift.
Hint Rewrite Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : push_Zshift.
Hint Rewrite <- Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : push_Zshift.
Hint Rewrite Z.shiftr_opp_r Z.shiftl_opp_r Z.shiftr_0_r Z.shiftr_0_l Z.shiftl_0_r Z.shiftl_0_l : push_Zshift.
Hint Rewrite Z.shiftl_1_l Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_opp_r using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : Zpow_to_shift.

(** For the occasional lemma that can remove the use of [Z.div] *)
Create HintDb zstrip_div.
Hint Rewrite Z.div_small_iff using zutil_arith : zstrip_div.

(** It's not clear that [mod] is much easier for [lia] than [Z.div],
    so we separate out the transformations between [mod] and [div].
    We'll put, e.g., [mul_div_eq] into it below. *)
Create HintDb zstrip_div.

(** Work around bug #5019, that [zify] loops on dependent types.  We
    copy/paste [zify_nat_op] from the standard library and add a case
    to each of the [match isnat with ... end]. *)
Ltac zify_nat_op ::=
 match goal with
  (* misc type conversions: positive/N/Z to nat *)
  | H : context [ Z.of_nat (Pos.to_nat ?a) ] |- _ => rewrite (positive_nat_Z a) in H
  | |- context [ Z.of_nat (Pos.to_nat ?a) ] => rewrite (positive_nat_Z a)
  | H : context [ Z.of_nat (N.to_nat ?a) ] |- _ => rewrite (N_nat_Z a) in H
  | |- context [ Z.of_nat (N.to_nat ?a) ] => rewrite (N_nat_Z a)
  | H : context [ Z.of_nat (Z.abs_nat ?a) ] |- _ => rewrite (Zabs2Nat.id_abs a) in H
  | |- context [ Z.of_nat (Z.abs_nat ?a) ] => rewrite (Zabs2Nat.id_abs a)

  (* plus -> Z.add *)
  | H : context [ Z.of_nat (plus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_add a b) in H
  | |- context [ Z.of_nat (plus ?a ?b) ] => rewrite (Nat2Z.inj_add a b)

  (* min -> Z.min *)
  | H : context [ Z.of_nat (min ?a ?b) ] |- _ => rewrite (Nat2Z.inj_min a b) in H
  | |- context [ Z.of_nat (min ?a ?b) ] => rewrite (Nat2Z.inj_min a b)

  (* max -> Z.max *)
  | H : context [ Z.of_nat (max ?a ?b) ] |- _ => rewrite (Nat2Z.inj_max a b) in H
  | |- context [ Z.of_nat (max ?a ?b) ] => rewrite (Nat2Z.inj_max a b)

  (* minus -> Z.max (Z.sub ... ...) 0 *)
  | H : context [ Z.of_nat (minus ?a ?b) ] |- _ => rewrite (Nat2Z.inj_sub_max a b) in H
  | |- context [ Z.of_nat (minus ?a ?b) ] => rewrite (Nat2Z.inj_sub_max a b)

  (* pred -> minus ... -1 -> Z.max (Z.sub ... -1) 0 *)
  | H : context [ Z.of_nat (pred ?a) ] |- _ => rewrite (pred_of_minus a) in H
  | |- context [ Z.of_nat (pred ?a) ] => rewrite (pred_of_minus a)

  (* mult -> Z.mul and a positivity hypothesis *)
  | H : context [ Z.of_nat (mult ?a ?b) ] |- _ =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *
  | |- context [ Z.of_nat (mult ?a ?b) ] =>
        pose proof (Nat2Z.is_nonneg (mult a b));
        rewrite (Nat2Z.inj_mul a b) in *

  (* O -> Z0 *)
  | H : context [ Z.of_nat O ] |- _ => simpl (Z.of_nat O) in H
  | |- context [ Z.of_nat O ] => simpl (Z.of_nat O)

  (* S -> number or Z.succ *)
  | H : context [ Z.of_nat (S ?a) ] |- _ =>
     let isnat := isnatcst a in
     match isnat with
      | true => simpl (Z.of_nat (S a)) in H
      | _ => rewrite (Nat2Z.inj_succ a) in H
      | _ => change (Z.of_nat (S a)) with (Z_of_nat' (S a)) in H
     end
  | |- context [ Z.of_nat (S ?a) ] =>
     let isnat := isnatcst a in
     match isnat with
      | true => simpl (Z.of_nat (S a))
      | _ => rewrite (Nat2Z.inj_succ a)
      | _ => change (Z.of_nat (S a)) with (Z_of_nat' (S a))
     end

  (* atoms of type nat : we add a positivity condition (if not already there) *)
  | _ : 0 <= Z.of_nat ?a |- _ => hide_Z_of_nat a
  | _ : context [ Z.of_nat ?a ] |- _ =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
  | |- context [ Z.of_nat ?a ] =>
    pose proof (Nat2Z.is_nonneg a); hide_Z_of_nat a
 end.

Ltac comes_before ls x y :=
  match ls with
  | context[cons x ?xs]
    => match xs with
       | context[y] => idtac
       end
  end.
Ltac canonicalize_comm_step mul ls comm comm3 :=
  match goal with
  | [ |- appcontext[mul ?x ?y] ]
    => comes_before ls y x;
       rewrite (comm x y)
  | [ |- appcontext[mul ?x (mul ?y ?z)] ]
    => comes_before ls y x;
       rewrite (comm3 x y z)
  end.
Ltac canonicalize_comm mul ls comm comm3 := repeat canonicalize_comm_step mul ls comm comm3.

Module Z.
  Definition pow2_mod n i := (n & (Z.ones i)).

  Lemma pow2_mod_spec : forall a b, (0 <= b) -> Z.pow2_mod a b = a mod (2 ^ b).
  Proof.
    intros.
    unfold Z.pow2_mod.
    rewrite Z.land_ones; auto.
  Qed.

  Lemma mul_comm3 x y z : x * (y * z) = y * (x * z).
  Proof. lia. Qed.

  Ltac Zcanonicalize_comm ls := canonicalize_comm Z.mul ls Z.mul_comm mul_comm3.

  Lemma positive_is_nonzero : forall x, x > 0 -> x <> 0.
  Proof. intros; omega. Qed.

  Hint Resolve positive_is_nonzero : zarith.

  Lemma div_positive_gt_0 : forall a b, a > 0 -> b > 0 -> a mod b = 0 ->
    a / b > 0.
  Proof.
    intros; rewrite Z.gt_lt_iff.
    apply Z.div_str_pos.
    split; intuition auto with omega.
    apply Z.divide_pos_le; try (apply Zmod_divide); omega.
  Qed.

  Lemma elim_mod : forall a b m, a = b -> a mod m = b mod m.
  Proof. intros; subst; auto. Qed.

  Hint Resolve elim_mod : zarith.

  Lemma mod_add_l : forall a b c, b <> 0 -> (a * b + c) mod b = c mod b.
  Proof. intros; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_l using zutil_arith : zsimplify.

  Lemma mod_add' : forall a b c, b <> 0 -> (a + b * c) mod b = a mod b.
  Proof. intros; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l' : forall a b c, a <> 0 -> (a * b + c) mod a = c mod a.
  Proof. intros; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add' mod_add_l' using zutil_arith : zsimplify.

  Lemma pos_pow_nat_pos : forall x n,
    Z.pos x ^ Z.of_nat n > 0.
  Proof.
    do 2 (intros; induction n; subst; simpl in *; auto with zarith).
    rewrite <- Pos.add_1_r, Zpower_pos_is_exp.
    apply Zmult_gt_0_compat; auto; reflexivity.
  Qed.

  Lemma div_mul' : forall a b : Z, b <> 0 -> (b * a) / b = a.
  Proof. intros. rewrite Z.mul_comm. apply Z.div_mul; auto. Qed.
  Hint Rewrite div_mul' using zutil_arith : zsimplify.

  (** TODO: Should we get rid of this duplicate? *)
  Notation gt0_neq0 := positive_is_nonzero (only parsing).

  Lemma pow_Z2N_Zpow : forall a n, 0 <= a ->
    ((Z.to_nat a) ^ n = Z.to_nat (a ^ Z.of_nat n)%Z)%nat.
  Proof.
    intros; induction n; try reflexivity.
    rewrite Nat2Z.inj_succ.
    rewrite pow_succ_r by apply le_0_n.
    rewrite Z.pow_succ_r by apply Zle_0_nat.
    rewrite IHn.
    rewrite Z2Nat.inj_mul; auto using Z.pow_nonneg.
  Qed.

  Lemma pow_Zpow : forall a n : nat, Z.of_nat (a ^ n) = Z.of_nat a ^ Z.of_nat n.
  Proof with auto using Zle_0_nat, Z.pow_nonneg.
    intros; apply Z2Nat.inj...
    rewrite <- pow_Z2N_Zpow, !Nat2Z.id...
  Qed.
  Hint Rewrite pow_Zpow : push_Zof_nat.
  Hint Rewrite <- pow_Zpow : pull_Zof_nat.

  Lemma mod_exp_0 : forall a x m, x > 0 -> m > 1 -> a mod m = 0 ->
    a ^ x mod m = 0.
  Proof.
    intros.
    replace x with (Z.of_nat (Z.to_nat x)) in * by (apply Z2Nat.id; omega).
    induction (Z.to_nat x). {
      simpl in *; omega.
    } {
      rewrite Nat2Z.inj_succ in *.
      rewrite Z.pow_succ_r by omega.
      rewrite Z.mul_mod by omega.
      case_eq n; intros. {
        subst. simpl.
        rewrite Zmod_1_l by omega.
        rewrite H1.
        apply Zmod_0_l.
      } {
        subst.
        rewrite IHn by (rewrite Nat2Z.inj_succ in *; omega).
        rewrite H1.
        auto.
      }
    }
  Qed.

  Lemma mod_pow : forall (a m b : Z), (0 <= b) -> (m <> 0) ->
      a ^ b mod m = (a mod m) ^ b mod m.
  Proof.
    intros; rewrite <- (Z2Nat.id b) by auto.
    induction (Z.to_nat b); auto.
    rewrite Nat2Z.inj_succ.
    do 2 rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
    rewrite Z.mul_mod by auto.
    rewrite (Z.mul_mod (a mod m) ((a mod m) ^ Z.of_nat n) m) by auto.
    rewrite <- IHn by auto.
    rewrite Z.mod_mod by auto.
    reflexivity.
  Qed.

  Ltac divide_exists_mul := let k := fresh "k" in
  match goal with
  | [ H : (?a | ?b) |- _ ] => apply Z.mod_divide in H; try apply Zmod_divides in H; destruct H as [k H]
  | [ |- (?a | ?b) ] => apply Z.mod_divide; try apply Zmod_divides
  end; (omega || auto).

  Lemma divide_mul_div: forall a b c (a_nonzero : a <> 0) (c_nonzero : c <> 0),
    (a | b * (a / c)) -> (c | a) -> (c | b).
  Proof.
    intros ? ? ? ? ? divide_a divide_c_a; do 2 divide_exists_mul.
    rewrite divide_c_a in divide_a.
    rewrite div_mul' in divide_a by auto.
    replace (b * k) with (k * b) in divide_a by ring.
    replace (c * k * k0) with (k * (k0 * c)) in divide_a by ring.
    rewrite Z.mul_cancel_l in divide_a by (intuition auto with nia; rewrite H in divide_c_a; ring_simplify in divide_a; intuition).
    eapply Zdivide_intro; eauto.
  Qed.

  Lemma divide2_even_iff : forall n, (2 | n) <-> Z.even n = true.
  Proof.
    intro; split. {
      intro divide2_n.
      divide_exists_mul; [ | pose proof (Z.mod_pos_bound n 2); omega].
      rewrite divide2_n.
      apply Z.even_mul.
    } {
      intro n_even.
      pose proof (Zmod_even n).
      rewrite n_even in H.
      apply Zmod_divide; omega || auto.
    }
  Qed.

  Lemma prime_odd_or_2 : forall p (prime_p : prime p), p = 2 \/ Z.odd p = true.
  Proof.
    intros.
    apply Decidable.imp_not_l; try apply Z.eq_decidable.
    intros p_neq2.
    pose proof (Zmod_odd p) as mod_odd.
    destruct (Sumbool.sumbool_of_bool (Z.odd p)) as [? | p_not_odd]; auto.
    rewrite p_not_odd in mod_odd.
    apply Zmod_divides in mod_odd; try omega.
    destruct mod_odd as [c c_id].
    rewrite Z.mul_comm in c_id.
    apply Zdivide_intro in c_id.
    apply prime_divisors in c_id; auto.
    destruct c_id; [omega | destruct H; [omega | destruct H; auto] ].
    pose proof (prime_ge_2 p prime_p); omega.
  Qed.

  Lemma mul_div_eq : forall a m, m > 0 -> m * (a / m) = (a - a mod m).
  Proof.
    intros.
    rewrite (Z_div_mod_eq a m) at 2 by auto.
    ring.
  Qed.

  Lemma mul_div_eq' : (forall a m, m > 0 -> (a / m) * m = (a - a mod m))%Z.
  Proof.
    intros.
    rewrite (Z_div_mod_eq a m) at 2 by auto.
    ring.
  Qed.

  Hint Rewrite mul_div_eq mul_div_eq' using zutil_arith : zdiv_to_mod.
  Hint Rewrite <- mul_div_eq' using zutil_arith : zmod_to_div.

  Ltac prime_bound := match goal with
  | [ H : prime ?p |- _ ] => pose proof (prime_ge_2 p H); try omega
  end.

  Lemma testbit_low : forall n x i, (0 <= i < n) ->
    Z.testbit x i = Z.testbit (Z.land x (Z.ones n)) i.
  Proof.
    intros.
    rewrite Z.land_ones by omega.
    symmetry.
    apply Z.mod_pow2_bits_low.
    omega.
  Qed.


  Lemma testbit_add_shiftl_low : forall i, (0 <= i) -> forall a b n, (i < n) ->
    Z.testbit (a + Z.shiftl b n) i = Z.testbit a i.
  Proof.
    intros.
    erewrite Z.testbit_low; eauto.
    rewrite Z.land_ones, Z.shiftl_mul_pow2 by omega.
    rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 n); omega).
    auto using Z.mod_pow2_bits_low.
  Qed.

  Lemma mod_div_eq0 : forall a b, 0 < b -> (a mod b) / b = 0.
  Proof.
    intros.
    apply Z.div_small.
    auto using Z.mod_pos_bound.
  Qed.
  Hint Rewrite mod_div_eq0 using zutil_arith : zsimplify.

  Lemma shiftr_add_shiftl_high : forall n m a b, 0 <= n <= m -> 0 <= a < 2 ^ n ->
    Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr b (m - n).
  Proof.
    intros.
    rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by omega.
    replace (2 ^ m) with (2 ^ n * 2 ^ (m - n)) by
      (rewrite <-Z.pow_add_r by omega; f_equal; ring).
    rewrite <-Z.div_div, Z.div_add, (Z.div_small a) ; try solve
      [assumption || apply Z.pow_nonzero || apply Z.pow_pos_nonneg; omega].
    f_equal; ring.
  Qed.
  Hint Rewrite Z.shiftr_add_shiftl_high using zutil_arith : pull_Zshift.
  Hint Rewrite <- Z.shiftr_add_shiftl_high using zutil_arith : push_Zshift.

  Lemma shiftr_add_shiftl_low : forall n m a b, 0 <= m <= n -> 0 <= a < 2 ^ n ->
    Z.shiftr (a + (Z.shiftl b n)) m = Z.shiftr a m + Z.shiftr b (m - n).
  Proof.
    intros.
    rewrite !Z.shiftr_div_pow2, Z.shiftl_mul_pow2, Z.shiftr_mul_pow2 by omega.
    replace (2 ^ n) with (2 ^ (n - m) * 2 ^ m) by
      (rewrite <-Z.pow_add_r by omega; f_equal; ring).
    rewrite Z.mul_assoc, Z.div_add by (apply Z.pow_nonzero; omega).
    repeat f_equal; ring.
  Qed.
  Hint Rewrite Z.shiftr_add_shiftl_low using zutil_arith : pull_Zshift.
  Hint Rewrite <- Z.shiftr_add_shiftl_low using zutil_arith : push_Zshift.

  Lemma testbit_add_shiftl_high : forall i, (0 <= i) -> forall a b n, (0 <= n <= i) ->
    0 <= a < 2 ^ n ->
    Z.testbit (a + Z.shiftl b n) i = Z.testbit b (i - n).
  Proof.
    intros ? ?.
    apply natlike_ind with (x := i); intros; try assumption;
      (destruct (Z_eq_dec 0 n); [ subst; rewrite Z.pow_0_r in *;
       replace a with 0 by omega; f_equal; ring | ]); try omega.
    rewrite <-Z.add_1_r at 1. rewrite <-Z.shiftr_spec by assumption.
    replace (Z.succ x - n) with (x - (n - 1)) by ring.
    rewrite shiftr_add_shiftl_low, <-Z.shiftl_opp_r with (a := b) by omega.
    rewrite <-H1 with (a := Z.shiftr a 1); try omega; [ repeat f_equal; ring | ].
    rewrite Z.shiftr_div_pow2 by omega.
    split; apply Z.div_pos || apply Z.div_lt_upper_bound;
      try solve [rewrite ?Z.pow_1_r; omega].
    rewrite <-Z.pow_add_r by omega.
    replace (1 + (n - 1)) with n by ring; omega.
  Qed.

  Lemma land_add_land : forall n m a b, (m <= n)%nat ->
    Z.land ((Z.land a (Z.ones (Z.of_nat n))) + (Z.shiftl b (Z.of_nat n))) (Z.ones (Z.of_nat m)) = Z.land a (Z.ones (Z.of_nat m)).
  Proof.
    intros.
    rewrite !Z.land_ones by apply Nat2Z.is_nonneg.
    rewrite Z.shiftl_mul_pow2 by apply Nat2Z.is_nonneg.
    replace (b * 2 ^ Z.of_nat n) with
      ((b * 2 ^ Z.of_nat (n - m)) * 2 ^ Z.of_nat m) by
      (rewrite (le_plus_minus m n) at 2; try assumption;
       rewrite Nat2Z.inj_add, Z.pow_add_r by apply Nat2Z.is_nonneg; ring).
    rewrite Z.mod_add by (pose proof (Z.pow_pos_nonneg 2 (Z.of_nat m)); omega).
    symmetry. apply Znumtheory.Zmod_div_mod; try (apply Z.pow_pos_nonneg; omega).
    rewrite (le_plus_minus m n) by assumption.
    rewrite Nat2Z.inj_add, Z.pow_add_r by apply Nat2Z.is_nonneg.
    apply Z.divide_factor_l.
  Qed.

  Lemma div_pow2succ : forall n x, (0 <= x) ->
    n / 2 ^ Z.succ x = Z.div2 (n / 2 ^ x).
  Proof.
    intros.
    rewrite Z.pow_succ_r, Z.mul_comm by auto.
    rewrite <- Z.div_div by (try apply Z.pow_nonzero; omega).
    rewrite Zdiv2_div.
    reflexivity.
  Qed.

  Lemma shiftr_succ : forall n x,
    Z.shiftr n (Z.succ x) = Z.shiftr (Z.shiftr n x) 1.
  Proof.
    intros.
    rewrite Z.shiftr_shiftr by omega.
    reflexivity.
  Qed.
  Hint Rewrite Z.shiftr_succ using zutil_arith : push_Zshift.
  Hint Rewrite <- Z.shiftr_succ using zutil_arith : pull_Zshift.

  Definition shiftl_by n a := Z.shiftl a n.

  Lemma shiftl_by_mul_pow2 : forall n a, 0 <= n -> Z.mul (2 ^ n) a = Z.shiftl_by n a.
  Proof.
    intros.
    unfold Z.shiftl_by.
    rewrite Z.shiftl_mul_pow2 by assumption.
    apply Z.mul_comm.
  Qed.

  Lemma map_shiftl : forall n l, 0 <= n -> map (Z.mul (2 ^ n)) l = map (Z.shiftl_by n) l.
  Proof.
    intros; induction l; auto using Z.shiftl_by_mul_pow2.
    simpl.
    rewrite IHl.
    f_equal.
    apply Z.shiftl_by_mul_pow2.
    assumption.
  Qed.

  Lemma odd_mod : forall a b, (b <> 0)%Z ->
    Z.odd (a mod b) = if Z.odd b then xorb (Z.odd a) (Z.odd (a / b)) else Z.odd a.
  Proof.
    intros.
    rewrite Zmod_eq_full by assumption.
    rewrite <-Z.add_opp_r, Z.odd_add, Z.odd_opp, Z.odd_mul.
    case_eq (Z.odd b); intros; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; auto using Bool.xorb_false_r.
  Qed.

  Lemma mod_same_pow : forall a b c, 0 <= c <= b -> a ^ b mod a ^ c = 0.
  Proof.
    intros.
    replace b with (b - c + c) by ring.
    rewrite Z.pow_add_r by omega.
    apply Z_mod_mult.
  Qed.
  Hint Rewrite mod_same_pow using zutil_arith : zsimplify.

  Lemma ones_succ : forall x, (0 <= x) ->
    Z.ones (Z.succ x) = 2 ^ x + Z.ones x.
  Proof.
    unfold Z.ones; intros.
    rewrite !Z.shiftl_1_l.
    rewrite Z.add_pred_r.
    apply Z.succ_inj.
    rewrite !Z.succ_pred.
    rewrite Z.pow_succ_r; omega.
  Qed.

  Lemma div_floor : forall a b c, 0 < b -> a < b * (Z.succ c) -> a / b <= c.
  Proof.
    intros.
    apply Z.lt_succ_r.
    apply Z.div_lt_upper_bound; try omega.
  Qed.

  Lemma shiftr_1_r_le : forall a b, a <= b ->
    Z.shiftr a 1 <= Z.shiftr b 1.
  Proof.
    intros.
    rewrite !Z.shiftr_div_pow2, Z.pow_1_r by omega.
    apply Z.div_le_mono; omega.
  Qed.
  Hint Resolve shiftr_1_r_le : zarith.

  Lemma shiftr_le : forall a b i : Z, 0 <= i -> a <= b -> a >> i <= b >> i.
  Proof.
    intros until 1. revert a b. apply natlike_ind with (x := i); intros; auto.
    rewrite !shiftr_succ, shiftr_1_r_le; eauto. reflexivity.
  Qed.
  Hint Resolve shiftr_le : zarith.

  Lemma ones_pred : forall i, 0 < i -> Z.ones (Z.pred i) = Z.shiftr (Z.ones i) 1.
  Proof.
    induction i; [ | | pose proof (Pos2Z.neg_is_neg p) ]; try omega.
    intros.
    unfold Z.ones.
    rewrite !Z.shiftl_1_l, Z.shiftr_div_pow2, <-!Z.sub_1_r, Z.pow_1_r, <-!Z.add_opp_r by omega.
    replace (2 ^ (Z.pos p)) with (2 ^ (Z.pos p - 1)* 2).
    rewrite Z.div_add_l by omega.
    reflexivity.
    change 2 with (2 ^ 1) at 2.
    rewrite <-Z.pow_add_r by (pose proof (Pos2Z.is_pos p); omega).
    f_equal. omega.
  Qed.
  Hint Rewrite <- ones_pred using zutil_arith : push_Zshift.

  Lemma shiftr_ones' : forall a n, 0 <= a < 2 ^ n -> forall i, (0 <= i) ->
    Z.shiftr a i <= Z.ones (n - i) \/ n <= i.
  Proof.
    intros until 1.
    apply natlike_ind.
    + unfold Z.ones.
      rewrite Z.shiftr_0_r, Z.shiftl_1_l, Z.sub_0_r.
      omega.
    + intros.
      destruct (Z_lt_le_dec x n); try omega.
      intuition auto with zarith lia.
      left.
      rewrite shiftr_succ.
      replace (n - Z.succ x) with (Z.pred (n - x)) by omega.
      rewrite Z.ones_pred by omega.
      apply Z.shiftr_1_r_le.
      assumption.
  Qed.

  Lemma shiftr_ones : forall a n i, 0 <= a < 2 ^ n -> (0 <= i) -> (i <= n) ->
    Z.shiftr a i <= Z.ones (n - i) .
  Proof.
    intros a n i G G0 G1.
    destruct (Z_le_lt_eq_dec i n G1).
    + destruct (Z.shiftr_ones' a n G i G0); omega.
    + subst; rewrite Z.sub_diag.
      destruct (Z_eq_dec a 0).
      - subst; rewrite Z.shiftr_0_l; reflexivity.
      - rewrite Z.shiftr_eq_0; try omega; try reflexivity.
        apply Z.log2_lt_pow2; omega.
  Qed.
  Hint Resolve shiftr_ones : zarith.

  Lemma shiftr_upper_bound : forall a n, 0 <= n -> 0 <= a <= 2 ^ n -> Z.shiftr a n <= 1.
  Proof.
    intros a ? ? [a_nonneg a_upper_bound].
    apply Z_le_lt_eq_dec in a_upper_bound.
    destruct a_upper_bound.
    + destruct (Z_eq_dec 0 a).
      - subst; rewrite Z.shiftr_0_l; omega.
      - rewrite Z.shiftr_eq_0; auto; try omega.
        apply Z.log2_lt_pow2; auto; omega.
    + subst.
      rewrite Z.shiftr_div_pow2 by assumption.
      rewrite Z.div_same; try omega.
      assert (0 < 2 ^ n) by (apply Z.pow_pos_nonneg; omega).
      omega.
  Qed.
  Hint Resolve shiftr_upper_bound : zarith.

  Lemma lor_shiftl : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor a (Z.shiftl b n) = a + (Z.shiftl b n).
  Proof.
    intros.
    apply Z.bits_inj'; intros t ?.
    rewrite Z.lor_spec, Z.shiftl_spec by assumption.
    destruct (Z_lt_dec t n).
    + rewrite testbit_add_shiftl_low by omega.
      rewrite Z.testbit_neg_r with (n := t - n) by omega.
      apply Bool.orb_false_r.
    + rewrite testbit_add_shiftl_high by omega.
      replace (Z.testbit a t) with false; [ apply Bool.orb_false_l | ].
      symmetry.
      apply Z.testbit_false; try omega.
      rewrite Z.div_small; try reflexivity.
      split; try eapply Z.lt_le_trans with (m := 2 ^ n); try omega.
      apply Z.pow_le_mono_r; omega.
  Qed.

  (* prove that combinations of known positive/nonnegative numbers are positive/nonnegative *)
  Ltac zero_bounds' :=
    repeat match goal with
    | [ |- 0 <= _ + _] => apply Z.add_nonneg_nonneg
    | [ |- 0 <= _ - _] => apply Z.le_0_sub
    | [ |- 0 <= _ * _] => apply Z.mul_nonneg_nonneg
    | [ |- 0 <= _ / _] => apply Z.div_pos
    | [ |- 0 <= _ ^ _ ] => apply Z.pow_nonneg
    | [ |- 0 <= Z.shiftr _ _] => apply Z.shiftr_nonneg
    | [ |- 0 <= _ mod _] => apply Z.mod_pos_bound
    | [ |- 0 < _ + _] => try solve [apply Z.add_pos_nonneg; zero_bounds'];
                         try solve [apply Z.add_nonneg_pos; zero_bounds']
    | [ |- 0 < _ - _] => apply Z.lt_0_sub
    | [ |- 0 < _ * _] => apply Z.lt_0_mul; left; split
    | [ |- 0 < _ / _] => apply Z.div_str_pos
    | [ |- 0 < _ ^ _ ] => apply Z.pow_pos_nonneg
    end; try omega; try prime_bound; auto.

  Ltac zero_bounds := try omega; try prime_bound; zero_bounds'.

  Hint Extern 1 => progress zero_bounds : zero_bounds.

  Lemma ones_nonneg : forall i, (0 <= i) -> 0 <= Z.ones i.
  Proof.
    apply natlike_ind.
    + unfold Z.ones. simpl; omega.
    + intros.
      rewrite Z.ones_succ by assumption.
      zero_bounds.
  Qed.

  Lemma ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
  Proof.
    intros.
    unfold Z.ones.
    rewrite Z.shiftl_1_l.
    apply Z.lt_succ_lt_pred.
    apply Z.pow_gt_1; omega.
  Qed.

  Lemma N_le_1_l : forall p, (1 <= N.pos p)%N.
  Proof.
    destruct p; cbv; congruence.
  Qed.

  Lemma Pos_land_upper_bound_l : forall a b, (Pos.land a b <= N.pos a)%N.
  Proof.
    induction a; destruct b; intros; try solve [cbv; congruence];
      simpl; specialize (IHa b); case_eq (Pos.land a b); intro; simpl;
      try (apply N_le_1_l || apply N.le_0_l); intro land_eq;
      rewrite land_eq in *; unfold N.le, N.compare in *;
      rewrite ?Pos.compare_xI_xI, ?Pos.compare_xO_xI, ?Pos.compare_xO_xO;
      try assumption.
    destruct (p ?=a)%positive; cbv; congruence.
  Qed.

  Lemma land_upper_bound_l : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= a.
  Proof.
    intros.
    destruct a, b; try solve [exfalso; auto]; try solve [cbv; congruence].
    cbv [Z.land].
    rewrite <-N2Z.inj_pos, <-N2Z.inj_le.
    auto using Pos_land_upper_bound_l.
  Qed.

  Lemma land_upper_bound_r : forall a b, (0 <= a) -> (0 <= b) ->
    Z.land a b <= b.
  Proof.
    intros.
    rewrite Z.land_comm.
    auto using Z.land_upper_bound_l.
  Qed.

  Lemma le_fold_right_max : forall low l x, (forall y, In y l -> low <= y) ->
    In x l -> x <= fold_right Z.max low l.
  Proof.
    induction l; intros ? lower_bound In_list; [cbv [In] in *; intuition | ].
    simpl.
    destruct (in_inv In_list); subst.
    + apply Z.le_max_l.
    + etransitivity.
      - apply IHl; auto; intuition auto with datatypes.
      - apply Z.le_max_r.
  Qed.

  Lemma le_fold_right_max_initial : forall low l, low <= fold_right Z.max low l.
  Proof.
    induction l; intros; try reflexivity.
    etransitivity; [ apply IHl | apply Z.le_max_r ].
  Qed.

  Ltac ltb_to_lt_with_hyp H lem :=
    let H' := fresh in
    rename H into H';
    pose proof lem as H;
    rewrite H' in H;
    clear H'.

  Ltac ltb_to_lt :=
    repeat match goal with
           | [ H : (?x <? ?y) = ?b |- _ ]
             => ltb_to_lt_with_hyp H (Zlt_cases x y)
           | [ H : (?x <=? ?y) = ?b |- _ ]
             => ltb_to_lt_with_hyp H (Zle_cases x y)
           | [ H : (?x >? ?y) = ?b |- _ ]
             => ltb_to_lt_with_hyp H (Zgt_cases x y)
           | [ H : (?x >=? ?y) = ?b |- _ ]
             => ltb_to_lt_with_hyp H (Zge_cases x y)
           end.

  Ltac compare_to_sgn :=
    repeat match goal with
           | [ H : _ |- _ ] => progress rewrite <- ?Z.sgn_neg_iff, <- ?Z.sgn_pos_iff, <- ?Z.sgn_null_iff in H
           | _ => progress rewrite <- ?Z.sgn_neg_iff, <- ?Z.sgn_pos_iff, <- ?Z.sgn_null_iff
           end.

  Local Ltac replace_to_const c :=
    repeat match goal with
           | [ H : ?x = ?x |- _ ] => clear H
           | [ H : ?x = c, H' : context[?x] |- _ ] => rewrite H in H'
           | [ H : c = ?x, H' : context[?x] |- _ ] => rewrite <- H in H'
           | [ H : ?x = c |- context[?x] ] => rewrite H
           | [ H : c = ?x |- context[?x] ] => rewrite <- H
           end.

  Lemma lt_div_0 n m : n / m < 0 <-> ((n < 0 < m \/ m < 0 < n) /\ 0 < -(n / m)).
  Proof.
    Z.compare_to_sgn; rewrite Z.sgn_opp; simpl.
    pose proof (Zdiv_sgn n m) as H.
    pose proof (Z.sgn_spec (n / m)) as H'.
    repeat first [ progress intuition auto
                 | progress simpl in *
                 | congruence
                 | lia
                 | progress replace_to_const (-1)
                 | progress replace_to_const 0
                 | progress replace_to_const 1
                 | match goal with
                   | [ x : Z |- _ ] => destruct x
                   end ].
  Qed.

  Lemma two_times_x_minus_x x : 2 * x - x = x.
  Proof. lia. Qed.

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

  Lemma sub_same_minus (x y : Z) : x - (x - y) = y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus : zsimplify.
  Lemma sub_same_plus (x y : Z) : x - (x + y) = -y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus : zsimplify.
  Lemma sub_same_minus_plus (x y z : Z) : x - (x - y + z) = y - z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_plus : zsimplify.
  Lemma sub_same_plus_plus (x y z : Z) : x - (x + y + z) = -y - z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_plus : zsimplify.
  Lemma sub_same_minus_minus (x y z : Z) : x - (x - y - z) = y + z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_minus : zsimplify.
  Lemma sub_same_plus_minus (x y z : Z) : x - (x + y - z) = z - y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_minus : zsimplify.
  Lemma sub_same_minus_then_plus (x y w : Z) : x - (x - y) + w = y + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_then_plus : zsimplify.
  Lemma sub_same_plus_then_plus (x y w : Z) : x - (x + y) + w = w - y.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_then_plus : zsimplify.
  Lemma sub_same_minus_plus_then_plus (x y z w : Z) : x - (x - y + z) + w = y - z + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_plus_then_plus : zsimplify.
  Lemma sub_same_plus_plus_then_plus (x y z w : Z) : x - (x + y + z) + w = w - y - z.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_plus_then_plus : zsimplify.
  Lemma sub_same_minus_minus_then_plus (x y z w : Z) : x - (x - y - z) + w = y + z + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_minus_minus : zsimplify.
  Lemma sub_same_plus_minus_then_plus (x y z w : Z) : x - (x + y - z) + w = z - y + w.
  Proof. lia. Qed.
  Hint Rewrite sub_same_plus_minus_then_plus : zsimplify.

  (** * [Z.simplify_fractions_le] *)
  (** The culmination of this series of tactics,
      [Z.simplify_fractions_le], will use the fact that [a * (b / c) <=
      (a * b) / c], and do some reasoning modulo associativity and
      commutativity in [Z] to perform such a reduction.  It may leave
      over goals if it cannot prove that some denominators are non-zero.
      If the rewrite [a * (b / c)] → [(a * b) / c] is safe to do on the
      LHS of the goal, this tactic should not turn a solvable goal into
      an unsolvable one.

      After running, the tactic does some basic rewriting to simplify
      fractions, e.g., that [a * b / b = a]. *)
  Ltac split_sums_step :=
    match goal with
    | [ |- _ + _ <= _ ]
      => etransitivity; [ eapply Z.add_le_mono | ]
    | [ |- _ - _ <= _ ]
      => etransitivity; [ eapply Z.sub_le_mono | ]
    end.
  Ltac split_sums :=
    try (split_sums_step; [ split_sums.. | ]).
  Ltac pre_reorder_fractions_step :=
    match goal with
    | [ |- context[?x / ?y * ?z] ]
      => lazymatch z with
         | context[_ / _] => fail
         | _ => idtac
         end;
         rewrite (Z.mul_comm (x / y) z)
    | _ => let LHS := match goal with |- ?LHS <= ?RHS => LHS end in
           match LHS with
           | context G[?x * (?y / ?z)]
             => let G' := context G[(x * y) / z] in
                transitivity G'
           end
    end.
  Ltac pre_reorder_fractions :=
    try first [ split_sums_step; [ pre_reorder_fractions.. | ]
              | pre_reorder_fractions_step; [ .. | pre_reorder_fractions ] ].
  Ltac split_comparison :=
    match goal with
    | [ |- ?x <= ?x ] => reflexivity
    | [ H : _ >= _ |- _ ]
      => apply Z.ge_le_iff in H
    | [ |- ?x * ?y <= ?z * ?w ]
      => lazymatch goal with
         | [ H : 0 <= x |- _ ] => idtac
         | [ H : x < 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0)
         end;
         [ ..
         | lazymatch goal with
           | [ H : 0 <= y |- _ ] => idtac
           | [ H : y < 0 |- _ ] => fail
           | _ => destruct (Z_lt_le_dec y 0)
           end;
           [ ..
           | apply Zmult_le_compat; [ | | assumption | assumption ] ] ]
    | [ |- ?x / ?y <= ?z / ?y ]
      => lazymatch goal with
         | [ H : 0 < y |- _ ] => idtac
         | [ H : y <= 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec 0 y)
         end;
         [ apply Z_div_le; [ apply Z.gt_lt_iff; assumption | ]
         | .. ]
    | [ |- ?x / ?y <= ?x / ?z ]
      => lazymatch goal with
         | [ H : 0 <= x |- _ ] => idtac
         | [ H : x < 0 |- _ ] => fail
         | _ => destruct (Z_lt_le_dec x 0)
         end;
         [ ..
         | lazymatch goal with
           | [ H : 0 < z |- _ ] => idtac
           | [ H : z <= 0 |- _ ] => fail
           | _ => destruct (Z_lt_le_dec 0 z)
           end;
           [ apply Z.div_le_compat_l; [ assumption | split; [ assumption | ] ]
           | .. ] ]
    | [ |- _ + _ <= _ + _ ]
      => apply Z.add_le_mono
    | [ |- _ - _ <= _ - _ ]
      => apply Z.sub_le_mono
    | [ |- ?x * (?y / ?z) <= (?x * ?y) / ?z ]
      => apply Z.div_mul_le
    end.
  Ltac split_comparison_fin_step :=
    match goal with
    | _ => assumption
    | _ => lia
    | _ => progress subst
    | [ H : ?n * ?m < 0 |- _ ]
      => apply (proj1 (Z.lt_mul_0 n m)) in H; destruct H as [ [??]|[??] ]
    | [ H : ?n / ?m < 0 |- _ ]
      => apply (proj1 (lt_div_0 n m)) in H; destruct H as [ [ [??]|[??] ] ? ]
    | [ H : (?x^?y) <= ?n < _, H' : ?n < 0 |- _ ]
      => assert (0 <= x^y) by zero_bounds; lia
    | [ H : (?x^?y) < 0 |- _ ]
      => assert (0 <= x^y) by zero_bounds; lia
    | [ H : (?x^?y) <= 0 |- _ ]
      => let H' := fresh in
         assert (H' : 0 <= x^y) by zero_bounds;
         assert (x^y = 0) by lia;
         clear H H'
    | [ H : _^_ = 0 |- _ ]
      => apply Z.pow_eq_0_iff in H; destruct H as [ ?|[??] ]
    | [ H : 0 <= ?x, H' : ?x - 1 < 0 |- _ ]
      => assert (x = 0) by lia; clear H H'
    | [ |- ?x <= ?y ] => is_evar x; reflexivity
    | [ |- ?x <= ?y ] => is_evar y; reflexivity
    end.
  Ltac split_comparison_fin := repeat split_comparison_fin_step.
  Ltac simplify_fractions_step :=
    match goal with
    | _ => rewrite Z.div_mul by (try apply Z.pow_nonzero; zero_bounds)
    | [ |- context[?x * ?y / ?x] ]
      => rewrite (Z.mul_comm x y)
    | [ |- ?x <= ?x ] => reflexivity
    end.
  Ltac simplify_fractions := repeat simplify_fractions_step.
  Ltac simplify_fractions_le :=
    pre_reorder_fractions;
    [ repeat split_comparison; split_comparison_fin; zero_bounds..
    | simplify_fractions ].

  Lemma log2_nonneg' n a : n <= 0 -> n <= Z.log2 a.
  Proof.
    intros; transitivity 0; auto with zarith.
  Qed.

  Hint Resolve log2_nonneg' : zarith.

  (** We create separate databases for two directions of transformations
      involving [Z.log2]; combining them leads to loops. *)
  (* for hints that take in hypotheses of type [log2 _], and spit out conclusions of type [_ ^ _] *)
  Create HintDb hyp_log2.

  (* for hints that take in hypotheses of type [_ ^ _], and spit out conclusions of type [log2 _] *)
  Create HintDb concl_log2.

  Hint Resolve (fun a b H => proj1 (Z.log2_lt_pow2 a b H)) (fun a b H => proj1 (Z.log2_le_pow2 a b H)) : concl_log2.
  Hint Resolve (fun a b H => proj2 (Z.log2_lt_pow2 a b H)) (fun a b H => proj2 (Z.log2_le_pow2 a b H)) : hyp_log2.

  Lemma le_lt_to_log2 x y z : 0 <= z -> 0 < y -> 2^x <= y < 2^z -> x <= Z.log2 y < z.
  Proof.
    destruct (Z_le_gt_dec 0 x); auto with concl_log2 lia.
  Qed.

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
  Proof. lia. Qed.

  Hint Rewrite <- mod_opp_l_z_iff using zutil_arith : zsimplify.
  Hint Rewrite opp_eq_0_iff : zsimplify.

  Lemma sub_pos_bound a b X : 0 <= a < X -> 0 <= b < X -> -X < a - b < X.
  Proof. lia. Qed.

  Lemma div_opp_l_complete a b (Hb : b <> 0) : -a/b = -(a/b) - (if Z_zerop (a mod b) then 0 else 1).
  Proof.
    destruct (Z_zerop (a mod b)); autorewrite with zsimplify push_Zopp; reflexivity.
  Qed.

  Lemma div_opp_l_complete' a b (Hb : b <> 0) : -(a/b) = -a/b + (if Z_zerop (a mod b) then 0 else 1).
  Proof.
    destruct (Z_zerop (a mod b)); autorewrite with zsimplify pull_Zopp; lia.
  Qed.

  Hint Rewrite Z.div_opp_l_complete using zutil_arith : pull_Zopp.
  Hint Rewrite Z.div_opp_l_complete' using zutil_arith : push_Zopp.

  Lemma div_opp a : a <> 0 -> -a / a = -1.
  Proof.
    intros; autorewrite with pull_Zopp zsimplify; lia.
  Qed.

  Hint Rewrite Z.div_opp using zutil_arith : zsimplify.

  Lemma div_sub_1_0 x : x > 0 -> (x - 1) / x = 0.
  Proof. auto with zarith lia. Qed.

  Hint Rewrite div_sub_1_0 using zutil_arith : zsimplify.

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

  Lemma div_add' a b c : c <> 0 -> (a + c * b) / c = a / c + b.
  Proof. intro; rewrite <- Z.div_add, (Z.mul_comm c); try lia. Qed.

  Lemma div_add_l' a b c : b <> 0 -> (b * a + c) / b = a + c / b.
  Proof. intro; rewrite <- Z.div_add_l, (Z.mul_comm b); lia. Qed.

  Hint Rewrite div_add_l' div_add' using zutil_arith : zsimplify.

  Lemma div_sub a b c : c <> 0 -> (a - b * c) / c = a / c - b.
  Proof. intros; rewrite <- !Z.add_opp_r, <- Z.div_add by lia; apply f_equal2; lia. Qed.

  Lemma div_sub' a b c : c <> 0 -> (a - c * b) / c = a / c - b.
  Proof. intro; rewrite <- div_sub, (Z.mul_comm c); try lia. Qed.

  Hint Rewrite div_sub div_sub' using zutil_arith : zsimplify.

  Lemma div_add_sub_l a b c d : b <> 0 -> (a * b + c - d) / b = a + (c - d) / b.
  Proof. rewrite <- Z.add_sub_assoc; apply Z.div_add_l. Qed.

  Lemma div_add_sub_l' a b c d : b <> 0 -> (b * a + c - d) / b = a + (c - d) / b.
  Proof. rewrite <- Z.add_sub_assoc; apply Z.div_add_l'. Qed.

  Lemma div_add_sub a b c d : c <> 0 -> (a + b * c - d) / c = (a - d) / c + b.
  Proof. rewrite (Z.add_comm _ (_ * _)), (Z.add_comm (_ / _)); apply Z.div_add_sub_l. Qed.

  Lemma div_add_sub' a b c d : c <> 0 -> (a + c * b - d) / c = (a - d) / c + b.
  Proof. rewrite (Z.add_comm _ (_ * _)), (Z.add_comm (_ / _)); apply Z.div_add_sub_l'. Qed.

  Hint Rewrite Z.div_add_sub Z.div_add_sub' Z.div_add_sub_l Z.div_add_sub_l' using zutil_arith : zsimplify.

  Lemma div_mul_skip a b k : 0 < b -> 0 < k -> a * b / k / b = a / k.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm k), <- Z.div_div by lia.
    autorewrite with zsimplify; reflexivity.
  Qed.

  Lemma div_mul_skip' a b k : 0 < b -> 0 < k -> b * a / k / b = a / k.
  Proof.
    intros; rewrite Z.div_div, (Z.mul_comm k), <- Z.div_div by lia.
    autorewrite with zsimplify; reflexivity.
  Qed.

  Hint Rewrite Z.div_mul_skip Z.div_mul_skip' using zutil_arith : zsimplify.

  Lemma div_mul_skip_pow base e0 e1 x y : 0 < y -> 0 < base -> 0 <= e1 <= e0 -> x * base^e0 / y / base^e1 = x * base^(e0 - e1) / y.
  Proof.
    intros.
    assert (0 < base^e1) by auto with zarith.
    replace (base^e0) with (base^(e0 - e1) * base^e1) by (autorewrite with pull_Zpow zsimplify; reflexivity).
    rewrite !Z.mul_assoc.
    autorewrite with zsimplify; lia.
  Qed.
  Hint Rewrite div_mul_skip_pow using zutil_arith : zsimplify.

  Lemma div_mul_skip_pow' base e0 e1 x y : 0 < y -> 0 < base -> 0 <= e1 <= e0 -> base^e0 * x / y / base^e1 = base^(e0 - e1) * x / y.
  Proof.
    intros.
    rewrite (Z.mul_comm (base^e0) x), div_mul_skip_pow by lia.
    auto using f_equal2 with lia.
  Qed.
  Hint Rewrite div_mul_skip_pow' using zutil_arith : zsimplify.

  Lemma mod_eq_le_to_eq a b : 0 < a <= b -> a mod b = 0 -> a = b.
  Proof.
    intros H H'.
    assert (a = b * (a / b)) by auto with zarith lia.
    assert (a / b = 1) by nia.
    nia.
  Qed.
  Hint Resolve mod_eq_le_to_eq : zarith.

  Lemma div_same' a b : b <> 0 -> a = b -> a / b = 1.
  Proof.
    intros; subst; auto with zarith.
  Qed.
  Hint Resolve div_same' : zarith.

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

  Lemma le_lt_trans n m p : n <= m -> m < p -> n < p.
  Proof. lia. Qed.

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

  Lemma two_sub_sub_inner_sub x y z : 2 * x - y - (x - z) = x - y + z.
  Proof. clear; lia. Qed.
  Hint Rewrite two_sub_sub_inner_sub : zsimplify.

  Lemma f_equal_mul_mod x y x' y' m : x mod m = x' mod m -> y mod m = y' mod m -> (x * y) mod m = (x' * y') mod m.
  Proof.
    intros H0 H1; rewrite Zmult_mod, H0, H1, <- Zmult_mod; reflexivity.
  Qed.
  Hint Resolve f_equal_mul_mod : zarith.

  Lemma f_equal_add_mod x y x' y' m : x mod m = x' mod m -> y mod m = y' mod m -> (x + y) mod m = (x' + y') mod m.
  Proof.
    intros H0 H1; rewrite Zplus_mod, H0, H1, <- Zplus_mod; reflexivity.
  Qed.
  Hint Resolve f_equal_add_mod : zarith.

  Lemma f_equal_opp_mod x x' m : x mod m = x' mod m -> (-x) mod m = (-x') mod m.
  Proof.
    intro H.
    destruct (Z_zerop (x mod m)) as [H'|H'], (Z_zerop (x' mod m)) as [H''|H''];
      try congruence.
    { rewrite !Z_mod_zero_opp_full by assumption; reflexivity. }
    { rewrite Z_mod_nz_opp_full, H, <- Z_mod_nz_opp_full by assumption; reflexivity. }
  Qed.
  Hint Resolve f_equal_opp_mod : zarith.

  Lemma f_equal_sub_mod x y x' y' m : x mod m = x' mod m -> y mod m = y' mod m -> (x - y) mod m = (x' - y') mod m.
  Proof.
    rewrite <- !Z.add_opp_r; auto with zarith.
  Qed.
  Hint Resolve f_equal_sub_mod : zarith.

  Lemma base_pow_neg b n : n < 0 -> b^n = 0.
  Proof.
    destruct n; intro H; try reflexivity; compute in H; congruence.
  Qed.
  Hint Rewrite base_pow_neg using zutil_arith : zsimplify.

  Lemma div_mod' a b : b <> 0 -> a = (a / b) * b + a mod b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod' using zutil_arith : zsimplify.

  Lemma div_mod'' a b : b <> 0 -> a = a mod b + b * (a / b).
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod'' using zutil_arith : zsimplify.

  Lemma div_mod''' a b : b <> 0 -> a = a mod b + (a / b) * b.
  Proof. intro; etransitivity; [ apply (Z.div_mod a b); assumption | lia ]. Qed.
  Hint Rewrite <- div_mod''' using zutil_arith : zsimplify.

  Lemma div_sub_mod_exact a b : b <> 0 -> a / b = (a - a mod b) / b.
  Proof.
    intro.
    rewrite (Z.div_mod a b) at 2 by lia.
    autorewrite with zsimplify.
    reflexivity.
  Qed.

  Definition opp_distr_if (b : bool) x y : -(if b then x else y) = if b then -x else -y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite opp_distr_if : push_Zopp.
  Hint Rewrite <- opp_distr_if : pull_Zopp.

  Lemma mul_r_distr_if (b : bool) x y z : z * (if b then x else y) = if b then z * x else z * y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mul_r_distr_if : push_Zmul.
  Hint Rewrite <- mul_r_distr_if : pull_Zmul.

  Lemma mul_l_distr_if (b : bool) x y z : (if b then x else y) * z = if b then x * z else y * z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mul_l_distr_if : push_Zmul.
  Hint Rewrite <- mul_l_distr_if : pull_Zmul.

  Lemma add_r_distr_if (b : bool) x y z : z + (if b then x else y) = if b then z + x else z + y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite add_r_distr_if : push_Zadd.
  Hint Rewrite <- add_r_distr_if : pull_Zadd.

  Lemma add_l_distr_if (b : bool) x y z : (if b then x else y) + z = if b then x + z else y + z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite add_l_distr_if : push_Zadd.
  Hint Rewrite <- add_l_distr_if : pull_Zadd.

  Lemma sub_r_distr_if (b : bool) x y z : z - (if b then x else y) = if b then z - x else z - y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite sub_r_distr_if : push_Zsub.
  Hint Rewrite <- sub_r_distr_if : pull_Zsub.

  Lemma sub_l_distr_if (b : bool) x y z : (if b then x else y) - z = if b then x - z else y - z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite sub_l_distr_if : push_Zsub.
  Hint Rewrite <- sub_l_distr_if : pull_Zsub.

  Lemma div_r_distr_if (b : bool) x y z : z / (if b then x else y) = if b then z / x else z / y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite div_r_distr_if : push_Zdiv.
  Hint Rewrite <- div_r_distr_if : pull_Zdiv.

  Lemma div_l_distr_if (b : bool) x y z : (if b then x else y) / z = if b then x / z else y / z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite div_l_distr_if : push_Zdiv.
  Hint Rewrite <- div_l_distr_if : pull_Zdiv.

  Lemma mod_r_distr_if (b : bool) x y z : z mod (if b then x else y) = if b then z mod x else z mod y.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mod_r_distr_if : push_Zmod.
  Hint Rewrite <- mod_r_distr_if : pull_Zmod.

  Lemma mod_l_distr_if (b : bool) x y z : (if b then x else y) mod z = if b then x mod z else y mod z.
  Proof. destruct b; reflexivity. Qed.
  Hint Rewrite mod_l_distr_if : push_Zmod.
  Hint Rewrite <- mod_l_distr_if : pull_Zmod.

  Lemma minus_minus_one : - -1 = 1.
  Proof. reflexivity. Qed.
  Hint Rewrite minus_minus_one : zsimplify.

  Lemma div_add_exact x y d : d <> 0 -> x mod d = 0 -> (x + y) / d = x / d + y / d.
  Proof.
    intros; rewrite (Z_div_exact_full_2 x d) at 1 by assumption.
    rewrite Z.div_add_l' by assumption; lia.
  Qed.
  Hint Rewrite div_add_exact using zutil_arith : zsimplify.

  (** Version without the [n <> 0] assumption *)
  Lemma mul_mod_full a b n : (a * b) mod n = ((a mod n) * (b mod n)) mod n.
  Proof. auto using Zmult_mod. Qed.
  Hint Rewrite <- mul_mod_full : pull_Zmod.
  Hint Resolve mul_mod_full : zarith.

  Lemma mul_mod_l a b n : (a * b) mod n = ((a mod n) * b) mod n.
  Proof.
    intros; rewrite (mul_mod_full a b), (mul_mod_full (a mod n) b).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- mul_mod_l : pull_Zmod.
  Hint Resolve mul_mod_l : zarith.

  Lemma mul_mod_r a b n : (a * b) mod n = (a * (b mod n)) mod n.
  Proof.
    intros; rewrite (mul_mod_full a b), (mul_mod_full a (b mod n)).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- mul_mod_r : pull_Zmod.
  Hint Resolve mul_mod_r : zarith.

  Lemma add_mod_full a b n : (a + b) mod n = ((a mod n) + (b mod n)) mod n.
  Proof. auto using Zplus_mod. Qed.
  Hint Rewrite <- add_mod_full : pull_Zmod.
  Hint Resolve add_mod_full : zarith.

  Lemma add_mod_l a b n : (a + b) mod n = ((a mod n) + b) mod n.
  Proof.
    intros; rewrite (add_mod_full a b), (add_mod_full (a mod n) b).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- add_mod_l : pull_Zmod.
  Hint Resolve add_mod_l : zarith.

  Lemma add_mod_r a b n : (a + b) mod n = (a + (b mod n)) mod n.
  Proof.
    intros; rewrite (add_mod_full a b), (add_mod_full a (b mod n)).
    autorewrite with zsimplify; reflexivity.
  Qed.
  Hint Rewrite <- add_mod_r : pull_Zmod.
  Hint Resolve add_mod_r : zarith.

  Lemma opp_mod_mod a n : (-a) mod n = (-(a mod n)) mod n.
  Proof.
    intros; destruct (Z_zerop (a mod n)) as [H'|H']; [ rewrite H' | ];
      [ | rewrite !Z_mod_nz_opp_full ];
      autorewrite with zsimplify; lia.
  Qed.
  Hint Rewrite <- opp_mod_mod : pull_Zmod.
  Hint Resolve opp_mod_mod : zarith.

  (** Give alternate names for the next three lemmas, for consistency *)
  Lemma sub_mod_full a b n : (a - b) mod n = ((a mod n) - (b mod n)) mod n.
  Proof. auto using Zminus_mod. Qed.
  Hint Rewrite <- sub_mod_full : pull_Zmod.
  Hint Resolve sub_mod_full : zarith.

  Lemma sub_mod_l a b n : (a - b) mod n = ((a mod n) - b) mod n.
  Proof. auto using Zminus_mod_idemp_l. Qed.
  Hint Rewrite <- sub_mod_l : pull_Zmod.
  Hint Resolve sub_mod_l : zarith.

  Lemma sub_mod_r a b n : (a - b) mod n = (a - (b mod n)) mod n.
  Proof. auto using Zminus_mod_idemp_r. Qed.
  Hint Rewrite <- sub_mod_r : pull_Zmod.
  Hint Resolve sub_mod_r : zarith.

  Definition NoZMod (x : Z) := True.
  Ltac NoZMod :=
    lazymatch goal with
    | [ |- NoZMod (?x mod ?y) ] => fail 0 "Goal has" x "mod" y
    | [ |- NoZMod _ ] => constructor
    end.

  Lemma mul_mod_push a b n : NoZMod a -> NoZMod b -> (a * b) mod n = ((a mod n) * (b mod n)) mod n.
  Proof. intros; apply mul_mod_full; assumption. Qed.
  Hint Rewrite mul_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_push a b n : NoZMod a -> NoZMod b -> (a + b) mod n = ((a mod n) + (b mod n)) mod n.
  Proof. intros; apply add_mod_full; assumption. Qed.
  Hint Rewrite add_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma mul_mod_l_push a b n : NoZMod a -> (a * b) mod n = ((a mod n) * b) mod n.
  Proof. intros; apply mul_mod_l; assumption. Qed.
  Hint Rewrite mul_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma mul_mod_r_push a b n : NoZMod b -> (a * b) mod n = (a * (b mod n)) mod n.
  Proof. intros; apply mul_mod_r; assumption. Qed.
  Hint Rewrite mul_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_l_push a b n : NoZMod a -> (a + b) mod n = ((a mod n) + b) mod n.
  Proof. intros; apply add_mod_l; assumption. Qed.
  Hint Rewrite add_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma add_mod_r_push a b n : NoZMod b -> (a + b) mod n = (a + (b mod n)) mod n.
  Proof. intros; apply add_mod_r; assumption. Qed.
  Hint Rewrite add_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_push a b n : NoZMod a -> NoZMod b -> (a - b) mod n = ((a mod n) - (b mod n)) mod n.
  Proof. intros; apply Zminus_mod; assumption. Qed.
  Hint Rewrite sub_mod_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_l_push a b n : NoZMod a -> (a - b) mod n = ((a mod n) - b) mod n.
  Proof. intros; symmetry; apply Zminus_mod_idemp_l; assumption. Qed.
  Hint Rewrite sub_mod_l_push using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_r_push a b n : NoZMod b -> (a - b) mod n = (a - (b mod n)) mod n.
  Proof. intros; symmetry; apply Zminus_mod_idemp_r; assumption. Qed.
  Hint Rewrite sub_mod_r_push using solve [ NoZMod ] : push_Zmod.

  Lemma opp_mod_mod_push a n : NoZMod a -> (-a) mod n = (-(a mod n)) mod n.
  Proof. intros; apply opp_mod_mod; assumption. Qed.
  Hint Rewrite opp_mod_mod using solve [ NoZMod ] : push_Zmod.

  Lemma sub_mod_mod_0 x d : (x - x mod d) mod d = 0.
  Proof.
    destruct (Z_zerop d); subst; autorewrite with push_Zmod zsimplify; reflexivity.
  Qed.
  Hint Resolve sub_mod_mod_0 : zarith.
  Hint Rewrite sub_mod_mod_0 : zsimplify.

  Lemma div_sub_mod_cond x y d
    : d <> 0
      -> (x - y) / d
         = x / d + ((x mod d - y) / d).
  Proof. clear.
         intro.
         replace (x - y) with ((x - x mod d) + (x mod d - y)) by lia.
         rewrite div_add_exact by auto with zarith.
         rewrite <- Z.div_sub_mod_exact by lia; lia.
  Qed.
  Hint Resolve div_sub_mod_cond : zarith.

  Lemma div_between n a b : 0 <= n -> b <> 0 -> n * b <= a < (1 + n) * b -> a / b = n.
  Proof.
    intros.
    replace a with ((a - n * b) + n * b) by lia.
    autorewrite with zsimplify; reflexivity.
  Qed.
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

  Lemma leb_add_same x y : (x <=? y + x) = (0 <=? y).
  Proof. destruct (x <=? y + x) eqn:?, (0 <=? y) eqn:?; ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite leb_add_same : zsimplify.

  Lemma ltb_add_same x y : (x <? y + x) = (0 <? y).
  Proof. destruct (x <? y + x) eqn:?, (0 <? y) eqn:?; ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite ltb_add_same : zsimplify.

  Lemma geb_add_same x y : (x >=? y + x) = (0 >=? y).
  Proof. destruct (x >=? y + x) eqn:?, (0 >=? y) eqn:?; ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite geb_add_same : zsimplify.

  Lemma gtb_add_same x y : (x >? y + x) = (0 >? y).
  Proof. destruct (x >? y + x) eqn:?, (0 >? y) eqn:?; ltb_to_lt; try reflexivity; omega. Qed.
  Hint Rewrite gtb_add_same : zsimplify.

  Lemma simplify_twice_sub_sub x y : 2 * x - (x - y) = x + y.
  Proof. lia. Qed.
  Hint Rewrite simplify_twice_sub_sub : zsimplify.

  Lemma simplify_twice_sub_add x y : 2 * x - (x + y) = x - y.
  Proof. lia. Qed.
  Hint Rewrite simplify_twice_sub_add : zsimplify.

  Local Ltac simplify_div_tac :=
    intros; autorewrite with zsimplify; rewrite <- ?Z_div_plus_full_l, <- ?Z_div_plus_full by assumption;
    try (apply f_equal2; [ | reflexivity ]);
    try zutil_arith.

  (* Naming Convention: [X] for thing being divided by, [p] for plus,
     [m] for minus, [d] for div, and [_] to separate parentheses and
     multiplication. *)
  (* Mathematica code to generate these hints:
<<
ClearAll[minus, plus, div, mul, combine, parens, ExprToString,
  ExprToExpr, ExprToName, SymbolsIn, Chars, RestFrom, a, b, c, d, e,
  f, g, h, i, j, k, l, m, n, o, p, q, r, s, t, u, v, w, x, y, z, X];
Chars = StringSplit["abcdefghijklmnopqrstuvwxyz", ""];
RestFrom[i_, len_] :=
 Join[{mul[Chars[[i]], "X"]}, Take[Drop[Chars, i], len]]
Exprs = Flatten[
   Map[{#1, #1 /. mul[a_, "X"] :> mul["X", a]} &, Flatten[{
      Table[
       Table[div[
         combine @@
          Join[Take[Chars, start - 1], RestFrom[start, len]],
         "X"], {len, 0, 10 - start}], {start, 1, 2}],
      Table[
       Table[div[
         combine["a",
          parens @@
           Join[Take[Chars, 1 + start - 1],
            RestFrom[1 + start, len]]], "X"], {len, 0,
         10 - start}], {start, 1, 2}],
      div[combine["a", parens["b", parens["c", mul["d", "X"]], "e"]],
       "X"],
      div[combine["a", "b", parens["c", mul["d", "X"]], "e"], "X"]}]]];
ExprToString[div[x_, y_], withparen_: False] :=
 With[{v := ExprToString[x, True] <> " / " <> ExprToString[y, True]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[combine[x_], withparen_: False] :=
 ExprToString[x, withparen]
ExprToString[combine[x_, minus, y__], withparen_: False] :=
 With[{v :=
    ExprToString[x, False] <> " - " <>
     ExprToString[combine[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[combine[minus, y__], withparen_: False] :=
 With[{v := "-" <> ExprToString[combine[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[combine[x_, y__], withparen_: False] :=
 With[{v :=
    ExprToString[x, False] <> " + " <>
     ExprToString[combine[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[mul[x_], withparen_: False] := ExprToString[x]
ExprToString[mul[x_, y__], withparen_: False] :=
 With[{v :=
    ExprToString[x, False] <> " * " <> ExprToString[mul[y], False]},
  If[withparen, "(" <> v <> ")", v]]
ExprToString[parens[x__], withparen_: False] :=
 "(" <> ExprToString[combine[x]] <> ")"
ExprToString[x_String, withparen_: False] := x
ExprToExpr[div[x__]] := Divide @@ Map[ExprToExpr, {x}]
ExprToExpr[mul[x__]] := Times @@ Map[ExprToExpr, {x}]
ExprToExpr[combine[]] := 0
ExprToExpr[combine[minus, y_, z___]] := -ExprToExpr[y] +
  ExprToExpr[combine[z]]
ExprToExpr[combine[x_, y___]] := ExprToExpr[x] + ExprToExpr[combine[y]]
ExprToExpr[parens[x__]] := ExprToExpr[combine[x]]
ExprToExpr[x_String] := Symbol[x]
ExprToName["X", ispos_: True] := If[ispos, "X", "mX"]
ExprToName[x_String, ispos_: True] := If[ispos, "p", "m"]
ExprToName[div[x_, y_], ispos_: True] :=
 If[ispos, "p", "m"] <> ExprToName[x] <> "d" <> ExprToName[y]
ExprToName[mul[x_], ispos_: True] :=
 If[ispos, "", "m_"] <> ExprToName[x] <> "_"
ExprToName[mul[x_, y__], ispos_: True] :=
 If[ispos, "", "m_"] <> ExprToName[x] <> ExprToName[mul[y]]
ExprToName[combine[], ispos_: True] := ""
ExprToName[combine[x_], ispos_: True] := ExprToName[x, ispos]
ExprToName[combine[x_, minus, mul[y__], z___], ispos_: True] :=
 ExprToName[x, ispos] <> "m_" <> ExprToName[mul[y], True] <>
  ExprToName[combine[z], True]
ExprToName[combine[x_, mul[y__], z___], ispos_: True] :=
 ExprToName[x, ispos] <> "p_" <> ExprToName[mul[y], True] <>
  ExprToName[combine[z], True]
ExprToName[combine[x_, y__], ispos_: True] :=
 ExprToName[x, ispos] <> ExprToName[combine[y], True]
ExprToName[combine[x_, minus, y__], ispos_: True] :=
 ExprToName[x, ispos] <> ExprToName[combine[y], True]
ExprToName[combine[x_, y__], ispos_: True] :=
 ExprToName[x, ispos] <> ExprToName[combine[y], True]
ExprToName[parens[x__], ispos_: True] :=
 "_o_" <> ExprToName[combine[x], ispos] <> "_c_"
SymbolsIn[x_String] := {x <> " "}
SymbolsIn[f_[y___]] := Join @@ Map[SymbolsIn, {y}]
StringJoin @@
 Map[{"  Lemma simplify_div_" <> ExprToName[#1] <> " " <>
     StringJoin @@ Sort[DeleteDuplicates[SymbolsIn[#1]]] <>
     ": X <> 0 -> " <> ExprToString[#1] <> " = " <>
     StringReplace[(FullSimplify[ExprToExpr[#1]] // InputForm //
        ToString), "/" -> " / "] <> "." <>
     "\n  Proof. simplify_div_tac. Qed.\n  Hint Rewrite \
simplify_div_" <> ExprToName[#1] <>
     " using zutil_arith : zsimplify.\n"} &, Exprs]
>> *)
  Lemma simplify_div_ppX_dX a X : X <> 0 -> (a * X) / X = a.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_dX a X : X <> 0 -> (X * a) / X = a.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pdX a b X : X <> 0 -> (a * X + b) / X = a + b / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pdX a b X : X <> 0 -> (X * a + b) / X = a + b / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppdX a b c X : X <> 0 -> (a * X + b + c) / X = a + (b + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppdX a b c X : X <> 0 -> (X * a + b + c) / X = a + (b + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppdX a b c d X : X <> 0 -> (a * X + b + c + d) / X = a + (b + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppdX a b c d X : X <> 0 -> (X * a + b + c + d) / X = a + (b + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppppdX a b c d e X : X <> 0 -> (a * X + b + c + d + e) / X = a + (b + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppppdX a b c d e X : X <> 0 -> (X * a + b + c + d + e) / X = a + (b + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppppdX a b c d e f X : X <> 0 -> (a * X + b + c + d + e + f) / X = a + (b + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppppdX a b c d e f X : X <> 0 -> (X * a + b + c + d + e + f) / X = a + (b + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppppppdX a b c d e f g X : X <> 0 -> (a * X + b + c + d + e + f + g) / X = a + (b + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppppppdX a b c d e f g X : X <> 0 -> (X * a + b + c + d + e + f + g) / X = a + (b + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppppppdX a b c d e f g h X : X <> 0 -> (a * X + b + c + d + e + f + g + h) / X = a + (b + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppppppdX a b c d e f g h X : X <> 0 -> (X * a + b + c + d + e + f + g + h) / X = a + (b + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_ppppppppdX a b c d e f g h i X : X <> 0 -> (a * X + b + c + d + e + f + g + h + i) / X = a + (b + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_ppppppppdX a b c d e f g h i X : X <> 0 -> (X * a + b + c + d + e + f + g + h + i) / X = a + (b + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppX_pppppppppdX a b c d e f g h i j X : X <> 0 -> (a * X + b + c + d + e + f + g + h + i + j) / X = a + (b + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppX_pppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pXp_pppppppppdX a b c d e f g h i j X : X <> 0 -> (X * a + b + c + d + e + f + g + h + i + j) / X = a + (b + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pXp_pppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_dX a b X : X <> 0 -> (a + b * X) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_dX a b X : X <> 0 -> (a + X * b) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pdX a b c X : X <> 0 -> (a + b * X + c) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pdX a b c X : X <> 0 -> (a + X * b + c) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppdX a b c d X : X <> 0 -> (a + b * X + c + d) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppdX a b c d X : X <> 0 -> (a + X * b + c + d) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pppdX a b c d e X : X <> 0 -> (a + b * X + c + d + e) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pppdX a b c d e X : X <> 0 -> (a + X * b + c + d + e) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppppdX a b c d e f X : X <> 0 -> (a + b * X + c + d + e + f) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppppdX a b c d e f X : X <> 0 -> (a + X * b + c + d + e + f) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pppppdX a b c d e f g X : X <> 0 -> (a + b * X + c + d + e + f + g) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pppppdX a b c d e f g X : X <> 0 -> (a + X * b + c + d + e + f + g) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppppppdX a b c d e f g h X : X <> 0 -> (a + b * X + c + d + e + f + g + h) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppppppdX a b c d e f g h X : X <> 0 -> (a + X * b + c + d + e + f + g + h) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_pppppppdX a b c d e f g h i X : X <> 0 -> (a + b * X + c + d + e + f + g + h + i) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_pppppppdX a b c d e f g h i X : X <> 0 -> (a + X * b + c + d + e + f + g + h + i) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_pppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pX_ppppppppdX a b c d e f g h i j X : X <> 0 -> (a + b * X + c + d + e + f + g + h + i + j) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pX_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xp_ppppppppdX a b c d e f g h i j X : X <> 0 -> (a + X * b + c + d + e + f + g + h + i + j) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xp_ppppppppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX__c_dX a b X : X <> 0 -> (a + (a + b * X)) / X = b + (2*a) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp__c_dX a b X : X <> 0 -> (a + (a + X * b)) / X = b + (2*a) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_p_c_dX a b c X : X <> 0 -> (a + (a + b * X + c)) / X = b + (2*a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_p_c_dX a b c X : X <> 0 -> (a + (a + X * b + c)) / X = b + (2*a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pp_c_dX a b c d X : X <> 0 -> (a + (a + b * X + c + d)) / X = b + (2*a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pp_c_dX a b c d X : X <> 0 -> (a + (a + X * b + c + d)) / X = b + (2*a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppp_c_dX a b c d e X : X <> 0 -> (a + (a + b * X + c + d + e)) / X = b + (2*a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppp_c_dX a b c d e X : X <> 0 -> (a + (a + X * b + c + d + e)) / X = b + (2*a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppp_c_dX a b c d e f X : X <> 0 -> (a + (a + b * X + c + d + e + f)) / X = b + (2*a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppp_c_dX a b c d e f X : X <> 0 -> (a + (a + X * b + c + d + e + f)) / X = b + (2*a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppppp_c_dX a b c d e f g X : X <> 0 -> (a + (a + b * X + c + d + e + f + g)) / X = b + (2*a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppppp_c_dX a b c d e f g X : X <> 0 -> (a + (a + X * b + c + d + e + f + g)) / X = b + (2*a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (a + b * X + c + d + e + f + g + h)) / X = b + (2*a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (a + X * b + c + d + e + f + g + h)) / X = b + (2*a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (a + b * X + c + d + e + f + g + h + i)) / X = b + (2*a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (a + X * b + c + d + e + f + g + h + i)) / X = b + (2*a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (a + b * X + c + d + e + f + g + h + i + j)) / X = b + (2*a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (a + X * b + c + d + e + f + g + h + i + j)) / X = b + (2*a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (a + b * X + c + d + e + f + g + h + i + j + k)) / X = b + (2*a + c + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (a + X * b + c + d + e + f + g + h + i + j + k)) / X = b + (2*a + c + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX__c_dX a b c X : X <> 0 -> (a + (a + b + c * X)) / X = c + (2*a + b) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp__c_dX a b c X : X <> 0 -> (a + (a + b + X * c)) / X = c + (2*a + b) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_p_c_dX a b c d X : X <> 0 -> (a + (a + b + c * X + d)) / X = c + (2*a + b + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_p_c_dX a b c d X : X <> 0 -> (a + (a + b + X * c + d)) / X = c + (2*a + b + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_pp_c_dX a b c d e X : X <> 0 -> (a + (a + b + c * X + d + e)) / X = c + (2*a + b + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_pp_c_dX a b c d e X : X <> 0 -> (a + (a + b + X * c + d + e)) / X = c + (2*a + b + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_ppp_c_dX a b c d e f X : X <> 0 -> (a + (a + b + c * X + d + e + f)) / X = c + (2*a + b + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_ppp_c_dX a b c d e f X : X <> 0 -> (a + (a + b + X * c + d + e + f)) / X = c + (2*a + b + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_pppp_c_dX a b c d e f g X : X <> 0 -> (a + (a + b + c * X + d + e + f + g)) / X = c + (2*a + b + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_pppp_c_dX a b c d e f g X : X <> 0 -> (a + (a + b + X * c + d + e + f + g)) / X = c + (2*a + b + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_ppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (a + b + c * X + d + e + f + g + h)) / X = c + (2*a + b + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_ppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (a + b + X * c + d + e + f + g + h)) / X = c + (2*a + b + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_pppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (a + b + c * X + d + e + f + g + h + i)) / X = c + (2*a + b + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_pppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (a + b + X * c + d + e + f + g + h + i)) / X = c + (2*a + b + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_ppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (a + b + c * X + d + e + f + g + h + i + j)) / X = c + (2*a + b + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_ppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (a + b + X * c + d + e + f + g + h + i + j)) / X = c + (2*a + b + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_pX_pppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (a + b + c * X + d + e + f + g + h + i + j + k)) / X = c + (2*a + b + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_pX_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_ppp_Xp_pppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (a + b + X * c + d + e + f + g + h + i + j + k)) / X = c + (2*a + b + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_ppp_Xp_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_pX__c_p_c_dX a b c d e X : X <> 0 -> (a + (b + (c + d * X) + e)) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_pX__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_Xp__c_p_c_dX a b c d e X : X <> 0 -> (a + (b + (c + X * d) + e)) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_Xp__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_o_pp_pX__c_pdX a b c d e X : X <> 0 -> (a + b + (c + d * X) + e) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_o_pp_pX__c_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_o_pp_Xp__c_pdX a b c d e X : X <> 0 -> (a + b + (c + X * d) + e) / X = d + (a + b + c + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_o_pp_Xp__c_pdX using zutil_arith : zsimplify.


  (* Naming convention: [X] for thing being aggregated, [p] for plus,
     [m] for minus, [_] for parentheses *)
  (* Python code to generate these hints:
<<
#!/usr/bin/env python

def to_eqn(name):
    vars_left = list('abcdefghijklmnopqrstuvwxyz')
    ret = ''
    close = ''
    while name:
        if name[0] == 'X':
            ret += ' X'
            name = name[1:]
        else:
            ret += ' ' + vars_left[0]
            vars_left = vars_left[1:]
        if name:
            if name[0] == 'm': ret += ' -'
            elif name[0] == 'p': ret += ' +'
            name = name[1:]
        if name and name[0] == '_':
            ret += ' ('
            close += ')'
            name = name[1:]
    if ret[-1] != 'X':
        ret += ' ' + vars_left[0]
    return (ret + close).strip().replace('( ', '(')

def simplify(eqn):
    counts = {}
    sign_stack = [1, 1]
    for i in eqn:
        if i == ' ': continue
        elif i == '(': sign_stack.append(sign_stack[-1])
        elif i == ')': sign_stack.pop()
        elif i == '+': sign_stack.append(sign_stack[-1])
        elif i == '-': sign_stack.append(-sign_stack[-1])
        else:
            counts[i] = counts.get(i,0) + sign_stack.pop()
    ret = ''
    for k in sorted(counts.keys()):
        if counts[k] == 1: ret += ' + %s' % k
        elif counts[k] == -1: ret += ' - %s' % k
        elif counts[k] < 0: ret += ' - %d * %s' % (abs(counts[k]), k)
        elif counts[k] > 0: ret += ' + %d * %s' % (abs(counts[k]), k)
    if ret == '': ret = '0'
    return ret.strip(' +')


def to_def(name):
    eqn = to_eqn(name)
    return r'''  Lemma simplify_%s %s X : %s = %s.
  Proof. lia. Qed.
  Hint Rewrite simplify_%s : zsimplify.''' % (name, ' '.join(sorted(set(eqn) - set('+-() X'))), eqn, simplify(eqn), name)

names = []
names += ['%sX%s%sX' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['X%s%s_X%s' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']

for name in names:
    print(to_def(name))
>> *)
  Lemma simplify_mXmmX a b X : a - X - b - X = - 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXmmX : zsimplify.
  Lemma simplify_mXmpX a b X : a - X - b + X = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXmpX : zsimplify.
  Lemma simplify_mXpmX a b X : a - X + b - X = - 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXpmX : zsimplify.
  Lemma simplify_mXppX a b X : a - X + b + X = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXppX : zsimplify.
  Lemma simplify_pXmmX a b X : a + X - b - X = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXmmX : zsimplify.
  Lemma simplify_pXmpX a b X : a + X - b + X = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXmpX : zsimplify.
  Lemma simplify_pXpmX a b X : a + X + b - X = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXpmX : zsimplify.
  Lemma simplify_pXppX a b X : a + X + b + X = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXppX : zsimplify.
  Lemma simplify_Xmm_Xm a b X : X - a - (X - b) = - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_Xm : zsimplify.
  Lemma simplify_Xmm_Xp a b X : X - a - (X + b) = - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_Xp : zsimplify.
  Lemma simplify_Xmp_Xm a b X : X - a + (X - b) = 2 * X - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_Xm : zsimplify.
  Lemma simplify_Xmp_Xp a b X : X - a + (X + b) = 2 * X - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_Xp : zsimplify.
  Lemma simplify_Xpm_Xm a b X : X + a - (X - b) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_Xm : zsimplify.
  Lemma simplify_Xpm_Xp a b X : X + a - (X + b) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_Xp : zsimplify.
  Lemma simplify_Xpp_Xm a b X : X + a + (X - b) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_Xm : zsimplify.
  Lemma simplify_Xpp_Xp a b X : X + a + (X + b) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_Xp : zsimplify.

  Section equiv_modulo.
    Context (N : Z).
    Definition equiv_modulo x y := x mod N = y mod N.
    Local Infix "==" := equiv_modulo.

    Local Instance equiv_modulo_Reflexive : Reflexive equiv_modulo := fun _ => Logic.eq_refl.
    Local Instance equiv_modulo_Symmetric : Symmetric equiv_modulo := fun _ _ => @Logic.eq_sym _ _ _.
    Local Instance equiv_modulo_Transitive : Transitive equiv_modulo := fun _ _ _ => @Logic.eq_trans _ _ _ _.

    Local Instance mul_mod_Proper : Proper (equiv_modulo ==> equiv_modulo ==> equiv_modulo) Z.mul.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance add_mod_Proper : Proper (equiv_modulo ==> equiv_modulo ==> equiv_modulo) Z.add.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance sub_mod_Proper : Proper (equiv_modulo ==> equiv_modulo ==> equiv_modulo) Z.sub.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance opp_mod_Proper : Proper (equiv_modulo ==> equiv_modulo) Z.opp.
    Proof. unfold equiv_modulo, Proper, respectful; auto with zarith. Qed.

    Local Instance modulo_equiv_modulo_Proper
      : Proper (equiv_modulo ==> (fun x y => x = N /\ N = y) ==> Logic.eq) Z.modulo.
    Proof.
      repeat intro; hnf in *; intuition congruence.
    Qed.
    Local Instance eq_to_ProperProxy : ProperProxy (fun x y : Z => x = N /\ N = y) N.
    Proof. split; reflexivity. Qed.

    Lemma div_to_inv_modulo a x x' : x > 0 -> x * x' mod N = 1 mod N -> (a / x) == ((a - a mod x) * x').
    Proof.
      intros H xinv.
      replace (a / x) with ((a / x) * 1) by lia.
      change (x * x' == 1) in xinv.
      rewrite <- xinv.
      replace ((a / x) * (x * x')) with ((x * (a / x)) * x') by lia.
      rewrite Z.mul_div_eq by assumption.
      reflexivity.
    Qed.
  End equiv_modulo.
  Hint Rewrite div_to_inv_modulo using solve [ eassumption | lia ] : zstrip_div.

  Module EquivModuloInstances (dummy : Nop). (* work around https://coq.inria.fr/bugs/show_bug.cgi?id=4973 *)
    Existing Instance equiv_modulo_Reflexive.
    Existing Instance eq_Reflexive. (* prioritize [Reflexive eq] *)
    Existing Instance equiv_modulo_Symmetric.
    Existing Instance equiv_modulo_Transitive.
    Existing Instance mul_mod_Proper.
    Existing Instance add_mod_Proper.
    Existing Instance sub_mod_Proper.
    Existing Instance opp_mod_Proper.
    Existing Instance modulo_equiv_modulo_Proper.
    Existing Instance eq_to_ProperProxy.
  End EquivModuloInstances.
  Module RemoveEquivModuloInstances (dummy : Nop).
    Global Remove Hints equiv_modulo_Reflexive equiv_modulo_Symmetric equiv_modulo_Transitive mul_mod_Proper add_mod_Proper sub_mod_Proper opp_mod_Proper modulo_equiv_modulo_Proper eq_to_ProperProxy : typeclass_instances.
  End RemoveEquivModuloInstances.
End Z.

Module Export BoundsTactics.
  Ltac prime_bound := Z.prime_bound.
  Ltac zero_bounds := Z.zero_bounds.
End BoundsTactics.

Ltac push_Zmod :=
  repeat match goal with
         | _ => progress autorewrite with push_Zmod
         | [ |- context[(?x * ?y) mod ?z] ]
           => first [ rewrite (Z.mul_mod_push x y z) by Z.NoZMod
                    | rewrite (Z.mul_mod_l_push x y z) by Z.NoZMod
                    | rewrite (Z.mul_mod_r_push x y z) by Z.NoZMod ]
         | [ |- context[(?x + ?y) mod ?z] ]
           => first [ rewrite (Z.add_mod_push x y z) by Z.NoZMod
                    | rewrite (Z.add_mod_l_push x y z) by Z.NoZMod
                    | rewrite (Z.add_mod_r_push x y z) by Z.NoZMod ]
         | [ |- context[(?x - ?y) mod ?z] ]
           => first [ rewrite (Z.sub_mod_push x y z) by Z.NoZMod
                    | rewrite (Z.sub_mod_l_push x y z) by Z.NoZMod
                    | rewrite (Z.sub_mod_r_push x y z) by Z.NoZMod ]
         | [ |- context[(-?y) mod ?z] ]
           => rewrite (Z.opp_mod_mod_push y z) by Z.NoZMod
         end.

Ltac push_Zmod_hyps :=
  repeat match goal with
         | _ => progress autorewrite with push_Zmod in * |-
         | [ H : context[(?x * ?y) mod ?z] |- _ ]
           => first [ rewrite (Z.mul_mod_push x y z) in H by Z.NoZMod
                    | rewrite (Z.mul_mod_l_push x y z) in H by Z.NoZMod
                    | rewrite (Z.mul_mod_r_push x y z) in H by Z.NoZMod ]
         | [ H : context[(?x + ?y) mod ?z] |- _ ]
           => first [ rewrite (Z.add_mod_push x y z) in H by Z.NoZMod
                    | rewrite (Z.add_mod_l_push x y z) in H by Z.NoZMod
                    | rewrite (Z.add_mod_r_push x y z) in H by Z.NoZMod ]
         | [ H : context[(?x - ?y) mod ?z] |- _ ]
           => first [ rewrite (Z.sub_mod_push x y z) in H by Z.NoZMod
                    | rewrite (Z.sub_mod_l_push x y z) in H by Z.NoZMod
                    | rewrite (Z.sub_mod_r_push x y z) in H by Z.NoZMod ]
         | [ H : context[(-?y) mod ?z] |- _ ]
           => rewrite (Z.opp_mod_mod_push y z) in H by Z.NoZMod
         end.

Ltac has_no_mod x z :=
  lazymatch x with
  | context[_ mod z] => fail
  | _ => idtac
  end.
Ltac pull_Zmod :=
  repeat match goal with
         | [ |- context[((?x mod ?z) * (?y mod ?z)) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.mul_mod_full x y z)
         | [ |- context[((?x mod ?z) * ?y) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.mul_mod_l x y z)
         | [ |- context[(?x * (?y mod ?z)) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.mul_mod_r x y z)
         | [ |- context[((?x mod ?z) + (?y mod ?z)) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.add_mod_full x y z)
         | [ |- context[((?x mod ?z) + ?y) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.add_mod_l x y z)
         | [ |- context[(?x + (?y mod ?z)) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.add_mod_r x y z)
         | [ |- context[((?x mod ?z) - (?y mod ?z)) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.sub_mod_full x y z)
         | [ |- context[((?x mod ?z) - ?y) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.sub_mod_l x y z)
         | [ |- context[(?x - (?y mod ?z)) mod ?z] ]
           => has_no_mod x z; has_no_mod y z;
              rewrite <- (Z.sub_mod_r x y z)
         | [ |- context[(((-?y) mod ?z)) mod ?z] ]
           => has_no_mod y z;
              rewrite <- (Z.opp_mod_mod y z)
         | [ |- context[(?x mod ?z) mod ?z] ]
           => rewrite (Zmod_mod x z)
         | _ => progress autorewrite with pull_Zmod
         end.

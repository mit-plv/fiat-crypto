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
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.ZUtil.Notations.
Require Export Crypto.Util.ZUtil.Definitions.
Require Export Crypto.Util.ZUtil.Morphisms.
Import Nat.
Local Open Scope Z.

Hint Extern 1 => lia : lia.
Hint Extern 1 => lra : lra.
Hint Extern 1 => nia : nia.
Hint Extern 1 => omega : omega.
Hint Resolve Z.log2_nonneg Z.log2_up_nonneg Z.div_small Z.mod_small Z.pow_neg_r Z.pow_0_l Z.pow_pos_nonneg Z.lt_le_incl Z.pow_nonzero Z.div_le_upper_bound Z_div_exact_full_2 Z.div_same Z.div_lt_upper_bound Z.div_le_lower_bound Zplus_minus Zplus_gt_compat_l Zplus_gt_compat_r Zmult_gt_compat_l Zmult_gt_compat_r Z.pow_lt_mono_r Z.pow_lt_mono_l Z.pow_lt_mono Z.mul_lt_mono_nonneg Z.div_lt_upper_bound Z.div_pos Zmult_lt_compat_r Z.pow_le_mono_r Z.pow_le_mono_l Z.div_lt Z.div_le_compat_l Z.div_le_mono Z.max_le_compat Z.min_le_compat Z.log2_up_le_mono Z.pow_nonneg : zarith.
Hint Resolve (fun a b H => proj1 (Z.mod_pos_bound a b H)) (fun a b H => proj2 (Z.mod_pos_bound a b H)) (fun a b pf => proj1 (Z.pow_gt_1 a b pf)) : zarith.
Hint Resolve (fun n m => proj1 (Z.opp_le_mono n m)) : zarith.
Hint Resolve (fun n m => proj1 (Z.pred_le_mono n m)) : zarith.
Hint Resolve (fun a b => proj2 (Z.lor_nonneg a b)) : zarith.

Ltac zutil_arith := solve [ omega | lia | auto with nocore ].
Ltac zutil_arith_more_inequalities := solve [ zutil_arith | auto with zarith ].

(** Only hints that are always safe to apply (i.e., reversible), and
    which can reasonably be said to "simplify" the goal, should go in
    this database. *)
Create HintDb zsimplify discriminated.
(** Only hints that are always safe to apply, and "simplify" the goal,
    and don't require any side conditions, should go in this
    database. *)
Create HintDb zsimplify_fast discriminated.
(** Hints which turn [Z] operations on concrete positives into the
    corresponding operation on [Pos]. *)
Create HintDb zsimplify_Z_to_pos discriminated.
(** Only hints with no side conditions that strip constants, and
    nothing else. *)
Create HintDb zsimplify_const discriminated.
(** We create separate databases for two directions of transformations
      involving [Z.log2]; combining them leads to loops. *)
(* for hints that take in hypotheses of type [log2 _], and spit out conclusions of type [_ ^ _] *)
Create HintDb hyp_log2 discriminated.
(* for hints that take in hypotheses of type [_ ^ _], and spit out conclusions of type [log2 _] *)
Create HintDb concl_log2 discriminated.
Hint Resolve (fun a b H => proj1 (Z.log2_lt_pow2 a b H)) (fun a b H => proj1 (Z.log2_le_pow2 a b H)) : concl_log2.
Hint Resolve (fun a b H => proj2 (Z.log2_lt_pow2 a b H)) (fun a b H => proj2 (Z.log2_le_pow2 a b H)) : hyp_log2.
Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r Z_mod_same_full Z.sub_simpl_r Z.sub_simpl_l Z.add_opp_diag_r Z.add_opp_diag_l Zmod_0_l Z.add_simpl_r Z.add_simpl_l Z.opp_0 Zmod_0_r Zmod_mod Z.mul_succ_l Z.mul_succ_r Z.shiftr_0_r Z.shiftr_0_l Z.mod_1_r Zmod_0_l Zmod_0_r Z.shiftl_0_r Z.shiftl_0_l Z.shiftr_0_r Z.shiftr_0_l Z.sub_diag : zsimplify_fast.

Hint Rewrite Z.div_1_r Z.mul_1_r Z.mul_1_l Z.sub_diag Z.mul_0_r Z.mul_0_l Z.add_0_l Z.add_0_r Z.opp_involutive Z.sub_0_r Z_mod_same_full Z.sub_simpl_r Z.sub_simpl_l Z.add_opp_diag_r Z.add_opp_diag_l Zmod_0_l Z.add_simpl_r Z.add_simpl_l Z.opp_0 Zmod_0_r Zmod_mod Z.mul_succ_l Z.mul_succ_r Z.shiftr_0_r Z.shiftr_0_l Z.mod_1_r Zmod_0_l Zmod_0_r Z.shiftl_0_r Z.shiftl_0_l Z.shiftr_0_r Z.shiftr_0_l Zplus_minus Z.add_diag Z.abs_0 Z.sgn_0 Nat2Z.inj_0 Z2Nat.inj_0 : zsimplify.
Hint Rewrite Z.div_mul Z.div_1_l Z.div_same Z.mod_same Z.div_small Z.mod_small Z.div_add Z.div_add_l Z.mod_add Z.div_0_l Z.mod_mod Z.mod_small Z_mod_zero_opp_full Z.mod_1_l using zutil_arith : zsimplify.
Hint Rewrite <- Z.opp_eq_mul_m1 Z.one_succ Z.two_succ : zsimplify.
Hint Rewrite <- Z.div_mod using zutil_arith : zsimplify.
Hint Rewrite (fun x y => proj2 (Z.eqb_neq x y)) using assumption : zsimplify.
Hint Rewrite Z.mul_0_l Z.mul_0_r Z.mul_1_l Z.mul_1_r Z.add_0_l Z.add_0_r Z.sub_0_l Z.sub_0_r Zdiv_0_l Zdiv_0_r Zdiv_1_r Zmod_0_l Zmod_0_r Zmod_1_r Z.opp_0 Z.abs_0 Z.sgn_0 Nat2Z.inj_0 Z2Nat.inj_0 : zsimplify_const.

Hint Rewrite <- Z.one_succ Z.two_succ : zsimplify_const.

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
Create HintDb pull_Zof_N discriminated.
Create HintDb push_Zof_N discriminated.
Create HintDb pull_Zto_N discriminated.
Create HintDb push_Zto_N discriminated.
Create HintDb Zshift_to_pow discriminated.
Create HintDb Zpow_to_shift discriminated.
Create HintDb pull_Zmax discriminated.
Create HintDb push_Zmax discriminated.
Hint Extern 1 => progress autorewrite with push_Zopp in * : push_Zopp.
Hint Extern 1 => progress autorewrite with pull_Zopp in * : pull_Zopp.
Hint Extern 1 => progress autorewrite with push_Zpow in * : push_Zpow.
Hint Extern 1 => progress autorewrite with pull_Zpow in * : pull_Zpow.
Hint Extern 1 => progress autorewrite with push_Zmul in * : push_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zmul in * : pull_Zmul.
Hint Extern 1 => progress autorewrite with push_Zadd in * : push_Zadd.
Hint Extern 1 => progress autorewrite with pull_Zadd in * : pull_Zadd.
Hint Extern 1 => progress autorewrite with push_Zsub in * : push_Zsub.
Hint Extern 1 => progress autorewrite with pull_Zsub in * : pull_Zsub.
Hint Extern 1 => progress autorewrite with push_Zdiv in * : push_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zdiv in * : pull_Zmul.
Hint Extern 1 => progress autorewrite with pull_Zmod in * : pull_Zmod.
Hint Extern 1 => progress autorewrite with push_Zmod in * : push_Zmod.
Hint Extern 1 => progress autorewrite with pull_Zof_nat in * : pull_Zof_nat.
Hint Extern 1 => progress autorewrite with push_Zof_nat in * : push_Zof_nat.
Hint Extern 1 => progress autorewrite with pull_Zshift in * : pull_Zshift.
Hint Extern 1 => progress autorewrite with push_Zshift in * : push_Zshift.
Hint Extern 1 => progress autorewrite with Zshift_to_pow in * : Zshift_to_pow.
Hint Extern 1 => progress autorewrite with Zpow_to_shift in * : Zpow_to_shift.
Hint Extern 1 => progress autorewrite with pull_Zof_N in * : pull_Zof_N.
Hint Extern 1 => progress autorewrite with push_Zof_N in * : push_Zof_N.
Hint Extern 1 => progress autorewrite with pull_Zto_N in * : pull_Zto_N.
Hint Extern 1 => progress autorewrite with push_Zto_N in * : push_Zto_N.
Hint Extern 1 => progress autorewrite with push_Zmax in * : push_Zmax.
Hint Extern 1 => progress autorewrite with pull_Zmax in * : pull_Zmax.
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
Hint Rewrite Z_mod_same_full : push_Zmod.
Hint Rewrite Nat2Z.id N2Z.id : zsimplify.
Hint Rewrite Nat2Z.id : push_Zof_nat.
Hint Rewrite N2Z.id : push_Zto_N.
Hint Rewrite N2Z.id : pull_Zof_N.
Hint Rewrite N2Z.inj_pos N2Z.inj_abs_N N2Z.inj_add N2Z.inj_mul N2Z.inj_sub_max N2Z.inj_succ N2Z.inj_pred_max N2Z.inj_min N2Z.inj_max N2Z.inj_div N2Z.inj_quot N2Z.inj_rem N2Z.inj_div2 N2Z.inj_pow N2Z.inj_0 nat_N_Z : push_Zof_N.
Hint Rewrite N2Z.inj_compare N2Z.inj_testbit : pull_Zof_N.
Hint Rewrite <- N2Z.inj_abs_N N2Z.inj_add N2Z.inj_mul N2Z.inj_sub_max N2Z.inj_succ N2Z.inj_pred_max N2Z.inj_min N2Z.inj_max N2Z.inj_div N2Z.inj_quot N2Z.inj_rem N2Z.inj_div2 N2Z.inj_pow : pull_Zof_N.
Hint Rewrite Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : push_Zof_nat.
Hint Rewrite <- Nat2Z.inj_0 Nat2Z.inj_succ Nat2Z.inj_abs_nat Nat2Z.inj_add Nat2Z.inj_mul Nat2Z.inj_sub_max Nat2Z.inj_pred_max Nat2Z.inj_min Nat2Z.inj_max Zabs2Nat.id_abs Zabs2Nat.id : pull_Zof_nat.
Hint Rewrite Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : pull_Zshift.
Hint Rewrite <- Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : pull_Zshift.
Hint Rewrite Z.shiftr_lxor Z.shiftr_land Z.shiftr_lor Z.shiftr_ldiff Z.lnot_shiftr Z.ldiff_ones_r Z.shiftl_lxor Z.shiftl_land Z.shiftl_lor Z.shiftl_ldiff using zutil_arith : push_Zshift.
Hint Rewrite <- Z.shiftr_shiftl_l Z.shiftr_shiftl_r Z.shiftr_shiftr Z.shiftl_shiftl using zutil_arith : push_Zshift.
Hint Rewrite Z.shiftr_opp_r Z.shiftl_opp_r Z.shiftr_0_r Z.shiftr_0_l Z.shiftl_0_r Z.shiftl_0_l : push_Zshift.
Hint Rewrite Z.shiftl_1_l Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 Z.opp_involutive using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_opp_r using zutil_arith : Zshift_to_pow.
Hint Rewrite <- Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : Zpow_to_shift.
Hint Rewrite Z.add_max_distr_r Z.add_max_distr_l : push_Zmax.
Hint Rewrite <- Z.add_max_distr_r Z.add_max_distr_l : pull_Zmax.

(** For the occasional lemma that can remove the use of [Z.div] *)
Create HintDb zstrip_div.
Hint Rewrite Z.div_small_iff using zutil_arith : zstrip_div.

Hint Rewrite <- Z.shiftr_div_pow2 Z.shiftr_mul_pow2 Z.shiftl_mul_pow2 Z.shiftl_div_pow2 using zutil_arith : convert_to_Ztestbit.

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

Create HintDb Ztestbit discriminated.
Create HintDb Ztestbit_full discriminated.
Hint Rewrite Z.testbit_0_l Z.land_spec Z.lor_spec : Ztestbit.
Hint Rewrite Z.testbit_0_l Z.land_spec Z.lor_spec : Ztestbit_full.
Hint Rewrite Z.shiftl_spec Z.shiftr_spec using zutil_arith : Ztestbit.
Hint Rewrite Z.testbit_neg_r using zutil_arith : Ztestbit.
Hint Rewrite Bool.andb_true_r Bool.andb_false_r Bool.orb_true_r Bool.orb_false_r
             Bool.andb_true_l Bool.andb_false_l Bool.orb_true_l Bool.orb_false_l : Ztestbit.

Module Z.
  Ltac peel_le_step :=
    match goal with
    | [ |- ?x + _ <= ?x + _ ]
      => apply Z.add_le_mono_l
    | [ |- _ + ?x <= _ + ?x ]
      => apply Z.add_le_mono_r
    | [ |- ?x - _ <= ?x - _ ]
      => apply Z.sub_le_mono_l
    | [ |- _ - ?x <= _ - ?x ]
      => apply Z.sub_le_mono_r
    | [ |- ?x^_ <= ?x^_ ]
      => apply Z.pow_le_mono_r; [ zutil_arith | ]
    | [ |- _^?x <= _^?x ]
      => apply Z.pow_le_mono_l; split; [ zutil_arith | ]
    | [ |- Z.log2_up _ <= Z.log2_up _ ]
      => apply Z.log2_up_le_mono
    | [ |- Z.log2 _ <= Z.log2 _ ]
      => apply Z.log2_le_mono
    | [ |- Z.succ _ <= Z.succ _ ]
      => apply Zsucc_le_compat
    | [ |- Z.pred _ <= Z.pred _ ]
      => apply Z.pred_le_mono
    | [ |- ?x * _ <= ?x * _ ]
      => first [ apply Z.mul_le_mono_nonneg_l; [ zutil_arith | ]
               | apply Z.mul_le_mono_nonpos_l; [ zutil_arith | ] ]
    | [ |- _ * ?x <= _ * ?x ]
      => first [ apply Z.mul_le_mono_nonneg_r; [ zutil_arith | ]
               | apply Z.mul_le_mono_nonpos_r; [ zutil_arith | ] ]
    | [ |- -_ <= -_ ]
      => apply Z.opp_le_mono
    | [ |- _ / ?x <= _ / ?x ]
      => apply Z.div_le_mono; [ zutil_arith | ]
    | [ |- ?x / _ <= ?x / _ ]
      => apply Z.div_le_compat_l; [ zutil_arith | split; [ zutil_arith | ] ]
    | [ |- Z.quot _ ?x <= Z.quot _ ?x ]
      => apply Z.quot_le_mono; [ zutil_arith | ]
    | [ |- Z.quot ?x _ <= Z.quot ?x _ ]
      => apply Z.quot_le_compat_l; [ zutil_arith | split; [ zutil_arith | ] ]
    | [ |- Z.max ?x _ <= Z.max ?x _ ]
      => apply Z.max_le_compat_l
    | [ |- Z.max _ ?x <= Z.max _ ?x ]
      => apply Z.max_le_compat_r
    | [ |- Z.min ?x _ <= Z.min ?x _ ]
      => apply Z.min_le_compat_l
    | [ |- Z.min _ ?x <= Z.min _ ?x ]
      => apply Z.min_le_compat_r
    end.
  Ltac peel_le := repeat peel_le_step.

  Lemma pow2_mod_spec : forall a b, (0 <= b) -> Z.pow2_mod a b = a mod (2 ^ b).
  Proof.
    intros.
    unfold Z.pow2_mod.
    rewrite Z.land_ones; auto.
  Qed.
  Hint Rewrite <- Z.pow2_mod_spec using zutil_arith : convert_to_Ztestbit.

  Lemma ones_spec : forall n m, 0 <= n -> 0 <= m -> Z.testbit (Z.ones n) m = if Z_lt_dec m n then true else false.
  Proof.
    intros.
    break_match.
    + apply Z.ones_spec_low. omega.
    + apply Z.ones_spec_high. omega.
  Qed.
  Hint Rewrite ones_spec using zutil_arith : Ztestbit.

  Lemma ones_spec_full : forall n m, Z.testbit (Z.ones n) m
                                     = if Z_lt_dec m 0
                                       then false
                                       else if Z_lt_dec n 0
                                            then true
                                            else if Z_lt_dec m n then true else false.
  Proof.
    intros.
    repeat (break_match || autorewrite with Ztestbit); try reflexivity; try omega.
    unfold Z.ones.
    rewrite <- Z.shiftr_opp_r, Z.shiftr_eq_0 by (simpl; omega); simpl.
    destruct m; simpl in *; try reflexivity.
    exfalso; auto using Zlt_neg_0.
  Qed.
  Hint Rewrite ones_spec_full : Ztestbit_full.

  Lemma testbit_pow2_mod : forall a n i, 0 <= n ->
  Z.testbit (Z.pow2_mod a n) i = if Z_lt_dec i n then Z.testbit a i else false.
  Proof.
  cbv [Z.pow2_mod]; intros; destruct (Z_le_dec 0 i);
      repeat match goal with
          | |- _ => rewrite Z.testbit_neg_r by omega
          | |- _ => break_innermost_match_step
          | |- _ => omega
          | |- _ => reflexivity
          | |- _ => progress autorewrite with Ztestbit
          end.
  Qed.
  Hint Rewrite testbit_pow2_mod using zutil_arith : Ztestbit.

  Lemma testbit_pow2_mod_full : forall a n i,
      Z.testbit (Z.pow2_mod a n) i = if Z_lt_dec n 0
                                     then if Z_lt_dec i 0 then false else Z.testbit a i
                                     else if Z_lt_dec i n then Z.testbit a i else false.
  Proof.
    intros; destruct (Z_lt_dec n 0); [ | apply testbit_pow2_mod; omega ].
    unfold Z.pow2_mod.
    autorewrite with Ztestbit_full;
      repeat break_match;
      autorewrite with Ztestbit;
      reflexivity.
  Qed.
  Hint Rewrite testbit_pow2_mod_full : Ztestbit_full.

  Lemma bits_above_pow2 a n : 0 <= a < 2^n -> Z.testbit a n = false.
  Proof.
    intros.
    destruct (Z_zerop a); subst; autorewrite with Ztestbit; trivial.
    apply Z.bits_above_log2; auto with zarith concl_log2.
  Qed.
  Hint Rewrite bits_above_pow2 using zutil_arith : Ztestbit.

  Lemma pow2_mod_0_r : forall a, Z.pow2_mod a 0 = 0.
  Proof.
    intros; rewrite Z.pow2_mod_spec, Z.mod_1_r; reflexivity.
  Qed.

  Lemma pow2_mod_0_l : forall n, 0 <= n -> Z.pow2_mod 0 n = 0.
  Proof.
    intros; rewrite Z.pow2_mod_spec, Z.mod_0_l; try reflexivity; try apply Z.pow_nonzero; omega.
  Qed.

  Lemma pow2_mod_split : forall a n m, 0 <= n -> 0 <= m ->
                                       Z.pow2_mod a (n + m) = Z.lor (Z.pow2_mod a n) ((Z.pow2_mod (a >> n) m) << n).
  Proof.
    intros; cbv [Z.pow2_mod].
    apply Z.bits_inj'; intros.
    repeat progress (try break_match; autorewrite with Ztestbit zsimplify; try reflexivity).
    try match goal with H : ?a < ?b |- context[Z.testbit _ (?a - ?b)] =>
      rewrite !Z.testbit_neg_r with (n := a - b) by omega end.
    autorewrite with Ztestbit; reflexivity.
  Qed.

  Lemma pow2_mod_pow2_mod : forall a n m, 0 <= n -> 0 <= m ->
                                          Z.pow2_mod (Z.pow2_mod a n) m = Z.pow2_mod a (Z.min n m).
  Proof.
    intros; cbv [Z.pow2_mod].
    apply Z.bits_inj'; intros.
    apply Z.min_case_strong; intros; repeat progress (try break_match; autorewrite with Ztestbit zsimplify; try reflexivity).
  Qed.

  Lemma pow2_mod_pos_bound a b : 0 < b -> 0 <= Z.pow2_mod a b < 2^b.
  Proof.
    intros; rewrite Z.pow2_mod_spec by omega.
    auto with zarith.
  Qed.
  Hint Resolve pow2_mod_pos_bound : zarith.

  Lemma land_same_r : forall a b, (a &' b) &' b = a &' b.
  Proof.
  intros; apply Z.bits_inj'; intros.
  rewrite !Z.land_spec.
  case_eq (Z.testbit b n); intros;
      rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; reflexivity.
  Qed.

  Lemma div_lt_upper_bound' a b q : 0 < b -> a < q * b -> a / b < q.
  Proof. intros; apply Z.div_lt_upper_bound; nia. Qed.
  Hint Resolve div_lt_upper_bound' : zarith.

  Lemma mul_comm3 x y z : x * (y * z) = y * (x * z).
  Proof. lia. Qed.

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

  Lemma mod_add_full : forall a b c, (a + b * c) mod c = a mod c.
  Proof. intros; destruct (Z_zerop c); try subst; autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_full : zsimplify.

  Lemma mod_add_l_full : forall a b c, (a * b + c) mod b = c mod b.
  Proof. intros; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add_l_full : zsimplify.

  Lemma mod_add'_full : forall a b c, (a + b * c) mod b = a mod b.
  Proof. intros; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l'_full : forall a b c, (a * b + c) mod a = c mod a.
  Proof. intros; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.
  Hint Rewrite mod_add'_full mod_add_l'_full : zsimplify.

  Lemma mod_add_l : forall a b c, b <> 0 -> (a * b + c) mod b = c mod b.
  Proof. intros; rewrite (Z.add_comm _ c); autorewrite with zsimplify; reflexivity. Qed.

  Lemma mod_add' : forall a b c, b <> 0 -> (a + b * c) mod b = a mod b.
  Proof. intros; rewrite (Z.mul_comm _ c); autorewrite with zsimplify; reflexivity. Qed.
  Lemma mod_add_l' : forall a b c, a <> 0 -> (a * b + c) mod a = c mod a.
  Proof. intros; rewrite (Z.mul_comm _ b); autorewrite with zsimplify; reflexivity. Qed.

  Lemma add_pow_mod_l : forall a b c, a <> 0 -> 0 < b ->
                                      ((a ^ b) + c) mod a = c mod a.
  Proof.
    intros; replace b with (b - 1 + 1) by ring;
      rewrite Z.pow_add_r, Z.pow_1_r by omega; auto using Z.mod_add_l.
  Qed.

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

  Lemma mod_to_nat x m (Hm:(0 < m)%Z) (Hx:(0 <= x)%Z) : (Z.to_nat x mod Z.to_nat m = Z.to_nat (x mod m))%nat.
    pose proof Zdiv.mod_Zmod (Z.to_nat x) (Z.to_nat m) as H;
      rewrite !Z2Nat.id in H by omega.
    rewrite <-H by (change 0%nat with (Z.to_nat 0); rewrite Z2Nat.inj_iff; omega).
    rewrite !Nat2Z.id; reflexivity.
  Qed.

  Ltac divide_exists_mul := let k := fresh "k" in
  match goal with
  | [ H : (?a | ?b) |- _ ] => apply Z.mod_divide in H; try apply Zmod_divides in H;
                              match type of H with
                              | ex _ => destruct H as [k H]
                              | _ => destruct H
                              end
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

  Lemma mul_div_eq_full : forall a m, m <> 0 -> m * (a / m) = (a - a mod m).
  Proof.
    intros. rewrite (Z_div_mod_eq_full a m) at 2 by auto. ring.
  Qed.

  Hint Rewrite mul_div_eq_full using zutil_arith : zdiv_to_mod.
  Hint Rewrite <-mul_div_eq_full using zutil_arith : zmod_to_div.

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
  Hint Rewrite testbit_add_shiftl_low using zutil_arith : Ztestbit.

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
  Hint Rewrite testbit_add_shiftl_high using zutil_arith : Ztestbit.

  Lemma nonneg_pow_pos a b : 0 < a -> 0 < a^b -> 0 <= b.
  Proof.
    destruct (Z_lt_le_dec b 0); intros; auto.
    erewrite Z.pow_neg_r in * by eassumption.
    omega.
  Qed.
  Hint Resolve nonneg_pow_pos (fun n => nonneg_pow_pos 2 n Z.lt_0_2) : zarith.
  Lemma nonneg_pow_pos_helper a b dummy : 0 < a -> 0 <= dummy < a^b -> 0 <= b.
  Proof. eauto with zarith omega. Qed.
  Hint Resolve nonneg_pow_pos_helper (fun n dummy => nonneg_pow_pos_helper 2 n dummy Z.lt_0_2) : zarith.

  Lemma testbit_add_shiftl_full i (Hi : 0 <= i) a b n (Ha : 0 <= a < 2^n)
    : Z.testbit (a + b << n) i
      = if (i <? n) then Z.testbit a i else Z.testbit b (i - n).
  Proof.
    assert (0 < 2^n) by omega.
    assert (0 <= n) by eauto 2 with zarith.
    pose proof (Zlt_cases i n); break_match; autorewrite with Ztestbit; reflexivity.
  Qed.
  Hint Rewrite testbit_add_shiftl_full using zutil_arith : Ztestbit.

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

  Lemma pow2_lt_or_divides : forall a b, 0 <= b ->
    2 ^ a < 2 ^ b \/ (2 ^ a) mod 2 ^ b = 0.
  Proof.
    intros.
    destruct (Z_lt_dec a b); [left|right].
    { apply Z.pow_lt_mono_r; auto; omega. }
    { replace a with (a - b + b) by ring.
      rewrite Z.pow_add_r by omega.
      apply Z.mod_mul, Z.pow_nonzero; omega. }
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
  Hint Rewrite <- Z.lor_shiftl using zutil_arith : convert_to_Ztestbit.

  Lemma lor_shiftl' : forall a b n, 0 <= n -> 0 <= a < 2 ^ n ->
    Z.lor (Z.shiftl b n) a = (Z.shiftl b n) + a.
  Proof.
    intros; rewrite Z.lor_comm, Z.add_comm; apply lor_shiftl; assumption.
  Qed.
  Hint Rewrite <- Z.lor_shiftl' using zutil_arith : convert_to_Ztestbit.

  Lemma shiftl_spec_full a n m
    : Z.testbit (a << n) m = if Z_lt_dec m n
                             then false
                             else if Z_le_dec 0 m
                                  then Z.testbit a (m - n)
                                  else false.
  Proof.
    repeat break_match; auto using Z.shiftl_spec_low, Z.shiftl_spec, Z.testbit_neg_r with omega.
  Qed.
  Hint Rewrite shiftl_spec_full : Ztestbit_full.

  Lemma shiftr_spec_full a n m
    : Z.testbit (a >> n) m = if Z_lt_dec m (-n)
                             then false
                             else if Z_le_dec 0 m
                                  then Z.testbit a (m + n)
                                  else false.
  Proof.
    rewrite <- Z.shiftl_opp_r, shiftl_spec_full, Z.sub_opp_r; reflexivity.
  Qed.
  Hint Rewrite shiftr_spec_full : Ztestbit_full.

  Lemma lnot_sub1 x : Z.lnot (x-1) = (-x).
  Proof.
    replace (-x) with (- (1) - (x - 1)) by omega.
    rewrite <-(Z.add_lnot_diag (x-1)); omega.
  Qed.

  Lemma lnot_opp x : Z.lnot (- x) = x-1.
  Proof.
    rewrite <-Z.lnot_involutive, lnot_sub1; reflexivity.
  Qed.

  Lemma testbit_sub_pow2 n i x (i_range:0 <= i < n) (x_range:0 < x < 2 ^ n) :
    Z.testbit (2 ^ n - x) i = negb (Z.testbit (x - 1)  i).
  Proof.
    rewrite <-Z.lnot_spec, lnot_sub1 by omega.
    rewrite <-(Z.mod_pow2_bits_low (-x) _ _ (proj2 i_range)).
    f_equal.
    rewrite Z.mod_opp_l_nz; autorewrite with zsimplify; omega.
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
  Hint Resolve ones_nonneg : zarith.

  Lemma ones_pos_pos : forall i, (0 < i) -> 0 < Z.ones i.
  Proof.
    intros.
    unfold Z.ones.
    rewrite Z.shiftl_1_l.
    apply Z.lt_succ_lt_pred.
    apply Z.pow_gt_1; omega.
  Qed.
  Hint Resolve ones_pos_pos : zarith.

  Lemma pow2_mod_id_iff : forall a n, 0 <= n ->
                                      (Z.pow2_mod a n = a <-> 0 <= a < 2 ^ n).
  Proof.
    intros.
    rewrite Z.pow2_mod_spec by assumption.
    assert (0 < 2 ^ n) by zero_bounds.
    rewrite Z.mod_small_iff by omega.
    split; intros; intuition omega.
  Qed.

  Lemma testbit_false_bound : forall a x, 0 <= x ->
    (forall n, ~ (n < x) -> Z.testbit a n = false) ->
    a < 2 ^ x.
  Proof.
    intros.
    assert (a = Z.pow2_mod a x). {
     apply Z.bits_inj'; intros.
     rewrite Z.testbit_pow2_mod by omega; break_match; auto.
    }
    rewrite H1.
    rewrite Z.pow2_mod_spec; try apply Z.mod_pos_bound; zero_bounds.
  Qed.

  Lemma lor_range : forall x y n, 0 <= x < 2 ^ n -> 0 <= y < 2 ^ n ->
                                  0 <= Z.lor x y < 2 ^ n.
  Proof.
    intros; assert (0 <= n) by auto with zarith omega.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => rewrite Z.lor_spec
           | |- _ => rewrite Z.testbit_eqb by auto with zarith omega
           | |- _ => rewrite !Z.div_small by (split; try omega; eapply Z.lt_le_trans;
                             [ intuition eassumption | apply Z.pow_le_mono_r; omega])
           | |- _ => split
           | |- _ => apply testbit_false_bound
           | |- _ => solve [auto with zarith]
           | |- _ => solve [apply Z.lor_nonneg; intuition auto]
           end.
  Qed.
  Hint Resolve lor_range : zarith.

  Lemma lor_shiftl_bounds : forall x y n m,
      (0 <= n)%Z -> (0 <= m)%Z ->
      (0 <= x < 2 ^ m)%Z ->
      (0 <= y < 2 ^ n)%Z ->
      (0 <= Z.lor y (Z.shiftl x n) < 2 ^ (n + m))%Z.
  Proof.
    intros.
    apply Z.lor_range.
    { split; try omega.
      apply Z.lt_le_trans with (m := (2 ^ n)%Z); try omega.
      apply Z.pow_le_mono_r; omega. }
    { rewrite Z.shiftl_mul_pow2 by omega.
      rewrite Z.pow_add_r by omega.
      split; zero_bounds.
      rewrite Z.mul_comm.
      apply Z.mul_lt_mono_pos_l; omega. }
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

  Lemma add_compare_mono_r: forall n m p, (n + p ?= m + p) = (n ?= m).
  Proof.
    intros.
    rewrite <-!(Z.add_comm p).
    apply Z.add_compare_mono_l.
  Qed.

  Lemma compare_add_shiftl : forall x1 y1 x2 y2 n, 0 <= n ->
    Z.pow2_mod x1 n = x1 -> Z.pow2_mod x2 n = x2  ->
    x1 + (y1 << n) ?= x2 + (y2 << n) =
      if Z_eq_dec y1 y2
      then x1 ?= x2
      else y1 ?= y2.
  Proof.
    repeat match goal with
           | |- _ => progress intros
           | |- _ => progress subst y1
           | |- _ => rewrite Z.shiftl_mul_pow2 by omega
           | |- _ => rewrite add_compare_mono_r
           | |- _ => rewrite <-Z.mul_sub_distr_r
           | |- _ => break_innermost_match_step
           | H : Z.pow2_mod _ _ = _ |- _ => rewrite pow2_mod_id_iff in H by omega
           | H : ?a <> ?b |- _ = (?a ?= ?b) =>
             case_eq (a ?= b); rewrite ?Z.compare_eq_iff, ?Z.compare_gt_iff, ?Z.compare_lt_iff
           | |- _ + (_ * _) > _ + (_ * _) => cbv [Z.gt]
           | |- _ + (_ * ?x) < _ + (_ * ?x) =>
             apply Z.lt_sub_lt_add; apply Z.lt_le_trans with (m := 1 * x); [omega|]
           | |- _ => apply Z.mul_le_mono_nonneg_r; omega
           | |- _ => reflexivity
           | |- _ => congruence
           end.
  Qed.

  Lemma eqb_cases x y : if x =? y then x = y else x <> y.
  Proof.
    pose proof (Z.eqb_spec x y) as H.
    inversion H; trivial.
  Qed.

  Lemma ones_le x y : x <= y -> Z.ones x <= Z.ones y.
  Proof.
    rewrite !Z.ones_equiv; auto with zarith.
  Qed.
  Hint Resolve ones_le : zarith.

  Lemma geb_spec0 : forall x y : Z, Bool.reflect (x >= y) (x >=? y).
  Proof.
    intros x y; pose proof (Zge_cases x y) as H; destruct (Z.geb x y); constructor; omega.
  Qed.
  Lemma gtb_spec0 : forall x y : Z, Bool.reflect (x > y) (x >? y).
  Proof.
    intros x y; pose proof (Zgt_cases x y) as H; destruct (Z.gtb x y); constructor; omega.
  Qed.

  Ltac ltb_to_lt_with_hyp H lem :=
    let H' := fresh in
    rename H into H';
    pose proof lem as H;
    rewrite H' in H;
    clear H'.

  Ltac ltb_to_lt_in_goal b' lem :=
    refine (proj1 (@reflect_iff_gen _ _ lem b') _);
    cbv beta iota.

  Ltac ltb_to_lt_hyps_step :=
    match goal with
    | [ H : (?x <? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zlt_cases x y)
    | [ H : (?x <=? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zle_cases x y)
    | [ H : (?x >? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zgt_cases x y)
    | [ H : (?x >=? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (Zge_cases x y)
    | [ H : (?x =? ?y) = ?b |- _ ]
      => ltb_to_lt_with_hyp H (eqb_cases x y)
    end.
  Ltac ltb_to_lt_goal_step :=
    match goal with
    | [ |- (?x <? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.ltb_spec0 x y)
    | [ |- (?x <=? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.leb_spec0 x y)
    | [ |- (?x >? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.gtb_spec0 x y)
    | [ |- (?x >=? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.geb_spec0 x y)
    | [ |- (?x =? ?y) = ?b ]
      => ltb_to_lt_in_goal b (Z.eqb_spec x y)
    end.
  Ltac ltb_to_lt_step :=
    first [ ltb_to_lt_hyps_step
          | ltb_to_lt_goal_step ].
  Ltac ltb_to_lt := repeat ltb_to_lt_step.

  Section R_Rb.
    Local Ltac t := intros ? ? []; split; intro; ltb_to_lt; omega.
    Local Notation R_Rb Rb R nR := (forall x y b, Rb x y = b <-> if b then R x y else nR x y).
    Lemma ltb_lt_iff : R_Rb Z.ltb Z.lt Z.ge. Proof. t. Qed.
    Lemma leb_le_iff : R_Rb Z.leb Z.le Z.gt. Proof. t. Qed.
    Lemma gtb_gt_iff : R_Rb Z.gtb Z.gt Z.le. Proof. t. Qed.
    Lemma geb_ge_iff : R_Rb Z.geb Z.ge Z.lt. Proof. t. Qed.
    Lemma eqb_eq_iff : R_Rb Z.eqb (@Logic.eq Z) (fun x y => x <> y). Proof. t. Qed.
  End R_Rb.
  Hint Rewrite ltb_lt_iff leb_le_iff gtb_gt_iff geb_ge_iff eqb_eq_iff : ltb_to_lt.
  Ltac ltb_to_lt_in_context :=
    repeat autorewrite with ltb_to_lt in *;
    cbv beta iota in *.

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
  Proof. omega. Qed.

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

  Lemma div_between_if n a b : 0 <= n -> b <> 0 -> n * b <= a < (2 + n) * b -> (a / b = if (1 + n) * b <=? a then 1 + n else n)%Z.
  Proof.
    intros.
    break_match; ltb_to_lt;
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
    intros.
    replace (a mod b) with ((1 * b + (a - b)) mod b) by (f_equal; ring).
    rewrite Z.mod_add_l by auto.
    apply Z.mod_small.
    omega.
  Qed.


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

  Lemma shiftl_add x y z : 0 <= z -> (x + y) << z = (x << z) + (y << z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftl_add using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftl_add using zutil_arith : pull_Zshift.

  Lemma shiftr_add x y z : z <= 0 -> (x + y) >> z = (x >> z) + (y >> z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftr_add using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftr_add using zutil_arith : pull_Zshift.

  Lemma shiftl_sub x y z : 0 <= z -> (x - y) << z = (x << z) - (y << z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftl_sub using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftl_sub using zutil_arith : pull_Zshift.

  Lemma shiftr_sub x y z : z <= 0 -> (x - y) >> z = (x >> z) - (y >> z).
  Proof. intros; autorewrite with Zshift_to_pow; lia. Qed.
  Hint Rewrite shiftr_sub using zutil_arith : push_Zshift.
  Hint Rewrite <- shiftr_sub using zutil_arith : pull_Zshift.

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
    { split; zero_bounds.
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
    intros.
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
    intros; break_match; [ apply lt_pow_2_shiftr; omega | ].
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

  Lemma log2_pred_pow2_full a : Z.log2 (Z.pred (2^a)) = Z.max 0 (Z.pred a).
  Proof.
    destruct (Z_dec 0 a) as [ [?|?] | ?].
    { rewrite Z.log2_pred_pow2 by assumption.
      apply Z.max_case_strong; omega. }
    { autorewrite with zsimplify; simpl.
      apply Z.max_case_strong; omega. }
    { subst; compute; reflexivity. }
  Qed.
  Hint Rewrite log2_pred_pow2_full : zsimplify.

  Lemma log2_up_le_full a : a <= 2^Z.log2_up a.
  Proof.
    destruct (Z_dec 1 a) as [ [ ? | ? ] | ? ];
      first [ apply Z.log2_up_spec; assumption
            | rewrite Z.log2_up_eqn0 by omega; simpl; omega ].
  Qed.

  Lemma log2_up_le_pow2_full : forall a b : Z, (0 <= b)%Z -> (a <= 2 ^ b)%Z <-> (Z.log2_up a <= b)%Z.
  Proof.
    intros a b H.
    destruct (Z_lt_le_dec 0 a); [ apply Z.log2_up_le_pow2; assumption | ].
    split; transitivity 0%Z; try omega; auto with zarith.
    rewrite Z.log2_up_eqn0 by omega.
    reflexivity.
  Qed.

  Lemma ones_lt_pow2 x y : 0 <= x <= y -> Z.ones x < 2^y.
  Proof.
    rewrite Z.ones_equiv, Z.lt_pred_le.
    auto with zarith.
  Qed.
  Hint Resolve ones_lt_pow2 : zarith.

  Lemma log2_ones_full x : Z.log2 (Z.ones x) = Z.max 0 (Z.pred x).
  Proof.
    rewrite Z.ones_equiv, log2_pred_pow2_full; reflexivity.
  Qed.
  Hint Rewrite log2_ones_full : zsimplify.

  Lemma log2_ones_lt x y : 0 < x <= y -> Z.log2 (Z.ones x) < y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_lt : zarith.

  Lemma log2_ones_le x y : 0 <= x <= y -> Z.log2 (Z.ones x) <= y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_le : zarith.

  Lemma log2_ones_lt_nonneg x y : 0 < y -> x <= y -> Z.log2 (Z.ones x) < y.
  Proof.
    rewrite log2_ones_full; apply Z.max_case_strong; omega.
  Qed.
  Hint Resolve log2_ones_lt_nonneg : zarith.

  Lemma log2_lt_pow2_alt a b : 0 < b -> (a < 2^b <-> Z.log2 a < b).
  Proof.
    destruct (Z_lt_le_dec 0 a); auto using Z.log2_lt_pow2; [].
    rewrite Z.log2_nonpos by omega.
    split; auto with zarith; [].
    intro; eapply le_lt_trans; [ eassumption | ].
    auto with zarith.
  Qed.

  Section ZInequalities.
    Lemma land_le : forall x y, (0 <= x)%Z -> (Z.land x y <= x)%Z.
    Proof.
      intros; apply Z.ldiff_le; [assumption|].
      rewrite Z.ldiff_land, Z.land_comm, Z.land_assoc.
      rewrite <- Z.land_0_l with (a := y); f_equal.
      rewrite Z.land_comm, Z.land_lnot_diag.
      reflexivity.
    Qed.

    Lemma lor_lower : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (x <= Z.lor x y)%Z.
    Proof.
      intros; apply Z.ldiff_le; [apply Z.lor_nonneg; auto|].
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
      intros; apply Z.ldiff_le.

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

    Lemma pow2_ge_0: forall a, (0 <= 2 ^ a)%Z.
    Proof.
      intros; apply Z.pow_nonneg; omega.
    Qed.

    Lemma pow2_gt_0: forall a, (0 <= a)%Z -> (0 < 2 ^ a)%Z.
    Proof.
      intros; apply Z.pow_pos_nonneg; [|assumption]; omega.
    Qed.

    Local Ltac solve_pow2 :=
      repeat match goal with
             | [|- _ /\ _] => split
             | [|- (0 < 2 ^ _)%Z] => apply pow2_gt_0
             | [|- (0 <= 2 ^ _)%Z] => apply pow2_ge_0
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
      split; [apply Z.mod_pos_bound, pow2_gt_0; assumption|].
      eapply Z.lt_le_trans; [apply Z.mod_pos_bound, pow2_gt_0; assumption|].
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
      apply Z.div_lt_upper_bound; [apply pow2_gt_0; assumption|].
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

  Lemma max_log2_up x y : Z.max (Z.log2_up x) (Z.log2_up y) = Z.log2_up (Z.max x y).
  Proof. apply Z.max_monotone; intros ??; apply Z.log2_up_le_mono. Qed.
  Hint Rewrite max_log2_up : push_Zmax.
  Hint Rewrite <- max_log2_up : pull_Zmax.

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

  Lemma log2_up_le_full_max a : Z.max a 1 <= 2^Z.log2_up a.
  Proof.
    apply Z.max_case_strong; auto using Z.log2_up_le_full.
    intros; rewrite Z.log2_up_eqn0 by assumption; reflexivity.
  Qed.
  Lemma log2_up_le_1 a : Z.log2_up a <= 1 <-> a <= 2.
  Proof.
    pose proof (Z.log2_nonneg (Z.pred a)).
    destruct (Z_dec a 2) as [ [ ? | ? ] | ? ].
    { rewrite (proj2 (Z.log2_up_null a)) by omega; split; omega. }
    { rewrite Z.log2_up_eqn by omega.
      split; try omega; intro.
      assert (Z.log2 (Z.pred a) = 0) by omega.
      assert (Z.pred a <= 1) by (apply Z.log2_null; omega).
      omega. }
    { subst; cbv -[Z.le]; split; omega. }
  Qed.
  Lemma log2_up_1_le a : 1 <= Z.log2_up a <-> 2 <= a.
  Proof.
    pose proof (Z.log2_nonneg (Z.pred a)).
    destruct (Z_dec a 2) as [ [ ? | ? ] | ? ].
    { rewrite (proj2 (Z.log2_up_null a)) by omega; split; omega. }
    { rewrite Z.log2_up_eqn by omega; omega. }
    { subst; cbv -[Z.le]; split; omega. }
  Qed.

  Lemma simplify_twice_sub_sub x y : 2 * x - (x - y) = x + y.
  Proof. lia. Qed.
  Hint Rewrite simplify_twice_sub_sub : zsimplify.

  Lemma simplify_twice_sub_add x y : 2 * x - (x + y) = x - y.
  Proof. lia. Qed.
  Hint Rewrite simplify_twice_sub_add : zsimplify.

  Lemma simplify_2XmX X : 2 * X - X = X.
  Proof. omega. Qed.
  Hint Rewrite simplify_2XmX : zsimplify.

  Lemma simplify_add_pos x y : Z.pos x + Z.pos y = Z.pos (x + y).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_add_pos : zsimplify_Z_to_pos.
  Lemma simplify_add_pos10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    : Z.pos x0 + (Z.pos x1 + (Z.pos x2 + (Z.pos x3 + (Z.pos x4 + (Z.pos x5 + (Z.pos x6 + (Z.pos x7 + (Z.pos x8 + Z.pos x9))))))))
      = Z.pos (x0 + (x1 + (x2 + (x3 + (x4 + (x5 + (x6 + (x7 + (x8 + x9))))))))).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_add_pos10 : zsimplify_Z_to_pos.
  Lemma simplify_mul_pos x y : Z.pos x * Z.pos y = Z.pos (x * y).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_mul_pos : zsimplify_Z_to_pos.
  Lemma simplify_mul_pos10 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9
    : Z.pos x0 * (Z.pos x1 * (Z.pos x2 * (Z.pos x3 * (Z.pos x4 * (Z.pos x5 * (Z.pos x6 * (Z.pos x7 * (Z.pos x8 * Z.pos x9))))))))
      = Z.pos (x0 * (x1 * (x2 * (x3 * (x4 * (x5 * (x6 * (x7 * (x8 * x9))))))))).
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_mul_pos10 : zsimplify_Z_to_pos.
  Lemma simplify_sub_pos x y : Z.pos x - Z.pos y = Z.pos_sub x y.
  Proof. reflexivity. Qed.
  Hint Rewrite simplify_sub_pos : zsimplify_Z_to_pos.

  Lemma move_R_pX x y z : x + y = z -> x = z - y.
  Proof. omega. Qed.
  Lemma move_R_mX x y z : x - y = z -> x = z + y.
  Proof. omega. Qed.
  Lemma move_R_Xp x y z : y + x = z -> x = z - y.
  Proof. omega. Qed.
  Lemma move_R_Xm x y z : y - x = z -> x = y - z.
  Proof. omega. Qed.
  Lemma move_L_pX x y z : z = x + y -> z - y = x.
  Proof. omega. Qed.
  Lemma move_L_mX x y z : z = x - y -> z + y = x.
  Proof. omega. Qed.
  Lemma move_L_Xp x y z : z = y + x -> z - y = x.
  Proof. omega. Qed.
  Lemma move_L_Xm x y z : z = y - x -> y - z = x.
  Proof. omega. Qed.

  (** [linear_substitute x] attempts to maipulate equations using only
      addition and subtraction to put [x] on the left, and then
      eliminates [x].  Currently, it only handles equations where [x]
      appears once; it does not yet handle equations like [x - x + x =
      5]. *)
  Ltac linear_solve_for_in_step for_var H :=
    let LHS := match type of H with ?LHS = ?RHS => LHS end in
    let RHS := match type of H with ?LHS = ?RHS => RHS end in
    first [ match RHS with
            | ?a + ?b
              => first [ contains for_var b; apply move_L_pX in H
                       | contains for_var a; apply move_L_Xp in H ]
            | ?a - ?b
              => first [ contains for_var b; apply move_L_mX in H
                       | contains for_var a; apply move_L_Xm in H ]
            | for_var
              => progress symmetry in H
            end
          | match LHS with
            | ?a + ?b
              => first [ not contains for_var b; apply move_R_pX in H
                       | not contains for_var a; apply move_R_Xp in H ]
            | ?a - ?b
              => first [ not contains for_var b; apply move_R_mX in H
                       | not contains for_var a; apply move_R_Xm in H ]
            end ].
  Ltac linear_solve_for_in for_var H := repeat linear_solve_for_in_step for_var H.
  Ltac linear_solve_for for_var :=
    match goal with
    | [ H : for_var = _ |- _ ] => idtac
    | [ H : context[for_var] |- _ ]
      => linear_solve_for_in for_var H;
         lazymatch type of H with
         | for_var = _ => idtac
         | ?T => fail 0 "Could not fully solve for" for_var "in" T "(hypothesis" H ")"
         end
    end.
  Ltac linear_substitute for_var := linear_solve_for for_var; subst for_var.
  Ltac linear_substitute_all :=
    repeat match goal with
           | [ v : Z |- _ ] => linear_substitute v
           end.

  (** [div_mod_to_quot_rem] replaces [x / y] and [x mod y] with new
      variables [q] and [r] while simultaneously adding facts that
      uniquely specify [q] and [r] to the context (roughly, that [y *
      q + r = x] and that [0 <= r < y]. *)
  Ltac div_mod_to_quot_rem_inequality_solver :=
    zutil_arith_more_inequalities.
  Ltac generalize_div_eucl x y :=
    let H := fresh in
    let H' := fresh in
    assert (H' : y <> 0) by div_mod_to_quot_rem_inequality_solver;
    generalize (Z.div_mod x y H'); clear H';
    assert (H' : 0 < y) by div_mod_to_quot_rem_inequality_solver;
    generalize (Z.mod_pos_bound x y H'); clear H';
    let q := fresh "q" in
    let r := fresh "r" in
    set (q := x / y);
    set (r := x mod y);
    clearbody q r.

  Ltac div_mod_to_quot_rem_step :=
    match goal with
    | [ |- context[?x / ?y] ] => generalize_div_eucl x y
    | [ |- context[?x mod ?y] ] => generalize_div_eucl x y
    end.

  Ltac div_mod_to_quot_rem := repeat div_mod_to_quot_rem_step; intros.

  Lemma mod_mod_small a n m
        (Hnm : (m mod n = 0)%Z)
        (Hnm_le : (0 < n <= m)%Z)
        (H : (a mod m < n)%Z)
    : ((a mod n) mod m = a mod m)%Z.
  Proof.
    assert ((a mod n) < m)%Z
      by (eapply Z.lt_le_trans; [ apply Z.mod_pos_bound | ]; omega).
    rewrite (Z.mod_small _ m) by auto with zarith.
    apply Z.mod_divide in Hnm; [ | omega ].
    destruct Hnm as [x ?]; subst.
    repeat match goal with
           | [ H : context[(_ mod _)%Z] |- _ ]
             => revert H
           end.
    Z.div_mod_to_quot_rem.
    lazymatch goal with
    | [ H : a = (?x * ?n * ?q) + _, H' : a = (?n * ?q') + _ |- _ ]
      => assert (q' = x * q) by nia; subst q'; nia
    end.
  Qed.

  (** [rewrite_mod_small] is a better version of [rewrite Z.mod_small
      by rewrite_mod_small_solver]; it backtracks across occurences
      that the solver fails to solve the side-conditions on. *)
  Ltac rewrite_mod_small_solver :=
    zutil_arith_more_inequalities.
  Ltac rewrite_mod_small :=
    repeat match goal with
           | [ |- context[?x mod ?y] ]
             => rewrite (Z.mod_small x y) by rewrite_mod_small_solver
           end.
  Ltac rewrite_mod_mod_small :=
    repeat match goal with
           | [ |- context[(?a mod ?n) mod ?m] ]
             => rewrite (mod_mod_small a n m) by rewrite_mod_small_solver
           end.
  Ltac rewrite_mod_small_more :=
    repeat (rewrite_mod_small || rewrite_mod_mod_small).

  Local Ltac simplify_div_tac :=
    intros; autorewrite with zsimplify; rewrite <- ?Z_div_plus_full_l, <- ?Z_div_plus_full by assumption;
    try (apply f_equal2; [ | reflexivity ]);
    try zutil_arith.

  Ltac clean_neg :=
    repeat match goal with
           | [ H : (-?x) < 0 |- _ ] => assert (0 < x) by omega; clear H
           | [ H : 0 > (-?x) |- _ ] => assert (0 < x) by omega; clear H
           | [ H : (-?x) <= 0 |- _ ] => assert (0 <= x) by omega; clear H
           | [ H : 0 >= (-?x) |- _ ] => assert (0 <= x) by omega; clear H
           | [ H : -?x <= -?y |- _ ] => apply Z.opp_le_mono in H
           | [ |- -?x <= -?y ] => apply Z.opp_le_mono
           | _ => progress rewrite <- Z.opp_le_mono in *
           | [ H : 0 <= ?x, H' : 0 <= ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 <= ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 <= ?x, H' : 0 < ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 < ?y, H'' : -?x <= ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 <= ?y, H'' : -?x < ?y |- _ ] => clear H''
           | [ H : 0 <= ?x, H' : 0 < ?y, H'' : -?x < ?y |- _ ] => clear H''
           | [ H : 0 < ?x, H' : 0 < ?y, H'' : -?x < ?y |- _ ] => clear H''
           end.
  Ltac replace_with_neg x :=
    assert (x = -(-x)) by omega; generalize dependent (-x);
    let x' := fresh in
    rename x into x'; intro x; intros; subst x';
    clean_neg.
  Ltac replace_all_neg_with_pos :=
    repeat match goal with
           | [ H : ?x < 0 |- _ ] => replace_with_neg x
           | [ H : 0 > ?x |- _ ] => replace_with_neg x
           | [ H : ?x <= 0 |- _ ] => replace_with_neg x
           | [ H : 0 >= ?x |- _ ] => replace_with_neg x
           end.

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
      replace_all_neg_with_pos;
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
        Z.div_mod_to_quot_rem; nia. }
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
      replace_all_neg_with_pos;
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
                            Z.div_mod_to_quot_rem; subst;
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
            Z.div_mod_to_quot_rem; nia).
      assert (2^y <= x)
        by (repeat match goal with H : context[_ / _] |- _ => revert H end;
            Z.div_mod_to_quot_rem; nia).
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

  Lemma quot_div_full a b : Z.quot a b = Z.sgn a * Z.sgn b * (Z.abs a / Z.abs b).
  Proof.
    destruct (Z_zerop b); [ subst | apply Z.quot_div; assumption ].
    destruct a; simpl; reflexivity.
  Qed.

  Lemma div_abs_sgn_nonneg a b : 0 <= Z.sgn (Z.abs a / Z.abs b).
  Proof.
    generalize (Zdiv_sgn (Z.abs a) (Z.abs b)).
    destruct a, b; simpl; omega.
  Qed.
  Hint Resolve div_abs_sgn_nonneg : zarith.

  Local Arguments Z.mul !_ !_.

  Lemma quot_sgn_nonneg a b : 0 <= Z.sgn (Z.quot a b) * Z.sgn a * Z.sgn b.
  Proof.
    rewrite quot_div_full, !Z.sgn_mul, !Z.sgn_sgn.
    set (d := Z.abs a / Z.abs b).
    destruct a, b; simpl; try (subst d; simpl; omega);
      try rewrite (Z.mul_opp_l 1);
      do 2 try rewrite (Z.mul_opp_r _ 1);
      rewrite ?Z.mul_1_l, ?Z.mul_1_r, ?Z.opp_involutive;
      apply div_abs_sgn_nonneg.
  Qed.

  Lemma quot_nonneg_same_sgn a b : Z.sgn a = Z.sgn b -> 0 <= Z.quot a b.
  Proof.
    intro H.
    generalize (quot_sgn_nonneg a b); rewrite H.
    rewrite <- Z.mul_assoc, <- Z.sgn_mul.
    destruct (Z_zerop b); [ subst; destruct a; unfold Z.quot; simpl in *; congruence | ].
    rewrite (Z.sgn_pos (_ * _)) by nia.
    intro; apply Z.sgn_nonneg; omega.
  Qed.

  Lemma mul_quot_eq_full a m : m <> 0 -> m * (Z.quot a m) = a - a mod (Z.abs m * Z.sgn a).
  Proof.
    intro Hm.
    assert (0 <> m * m) by (intro; apply Hm; nia).
    assert (0 < m * m) by nia.
    assert (0 <> Z.abs m) by (destruct m; simpl in *; try congruence).
    rewrite quot_div_full.
    rewrite <- (Z.abs_sgn m) at 1.
    transitivity ((Z.sgn m * Z.sgn m) * Z.sgn a * (Z.abs m * (Z.abs a / Z.abs m))); [ nia | ].
    rewrite <- Z.sgn_mul, Z.sgn_pos, Z.mul_1_l, Z.mul_div_eq_full by omega.
    rewrite Z.mul_sub_distr_l.
    rewrite Z.mul_comm, Z.abs_sgn.
    destruct a; simpl Z.sgn; simpl Z.abs; autorewrite with zsimplify_const; [ reflexivity | reflexivity | ].
    repeat match goal with |- context[-1 * ?x] => replace (-1 * x) with (-x) by omega end.
    repeat match goal with |- context[?x * -1] => replace (x * -1) with (-x) by omega end.
    rewrite <- Zmod_opp_opp; simpl Z.opp.
    reflexivity.
  Qed.

  Lemma quot_sub_sgn a : Z.quot (a - Z.sgn a) a = 0.
  Proof.
    rewrite quot_div_full.
    destruct (Z_zerop a); subst; [ lia | ].
    rewrite Z.div_small; lia.
  Qed.

  Lemma quot_small_abs a b : 0 <= Z.abs a < Z.abs b -> Z.quot a b = 0.
  Proof.
    intros; rewrite Z.quot_small_iff by lia; lia.
  Qed.

  Lemma quot_add_sub_sgn_small a b : b <> 0 -> Z.sgn a = Z.sgn b -> Z.quot (a + b - Z.sgn b) b = Z.quot (a - Z.sgn b) b + 1.
  Proof.
    destruct (Z_zerop a), (Z_zerop b), (Z_lt_le_dec a 0), (Z_lt_le_dec b 0), (Z_lt_le_dec 1 (Z.abs a));
      subst;
      try lia;
      rewrite !Z.quot_div_full;
      try rewrite (Z.sgn_neg a) by omega;
      try rewrite (Z.sgn_neg b) by omega;
      repeat first [ reflexivity
                   | rewrite Z.sgn_neg by lia
                   | rewrite Z.sgn_pos by lia
                   | rewrite Z.abs_eq by lia
                   | rewrite Z.abs_neq by lia
                   | rewrite !Z.mul_opp_l
                   | rewrite Z.abs_opp in *
                   | rewrite Z.abs_eq in * by omega
                   | match goal with
                     | [ |- context[-1 * ?x] ]
                       => replace (-1 * x) with (-x) by omega
                     | [ |- context[?x * -1] ]
                       => replace (x * -1) with (-x) by omega
                     | [ |- context[-?x - ?y] ]
                       => replace (-x - y) with (-(x + y)) by omega
                     | [ |- context[-?x + - ?y] ]
                       => replace (-x + - y) with (-(x + y)) by omega
                     | [ |- context[(?a + ?b + ?c) / ?b] ]
                       => replace (a + b + c) with (((a + c) + b * 1)) by lia; rewrite Z.div_add' by omega
                     | [ |- context[(?a + ?b - ?c) / ?b] ]
                       => replace (a + b - c) with (((a - c) + b * 1)) by lia; rewrite Z.div_add' by omega
                     end
                   | progress intros
                   | progress Z.replace_all_neg_with_pos
                   | progress autorewrite with zsimplify ].
  Qed.


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
   Map[{#1, #1 /. mul[a_, "X", b___] :> mul["X", a, b]} &, Flatten[{
      Table[
       Table[div[
         combine @@
          Join[Take[Chars, start - 1], RestFrom[start, len]],
         "X"], {len, 0, 10 - start}], {start, 1, 2}],
      Table[
       Table[div[
         combine["a",
          parens @@
           Join[Take[Drop[Chars, 1], start - 1],
            RestFrom[1 + start, len]]], "X"], {len, 0,
         10 - start}], {start, 1, 2}],
      div[combine["a", parens["b", parens["c", mul["d", "X"]], "e"]],
       "X"],
      div[combine["a", "b", parens["c", mul["d", "X"]], "e"], "X"],
      div[combine["a", "b", mul["c", "X", "d"], "e", "f"], "X"],
      div[combine["a", mul["b", "X", "c"], "d", "e"], "X"],
      div[
       combine["a",
        parens["b", parens["c", mul["d", "X", "e"]], "f"]], "X"],
      div[combine["a", parens["b", mul["c", "X", "d"]], "e"], "X"]}]]];
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
  Lemma simplify_div_pp_o_pX__c_dX a b X : X <> 0 -> (a + (b * X)) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp__c_dX a b X : X <> 0 -> (a + (X * b)) / X = b + a / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_p_c_dX a b c X : X <> 0 -> (a + (b * X + c)) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_p_c_dX a b c X : X <> 0 -> (a + (X * b + c)) / X = b + (a + c) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pp_c_dX a b c d X : X <> 0 -> (a + (b * X + c + d)) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pp_c_dX a b c d X : X <> 0 -> (a + (X * b + c + d)) / X = b + (a + c + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppp_c_dX a b c d e X : X <> 0 -> (a + (b * X + c + d + e)) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppp_c_dX a b c d e X : X <> 0 -> (a + (X * b + c + d + e)) / X = b + (a + c + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pppp_c_dX a b c d e f X : X <> 0 -> (a + (b * X + c + d + e + f)) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pppp_c_dX a b c d e f X : X <> 0 -> (a + (X * b + c + d + e + f)) / X = b + (a + c + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppppp_c_dX a b c d e f g X : X <> 0 -> (a + (b * X + c + d + e + f + g)) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppppp_c_dX a b c d e f g X : X <> 0 -> (a + (X * b + c + d + e + f + g)) / X = b + (a + c + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (b * X + c + d + e + f + g + h)) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (X * b + c + d + e + f + g + h)) / X = b + (a + c + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (b * X + c + d + e + f + g + h + i)) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (X * b + c + d + e + f + g + h + i)) / X = b + (a + c + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_pppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (b * X + c + d + e + f + g + h + i + j)) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_pppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (X * b + c + d + e + f + g + h + i + j)) / X = b + (a + c + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pX_ppppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (b * X + c + d + e + f + g + h + i + j + k)) / X = b + (a + c + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pX_ppppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_Xp_ppppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (X * b + c + d + e + f + g + h + i + j + k)) / X = b + (a + c + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_Xp_ppppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX__c_dX a b c X : X <> 0 -> (a + (b + c * X)) / X = c + (a + b) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp__c_dX a b c X : X <> 0 -> (a + (b + X * c)) / X = c + (a + b) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp__c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_p_c_dX a b c d X : X <> 0 -> (a + (b + c * X + d)) / X = c + (a + b + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_p_c_dX a b c d X : X <> 0 -> (a + (b + X * c + d)) / X = c + (a + b + d) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pp_c_dX a b c d e X : X <> 0 -> (a + (b + c * X + d + e)) / X = c + (a + b + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pp_c_dX a b c d e X : X <> 0 -> (a + (b + X * c + d + e)) / X = c + (a + b + d + e) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppp_c_dX a b c d e f X : X <> 0 -> (a + (b + c * X + d + e + f)) / X = c + (a + b + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppp_c_dX a b c d e f X : X <> 0 -> (a + (b + X * c + d + e + f)) / X = c + (a + b + d + e + f) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppp_c_dX a b c d e f g X : X <> 0 -> (a + (b + c * X + d + e + f + g)) / X = c + (a + b + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppp_c_dX a b c d e f g X : X <> 0 -> (a + (b + X * c + d + e + f + g)) / X = c + (a + b + d + e + f + g) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (b + c * X + d + e + f + g + h)) / X = c + (a + b + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppppp_c_dX a b c d e f g h X : X <> 0 -> (a + (b + X * c + d + e + f + g + h)) / X = c + (a + b + d + e + f + g + h) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (b + c * X + d + e + f + g + h + i)) / X = c + (a + b + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppppp_c_dX a b c d e f g h i X : X <> 0 -> (a + (b + X * c + d + e + f + g + h + i)) / X = c + (a + b + d + e + f + g + h + i) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_ppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (b + c * X + d + e + f + g + h + i + j)) / X = c + (a + b + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_ppppppp_c_dX a b c d e f g h i j X : X <> 0 -> (a + (b + X * c + d + e + f + g + h + i + j)) / X = c + (a + b + d + e + f + g + h + i + j) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_ppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pX_pppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (b + c * X + d + e + f + g + h + i + j + k)) / X = c + (a + b + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pX_pppppppp_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xp_pppppppp_c_dX a b c d e f g h i j k X : X <> 0 -> (a + (b + X * c + d + e + f + g + h + i + j + k)) / X = c + (a + b + d + e + f + g + h + i + j + k) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xp_pppppppp_c_dX using zutil_arith : zsimplify.
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
  Lemma simplify_div_pppp_pXp_ppdX a b c d e f X : X <> 0 -> (a + b + c * X * d + e + f) / X = (a + b + e + f + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pppp_pXp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pppp_Xpp_ppdX a b c d e f X : X <> 0 -> (a + b + X * c * d + e + f) / X = (a + b + e + f + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pppp_Xpp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_pXp_ppdX a b c d e X : X <> 0 -> (a + b * X * c + d + e) / X = (a + d + e + b*c*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_pXp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_ppp_Xpp_ppdX a b c d e X : X <> 0 -> (a + X * b * c + d + e) / X = (a + d + e + b*c*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_ppp_Xpp_ppdX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_pXp__c_p_c_dX a b c d e f X : X <> 0 -> (a + (b + (c + d * X * e) + f)) / X = (a + b + c + f + d*e*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_pXp__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_p_o_pp_Xpp__c_p_c_dX a b c d e f X : X <> 0 -> (a + (b + (c + X * d * e) + f)) / X = (a + b + c + f + d*e*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_p_o_pp_Xpp__c_p_c_dX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_pXp__c_pdX a b c d e X : X <> 0 -> (a + (b + c * X * d) + e) / X = (a + b + e + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_pXp__c_pdX using zutil_arith : zsimplify.
  Lemma simplify_div_pp_o_pp_Xpp__c_pdX a b c d e X : X <> 0 -> (a + (b + X * c * d) + e) / X = (a + b + e + c*d*X) / X.
  Proof. simplify_div_tac. Qed.
  Hint Rewrite simplify_div_pp_o_pp_Xpp__c_pdX using zutil_arith : zsimplify.


  (* Naming convention: [X] for thing being aggregated, [p] for plus,
     [m] for minus, [_] for parentheses *)
  (* Python code to generate these hints:
<<
#!/usr/bin/env python

def sgn(v):
    if v < 0:
        return -1
    elif v == 0:
        return 0
    elif v > 0:
        return 1

def to_eqn(name):
    vars_left = list('abcdefghijklmnopqrstuvwxyz')
    ret = ''
    close = ''
    while name:
        if name[0] == 'X':
            ret += ' X'
            name = name[1:]
        elif not name[0].isdigit():
            ret += ' ' + vars_left[0]
            vars_left = vars_left[1:]
        if name:
            if name[0] == 'm': ret += ' -'
            elif name[0] == 'p': ret += ' +'
            elif name[0].isdigit(): ret += ' %s *' % name[0]
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
        elif i == '+': sign_stack.append(sgn(sign_stack[-1]))
        elif i == '-': sign_stack.append(-sgn(sign_stack[-1]))
        elif i == '*': continue
        elif i.isdigit(): sign_stack[-1] *= int(i)
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
  Hint Rewrite simplify_%s : zsimplify.''' % (name, ' '.join(sorted(set(eqn) - set('*+-() 0123456789X'))), eqn, simplify(eqn), name)

names = []
names += ['%sX%s%sX' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['%sX%s_X%s' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['X%s%s_X%s' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['%sX%s_%sX' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['X%s%s_%sX' % (a, b, c) for a in 'mp' for b in 'mp' for c in 'mp']
names += ['m2XpX', 'm2XpXpX']

print(r'''  (* Python code to generate these hints:
<<''')
print(open(__file__).read())
print(r'''
>> *)''')
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
  Lemma simplify_mXm_Xm a b X : a - X - (X - b) = - 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_Xm : zsimplify.
  Lemma simplify_mXm_Xp a b X : a - X - (X + b) = - 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_Xp : zsimplify.
  Lemma simplify_mXp_Xm a b X : a - X + (X - b) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_Xm : zsimplify.
  Lemma simplify_mXp_Xp a b X : a - X + (X + b) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_Xp : zsimplify.
  Lemma simplify_pXm_Xm a b X : a + X - (X - b) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_Xm : zsimplify.
  Lemma simplify_pXm_Xp a b X : a + X - (X + b) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_Xp : zsimplify.
  Lemma simplify_pXp_Xm a b X : a + X + (X - b) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_Xm : zsimplify.
  Lemma simplify_pXp_Xp a b X : a + X + (X + b) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_Xp : zsimplify.
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
  Lemma simplify_mXm_mX a b X : a - X - (b - X) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_mX : zsimplify.
  Lemma simplify_mXm_pX a b X : a - X - (b + X) = - 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXm_pX : zsimplify.
  Lemma simplify_mXp_mX a b X : a - X + (b - X) = - 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_mX : zsimplify.
  Lemma simplify_mXp_pX a b X : a - X + (b + X) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_mXp_pX : zsimplify.
  Lemma simplify_pXm_mX a b X : a + X - (b - X) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_mX : zsimplify.
  Lemma simplify_pXm_pX a b X : a + X - (b + X) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXm_pX : zsimplify.
  Lemma simplify_pXp_mX a b X : a + X + (b - X) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_mX : zsimplify.
  Lemma simplify_pXp_pX a b X : a + X + (b + X) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_pXp_pX : zsimplify.
  Lemma simplify_Xmm_mX a b X : X - a - (b - X) = 2 * X - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_mX : zsimplify.
  Lemma simplify_Xmm_pX a b X : X - a - (b + X) = - a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmm_pX : zsimplify.
  Lemma simplify_Xmp_mX a b X : X - a + (b - X) = - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_mX : zsimplify.
  Lemma simplify_Xmp_pX a b X : X - a + (b + X) = 2 * X - a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xmp_pX : zsimplify.
  Lemma simplify_Xpm_mX a b X : X + a - (b - X) = 2 * X + a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_mX : zsimplify.
  Lemma simplify_Xpm_pX a b X : X + a - (b + X) = a - b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpm_pX : zsimplify.
  Lemma simplify_Xpp_mX a b X : X + a + (b - X) = a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_mX : zsimplify.
  Lemma simplify_Xpp_pX a b X : X + a + (b + X) = 2 * X + a + b.
  Proof. lia. Qed.
  Hint Rewrite simplify_Xpp_pX : zsimplify.
  Lemma simplify_m2XpX a X : a - 2 * X + X = - X + a.
  Proof. lia. Qed.
  Hint Rewrite simplify_m2XpX : zsimplify.
  Lemma simplify_m2XpXpX a X : a - 2 * X + X + X = a.
  Proof. lia. Qed.
  Hint Rewrite simplify_m2XpXpX : zsimplify.

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
    Proof using Type.
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

Module N2Z.
  Lemma inj_land n m : Z.of_N (N.land n m) = Z.land (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.
  Hint Rewrite inj_land : push_Zof_N.
  Hint Rewrite <- inj_land : pull_Zof_N.

  Lemma inj_lor n m : Z.of_N (N.lor n m) = Z.lor (Z.of_N n) (Z.of_N m).
  Proof. destruct n, m; reflexivity. Qed.
  Hint Rewrite inj_lor : push_Zof_N.
  Hint Rewrite <- inj_lor : pull_Zof_N.

  Lemma inj_shiftl: forall x y, Z.of_N (N.shiftl x y) = Z.shiftl (Z.of_N x) (Z.of_N y).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftl_spec; [|assumption].

    assert ((Z.to_N k) >= y \/ (Z.to_N k) < y)%N as g by (
        unfold N.ge, N.lt; induction (N.compare (Z.to_N k) y); [left|auto|left];
        intro H; inversion H).

    destruct g as [g|g];
    [ rewrite N.shiftl_spec_high; [|apply N2Z.inj_le; rewrite Z2N.id|apply N.ge_le]
    | rewrite N.shiftl_spec_low]; try assumption.

    - rewrite <- N2Z.inj_testbit; f_equal.
        rewrite N2Z.inj_sub, Z2N.id; [reflexivity|assumption|apply N.ge_le; assumption].

    - apply N2Z.inj_lt in g.
        rewrite Z2N.id in g; [symmetry|assumption].
        apply Z.testbit_neg_r; omega.
  Qed.
  Hint Rewrite inj_shiftl : push_Zof_N.
  Hint Rewrite <- inj_shiftl : pull_Zof_N.

  Lemma inj_shiftr: forall x y, Z.of_N (N.shiftr x y) = Z.shiftr (Z.of_N x) (Z.of_N y).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftr_spec, N.shiftr_spec; [|apply N2Z.inj_le; rewrite Z2N.id|]; try assumption.
    rewrite <- N2Z.inj_testbit; f_equal.
    rewrite N2Z.inj_add; f_equal.
    apply Z2N.id; assumption.
  Qed.
  Hint Rewrite inj_shiftr : push_Zof_N.
  Hint Rewrite <- inj_shiftr : pull_Zof_N.
End N2Z.

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

Ltac Ztestbit_full_step :=
  match goal with
  | _ => progress autorewrite with Ztestbit_full
  | [ |- context[Z.testbit ?x ?y] ]
    => rewrite (Z.testbit_neg_r x y) by zutil_arith
  | [ |- context[Z.testbit ?x ?y] ]
    => rewrite (Z.bits_above_pow2 x y) by zutil_arith
  | [ |- context[Z.testbit ?x ?y] ]
    => rewrite (Z.bits_above_log2 x y) by zutil_arith
  end.
Ltac Ztestbit_full := repeat Ztestbit_full_step.

Ltac Ztestbit_step :=
  match goal with
  | _ => progress autorewrite with Ztestbit
  | _ => progress Ztestbit_full_step
  end.
Ltac Ztestbit := repeat Ztestbit_step.

(** Change [_ mod _ = _ mod _] to [Z.equiv_modulo _ _ _] *)
Ltac Zmod_to_equiv_modulo :=
  repeat match goal with
         | [ H : context T[?x mod ?M = ?y mod ?M] |- _ ]
           => let T' := context T[Z.equiv_modulo M x y] in change T' in H
         | [ |- context T[?x mod ?M = ?y mod ?M] ]
           => let T' := context T[Z.equiv_modulo M x y] in change T'
         end.

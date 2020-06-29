Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.BaseConversion.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Arithmetic.MontgomeryReduction.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.Proofs.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.Zselect Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Module MontgomeryReduction.
  Local Coercion Z.of_nat : nat >-> Z.
  Section MontRed'.
    Context (N R N' R' : Z).
    Context (HN_range : 0 <= N < R) (HN'_range : 0 <= N' < R) (HN_nz : N <> 0) (R_gt_1 : R > 1)
            (N'_good : Z.equiv_modulo R (N*N') (-1)) (R'_good: Z.equiv_modulo N (R*R') 1).

    Context (Zlog2R : Z) .
    Let w : nat -> Z := uweight Zlog2R.
    Context (n:nat) (Hn_nz: n <> 0%nat) (n_good : Zlog2R mod Z.of_nat n = 0).
    Context (R_big_enough : 2 <= Zlog2R)
            (R_two_pow : 2^Zlog2R = R).
    Let w_mul : nat -> Z := uweight (Zlog2R / n).

    Definition montred' (lo hi : Z) :=
      dlet_nd y := nth_default 0 (BaseConversion.widemul_inlined Zlog2R 1 2 [lo] [N']) 0  in
      dlet_nd t1_t2 := (BaseConversion.widemul_inlined_reverse Zlog2R 1 2 [N] [y]) in
      dlet_nd sum_carry := Rows.add w 2 [lo;hi] t1_t2 in
      dlet_nd y' := Z.zselect (snd sum_carry) 0 N in
      dlet_nd lo''_carry := Z.sub_get_borrow_full R (nth_default 0 (fst sum_carry) 1) y' in
      Z.add_modulo (fst lo''_carry) 0 N.

    Local Lemma Hw : forall i, w i = R ^ Z.of_nat i.
    Proof.
      clear -R_big_enough R_two_pow; cbv [w uweight weight]; intro.
      autorewrite with zsimplify.
      rewrite Z.pow_mul_r, R_two_pow by lia; reflexivity.
    Qed.

    Declare Equivalent Keys weight w.
    Local Ltac change_weight := rewrite !Hw, ?Z.pow_0_r, ?Z.pow_1_r, ?Z.pow_2_r, ?Z.pow_1_l in *.
    Local Ltac solve_range :=
      repeat match goal with
             | _ => progress change_weight
             | |- context [?a mod ?b] => unique pose proof (Z.mod_pos_bound a b ltac:(lia))
             | |- 0 <= _ => progress Z.zero_bounds
             | |- 0 <= _ * _ < _ * _ =>
               split; [ solve [Z.zero_bounds] | apply Z.mul_lt_mono_nonneg; lia ]
             | _ => solve [auto]
             | _ => lia
             end.

    Local Lemma eval2 x y : Positional.eval w 2 [x;y] = x + R * y.
    Proof. cbn. change_weight. ring. Qed.
    Local Lemma eval1 x : Positional.eval w 1 [x] = x.
    Proof. cbn. change_weight. ring. Qed.

    Hint Rewrite BaseConversion.widemul_inlined_reverse_correct BaseConversion.widemul_inlined_correct
         using (autorewrite with widemul push_nth_default; solve [solve_range]) : widemul.

    (* TODO: move *)
    Hint Rewrite Nat.mul_1_l : natsimplify.

    Lemma montred'_eq lo hi T (HT_range: 0 <= T < R * N)
          (Hlo: lo = T mod R) (Hhi: hi = T / R):
      montred' lo hi = reduce_via_partial N R N' T.
    Proof.
      rewrite <-reduce_via_partial_alt_eq by nia.
      cbv [montred' partial_reduce_alt reduce_via_partial_alt prereduce Let_In].
      rewrite Hlo, Hhi.
      assert (0 <= (T mod R) * N' < w 2) by  (solve_range).
      autorewrite with widemul.
      rewrite Rows.add_partitions, Rows.add_div by (distr_length; apply wprops; lia).
      (* rewrite R_two_pow. *)
      cbv [Partition.partition seq].
      repeat match goal with
               | _ => progress rewrite ?eval1, ?eval2
               | _ => progress rewrite ?Z.zselect_correct, ?Z.add_modulo_correct
               | _ => progress autorewrite with natsimplify push_nth_default push_map to_div_mod
             end.
      change_weight.

      (* pull out value before last modular reduction *)
      match goal with |- (if (?n <=? ?x)%Z then ?x - ?n else ?x) = (if (?n <=? ?y) then ?y - ?n else ?y)%Z =>
                      let P := fresh "H" in assert (x = y) as P; [|rewrite P; reflexivity] end.

      autorewrite with zsimplify.
      Z.rewrite_mod_small.
      autorewrite with zsimplify.
      rewrite (Z.mul_comm (((T mod R) * N') mod R) N) in *.
      match goal with
        |- context [(?x - (if dec (?a / ?b = 0) then 0 else ?y)) mod ?m
                    = if (?b <=? ?a) then (?x - ?y) mod ?m else ?x ] =>
        assert (a / b = 0 <-> a < b) by
            (rewrite Z.div_between_0_if by (Z.div_mod_to_quot_rem; nia);
             break_match; Z.ltb_to_lt; lia)
      end.
      break_match; Z.ltb_to_lt; try reflexivity; try lia; [ ].
      autorewrite with zsimplify_fast. Z.rewrite_mod_small. reflexivity.
    Qed.

    Lemma montred'_correct lo hi T (HT_range: 0 <= T < R * N)
          (Hlo: lo = T mod R) (Hhi: hi = T / R): montred' lo hi = (T * R') mod N.
    Proof.
      erewrite montred'_eq by eauto.
      apply Z.equiv_modulo_mod_small; auto using reduce_via_partial_correct.
      replace 0 with (Z.min 0 (R-N)) by (apply Z.min_l; lia).
      apply reduce_via_partial_in_range; lia.
    Qed.
  End MontRed'.
End MontgomeryReduction.

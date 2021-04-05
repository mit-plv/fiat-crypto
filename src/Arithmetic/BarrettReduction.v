Require Import Coq.ZArith.ZArith Coq.micromega.Lia Crypto.Algebra.Nsatz.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.BaseConversion.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Arithmetic.BarrettReduction.Generalized.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddModulo.
Require Import Crypto.Util.ZUtil.CC Crypto.Util.ZUtil.Rshi.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Section Generic.
  Context (b k M mu width : Z) (n : nat)
          (b_ok : 1 < b)
          (k_pos : 0 < k)
          (bk_eq : b^k = 2^(width * Z.of_nat n))
          (M_range : b ^ (k - 1) < M < b ^ k)
          (mu_eq : mu = b ^ (2 * k) / M)
          (width_pos : 0 < width)
          (strong_bound : b ^ 1 * (b ^ (2 * k) mod M) <= b ^ (k + 1) - mu).
  Local Notation weight := (uweight width).
  Local Notation partition := (Partition.partition weight).
  Context (q1 : list Z -> list Z)
          (q1_correct :
             forall x,
               0 <= x < b ^ (2 * k) ->
               q1 (partition (n*2)%nat x) = partition (n+1)%nat (x / b ^ (k - 1)))
          (q3 : list Z -> list Z -> list Z)
          (q3_correct :
             forall x q1,
               0 <= x < b ^ (2 * k) ->
               q1 = x / b ^ (k - 1) ->
               q3 (partition (n*2) x) (partition (n+1) q1) = partition (n+1) ((mu * q1) / b ^ (k + 1)))
          (r : list Z -> list Z -> list Z)
          (r_correct :
             forall x q3,
               0 <= x < M * b ^ k ->
               0 <= q3 ->
               (exists b : bool, q3 = x / M + (if b then -1 else 0)) ->
               r (partition (n*2) x) (partition (n+1) q3) = partition n (x mod M)).

  Context (x : Z) (x_range : 0 <= x < M * b ^ k)
          (xt : list Z) (xt_correct : xt = partition (n*2) x).

  Local Lemma M_pos : 0 < M.
  Proof. assert (0 <= b ^ (k - 1)) by Z.zero_bounds. lia. Qed.
  Local Lemma M_upper : M < weight n.
  Proof. rewrite uweight_eq_alt'. lia. Qed.
  Local Lemma x_upper : x < b ^ (2 * k).
  Proof.
    assert (0 < b ^ k) by Z.zero_bounds.
    apply Z.lt_le_trans with (m:= M * b^k); [ lia | ].
    transitivity (b^k * b^k); [ nia | ].
    rewrite <-Z.pow_2_r, <-Z.pow_mul_r by lia.
    rewrite (Z.mul_comm k 2); reflexivity.
  Qed.
  Local Lemma xmod_lt_M : x mod b ^ (k - 1) <= M.
  Proof. pose proof (Z.mod_pos_bound x (b ^ (k - 1)) ltac:(Z.zero_bounds)). lia. Qed.
  Local Hint Resolve M_pos x_upper xmod_lt_M : core.

  Definition reduce :=
    dlet_nd q1t := q1 xt in
    dlet_nd q3t := q3 xt q1t in
    r xt q3t.

  Lemma q1_range : 0 <= x / b^(k-1) < b^(k+1).
  Proof.
    split; [ solve [Z.zero_bounds] | ].
    assert (0 < b ^ (k - 1)) by Z.zero_bounds.
    assert (0 < b ^ k) by Z.zero_bounds.
    apply Z.div_lt_upper_bound; [ solve [Z.zero_bounds] | ].
    eapply Z.lt_le_trans with (m:=b^k * b^k);
      [ nia | autorewrite with pull_Zpow; apply Z.pow_le_mono; lia ].
  Qed.

  Lemma q3_range : 0 <= mu * (x / b ^ (k - 1)) / b ^ (k + 1).
  Proof.
    assert (0 < b ^ (k - 1)) by Z.zero_bounds.
    subst mu; Z.zero_bounds.
  Qed.

  Lemma reduce_correct : reduce = partition n (x mod M).
  Proof.
    cbv [reduce Let_In]. pose proof q3_range.
    rewrite xt_correct, q1_correct, q3_correct by auto with lia.
    assert (exists cond : bool, ((mu * (x / b^(k-1))) / b^(k+1)) = x / M + (if cond then -1 else 0)) as Hq3.
    { destruct q_nice_strong with (b:=b) (k:=k) (m:=mu) (offset:=1) (a:=x) (n:=M) as [cond Hcond];
        eauto using Z.lt_gt with zarith. }
    eauto using r_correct with lia.
  Qed.
End Generic.

(* Non-standard implementation -- uses specialized instructions and b=2 *)
Module Fancy.
  Section Fancy.
    Context (M mu width k : Z)
            (sz : nat) (sz_nz : sz <> 0%nat)
            (width_ok : 1 < width)
            (k_pos : 0 < k) (* this can be inferred from other arguments but is easier to put here for tactics *)
            (k_eq : k = width * Z.of_nat sz).
    (* sz = 1, width = k = 256 *)
    Local Notation w := (uweight width). Local Notation eval := (Positional.eval w).
    Context (mut Mt : list Z) (mut_correct : mut = Partition.partition w (sz+1) mu) (Mt_correct : Mt = Partition.partition w sz M).
    Context (mu_eq : mu = 2 ^ (2 * k) / M) (muHigh_one : mu / w sz = 1) (M_range : 2^(k-1) < M < 2^k).
    Local Lemma wprops : @weight_properties w. Proof using width_ok. clear - width_ok. apply uwprops ; lia. Qed.
    Local Hint Resolve wprops : core.
    Hint Rewrite mut_correct Mt_correct : pull_partition.

    Lemma w_eq_2k : w sz = 2^k. Proof. rewrite uweight_eq_alt' by auto. congruence. Qed.
    Lemma mu_range : 2^k <= mu < 2^(k+1).
    Proof.
      rewrite mu_eq. assert (0 < 2^(k-1)) by Z.zero_bounds.
      assert (2^k < M * 2).
      { replace (2^k) with (2^(k-1+1)) by (f_equal; lia).
        rewrite Z.pow_add_r, Z.pow_1_r by lia.
        lia. }
      replace (2 ^ (2 * k)) with (2^(k+k)) by (f_equal; lia).
      rewrite !Z.pow_add_r, Z.pow_1_r by lia. split.
      { apply Z.div_le_lower_bound; nia. }
      { apply Z.div_lt_upper_bound; nia. }
    Qed.
    Lemma mu_range' : 0 <= mu < 2 * w sz.
    Proof.
      pose proof mu_range. assert (0 < 2^k) by auto with zarith.
      assert (2^(k+1) = 2 * w sz); [ | lia].
      rewrite k_eq, uweight_eq_alt'.
      rewrite Z.pow_add_r, Z.pow_1_r by lia. lia.
    Qed.
    Lemma M_range' : 0 <= M < w sz. (* more convenient form, especially for mod_small *)
    Proof. assert (0 <= 2 ^ (k-1)) by Z.zero_bounds. pose proof w_eq_2k; lia. Qed.

    Definition shiftr' (m : nat) (t : list Z) (n : Z) : list Z :=
      map (fun i => Z.rshi (2^width) (nth_default 0 t (S i)) (nth_default 0 t i) n) (seq 0 m).

    Definition shiftr (m : nat) (t : list Z) (n : Z) : list Z :=
      (* if width <= n, drop limbs first *)
      if dec (width <= n)
      then shiftr' m (skipn (Z.to_nat (n / width)) t) (n mod width)
      else shiftr' m t n.

    Definition wideadd t1 t2 := fst (Rows.add w (sz*2) t1 t2).
    Definition widesub t1 t2 := fst (Rows.sub w (sz*2) t1 t2).
    Definition widemul := BaseConversion.widemul_inlined width sz 2.
    (* widemul_inlined takes the following argument order : (width of limbs in input) (# limbs in input) (# parts to split each limb into before multiplying) *)

    Definition fill (n : nat) (a : list Z) := a ++ Positional.zeros (n - length a).
    Definition low : list Z -> list Z := firstn sz.
    Definition high : list Z -> list Z := skipn sz.
    Definition mul_high (a b : list Z) a0b1 : list Z :=
      dlet_nd a0b0 := widemul (low a) (low b) in
      dlet_nd ab := wideadd (high a0b0 ++ high b) (fill (sz*2) (low b)) in
      wideadd ab a0b1.

    (* select based on the most significant bit of xHigh *)
    Definition muSelect xt :=
      let xHigh := nth_default 0 xt (sz*2 - 1) in
      Positional.select (Z.cc_m (2 ^ width) xHigh) (Positional.zeros sz) (low mut).

    Definition cond_sub (a y : list Z) : list Z :=
      let cond := Z.cc_l (nth_default 0 (high a) 0) in (* a[k] = least significant bit of (high a) *)
      dlet_nd maybe_y := Positional.select cond (Positional.zeros sz) y in
      dlet_nd diff := Rows.sub w sz (low a) maybe_y in (* (a mod (w sz) - y) mod (w sz)) = (a - y) mod (w sz); since we know a - y is < w sz this is okay by mod_small *)
      fst diff.

    Definition cond_subM x :=
      if Nat.eq_dec sz 1
      then [Z.add_modulo (nth_default 0 x 0) 0 M] (* use the special instruction if we can *)
      else Rows.conditional_sub w sz x Mt.

    Definition q1 (xt : list Z) := shiftr (sz+1) xt (k - 1).

    Definition q3 (xt q1t : list Z) :=
      dlet_nd muSelect := muSelect xt in (* make sure muSelect is not inlined in the output *)
      dlet_nd twoq := mul_high (fill (sz*2) mut) (fill (sz*2) q1t) (fill (sz*2) muSelect) in
      shiftr (sz+1) twoq 1.

    Definition r (xt q3t : list Z) :=
      dlet_nd r2 := widemul (low q3t) Mt in
      dlet_nd rt := widesub xt r2 in
      dlet_nd rt := cond_sub rt Mt in
      cond_subM rt.

    Section Proofs.
      Lemma shiftr'_correct m n :
        forall t tn,
          (m <= tn)%nat -> 0 <= t < w tn -> 0 <= n < width ->
          shiftr' m (Partition.partition w tn t) n = Partition.partition w m (t / 2 ^ n).
      Proof using width_ok.
        clear -width_ok.
        cbv [shiftr']. induction m; intros; [ reflexivity | ].
        rewrite !partition_step, seq_snoc.
        autorewrite with distr_length natsimplify push_map push_nth_default.
        rewrite IHm, Z.rshi_correct, !uweight_S by auto with zarith.
        rewrite <-!Z.mod_pull_div by auto with zarith.
        destruct (Nat.eq_dec (S m) tn); [subst tn | ].
        { rewrite uweight_S in * by auto with zarith.
          break_innermost_match; try lia.
          autorewrite with zsimplify_fast. Z.rewrite_mod_small.
          rewrite Z.div_div_comm by auto with zarith; reflexivity. }
        { break_innermost_match; try lia.
          rewrite <-!uweight_S by auto with zarith.
          repeat match goal with
                 | _ => rewrite uweight_pull_mod by auto with zarith
                 | _ => rewrite Z.mod_mod_small by auto with zarith
                 | _ => rewrite <-Znumtheory.Zmod_div_mod by (Z.zero_bounds; auto with zarith)
                 | _ => rewrite uweight_eq_alt with (n:=1%nat) by auto with zarith
                 | |- context [(t / w (S m)) mod 2^width * 2^width] =>
                   replace (t / w (S m)) with (t / w m / 2^width) by
                       (rewrite uweight_S, Z.div_div by auto with zarith; f_equal; lia);
                     rewrite Z.mod_pull_div with (b:=2^width) by auto with zarith;
                     rewrite Z.mul_div_eq' by auto with zarith
                 | _ => progress autorewrite with natsimplify zsimplify_fast zsimplify
                 end.
          replace (2^width*2^width) with (2^width*2^(width-n)*2^n) by (autorewrite with pull_Zpow; f_equal; lia).
          rewrite <-Z.mod_pull_div, <-Znumtheory.Zmod_div_mod by (Z.zero_bounds; auto with zarith).
          rewrite Z.div_div_comm by Z.zero_bounds. reflexivity. }
      Qed.
      Lemma shiftr_correct m n :
        forall t tn,
          (Z.to_nat (n / width) <= tn)%nat ->
          (m <= tn - Z.to_nat (n / width))%nat -> 0 <= t < w tn -> 0 <= n ->
          shiftr m (Partition.partition w tn t) n = Partition.partition w m (t / 2 ^ n).
      Proof.
        cbv [shiftr]; intros.
        break_innermost_match; [ | solve [auto using shiftr'_correct with zarith] ].
        pose proof (Z.mod_pos_bound n width ltac:(lia)).
        assert (t / 2 ^ (n - n mod width) < w (tn - Z.to_nat (n / width))).
        { apply Z.div_lt_upper_bound; [solve [Z.zero_bounds] | ].
          rewrite uweight_eq_alt' in *.
          rewrite <-Z.pow_add_r, Nat2Z.inj_sub, Z2Nat.id, <-Z.mul_div_eq by auto with zarith.
          autorewrite with push_Zmul zsimplify. auto with zarith. }
        repeat match goal with
               | _ => progress rewrite ?uweight_skipn_partition, ?uweight_eq_alt' by auto with lia
               | _ => rewrite Z2Nat.id by Z.zero_bounds
               | _ => rewrite Z.mul_div_eq_full by auto with zarith
               | _ => rewrite shiftr'_correct by auto with zarith
               | _ => progress rewrite ?Z.div_div, <-?Z.pow_add_r by auto with zarith
               end.
        autorewrite with zsimplify. reflexivity.
      Qed.
      Hint Rewrite shiftr_correct using (solve [auto with lia]) : pull_partition.

      (* 2 ^ (k + 1) bits fit in sz + 1 limbs because we know 2^k bits fit in sz and 1 <= width *)
      Lemma q1_correct x :
        0 <= x < w (sz * 2) ->
        q1 (Partition.partition w (sz*2)%nat x) = Partition.partition w (sz+1)%nat (x / 2 ^ (k - 1)).
      Proof.
        cbv [q1]; intros. assert (1 <= Z.of_nat sz) by (destruct sz; lia).
        assert (Z.to_nat ((k-1) / width) < sz)%nat. {
          subst k. rewrite <-Z.add_opp_r. autorewrite with zsimplify.
          apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
        assert (0 <= k - 1) by nia.
        autorewrite with pull_partition. reflexivity.
      Qed.

      Lemma low_correct n a : (sz <= n)%nat -> low (Partition.partition w n a) = Partition.partition w sz a.
      Proof. cbv [low]; auto using uweight_firstn_partition with lia. Qed.
      Lemma high_correct a : high (Partition.partition w (sz*2) a) = Partition.partition w sz (a / w sz).
      Proof. cbv [high]. rewrite uweight_skipn_partition by lia. f_equal; lia. Qed.
      Lemma fill_correct n m a :
        (n <= m)%nat ->
        fill m (Partition.partition w n a) = Partition.partition w m (a mod w n).
      Proof.
        cbv [fill]; intros. distr_length.
        rewrite <-partition_0 with (weight:=w).
        rewrite uweight_partition_app by lia.
        f_equal; lia.
      Qed.
      Hint Rewrite low_correct high_correct fill_correct using lia : pull_partition.

      Lemma wideadd_correct a b :
        wideadd (Partition.partition w (sz*2) a) (Partition.partition w (sz*2) b) = Partition.partition w (sz*2) (a + b).
      Proof.
        cbv [wideadd]. rewrite Rows.add_partitions by (distr_length; auto).
        autorewrite with push_eval.
        apply partition_eq_mod; auto with zarith.
      Qed.
      Lemma widesub_correct a b :
        widesub (Partition.partition w (sz*2) a) (Partition.partition w (sz*2) b) = Partition.partition w (sz*2) (a - b).
      Proof.
        cbv [widesub]. rewrite Rows.sub_partitions by (distr_length; auto).
        autorewrite with push_eval.
        apply partition_eq_mod; auto with zarith.
      Qed.
      Lemma widemul_correct a b :
        widemul (Partition.partition w sz a) (Partition.partition w sz b) = Partition.partition w (sz*2) ((a mod w sz) * (b mod w sz)).
      Proof.
        cbv [widemul]. rewrite BaseConversion.widemul_inlined_correct; (distr_length; auto).
        autorewrite with push_eval. reflexivity.
      Qed.
      Hint Rewrite widemul_correct widesub_correct wideadd_correct using lia : pull_partition.

      Lemma mul_high_idea d a b a0 a1 b0 b1 :
        d <> 0 ->
        a = d * a1 + a0 ->
        b = d * b1 + b0 ->
        (a * b) / d = a0 * b0 / d + d * a1 * b1 + a1 * b0 + a0 * b1.
      Proof.
        intros. subst a b. autorewrite with push_Zmul.
        ring_simplify_subterms. rewrite Z.pow_2_r.
        rewrite Z.div_add_exact by (push_Zmod; autorewrite with zsimplify; lia).
        repeat match goal with
               | |- context [d * ?a * ?b * ?c] =>
                 replace (d * a * b * c) with (a * b * c * d) by ring
               | |- context [d * ?a * ?b] =>
                 replace (d * a * b) with (a * b * d) by ring
               end.
        rewrite !Z.div_add by lia.
        autorewrite with zsimplify.
        rewrite (Z.mul_comm a0 b0).
        ring_simplify. ring.
      Qed.

      Lemma mul_high_correct a b
            (Ha : a / w sz = 1)
            a0b1 (Ha0b1 : a0b1 = a mod w sz * (b / w sz)) :
        mul_high (Partition.partition w (sz*2) a) (Partition.partition w (sz*2) b) (Partition.partition w (sz*2) a0b1) =
        Partition.partition w (sz*2) (a * b / w sz).
      Proof.
        cbv [mul_high Let_In].
        erewrite mul_high_idea by auto using Z.div_mod with zarith.
        repeat match goal with
               | _ => progress autorewrite with pull_partition
               | _ => progress rewrite ?Ha, ?Ha0b1
               | _ => rewrite uweight_partition_app by lia;
                        replace (sz+sz)%nat with (sz*2)%nat by lia
               | _ => rewrite Z.mod_pull_div by auto with zarith
               | _ => progress Z.rewrite_mod_small
               | _ => f_equal; ring
               end.
      Qed.

      Hint Rewrite uweight_S uweight_eq_alt' using lia : weight_to_pow.
      Hint Rewrite <-uweight_S uweight_eq_alt' using lia : pow_to_weight.

      Lemma q1_range x :
        0 <= x < w (sz * 2) ->
        0 <= x / 2 ^ (k-1) < 2 * w sz.
      Proof.
        intros; split; [ solve [Z.zero_bounds] | ].
        apply Z.div_lt_upper_bound; [ solve [Z.zero_bounds] | ].
        assert (w (sz * 2) <= 2 ^ (k-1) * (2 * w sz)); [ | lia ].
        autorewrite with weight_to_pow pull_Zpow.
        apply Z.pow_le_mono_r; lia.
      Qed.

      Lemma muSelect_correct x :
        0 <= x < w (sz * 2) ->
        muSelect (Partition.partition w (sz*2) x) = Partition.partition w sz (mu mod (w sz) * (x / 2 ^ (k - 1) / (w sz))).
      Proof.
        cbv [muSelect]; intros;
          repeat match goal with
                 | _ => progress autorewrite with pull_partition natsimplify
                 | _ => progress rewrite ?Z.cc_m_eq by auto with zarith
                 | _ => erewrite Positional.select_eq by (distr_length; eauto)
                 | _ => rewrite nth_default_partition by lia
                 | _ => progress replace (S (sz * 2 - 1)) with (sz * 2)%nat by lia
                 | H : 0 <= ?x < ?m |- context [?x mod ?m] => rewrite (Z.mod_small x m) by auto with zarith
                 end.
        replace (x / (w (sz * 2 - 1)) / (2 ^ width / 2)) with (x / (2 ^ (k - 1)) / w sz) by
            (autorewrite with weight_to_pow pull_Zpow;
             rewrite !Z.div_div, <-!Z.pow_add_r by (Core.zutil_arith || Z.zero_bounds); do 2 f_equal; nia).
        rewrite Z.div_between_0_if with (a:=x / 2^(k-1)) by (Z.zero_bounds; auto using q1_range).
        break_innermost_match; try lia; autorewrite with zsimplify_fast; [ | ].
        { apply partition_eq_mod; auto with zarith. }
        { rewrite partition_0; reflexivity. }
      Qed.
      Hint Rewrite muSelect_correct using lia : pull_partition.

      Lemma mu_q1_range x (Hx : 0 <= x < w (sz * 2)) : mu * (x / 2^(k-1)) < w sz * w (sz * 2).
      Proof.
        pose proof mu_range'. pose proof q1_range x ltac:(lia).
        replace (w (sz * 2)) with (w sz * w sz) by
            (autorewrite with weight_to_pow pull_Zpow; f_equal; lia).
        apply Z.lt_le_trans with (m:= 2 * w sz * (2 * w sz)); [ nia | ].
        assert (4 <= w sz); [ | nia ]. change 4 with (Z.pow 2 2).
        autorewrite with weight_to_pow. apply Z.pow_le_mono_r; nia.
      Qed.

      Lemma q3_correct x (Hx : 0 <= x < w (sz * 2)) q1 (Hq1 : q1 = x / 2 ^ (k - 1)) :
        q3 (Partition.partition w (sz*2) x) (Partition.partition w (sz+1) q1) = Partition.partition w (sz+1) ((mu*q1) / 2 ^ (k + 1)).
      Proof.
        cbv [q3 Let_In]. intros. pose proof mu_q1_range x ltac:(lia).
        pose proof mu_range'. pose proof q1_range x ltac:(lia).
        autorewrite with pull_partition pull_Zmod.
        assert (2 * w sz < w (sz + 1)) by (autorewrite with weight_to_pow pull_Zpow; auto with zarith lia).
        Z.rewrite_mod_small. rewrite <-Hq1 in *.
        rewrite mul_high_correct by
            (try lia; rewrite Z.div_between_0_if with (a:=q1) by lia;
             break_innermost_match; autorewrite with zsimplify; reflexivity).
        rewrite shiftr_correct by (rewrite ?Z.div_small, ?Z2Nat.inj_0 by lia; auto with zarith lia).
        autorewrite with weight_to_pow pull_Zpow pull_Zdiv.
        rewrite ?Z.div_div, <-?Z.pow_add_r by (Core.zutil_arith || Z.zero_bounds).
        congruence.
      Qed.

      Lemma cond_sub_correct a b :
        cond_sub (Partition.partition w (sz*2) a) (Partition.partition w sz b)
        = Partition.partition w sz (if dec ((a / w sz) mod 2 = 0)
                          then a
                          else a - b).
      Proof.
        intros; cbv [cond_sub Let_In Z.cc_l]. autorewrite with pull_partition.
        rewrite nth_default_partition by lia.
        rewrite weight_0 by auto. autorewrite with zsimplify_fast.
        rewrite uweight_eq_alt' with (n:=1%nat). autorewrite with push_Zof_nat zsimplify.
        rewrite <-Znumtheory.Zmod_div_mod by auto using Zpow_facts.Zpower_divide with zarith.
        rewrite Positional.select_eq with (n:=sz) by (distr_length; apply w).
        rewrite Rows.sub_partitions by (break_innermost_match; distr_length; auto).
        break_innermost_match; autorewrite with push_eval zsimplify_fast;
          apply partition_eq_mod; auto with zarith.
      Qed.
      Hint Rewrite cond_sub_correct : pull_partition.
      Lemma cond_subM_correct a :
        cond_subM (Partition.partition w sz a)
        = Partition.partition w sz (if dec (a mod w sz < M)
                          then a
                          else a - M).
      Proof.
        cbv [cond_subM]. autorewrite with pull_partition. pose proof M_range'.
        rewrite Rows.conditional_sub_partitions by
            (distr_length; auto; autorewrite with push_eval; try apply partition_eq_mod; auto with zarith).
        rewrite nth_default_partition, weight_0, Z.add_modulo_correct by auto with lia.
        autorewrite with zsimplify_fast push_eval. Z.rewrite_mod_small.
        pose proof Z.mod_pos_bound a (w 1) ltac:(auto).
        break_innermost_match; Z.ltb_to_lt;
          repeat match goal with
                 | _ => lia
                 | _ => reflexivity
                 | _ => apply partition_eq_mod; solve [auto with zarith]
                 | _ => rewrite partition_step, weight_0 by auto
                 | _ => progress autorewrite with zsimplify_fast
                 | _ => progress Z.rewrite_mod_small
                 | _ => rewrite Z.sub_mod_l with (a:=a)
                 end.
      Qed.
      Hint Rewrite cond_subM_correct : pull_partition.

      Lemma w_eq_22k : w (sz * 2) = 2 ^ (2 * k).
      Proof.
        replace (sz * 2)%nat with (sz + sz)%nat by lia.
        rewrite uweight_sum_indices, w_eq_2k, <-Z.pow_add_r by lia.
        f_equal; lia.
      Qed.

      Lemma r_idea x q3 (b:bool) :
        0 <= x < M * 2 ^ k ->
        0 <= q3 ->
        q3 = x / M + (if b then -1 else 0) ->
        x - q3 mod w sz * M = x mod M + (if b then M else 0).
      Proof.
        intros. assert (0 < 2^(k-1)) by Z.zero_bounds.
        assert (q3 < w sz).
        { apply Z.le_lt_trans with (m:=x/M); [ subst q3; break_innermost_match; lia | ].
          autorewrite with weight_to_pow. rewrite <-k_eq. auto with zarith. }
        Z.rewrite_mod_small.
        repeat match goal with
               | _ => progress autorewrite with push_Zmul
               | H : q3 = ?e |- _ => progress replace (q3 * M) with (e * M)  by (rewrite H; reflexivity)
               | _ => rewrite (Z.mul_div_eq' x M) by lia
               end.
        break_innermost_match; Z.ltb_to_lt; lia.
      Qed.

      Lemma r_correct x q3 :
        0 <= x < M * 2 ^ k ->
        0 <= q3 ->
        (exists b : bool, q3 = x / M + (if b then -1 else 0)) ->
        r (Partition.partition w (sz*2) x) (Partition.partition w (sz+1) q3) = Partition.partition w sz (x mod M).
      Proof.
        intros; cbv [r Let_In]. pose proof M_range'. assert (0 < 2^(k-1)) by Z.zero_bounds.
        autorewrite with pull_partition. Z.rewrite_mod_small.
        match goal with H : exists _, q3 = _ |- _ => destruct H end.
        erewrite r_idea by eassumption.
        pose proof (Z.mod_pos_bound x M ltac:(lia)).
        rewrite Z.div_between_0_if with (b:=w sz) by (break_innermost_match; auto with zarith).
        rewrite Z.mod_small with (b:=2) by (break_innermost_match; lia).
        break_innermost_match; Z.ltb_to_lt; try lia; autorewrite with zsimplify_fast;
          repeat match goal with
                 | |- exists e, _ /\ _ /\ ?f ?x = ?f e => exists x; split; [ | split ]
                 | _ => rewrite Z.mod_small in * by lia
                 | _ => progress Z.rewrite_mod_small
                 | _ => progress (push_Zmod; pull_Zmod); autorewrite with zsimplify_fast
                 | _ => lia
                 | _ => reflexivity
                 end.
      Qed.
    End Proofs.

    Section Def.
      Context (sz_eq_1 : sz = 1%nat). (* this is needed to get rid of branches in the templates; a different definition would be needed for sizes other than 1, but would be able to use the same proofs. *)
      Local Hint Resolve q1_correct q3_correct r_correct : core.

      (* muselect relies on an initially-set flag, so pull it out of q3 *)
      Definition fancy_reduce_muSelect_first xt :=
        dlet_nd muSelect := muSelect xt in
        dlet_nd q1t := q1 xt in
        dlet_nd twoq := mul_high (fill (sz * 2) mut) (fill (sz * 2) q1t) (fill (sz * 2) muSelect) in
        dlet_nd q3t := shiftr (sz+1) twoq 1 in
        r xt q3t.

      Lemma fancy_reduce_muSelect_first_correct x :
        0 <= x < M * 2^k ->
        2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - mu ->
        fancy_reduce_muSelect_first (Partition.partition w (sz*2) x) = Partition.partition w sz (x mod M).
      Proof.
        intros. pose proof w_eq_22k.
        erewrite <-reduce_correct with (b:=2) (k:=k) (mu:=mu) by
            (eauto with nia; intros; try rewrite q3'_correct; try rewrite <-k_eq; eauto with nia ).
        reflexivity.
      Qed.

      Derive fancy_reduce'
             SuchThat (
               forall x,
                 0 <= x < M * 2^k ->
                 2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - mu ->
                 fancy_reduce' (Partition.partition w (sz*2) x) = Partition.partition w sz (x mod M))
             As fancy_reduce'_correct.
      Proof.
        intros. assert (k = width) as width_eq_k by nia.
        erewrite <-fancy_reduce_muSelect_first_correct by nia.
        cbv [fancy_reduce_muSelect_first q1 q3 shiftr r cond_subM].
        break_match; try solve [exfalso; lia].
        match goal with |- ?g ?x = ?rhs =>
                        let f := (match (eval pattern x in rhs) with ?f _ => f end) in
                        assert (f = g); subst fancy_reduce'; reflexivity
        end.
      Qed.

      Definition fancy_reduce xLow xHigh := hd 0 (fancy_reduce' [xLow;xHigh]).

      Lemma partition_2 xLow xHigh :
        0 <= xLow < 2 ^ k ->
        0 <= xHigh < M ->
        Partition.partition w 2 (xLow + 2^k * xHigh) = [xLow;xHigh].
      Proof.
        replace k with width in M_range |- * by nia; intros. cbv [Partition.partition map seq].
        rewrite !uweight_S, !weight_0 by auto with zarith lia.
        autorewrite with zsimplify.
        rewrite <-Z.mod_pull_div by Z.zero_bounds.
        autorewrite with zsimplify. reflexivity.
      Qed.

      Lemma fancy_reduce_correct xLow xHigh :
        0 <= xLow < 2 ^ k ->
        0 <= xHigh < M ->
        2 * (2 ^ (2 * k) mod M) <= 2 ^ (k + 1) - mu ->
        fancy_reduce xLow xHigh = (xLow + 2^k * xHigh) mod M.
      Proof.
        assert (M < 2^width) by  (replace width with k by nia; lia).
        assert (0 < 2 ^ (k - 1)) by Z.zero_bounds.
        pose proof (Z.mod_pos_bound (xLow + 2^k * xHigh) M ltac:(lia)).
        intros. cbv [fancy_reduce]. rewrite <-partition_2 by lia.
        replace 2%nat with (sz*2)%nat by lia.
        rewrite fancy_reduce'_correct by nia.
        rewrite sz_eq_1; cbv [Partition.partition map seq hd].
        rewrite !uweight_S, !weight_0 by auto with zarith lia.
        autorewrite with zsimplify. reflexivity.
      Qed.
    End Def.
  End Fancy.
End Fancy.

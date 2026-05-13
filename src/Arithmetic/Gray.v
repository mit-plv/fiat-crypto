(* https://en.wikipedia.org/wiki/Gray_code *)

From Coq Require Import ZArith Lia Zbitwise Wf_Z.
Local Open Scope Z_scope.
Local Infix ".|" := Z.lor (at level 40).
Local Infix ".&" := Z.land (at level 40).
Local Infix ".^" := Z.lxor (at level 40).
Local Notation ".~ x" := (Z.lnot x) (at level 35).
Local Notation "x .[ i ]" := (Z.testbit x i) (at level 9, format "x .[ i ]").

Module Z.

Lemma land_opp_same_r_is_pow2 n : n <> 0 -> Z.land n (-n) = 2^Z.log2 (Z.land n (-n)).
Proof.
  enough (forall n : N, n <> 0%N ->
    Z.of_N (N.ldiff n (N.pred n)) = 2 ^ Z.log2 (Z.of_N (N.ldiff n (N.pred n)))).
  { case n; try contradiction; cbn [Z.opp Z.land]; intros; eapply H; discriminate. }
  clear n; intros n; induction n using N.binary_induction; try congruence; intros Hn.
  { rewrite N.ldiff_even_l.
    assert (N.div2 (N.pred (2 * n)) = N.pred n) as ->.
    { cbn. case n; cbn; trivial. intros. destruct Pos.pred_double eqn:?; try lia. }
    rewrite N2Z.inj_mul, Z.log2_double, Z.pow_succ_r; try apply Z.log2_nonneg.
    { apply f_equal, IHn. lia. }
    { case N.ldiff eqn:E; try apply N.ldiff_le in E; try lia. } }
  { rewrite <-N.add_pred_r, N.add_0_r, N.ldiff_odd_even, ?N.ldiff_diag by discriminate; trivial. }
Qed.

Definition gray n := Z.lxor n (Z.shiftr n 1).

Require AdmitAxiom.
Lemma xor_gray_pred_same_r n :
  Z.lxor (gray n) (gray (Z.pred n)) = Z.land n (-n).
Proof.
  cbv [gray].
  apply Z.bits_inj'; intros i Hi.
  rewrite ?Z.lxor_spec, ?Z.land_spec, ?Z.bits_opp, ?Z.shiftr_spec; trivial.
  rewrite <-(Bool.negb_involutive (Z.testbit (Z.pred _) i)) at 1.
  rewrite <-(Bool.negb_involutive (Z.testbit (Z.pred _) (i+1))) at 1.
  rewrite <-?Z.sub_1_r, <-?Z.lnot_spec, !Z.lnot_pred, ?Z.lnot_spec; try lia.
  rewrite !Z.testbit_odd, <-!Z.shiftr_shiftr, ?Z.shiftr_div_pow2 by lia.
  case (Z.eq_dec (n mod 2^i) 0) as [];
    rewrite ?Z_div_zero_opp_full, ?Z_div_nz_opp_full, ?Zodd_mod by lia;
    repeat match goal with
         |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
         (* compat Coq 9.0:*) | |- context [Zeq_bool ?a ?b] => let H := fresh in destruct (Zeq_bool a b) eqn:H; first [apply Zeq_bool_eq in H | apply Zeq_bool_neq in H ]
         end;
    trivial; (Z.div_mod_to_equations; lia).
Qed.

Lemma gray_inj_0_iff a : gray a = 0 <-> (a = 0 \/ a = -1).
Proof.
  cbv [gray].
  rewrite Z.lxor_eq_0_iff, <-Z.div2_spec, Z.div2_div.
  Z.div_mod_to_equations; lia.
Qed.

Lemma gray_inj_0_neqm1 a : a <> -1 -> gray a = 0 -> a = 0.
Proof. rewrite gray_inj_0_iff; lia. Qed.

Lemma gray_inj_neqm1 a b : Z.lxor a b <> -1 -> gray a = gray b -> a = b.
Proof.
  intros Hneq; setoid_rewrite <-Z.lxor_eq_0_iff.
  intros H. apply gray_inj_0_neqm1; trivial.
  revert H; cbv [gray];
  repeat rewrite ?Z.lxor_assoc, ?Z.shiftr_lxor, ?(Z.lxor_comm b); trivial.
Qed.

Lemma gray_inj_0_nonneg a : 0 <= a -> gray a = 0 -> a = 0.
Proof. rewrite gray_inj_0_iff; lia. Qed.

Lemma gray_inj_nonneg a b : 0 <= a -> 0 <= b -> gray a = gray b -> a = b.
Proof. intros; pose proof Z.lxor_nonneg a b; apply gray_inj_neqm1; lia. Qed.

Lemma log2_gray n : 0 <= n -> Z.log2 (gray n) = Z.log2 n.
Proof.
  destruct n; trivial; try lia; set (Z.pos p) as n; intros _.
  pose proof Z.shiftr_nonneg n 1.
  pose proof Z.log2_nonneg n.
  cbv [gray].
  apply Z.log2_bits_unique.
  { rewrite Z.lxor_spec, Z.shiftr_spec, Z.bit_log2, Z.bits_above_log2; trivial; try lia. }
  intros i Hi; apply Z.bits_above_log2; try apply Z.lxor_nonneg; try lia.
  eapply Z.le_lt_trans; try eapply Z.log2_lxor; rewrite ?Z.log2_shiftr; try lia.
Qed.

Lemma reflect_gray_xor n a : 0 <= a < 2^n -> gray (2^n .^ a) = 2^n .^ gray (2^n - 1 - a).
Proof.
  intros H.
  case (Z.leb_spec n 0) as [].
  { pose proof Z.pow_le_mono_r 2 n 0 ltac:(lia) ltac:(trivial).
    replace a with 0 in * by lia; destruct n; trivial; lia. }
  assert (Z.log2 a < n).
  { destruct a; trivial. apply Z.log2_lt_pow2; try lia. }
  cbv [gray].
  rewrite Z.sub_1_r, <-?Z.ones_equiv, ?Z.sub_nocarry_ldiff, ?Z.ldiff_ones_l_low; try lia.
  2: { rewrite Z.ldiff_ones_r, Z.shiftr_eq_0, Z.shiftl_0_l; trivial; try lia. }
  repeat rewrite ?Z.lxor_assoc, ?Z.shiftr_lxor, ?(Z.lxor_comm (Z.shiftr a 1)). f_equal. f_equal.
  rewrite <-!Z.lxor_assoc. f_equal.
  
  apply Z.bits_inj'; intros i Hi.
  rewrite ?Z.lxor_spec, ?Z.shiftr_spec, ?Z.testbit_ones, ?Z.pow2_bits_eqb by lia.
  case Z.leb_spec; case Z.eqb_spec; case Z.ltb_spec; case Z.leb_spec; case Z.ltb_spec; trivial; try lia.
Qed.

Lemma reflect_gray_lnot n a : 0 <= a < 2^n -> gray (2^n .^ a) = 2^n .^ gray (2^n + Z.lnot a).
Proof. intros; rewrite reflect_gray_xor, Z.add_lnot_r by trivial; f_equal; f_equal; ring. Qed.

Lemma reflect_gray_add n a : 0 <= a < 2^n -> gray (2^n + a) = 2^n + gray (2^n - 1 - a).
Proof.
  intros H; generalize H.
  case (Z.leb_spec n 0) as [].
  { pose proof Z.pow_le_mono_r 2 n 0 ltac:(lia) ltac:(trivial).
    replace a with 0 in * by lia; destruct n; trivial; lia. }
  rewrite !Z.add_nocarry_lxor, !reflect_gray_xor; trivial.
  all: apply Z.bits_inj'; intros i Hi; rewrite ?Z.testbit_0_l, ?Z.land_spec, ?Z.pow2_bits_eqb by lia.
  all: case Z.eqb_spec; trivial; intros; subst i; rewrite ?Bool.andb_true_l.
  1: case (Z.eq_dec (2^n - 1 - a) 0) as [->|]; [apply Z.testbit_0_l|].
  all : rewrite Z.bits_above_log2; try lia.
  { apply Z.lxor_nonneg. rewrite Z.shiftr_nonneg. lia. }
  { rewrite log2_gray by lia. apply Z.log2_lt_pow2; lia. }
  { destruct a; trivial. apply Z.log2_lt_pow2; try lia. }
Qed.

Lemma reflect_gray_level n : List.map Z.gray (List.map Z.of_nat (List.seq (2^n) (2^n))) =
    List.map (Z.add (2^Z.of_nat n)) (List.rev (List.map Z.gray (List.map Z.of_nat (List.seq 0 (2^n))))).
Proof.
  apply List.nth_error_ext; intros i.
  repeat rewrite ?List.nth_error_map, ?List.nth_error_rev, ?List.nth_error_seq, ?List.length_map, ?List.length_seq.
  case Nat.ltb_spec; intros; trivial.
  case Nat.ltb_spec; intros; try lia.
  cbn; eapply f_equal.
  pose proof Nat2Z.inj_pow 2 n.
  rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_sub, ?Nat2Z.inj_pow by lia.
  rewrite reflect_gray_add; f_equal; f_equal; try lia.
Qed.


Local Lemma seq_add start len : List.seq start len = List.map (fun x => start + x)%nat (List.seq 0 len).
Proof.
  revert start; induction len; intros; trivial; [].
  rewrite ?List.seq_S, IHlen, List.map_app; trivial.
Qed.

Local Lemma seq2Sn n : List.seq 0 (2 ^ S n) = (List.seq 0 (2 ^ n) ++ List.seq (2 ^ n) (2 ^ n))%list.
Proof. rewrite Nat.pow_succ_r, <-List.seq_app; f_equal; lia. Qed.

From Coq Require Import Permutation FinFun.

Lemma Permutation_gray n :
  Permutation (List.map Z.gray (List.map Z.of_nat (List.seq 0 (2^n))))
                               (List.map Z.of_nat (List.seq 0 (2^n))).
Proof.
  induction n; trivial; [].
  rewrite seq2Sn, 2 List.map_app, reflect_gray_level, IHn; clear IHn; Morphisms.f_equiv.
  assert (List.map Z.of_nat (List.seq (2 ^ n) (2 ^ n)) =
          List.map (Z.add (2 ^ Z.of_nat n)) (List.map Z.of_nat (List.seq 0 (2 ^ n)))) as ->.
  { rewrite seq_add, ?List.map_map. apply List.map_ext; intros.
    rewrite Nat2Z.inj_add, Nat2Z.inj_pow; trivial. }
  eauto using Permutation_map, Permutation_sym, Permutation_rev.
Qed.

Lemma Permutation_gray_level n :
  Permutation (List.map Z.gray (List.map Z.of_nat (List.seq (2^n) (2^n))))
                               (List.map Z.of_nat (List.seq (2^n) (2^n))).
Proof.
  specialize (Permutation_gray (S n)).
  rewrite seq2Sn, ?List.map_app, Permutation_gray.
  eauto using Permutation_app_inv_l.
Qed.

End Z.

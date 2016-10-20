Require Import Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits ZArith Znat ZArith_dec Ndec.
Require Import List Basics Bool Nsatz.

Require Import Crypto.Assembly.QhasmUtil.
Require Import Crypto.Assembly.WordizeUtil.
Require Import Crypto.Assembly.Bounds.

Import ListNotations.

Section BoundedZ.

  Section Trans4.
    Definition min4 (a b c d: Z) :=
      Z.min 0 (Z.min (Z.min a b) (Z.min c d)).

    Definition max4 (a b c d: Z) :=
      Z.max 0 (Z.max (Z.max a b) (Z.max c d)).

    Ltac trans4min_tac := intros; unfold min4;
      repeat match goal with
      | [|- context[(Z.min ?x0 ?x1)%Z]] => is_var x1;
        let A := fresh in let B := fresh in
        destruct (Zmin_spec x0 x1)%Z as [A|A];
        destruct A as [A B];
        rewrite B; clear B
      end; nomega.

    Lemma trans4min_0: forall (x a b c d: Z),
      (0 <= x)%Z -> (min4 a b c d <= x)%Z.
    Proof. trans4min_tac. Qed.

    Lemma trans4min_a: forall (x a b c d: Z),
      (a <= x)%Z -> (min4 a b c d <= x)%Z.
    Proof. trans4min_tac. Qed.

    Lemma trans4min_b: forall (x a b c d: Z),
      (b <= x)%Z -> (min4 a b c d <= x)%Z.
    Proof. trans4min_tac. Qed.

    Lemma trans4min_c: forall (x a b c d: Z),
      (c <= x)%Z -> (min4 a b c d <= x)%Z.
    Proof. trans4min_tac. Qed.

    Lemma trans4min_d: forall (x a b c d: Z),
      (d <= x)%Z -> (min4 a b c d <= x)%Z.
    Proof. trans4min_tac. Qed.

    Ltac trans4max_tac := intros; unfold max4;
      repeat match goal with
      | [|- context[(Z.max ?x0 ?x1)%Z]] => is_var x1;
        let A := fresh in let B := fresh in
        destruct (Zmax_spec x0 x1)%Z as [A|A];
        destruct A as [A B];
        rewrite B; clear B
      end; try nomega.

    Lemma trans4max_0: forall (x a b c d: Z),
      (x <= 0)%Z -> (x <= max4 a b c d)%Z.
    Proof. trans4max_tac. Qed.

    Lemma trans4max_a: forall (x a b c d: Z),
      (x <= a)%Z -> (x <= max4 a b c d)%Z.
    Proof. trans4max_tac. Qed.

    Lemma trans4max_b: forall (x a b c d: Z),
      (x <= b)%Z -> (x <= max4 a b c d)%Z.
    Proof. trans4max_tac. Qed.

    Lemma trans4max_c: forall (x a b c d: Z),
      (x <= c)%Z -> (x <= max4 a b c d)%Z.
    Proof. trans4max_tac. Qed.

    Lemma trans4max_d: forall (x a b c d: Z),
      (x <= d)%Z -> (x <= max4 a b c d)%Z.
    Proof. trans4max_tac. Qed.
  End Trans4.

  Section BoundedMul.
    Lemma bZMul_min: forall (x0 low0 high0 x1 low1 high1: Z),
      (low0 <= x0)%Z -> (x0 <= high0)%Z ->
      (low1 <= x1)%Z -> (x1 <= high1)%Z ->
      (min4 (low0 * low1) (low0 * high1)
            (high0 * low1) (high0 * high1) <= x0 * x1)%Z.
    Proof.
      intros x0 low0 high0 x1 low1 high1
        Hlow0 Hhigh0 Hlow1 Hhigh1.
      destruct (Z_le_dec 0 x0), (Z_le_dec 0 x1).

      - apply trans4min_0.
        replace 0%Z with (0*0)%Z by nomega.
        apply Z.mul_le_mono_nonneg; nomega.

      - apply trans4min_c.
        transitivity (x0 * low1)%Z.

        + apply Z.mul_le_mono_nonpos_r; try nomega.
        + apply Z.mul_le_mono_nonneg_l; try nomega.

      - apply trans4min_b.
        transitivity (x0 * high1)%Z.

        + apply Z.mul_le_mono_nonneg_r; try nomega.
        + apply Z.mul_le_mono_nonpos_l; try nomega.

      - apply trans4min_0.
        replace 0%Z with (0*0)%Z by nomega.
        apply Z.mul_le_mono_nonpos; try nomega.
    Qed.

    Lemma bZMul_max: forall (x0 low0 high0 x1 low1 high1: Z),
      (low0 <= x0)%Z -> (x0 <= high0)%Z ->
      (low1 <= x1)%Z -> (x1 <= high1)%Z ->
      (x0 * x1 <=
      max4 (low0 * low1) (low0 * high1)
           (high0 * low1) (high0 * high1))%Z.
    Proof.
      intros x0 low0 high0 x1 low1 high1
        Hlow0 Hhigh0 Hlow1 Hhigh1.
      destruct (Z_le_dec 0 x0), (Z_le_dec 0 x1).

      - apply trans4max_d.
        apply Z.mul_le_mono_nonneg; nomega.

      - apply trans4max_0.
        replace 0%Z with (0*0)%Z by nomega.
        transitivity (x0 * 0)%Z.

        + apply Z.mul_le_mono_nonneg_l; try nomega.
        + apply Z.mul_le_mono_nonpos_r; try nomega.

      - apply trans4max_0.
        replace 0%Z with (0*0)%Z by nomega.
        transitivity (x0 * 0)%Z.

        + apply Z.mul_le_mono_nonpos_l; try nomega.
        + apply Z.mul_le_mono_nonneg_r; try nomega.

      - apply trans4max_a.
        apply Z.mul_le_mono_nonpos; try nomega.
    Qed.
  End BoundedMul.

  Inductive BoundedZ :=
    | boundedZ: forall (x low high: Z),
      (low <= x)%Z -> (x <= high)%Z -> BoundedZ.

  Definition bprojZ (x: BoundedZ) :=
    match x with
    | boundedZ x0 low0 high0 plow0 phigh0 => x0
    end.

  Definition bZAdd (a b: BoundedZ): BoundedZ.
    refine match a with
    | boundedZ x0 low0 high0 plow0 phigh0 =>
      match b with
      | boundedZ x1 low1 high1 plow1 phigh1 =>
        boundedZ (x0 + x1) (low0 + low1) (high0 + high1) _ _
      end
    end; abstract nomega.
  Defined.

  Definition bZSub (a b: BoundedZ): BoundedZ.
    refine match a with
    | boundedZ x0 low0 high0 plow0 phigh0 =>
      match b with
      | boundedZ x1 low1 high1 plow1 phigh1 =>
        boundedZ (x0 - x1) (low0 - high1) (high0 - low1) _ _
      end
    end; abstract nomega.
  Defined.

  Definition bZMul (a b: BoundedZ): BoundedZ.
    refine match a with
    | boundedZ x0 low0 high0 plow0 phigh0 =>
      match b with
      | boundedZ x1 low1 high1 plow1 phigh1 =>
        boundedZ (x0 * x1)
          (min4 (low0 * low1) (low0 * high1)
                (high0 * low1) (high0 * high1))
          (max4 (low0 * low1) (low0 * high1)
                (high0 * low1) (high0 * high1))
          _ _
      end
    end; try apply bZMul_min; try apply bZMul_max; try assumption.
  Defined.

  Definition bZShiftr (a: BoundedZ) (k: nat): BoundedZ.
    assert (forall k, 2 ^ (Z.of_nat k) > 0)%Z as H by abstract (
      intro m;
      rewrite <- two_p_equiv;
      apply two_p_gt_ZERO;
      induction m; try reflexivity;
      rewrite Nat2Z.inj_succ;
      nomega).

    refine match a with
    | boundedZ x low high plow phigh =>
      boundedZ (Z.shiftr x (Z.of_nat k))
               (Z.shiftr low (Z.of_nat k))
               (Z.succ (Z.shiftr high (Z.of_nat k))) _ _
    end.

    - abstract (
        repeat rewrite Z.shiftr_div_pow2;
        try apply Nat2Z.is_nonneg;
        apply Z_div_le; try assumption;
        try apply H).

    - abstract (
        apply Z.lt_succ_r;
        repeat rewrite Z.shiftr_div_pow2;
        try apply Nat2Z.is_nonneg;
        apply Z.lt_lt_succ_r;
        apply Z.lt_succ_r;
        apply Z_div_le;
        try apply H;
        try assumption).
  Qed.

  Definition bZMask (a: BoundedZ) (k: nat): BoundedZ.
    assert (0 < 2 ^ Z.of_nat k)%Z as Hk by (
      induction k;
      try abstract (vm_compute; reflexivity);
      rewrite Nat2Z.inj_succ;
      rewrite <- two_p_equiv;
      apply Z.gt_lt;
      apply two_p_gt_ZERO;
      apply Z.le_le_succ_r;
      apply Nat2Z.is_nonneg).

    refine match a with
    | boundedZ x low high plow phigh =>
      boundedZ (Z.land x (Z.ones (Z.of_nat k)))
               (Z.of_N 0%N)
               (Z.of_N (Npow2 k)) _ _
    end.

    - repeat rewrite Z.land_ones;
        try apply Nat2Z.is_nonneg.

      abstract (
        apply (Z.mod_pos_bound x) in Hk; destruct Hk;
        induction k; simpl in *; assumption).

    - repeat rewrite Z.land_ones;
        try apply Nat2Z.is_nonneg.

      abstract (
        rewrite Npow2_N;
        rewrite N2Z.inj_pow; simpl;
        apply (Z.mod_pos_bound x) in Hk; destruct Hk;
        apply Z.lt_le_incl;
        induction k; simpl in *; assumption).
  Qed.
End BoundedZ.

Section BoundedN.

  Inductive BoundedN :=
    | boundedN: forall (x low high: N),
      (low <= x)%N -> (x < high)%N -> BoundedN.

  Definition bprojN (x: BoundedN) :=
    match x with
    | boundedN x0 low0 high0 plow0 phigh0 => x0
    end.

  Definition bNAdd (a b: BoundedN): BoundedN.
    refine match a with
    | boundedN x0 low0 high0 plow0 phigh0 =>
      match b with
      | boundedN x1 low1 high1 plow1 phigh1 =>
        boundedN (x0 + x1) (low0 + low1) (high0 + high1) _ _
      end
    end.

    - abstract (apply N.add_le_mono; assumption).
    - abstract nomega.
  Defined.

  Definition bNSub (a b: BoundedN): BoundedN.
    refine match a with
    | boundedN x0 low0 high0 plow0 phigh0 =>
      match b with
      | boundedN x1 low1 high1 plow1 phigh1 =>
        boundedN (x0 - x1) (low0 - high1) (N.succ (high0 - low1)) _ _
      end
    end.

    - transitivity (x0 - high1)%N.

      + apply N.sub_le_mono_r; assumption.
      + apply N.sub_le_mono_l; apply N.lt_le_incl; assumption.

    - apply N.lt_succ_r; transitivity (high0 - x1)%N.

      + apply N.sub_le_mono_r; apply N.lt_le_incl; assumption.
      + apply N.sub_le_mono_l; assumption.

  Defined.

  Definition bNMul (a b: BoundedN): BoundedN.
    refine match a with
    | boundedN x0 low0 high0 plow0 phigh0 =>
      match b with
      | boundedN x1 low1 high1 plow1 phigh1 =>
        boundedN (x0 * x1)%N (low0 * low1)%N (high0 * high1)%N _ _
      end
    end; abstract (
      try apply N.mul_le_mono_nonneg;
      try apply N.mul_lt_mono_nonneg;
        try assumption;
        try apply N_ge_0).
  Qed.

  Definition bNShiftr (a: BoundedN) (k: nat): BoundedN.
    assert (forall k, 2 ^ (N.of_nat k) > 0)%N as H by abstract (
      intros;
      rewrite <- Npow2_N;
      apply N.lt_gt;
      apply Npow2_gt0).

    refine match a with
    | boundedN x low high plow phigh =>
      boundedN (N.shiftr x (N.of_nat k))
               (N.shiftr low (N.of_nat k))
               (N.succ (N.shiftr high (N.of_nat k))) _ _
    end.

    - repeat rewrite N.shiftr_div_pow2.
      apply N.div_le_mono; try assumption.
      pose proof (H k) as H0.
      induction ((2 ^ N.of_nat k)%N);
        [inversion H0; intuition |].
      apply N.neq_0_lt_0; apply N.gt_lt; assumption.

    - apply N.lt_succ_r.
      repeat rewrite N.shiftr_div_pow2.
      apply N.div_le_mono; [|apply N.lt_le_incl; assumption].
      pose proof (H k) as H0.
      induction ((2 ^ N.of_nat k)%N);
        [inversion H0; intuition |].
      apply N.neq_0_lt_0; apply N.gt_lt; assumption.
  Defined.

  Definition bNMask (a: BoundedN) (k: nat): BoundedN.
    assert (forall k, 0 < 2 ^ (N.of_nat k))%N as H by abstract (
      intros;
      rewrite <- Npow2_N;
      apply Npow2_gt0).

    refine match a with
    | boundedN x low high plow phigh =>
      boundedN (N.land x (N.ones (N.of_nat k)))
               0%N
               (Npow2 k) _ _
    end.

    - repeat rewrite N.land_ones;
        apply N_ge_0.

    - repeat rewrite N.land_ones.

      abstract (
        rewrite Npow2_N;
        pose proof (N.mod_bound_pos x (2 ^ N.of_nat k)%N (N_ge_0 _) (H k))
          as H0; destruct H0;
        assumption).
  Defined.

End BoundedN.

Section BoundedWord.
  Context {n: nat}.

  Section BoundedSub.
    Lemma NToWord_Npow2: wzero n = NToWord n (Npow2 n).
    Proof.
      induction n as [|n0].

      + repeat rewrite shatter_word_0; reflexivity.

      + unfold wzero in *; simpl in *.
        rewrite IHn0; simpl.
        induction (Npow2 n0); simpl; reflexivity.
    Qed.

    Lemma bWSub_lem0: forall (x0 x1: word n) (low0 high1: N),
      (low0 <= wordToN x0)%N -> (wordToN x1 < high1)%N ->
      (low0 - high1 <= & (x0 ^- x1))%N.
    Proof.
      intros.

      destruct (Nge_dec (wordToN x1) 1)%N as [e|e].
      destruct (Nge_dec (wordToN x1) (wordToN x0)).

      - unfold wminus, wneg.
        assert (low0 < high1)%N. {
          apply (N.le_lt_trans _ (wordToN x0) _); [assumption|].
          apply (N.le_lt_trans _ (wordToN x1) _); [apply N.ge_le|]; assumption.
        }

        replace (low0 - high1)%N with 0%N; [apply N_ge_0|].
        symmetry.
        apply N.sub_0_le.
        apply N.lt_le_incl.
        assumption.

        - transitivity (wordToN x0 - wordToN x1)%N.

          + transitivity (wordToN x0 - high1)%N.

            * apply N.sub_le_mono_r; assumption.

            * apply N.sub_le_mono_l; apply N.lt_le_incl; assumption.

          + assert (& x0 - & x1 < Npow2 n)%N. {
              transitivity (wordToN x0);
                try apply word_size_bound;
                apply N.sub_lt.

              + apply N.lt_le_incl; assumption.

              + nomega.
            }

            assert (& x0 - & x1 + & x1 < Npow2 n)%N. {
              replace (wordToN x0 - wordToN x1 + wordToN x1)%N
                with (wordToN x0) by nomega.
              apply word_size_bound.
            }

            assert (x0 = NToWord n (wordToN x0 - wordToN x1) ^+ x1) as Hv. {
              apply NToWord_equal.
              rewrite <- wordize_plus; rewrite wordToN_NToWord;
                try assumption.
              nomega.
            }

            apply N.eq_le_incl.
            rewrite Hv.
            unfold wminus.
            rewrite <- wplus_assoc.
            rewrite wminus_inv.
            rewrite (wplus_comm (NToWord n (wordToN x0 - wordToN x1)) (wzero n)).
            rewrite wplus_unit.
            rewrite <- wordize_plus; [nomega|].
            rewrite wordToN_NToWord; assumption.

      - unfold wminus, wneg.
        assert (wordToN x1 = 0)%N as e' by nomega.
        rewrite e'.
        replace (Npow2 n - 0)%N with (Npow2 n) by nomega.
        rewrite <- NToWord_Npow2.

        erewrite <- wordize_plus;
          try rewrite wordToN_zero;
          replace (wordToN x0 + 0)%N with (wordToN x0)%N by nomega;
          try apply word_size_bound.

        transitivity low0; try assumption.
        apply N.le_sub_le_add_r.
        apply N.le_add_r.
    Qed.

    Lemma bWSub_lem1: forall (x0 x1: word n) (low1 high0: N),
      (low1 <= wordToN x1)%N -> (wordToN x0 < high0)%N ->
      (& (x0 ^- x1) < N.succ (high0 + Npow2 n - low1))%N.
    Proof.
      intros; unfold wminus.
      destruct (Nge_dec (wordToN x1) 1)%N as [e|e].
      destruct (Nge_dec (wordToN x0) (wordToN x1)).

      - apply N.lt_succ_r.
        assert (& x0 - & x1 < Npow2 n)%N. {
          transitivity (wordToN x0);
          try apply word_size_bound;
          apply N.sub_lt.

          + apply N.ge_le; assumption.

          + nomega.
        }

        assert (& x0 - & x1 + & x1 < Npow2 n)%N. {
          replace (wordToN x0 - wordToN x1 + wordToN x1)%N
            with (wordToN x0) by nomega.
          apply word_size_bound.
        }

        assert (x0 = NToWord n (wordToN x0 - wordToN x1) ^+ x1) as Hv. {
          apply NToWord_equal.
          rewrite <- wordize_plus; rewrite wordToN_NToWord;
          try assumption.
          nomega.
        }

        rewrite Hv.
        rewrite <- wplus_assoc.
        rewrite wminus_inv.
        rewrite wplus_comm.
        rewrite wplus_unit.
        rewrite wordToN_NToWord.

        + transitivity (wordToN x0 - low1)%N.

          * apply N.sub_le_mono_l; assumption.

          * apply N.sub_le_mono_r.
            transitivity high0; [apply N.lt_le_incl; assumption|].
            replace' high0 with (high0 + 0)%N at 1 by nomega.
            apply N.add_le_mono_l.
            apply N_ge_0.

        + transitivity (wordToN x0); try apply word_size_bound.
            nomega.

      - rewrite <- wordize_plus; [apply N.lt_succ_r|].

        + transitivity (high0 + (wordToN (wneg x1)))%N.

          * apply N.add_le_mono_r; apply N.lt_le_incl; assumption.

          * unfold wneg.
            rewrite wordToN_NToWord; [|abstract (
              apply N.sub_lt;
              try apply N.lt_le_incl;
              try apply word_size_bound;
              nomega )].

            rewrite N.add_sub_assoc; [|abstract (
              try apply N.lt_le_incl;
              try apply word_size_bound)].

            apply N.sub_le_mono_l.
            assumption.

        + unfold wneg.

          rewrite wordToN_NToWord; [|abstract (
            apply N.sub_lt;
            try apply N.lt_le_incl;
            try apply word_size_bound;
            nomega )].

          replace (wordToN x0 + (Npow2 n - wordToN x1))%N
            with (Npow2 n - (wordToN x1 - wordToN x0))%N.

          * apply N.sub_lt; try nomega.
            transitivity (wordToN x1); [apply N.le_sub_l|].
            apply N.lt_le_incl.
            apply word_size_bound.

          * apply N.add_sub_eq_l.
            rewrite <- N.add_sub_swap;
                [|apply N.lt_le_incl; assumption].
            rewrite (N.add_comm (wordToN x0)).
            rewrite N.add_assoc.
            rewrite N.add_sub_assoc;
                [|apply N.lt_le_incl; apply word_size_bound].
            rewrite N.add_sub.
            rewrite N.add_comm.
            rewrite N.add_sub.
            reflexivity.

      - apply N.lt_succ_r.
        assert (wordToN x1 = 0)%N as e' by nomega.
        assert (NToWord n (wordToN x1) = NToWord n 0%N) as E by
            (rewrite e'; reflexivity).
        rewrite NToWord_wordToN in E.
        simpl in E; rewrite wzero'_def in E.
        rewrite E.
        unfold wneg.
        rewrite wordToN_zero.
        rewrite N.sub_0_r.
        rewrite <- NToWord_Npow2.
        rewrite wplus_comm.
        rewrite wplus_unit.
        transitivity high0.

        + apply N.lt_le_incl.
          assumption.

        + rewrite <- N.add_sub_assoc.

          * replace high0 with (high0 + 0)%N by nomega.
            apply N.add_le_mono; [|apply N_ge_0].
            apply N.eq_le_incl.
            rewrite N.add_0_r.
            reflexivity.

          * transitivity (wordToN x1);
            [ assumption
            | apply N.lt_le_incl;
                apply word_size_bound].

    Qed.
  End BoundedSub.

  Inductive BoundedWord :=
    | boundedWord: forall (x: word n) (low high: N) (overflowed: bool),
      (low <= wordToN x)%N -> (wordToN x < high)%N -> BoundedWord.

  Definition bprojW (x: BoundedWord) :=
    match x with
    | boundedWord x0 _ _ _ _ _ => x0
    end.

  Definition bWAdd (a b: BoundedWord): BoundedWord.
    refine match a with
    | boundedWord x0 low0 high0 o0 plow0 phigh0 =>
      match b with
      | boundedWord x1 low1 high1 o1 plow1 phigh1 =>
        if (overflows n (high0 + high1))
        then boundedWord (x0 ^+ x1) 0%N (high0 + high1) (orb o0 o1) _ _
        else boundedWord (x0 ^+ x1) (low0 + low1) (high0 + high1) true _ _
      end
    end; try abstract (
      apply (N.le_lt_trans _ (wordToN x0 + wordToN x1)%N _);
        try apply plus_le;
        abstract nomega).

    - apply N_ge_0.

    - erewrite <- wordize_plus';
        try eassumption;
        try abstract nomega.

      + apply N.add_le_mono; assumption.

      + abstract (apply N.lt_le_incl; nomega).
  Qed.

  Definition bWSub (a b: BoundedWord): BoundedWord.
    refine match a with
    | boundedWord x0 low0 high0 o0 plow0 phigh0 =>
      match b with
      | boundedWord x1 low1 high1 o1 plow1 phigh1 =>
        let upper_bound :=
          if (Nge_dec high0 (Npow2 n))
          then Npow2 n
          else if (Nge_dec high1 (Npow2 n))
               then Npow2 n
               else (N.succ (high0 + Npow2 n - low1)) in

        if (Nge_dec low0 high1)
        then boundedWord (x0 ^- x1) (low0 - high1)%N upper_bound (orb o0 o1) _ _
        else boundedWord (x0 ^- x1) 0%N upper_bound (orb o0 o1) _ _
      end
    end; abstract (unfold upper_bound; try apply N_ge_0;
      destruct (Nge_dec high0 (Npow2 n)), (Nge_dec high1 (Npow2 n));
      repeat match goal with
      | [|- (_ - ?x <= wordToN _)%N] => apply bWSub_lem0
      | [|- (wordToN _ < N.succ (?x + _ - _))%N] => apply bWSub_lem1
      | [|- (wordToN _ < Npow2 _)%N] => apply word_size_bound
      | [|- (0 <= _)%N] => apply N_ge_0
      end; assumption).
  Qed.

  Definition bWMul (a b: BoundedWord): BoundedWord.
    refine match a with
    | boundedWord x0 low0 high0 o0 plow0 phigh0 =>
      match b with
      | boundedWord x1 low1 high1 o1 plow1 phigh1 =>
        if (overflows n (high0 * high1))
        then boundedWord (x0 ^* x1)%N 0%N (high0 * high1)%N true _ _
        else boundedWord (x0 ^* x1)%N (low0 * low1)%N (high0 * high1)%N (orb o0 o1) _ _
      end
    end.

    - apply N_ge_0.

    - apply (N.le_lt_trans _ (wordToN x0 * wordToN x1)%N _); [apply mult_le|].
      apply N.mul_lt_mono; assumption.

    - rewrite <- wordize_mult.

      + apply N.mul_le_mono; assumption.

      + transitivity (high0 * high1)%N; [|assumption].
        apply N.mul_lt_mono; assumption.

    - apply (N.le_lt_trans _ (wordToN x0 * wordToN x1)%N _); [apply mult_le|].
      apply N.mul_lt_mono; assumption.
  Qed.

  Definition bWShiftr (a: BoundedWord) (k: nat): BoundedWord.
    assert (forall k, 2 ^ (N.of_nat k) > 0)%N as H by abstract (
      intros;
      rewrite <- Npow2_N;
      apply N.lt_gt;
      apply Npow2_gt0).

    refine match a with
    | boundedWord x low high o plow phigh =>
      boundedWord (extend (le_n _) (shiftr x k))
        (N.shiftr low (N.of_nat k))
        (N.succ (N.shiftr high (N.of_nat k))) o _ _
           end.

    - unfold extend; rewrite wordToN_convS.

      rewrite wordToN_zext.
      rewrite <- wordize_shiftr.
      rewrite <- Nshiftr_equiv_nat.
      repeat rewrite N.shiftr_div_pow2.
      apply N.div_le_mono; try assumption.
      pose proof (H k) as H0.
      induction ((2 ^ N.of_nat k)%N);
        [inversion H0; intuition |].
      apply N.neq_0_lt_0; apply N.gt_lt; assumption.

    - unfold extend; rewrite wordToN_convS.
      rewrite wordToN_zext.
      rewrite Nshiftr_equiv_nat.
      eapply N.lt_le_trans; [apply shiftr_bound; eassumption|].
      try apply N.eq_le_incl.
      try eassumption; reflexivity.
  Qed.

  Definition bWMask (a: BoundedWord) (k: nat): BoundedWord.
    refine match a with
    | boundedWord x low high o plow phigh =>
      boundedWord (mask k x) 0%N (Npow2 k) o _ _
    end; [apply N_ge_0 | apply mask_bound].
  Qed.
End BoundedWord.

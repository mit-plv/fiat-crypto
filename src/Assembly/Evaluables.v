Require Import Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits ZArith Znat ZArith_dec Ndec.
Require Import List Basics Bool Nsatz Sumbool Datatypes.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import QhasmUtil WordizeUtil Bounds.
Require Import ProofIrrelevance.

Import ListNotations.

Section Evaluability.
  Class Evaluable T := evaluator {
    ezero: T;

    (* Conversions *)
    toT: Z -> T;
    fromT: T -> Z;

    (* Operations *)
    eadd: T -> T -> T;
    esub: T -> T -> T;
    emul: T -> T -> T;
    eshiftr: T -> T -> T;
    eand: T -> T -> T;

    (* Comparisons *)
    eltb: T -> T -> bool;
    eeqb: T -> T -> bool
  }.
End Evaluability.

Section Z.
  Instance ZEvaluable : Evaluable Z := {
    ezero := 0%Z;

    (* Conversions *)
    toT := id;
    fromT := id;

    (* Operations *)
    eadd := Z.add;
    esub := Z.sub;
    emul := Z.mul;
    eshiftr := Z.shiftr;
    eand := Z.land;

    (* Comparisons *)
    eltb := Z.ltb;
    eeqb := Z.eqb;
  }.

End Z.

Section Word.
  Context {n: nat}.

  Instance WordEvaluable : Evaluable (word n) := {
    ezero := wzero n;

    (* Conversions *)
    toT := fun x => @NToWord n (Z.to_N x);
    fromT := @wordToZ n;

    (* Operations *)
    eadd := @wplus n;
    esub := @wminus n;
    emul := @wmult n;
    eshiftr := fun x y => @shiftr n x (wordToNat y);
    eand := @wand n;

    (* Comparisons *)
    eltb := fun x y => N.ltb (wordToN x) (wordToN y);
    eeqb := fun x y => proj1_sig (bool_of_sumbool (@weq n x y))
  }.
End Word.

Section RangeUpdate.
  Context {n: nat}.

  Inductive Range T := | range: forall (low high: T), Range T.

  Definition validBinaryWordOp
        (rangeF: Range N -> Range N -> option (Range N))
        (wordF: word n -> word n -> word n): Prop :=
    forall (low0 high0 low1 high1: N) (x y: word n),
      (low0 <= wordToN x < high0)%N
    -> (low1 <= wordToN y < high1)%N
    -> match rangeF (range N low0 high0) (range N low1 high1) with
      | Some (range low2 high2) =>
        (low2 <= @wordToN n (wordF x y) < high2)%N
      | _ => True 
      end.

  Definition validNatWordOp
        (rangeF: Range N -> nat -> option (Range N))
        (wordF: word n -> nat -> word n): Prop :=
    forall (low0 high0: N) (k: nat) (x: word n),
      (low0 <= wordToN x < high0)%N
    -> match rangeF (range N low0 high0) k with
      | Some (range low2 high2) =>
        (low2 <= @wordToN n (wordF x k) < high2)%N
      | _ => True 
      end.

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

  Section LandOnes.
    Definition getBits (x: N) := N.succ (N.log2 x).

    Lemma land_intro_ones: forall x, x = N.land x (N.ones (getBits x)).
    Proof.
      intros.
      rewrite N.land_ones_low; [reflexivity|].
      unfold getBits; nomega.
    Qed.

    Lemma land_lt_Npow2: forall x k, (N.land x (N.ones k) < 2 ^ k)%N.
    Proof.
      intros.
      rewrite N.land_ones.
      apply N.mod_lt.
      rewrite <- (N2Nat.id k).
      rewrite <- Npow2_N.
      apply N.neq_0_lt_0.
      apply Npow2_gt0.
    Qed.

    Lemma land_prop_bound_l: forall a b, (N.land a b < Npow2 (N.to_nat (getBits a)))%N.
    Proof.
      intros; rewrite Npow2_N.
      rewrite (land_intro_ones a).
      rewrite <- N.land_comm.
      rewrite N.land_assoc.
      rewrite N2Nat.id.
      apply (N.lt_le_trans _ (2 ^ (getBits a))%N _); [apply land_lt_Npow2|].
      rewrite <- (N2Nat.id (getBits a)).
      rewrite <- (N2Nat.id (getBits (N.land _ _))).
      repeat rewrite <- Npow2_N.
      rewrite N2Nat.id.
      apply Npow2_ordered.
      apply to_nat_le.
      apply N.eq_le_incl; f_equal.
      apply land_intro_ones.
    Qed.

    Lemma land_prop_bound_r: forall a b, (N.land a b < Npow2 (N.to_nat (getBits b)))%N.
    Proof.
      intros; rewrite N.land_comm; apply land_prop_bound_l.
    Qed.
  End LandOnes.

  Lemma range_add_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           if (overflows n (high0 + high1))
           then None
           else Some (range N (low0 + low1) (high0 + high1))
         end)%N
      (@wplus n).
  Proof.
    unfold validBinaryWordOp; intros until y; intros H0 H1.
    destruct H0 as [H0a H0b].
    destruct H1 as [H1a H1b].

    destruct (overflows n (high0 + high1))%N; split.

    - erewrite <- wordize_plus';
        try eassumption;
        try abstract nomega.

      + apply N.add_le_mono; assumption.

      + apply N.lt_le_incl; nomega.

    - apply (N.le_lt_trans _ (wordToN x + wordToN y)%N _);
        try apply plus_le.
      nomega.
  Qed.

  Lemma range_sub_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           if (Nge_dec low0 high1)
           then Some (range N (low0 - high1)%N
              (if (Nge_dec high0 (Npow2 n)) then Npow2 n else
               if (Nge_dec high1 (Npow2 n)) then Npow2 n else
               N.succ (high0 + Npow2 n - low1))%N)
           else None
         end)
      (@wminus n).
  Proof.
    unfold validBinaryWordOp; intros until y; intros H0 H1.
    destruct H0 as [H0a H0b].
    destruct H1 as [H1a H1b].

    destruct (Nge_dec high0 (Npow2 n)),
             (Nge_dec high1 (Npow2 n)),
             (Nge_dec low0 high1); split;
      repeat match goal with
      | [|- (_ - ?x <= wordToN _)%N] => apply bWSub_lem0
      | [|- (wordToN _ < N.succ (?x + _ - _))%N] => apply bWSub_lem1
      | [|- (wordToN _ < Npow2 _)%N] => apply word_size_bound
      | [|- (0 <= _)%N] => apply N_ge_0
      end; assumption.
  Qed.

  Lemma range_mul_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           if (overflows n (high0 * high1)) then None else
           Some (range N (low0 * low1) (high0 * high1))%N
          end)
      (@wmult n).
  Proof.
    unfold validBinaryWordOp; intros until y; intros H0 H1.
    destruct H0 as [H0a H0b].
    destruct H1 as [H1a H1b].

    destruct (overflows n (high0 * high1))%N; split.

    - rewrite <- wordize_mult.

      + apply N.mul_le_mono; assumption.

      + transitivity (high0 * high1)%N; [|assumption].
        apply N.mul_lt_mono; assumption.

    - apply (N.le_lt_trans _ (wordToN x * wordToN y)%N _); [apply mult_le|].
      apply N.mul_lt_mono; assumption.
  Qed.

  Lemma range_shiftr_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           Some (range N (N.shiftr low0 high1) (N.succ (N.shiftr high0 low1)))%N
          end)
      (fun x k => extend (Nat.eq_le_incl _ _ eq_refl) (shiftr x (wordToNat k))).
  Proof.
    unfold validBinaryWordOp; intros until y; intros H0 H1.
    destruct H0 as [H0a H0b], H1 as [H1a H1b].
    split; unfold extend; rewrite wordToN_convS, wordToN_zext.

    - rewrite <- wordize_shiftr.
      rewrite <- Nshiftr_equiv_nat.
      repeat rewrite N.shiftr_div_pow2.
      transitivity (wordToN x / 2 ^ high1)%N.

      + apply N.div_le_mono; [|assumption].
        rewrite <- (N2Nat.id high1).
        rewrite <- Npow2_N.
        apply N.neq_0_lt_0.
        apply Npow2_gt0.

      + apply N.div_le_compat_l; split.

        * rewrite <- Npow2_N; apply Npow2_gt0.

        * rewrite <- (N2Nat.id high1).
          repeat rewrite <- Npow2_N.
          apply Npow2_ordered.
          rewrite <- (Nat2N.id (wordToNat y)).
          apply to_nat_le.
          rewrite <- wordToN_nat.
          apply N.lt_le_incl; assumption.

    - eapply N.lt_le_trans.

      + apply shiftr_bound; eassumption.

      + rewrite <- (Nat2N.id (wordToNat y)).
        rewrite <- Nshiftr_equiv_nat.
        rewrite N2Nat.id.
        rewrite <- wordToN_nat.
        apply N.le_pred_le_succ.
        rewrite N.pred_succ.
        repeat rewrite N.shiftr_div_pow2.
        apply N.div_le_compat_l; split;
          rewrite <- (N2Nat.id low1);
          [| rewrite <- (N2Nat.id (wordToN y))];
          repeat rewrite <- Npow2_N;
          [apply Npow2_gt0 |].
        apply Npow2_ordered.
        apply to_nat_le.
        assumption.
  Qed.

  Lemma range_and_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           Some (range N 0%N (Npow2 (min (N.to_nat (getBits high0)) (N.to_nat (getBits high1))))%N)
          end)
      (@wand n).
  Proof.
    unfold validBinaryWordOp; intros until y; intros H0 H1.
    destruct H0 as [H0a H0b], H1 as [H1a H1b].
    split; [apply N_ge_0 |].
    destruct (lt_dec (N.to_nat (getBits high0)) (N.to_nat (getBits high1))).

    - rewrite min_l; [|omega].
      rewrite wordize_and.
      apply (N.lt_le_trans _ (Npow2 (N.to_nat (getBits (wordToN x)))) _);
        [apply land_prop_bound_l|].
      apply Npow2_ordered.
      apply to_nat_le.
      unfold getBits.
      apply N.le_pred_le_succ.
      rewrite N.pred_succ.
      apply N.log2_le_mono.
      apply N.lt_le_incl; assumption.

    - rewrite min_r; [|omega].
      rewrite wordize_and.
      apply (N.lt_le_trans _ (Npow2 (N.to_nat (getBits (wordToN y)))) _);
        [apply land_prop_bound_r|].
      apply Npow2_ordered.
      apply to_nat_le.
      unfold getBits.
      apply N.le_pred_le_succ.
      rewrite N.pred_succ.
      apply N.log2_le_mono.
      apply N.lt_le_incl; assumption.
  Qed.
End RangeUpdate.

Section WordRange.
  Context {n: nat}.

  Inductive WordRangeOpt :=
    | someRange: forall (low high: N),
        (low < high)%N -> (high <= Npow2 n)%N -> WordRangeOpt
    | applyBinOp: forall rangeF wordF,
        @validBinaryWordOp n rangeF wordF ->
        WordRangeOpt -> WordRangeOpt -> WordRangeOpt
    | applyNatOp: forall rangeF wordF,
        @validNatWordOp n rangeF wordF ->
        WordRangeOpt -> nat -> WordRangeOpt.

  Fixpoint evalWordRangeOpt (r: WordRangeOpt): option (Range N) :=
    match r with
    | someRange low high _ _ => Some (range N low high)
    | applyBinOp rangeF wordF _ a b =>
      omap (evalWordRangeOpt a) (fun a' =>
        omap (evalWordRangeOpt a) (fun b' =>
          rangeF a' b'))
    | applyNatOp rangeF wordF _ x k =>
      omap (evalWordRangeOpt x) (fun x' =>
        rangeF x' k)
    end.

  Definition anyWord: WordRangeOpt.
    refine (someRange 0%N (Npow2 n) _ _).
    - apply Npow2_gt0.
    - reflexivity.
  Defined.

  Definition getLowerBoundOpt (w: WordRangeOpt): option N :=
    omap (evalWordRangeOpt w) (fun r =>
      match r with | range low high => Some low end).

  Definition getUpperBoundOpt (w: WordRangeOpt): option N :=
    omap (evalWordRangeOpt w) (fun r =>
      match r with | range low high => Some high end).

  Definition makeRangeOpt (low high: N): option WordRangeOpt.
    refine (
      match (Nge_dec low high, Nge_dec high (Npow2 n)) with
      | (right _, right _) => Some (someRange low high _ _)
      | _ => None
      end); [assumption|].

    apply N.lt_le_incl; assumption.
  Defined.

  Definition getOrElse {T} (d: T) (o: option T) :=
    match o with | Some x => x | None => d end.

  Instance WordRangeOptEvaluable : Evaluable WordRangeOpt := {
    ezero := anyWord;

    (* Conversions *)
    toT := fun x => getOrElse anyWord (makeRangeOpt 0%N (Z.to_N x));
    fromT := fun x => Z.of_N (getOrElse (Npow2 n) (getUpperBoundOpt x));

    (* Operations *)
    eadd := applyBinOp _ _ range_add_valid;
    esub := applyBinOp _ _ range_sub_valid;
    emul := applyBinOp _ _ range_mul_valid;
    eshiftr := applyBinOp _ _ range_shiftr_valid;
    eand := applyBinOp _ _ range_and_valid;

    (* Comparisons just test upper bounds.
       We won't bounds-check Ite in our PHOAS formalism *)
    eltb := fun x y =>
      getOrElse false (
        omap (getUpperBoundOpt x) (fun xb =>
          omap (getUpperBoundOpt y) (fun yb =>
            Some (N.ltb xb yb))));

    eeqb := fun x y =>
      getOrElse false (
        omap (getUpperBoundOpt x) (fun xub =>
          omap (getUpperBoundOpt y) (fun yub =>
            omap (getLowerBoundOpt x) (fun xlb =>
              omap (getLowerBoundOpt y) (fun ylb =>
                Some (andb (N.eqb xub yub) (N.eqb xlb ylb)))))))
  }.
End WordRange.

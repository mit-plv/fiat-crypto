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
      (low0 <= wordToN x)%N -> (wordToN x <= high0)%N -> (high0 < Npow2 n)%N
    -> (low1 <= wordToN y)%N -> (wordToN y <= high1)%N -> (high1 < Npow2 n)%N
    -> match rangeF (range N low0 high0) (range N low1 high1) with
      | Some (range low2 high2) =>
          (low2 <= @wordToN n (wordF x y))%N
        /\ (@wordToN n (wordF x y) <= high2)%N
        /\ (high2 < Npow2 n)%N
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
      (low0 <= wordToN x0)%N -> (wordToN x1 <= high1)%N -> 
      (low0 - high1 <= & (x0 ^- x1))%N.
    Proof.
      intros.

      destruct (Nge_dec (wordToN x1) 1)%N as [e|e].
      destruct (Nge_dec (wordToN x1) (wordToN x0)).

      - unfold wminus, wneg.
        assert (low0 <= high1)%N. {
          transitivity (wordToN x0); [assumption|].
          transitivity (wordToN x1); [apply N.ge_le|]; assumption.
        }

        replace (low0 - high1)%N with 0%N; [apply N_ge_0|].
        symmetry.
        apply N.sub_0_le.
        assumption.

      - transitivity (wordToN x0 - wordToN x1)%N.

        + transitivity (wordToN x0 - high1)%N;
            [apply N.sub_le_mono_r | apply N.sub_le_mono_l];
            assumption.

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
      (low1 <= wordToN x1)%N -> (wordToN x0 <= high0)%N -> 
      (& (x0 ^- x1) <= high0 + Npow2 n - low1)%N.
    Proof.
      intros; unfold wminus.
      destruct (Nge_dec (wordToN x1) 1)%N as [e|e].
      destruct (Nge_dec (wordToN x0) (wordToN x1)).

      - assert (& x0 - & x1 < Npow2 n)%N. {
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
            transitivity high0; [assumption|].
            replace' high0 with (high0 + 0)%N at 1 by nomega.
            apply N.add_le_mono_l.
            apply N_ge_0.

        + transitivity (wordToN x0); try apply word_size_bound.
          nomega.

      - rewrite <- wordize_plus.

        + transitivity (high0 + (wordToN (wneg x1)))%N.

          * apply N.add_le_mono_r; assumption.

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

      - assert (wordToN x1 = 0)%N as e' by nomega.
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

        + assumption.

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
    unfold validBinaryWordOp; intros.

    destruct (overflows n (high0 + high1))%N; repeat split; try assumption.

    - rewrite <- wordize_plus.

      + apply N.add_le_mono; assumption.

      + apply (N.le_lt_trans _ (high0 + high1)%N _); [|assumption].
        apply N.add_le_mono; assumption.

    - transitivity (wordToN x + wordToN y)%N; [apply plus_le|].
      apply N.add_le_mono; assumption.
  Qed.

  Lemma range_sub_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           if (Nge_dec low0 high1)
           then Some (range N (low0 - high1)%N
              (if (Nge_dec high0 (Npow2 n)) then N.pred (Npow2 n) else
               if (Nge_dec high1 (Npow2 n)) then N.pred (Npow2 n) else
               if (Nge_dec (high0 + Npow2 n - low1) (Npow2 n))
               then N.pred (Npow2 n)
               else high0 + Npow2 n - low1)%N)
           else None
         end)
      (@wminus n).
  Proof.
    unfold validBinaryWordOp; intros.

    destruct (Nge_dec high0 (Npow2 n)),
             (Nge_dec high1 (Npow2 n)),
             (Nge_dec low0 high1),
             (Nge_dec (high0 + Npow2 n - low1) (Npow2 n));
      repeat split;
      repeat match goal with
      | [|- (N.pred _ < _)%N] =>
        rewrite <- (N.pred_succ (Npow2 n));
          apply -> N.pred_lt_mono;
          rewrite N.pred_succ;
        [ apply N.lt_succ_diag_r
        | apply N.neq_0_lt_0; apply Npow2_gt0]

      | [|- (wordToN _ <= N.pred _)%N] => apply N.lt_le_pred
      | [|- (wordToN _ < Npow2 _)%N] => apply word_size_bound
      | [|- (_ - ?x <= wordToN _)%N] => apply bWSub_lem0
      | [|- (wordToN _ <= ?x + _ - _)%N] => apply bWSub_lem1
      | [|- (0 <= _)%N] => apply N_ge_0
      end; try assumption.
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
    unfold validBinaryWordOp; intros.
    destruct (overflows n (high0 * high1))%N; repeat split.

    - rewrite <- wordize_mult.

      + apply N.mul_le_mono; assumption.

      + apply (N.le_lt_trans _ (high0 * high1)%N _); [|assumption].
        apply N.mul_le_mono; assumption.

    - transitivity (wordToN x * wordToN y)%N; [apply mult_le|].
      apply N.mul_le_mono; assumption.

    - assumption.
  Qed.

  Lemma range_shiftr_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           Some (range N (N.shiftr low0 high1) (
             if (Nge_dec high0 (Npow2 n))
             then (N.pred (Npow2 n))
             else (N.shiftr high0 low1)))%N
          end)
      (fun x k => extend (Nat.eq_le_incl _ _ eq_refl) (shiftr x (wordToNat k))).
  Proof.
    unfold validBinaryWordOp; intros.
    repeat split; unfold extend; try rewrite wordToN_convS, wordToN_zext.

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
          assumption.

    - destruct (Nge_dec high0 (Npow2 n));
        [apply N.lt_le_pred; apply word_size_bound |].

      etransitivity; [eapply shiftr_bound'; eassumption|].

      rewrite <- (Nat2N.id (wordToNat y)).
      rewrite <- Nshiftr_equiv_nat.
      rewrite N2Nat.id.
      rewrite <- wordToN_nat.
      repeat rewrite N.shiftr_div_pow2.

      apply N.div_le_compat_l; split;
        rewrite <- (N2Nat.id low1);
        [| rewrite <- (N2Nat.id (wordToN y))];
        repeat rewrite <- Npow2_N;
        [apply Npow2_gt0 |].
      apply Npow2_ordered.
      apply to_nat_le.
      assumption.

    - destruct (Nge_dec high0 (Npow2 n)).

      + rewrite <- (N.pred_succ (Npow2 n)).
        apply -> N.pred_lt_mono;
          rewrite (N.pred_succ (Npow2 n));
          [nomega|].
        apply N.neq_0_lt_0.
        apply Npow2_gt0.

      + eapply N.le_lt_trans; [|eassumption].
        rewrite N.shiftr_div_pow2.
        apply N.div_le_upper_bound.

        * induction low1; simpl; intro Z; inversion Z.

        * replace' high0 with (1 * high0)%N at 1
            by (rewrite N.mul_comm; nomega).
          apply N.mul_le_mono; [|reflexivity].
          rewrite <- (N2Nat.id low1).
          rewrite <- Npow2_N.
          apply Npow2_ge1.
  Qed.

  Lemma range_and_valid :
    validBinaryWordOp
      (fun range0 range1 =>
         match (range0, range1) with
         | (range low0 high0, range low1 high1) =>
           let upper := (N.pred (Npow2 (min (N.to_nat (getBits high0)) (N.to_nat (getBits high1)))))%N in
           Some (range N 0%N (
             if (Nge_dec upper (Npow2 n))
             then (N.pred (Npow2 n)) else upper))
          end)
      (@wand n).
  Proof.
    unfold validBinaryWordOp; intros.
    repeat split; [apply N_ge_0 | |].
    destruct (lt_dec (N.to_nat (getBits high0)) (N.to_nat (getBits high1))),
             (Nge_dec _ (Npow2 n));
      try apply N.lt_le_pred;
      try apply word_size_bound.

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
      assumption.

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
      assumption.

    - destruct (Nge_dec _ (Npow2 n)); [|assumption].

      rewrite <- (N.pred_succ (Npow2 n)).
      apply -> N.pred_lt_mono;
        rewrite (N.pred_succ (Npow2 n));
        [nomega|].
      apply N.neq_0_lt_0.
      apply Npow2_gt0.
  Qed.
End RangeUpdate.

Section WordRange.
  Context {n: nat}.

  (* A tree type evaluable to option (range N) *)
  Inductive WordRangeOpt :=
    | noRange: WordRangeOpt
    | someRange: forall (low high: N),
        (low <= high)%N -> (high < Npow2 n)%N -> WordRangeOpt
    | binOpRange: forall rangeF wordF,
        @validBinaryWordOp n rangeF wordF ->
        WordRangeOpt -> WordRangeOpt -> WordRangeOpt.

  Fixpoint rangeEval (r: WordRangeOpt): option (Range N) :=
    match r with
    | noRange => None
    | someRange low high _ _ => Some (range N low high)
    | binOpRange rangeF wordF _ a b =>
      omap (rangeEval a) (fun a' =>
        omap (rangeEval b) (fun b' =>
          rangeF a' b'))
    end.

  Definition inRange (r: WordRangeOpt) (w: word n): Prop :=
    match (rangeEval r) with
    | None => False
    | Some (range low high) =>
        (low <= wordToN w)%N
      /\ (wordToN w <= high)%N
      /\ (high < Npow2 n)%N
    end.

  Lemma rangeEval_Some_spec_low: forall x low high,
    rangeEval x = Some (range N low high)
  -> (low <= high)%N.
  Proof.
    induction x as [| |f g p x1 E1 x2 E2];
      intros low' high' H; simpl in H;
      [ inversion H
      | inversion H; subst; assumption
      | unfold validBinaryWordOp in p].

    destruct (rangeEval x1) as [r1|], (rangeEval x2) as [r2|];
      try destruct r1 as [low1 high1];
      try destruct r2 as [low2 high2];
      simpl in H; inversion H.

    refine (_ (p low1 high1 low2 high2
      (NToWord n low1) (NToWord n low2) _ _ _ _ _ _)).

    - rewrite H; intro H2; destruct H2 as [H2 H3].
      destruct H3 as [H3 H4].
      etransitivity; eassumption.

    - rewrite wordToN_NToWord.
      split; [apply N.eq_le_incl; reflexivity|].
      apply E1; repeat f_equal; reflexivity.

    - rewrite wordToN_NToWord.

      rewrite H in p';
      do 2 rewrite wordToN_NToWord in p'.
    apply p'.
    admit.
    admit.
    admit.
    admit.
      try rewrite <- H in *; clear H.

    - 
    - 
    - 
    - 
  Admitted.

  Lemma rangeEval_Some_spec_high: forall x low high,
    rangeEval x = Some (range N low high)
  -> (high < Npow2 n)%N.
  Proof.
    intros x low high H.
  Admitted.

  Definition wreq a b :=
    rangeEval a = rangeEval b.

  Definition applyBinOp' {rangeF wordF} (a b: WordRangeOpt) 
        (p: @validBinaryWordOp n rangeF wordF):
      {c: WordRangeOpt | wreq c (binOpRange _ _ p a b)}.

    unfold wreq; refine (
      match rangeEval (binOpRange _ _ p a b) as v
        return rangeEval (binOpRange _ _ p a b) = v
        -> {b | rangeEval b = v} with
      | Some (range low high) => fun p =>
        exist _ (someRange low high
          (rangeEval_Some_spec_low _ low high p)
          (rangeEval_Some_spec_high _ low high p)) _
      | None => fun _ => exist _ noRange _
      end eq_refl); abstract auto.
  Defined.

  Definition applyBinOp {f g} (p: @validBinaryWordOp n f g) a b :=
    Eval simpl in proj1_sig (applyBinOp' a b p).

  Definition canApply {f g} (p: @validBinaryWordOp n f g) a b :=
    omap (rangeEval a) (fun ra =>
      omap (rangeEval b) (fun rb =>
        f ra rb)) <> None.

  Lemma applyBinOp_spec: forall {f g} (p: @validBinaryWordOp n f g) a b x y,
      inRange a x
    -> inRange b y
    -> canApply p a b
    -> inRange (applyBinOp p a b) (g x y).
  Proof.
    intros until y; intros Ha Hb Hp.
    unfold applyBinOp; destruct (applyBinOp' a b p) as [c H].
    unfold inRange; cbn; rewrite H; clear H; cbn.
    unfold inRange in Ha, Hb.
    unfold canApply in Hp.
    induction (rangeEval a) as [a'|], (rangeEval b) as [b'|]; auto.
    destruct a' as [low0 high0], b' as [low1 high1]; simpl in *.
    pose proof (p low0 high0 low1 high1 x y) as p'.
    induction (f (range N low0 high0) (range N low1 high1));
      [|apply Hp; reflexivity].
    apply p'; assumption.
  Qed.

  Definition anyWord: WordRangeOpt.
    refine (someRange 0%N (N.pred (Npow2 n)) _ _).
    - apply N.lt_le_pred; apply Npow2_gt0.
    - apply N.lt_pred_l.
      apply N.neq_0_lt_0.
      apply Npow2_gt0.
  Defined.

  Lemma anyWord_spec: forall x, inRange anyWord x.
  Proof.
    intro; cbn; split; [apply N_ge_0 | ].
    apply N.lt_le_pred; apply word_size_bound.
  Qed.

  Definition getLowerBoundOpt (w: WordRangeOpt): option N :=
    omap (rangeEval w) (fun r =>
      match r with | range low high => Some low end).

  Definition getUpperBoundOpt (w: WordRangeOpt): option N :=
    omap (rangeEval w) (fun r =>
      match r with | range low high => Some high end).

  Definition makeRange (low high: N): WordRangeOpt.
    refine (
      match (Nge_dec high low, Nge_dec high (Npow2 n)) with
      | (left _, right _) => someRange low high _ _
      | _ => noRange
      end); [apply N.ge_le|]; assumption.
  Defined.

  Lemma makeRange_spec: forall x low high,
      (low <= wordToN x <= high)%N <-> inRange (makeRange low high) x.
  Proof.
    intros; split; intro H; [destruct H|]; simpl in *;
      unfold inRange, makeRange in *;
      destruct (Nge_dec high low), (Nge_dec high (Npow2 n));
      simpl in *; try split; intuition.

    admit.
    admit.
    admit.
  Qed.

  Definition getOrElse {T} (d: T) (o: option T) :=
    match o with | Some x => x | None => d end.

  Instance WordRangeOptEvaluable : Evaluable WordRangeOpt := {
    ezero := anyWord;

    (* Conversions *)
    toT := fun x => getOrElse anyWord (makeRangeOpt (Z.to_N x) (Z.to_N x));
    fromT := fun x => Z.of_N (getOrElse (N.pred (Npow2 n)) (getUpperBoundOpt x));

    (* Operations *)
    eadd := fun x y => simplifyRange (applyBinOp _ _ range_add_valid x y);
    esub := fun x y => simplifyRange (applyBinOp _ _ range_sub_valid x y);
    emul := fun x y => simplifyRange (applyBinOp _ _ range_mul_valid x y);
    eshiftr := fun x y => simplifyRange (applyBinOp _ _ range_shiftr_valid x y);
    eand := fun x y => simplifyRange (applyBinOp _ _ range_and_valid x y);

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

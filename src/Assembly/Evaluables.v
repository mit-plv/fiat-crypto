Require Import Bedrock.Word Bedrock.Nomega.
Require Import NPeano NArith PArith Ndigits ZArith Znat ZArith_dec Ndec.
Require Import List Basics Bool Nsatz Sumbool Datatypes.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import QhasmUtil WordizeUtil Bounds.
Require Import ProofIrrelevance.

Import ListNotations.

Section BaseTypes.
  Inductive Range T := | range: forall (low high: T), Range T.

  Record RangeWithValue := rwv {
    rwv_low: N;
    rwv_value: N;
    rwv_high: N;
  }.

  Record BoundedWord {n} := bounded {
    bw_low: N;
    bw_value: word n;
    bw_high: N;

    ge_low: (bw_low <= wordToN bw_value)%N;
    le_high: (wordToN bw_value <= bw_high)%N;
    high_bound: (bw_high < Npow2 n)%N;
  }.
End BaseTypes.

Section Evaluability.
  Class Evaluable T := evaluator {
    ezero: T;

    (* Conversions *)
    toT: option RangeWithValue -> T;
    fromT: T -> option RangeWithValue;

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
  Context {n: nat}.
  Instance ZEvaluable : Evaluable Z := {
    ezero := 0%Z;

    (* Conversions *)
    toT     := fun x => Z.of_N (orElse 0%N (option_map rwv_value x));
    fromT   := fun x =>
      if (Nge_dec (N.pred (Npow2 n)) (Z.to_N x))
      then Some (rwv (Z.to_N x) (Z.to_N x) (Z.to_N x))
      else None;

    (* Operations *)
    eadd    := Z.add;
    esub    := Z.sub;
    emul    := Z.mul;
    eshiftr := Z.shiftr;
    eand    := Z.land;

    (* Comparisons *)
    eltb    := Z.ltb;
    eeqb    := Z.eqb
  }.
End Z.

Section Word.
  Context {n: nat}.

  Instance WordEvaluable : Evaluable (word n) := {
    ezero := wzero n;

    (* Conversions *)
    toT := fun x => @NToWord n (orElse 0%N (option_map rwv_value x));
    fromT := fun x => let v := @wordToN n x in (Some (rwv v v v));

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

    Lemma bWSub_lem: forall (x0 x1: word n) (low0 high1: N),
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
               high0 - low1)%N)
           else None
         end)
      (@wminus n).
  Proof.
    unfold validBinaryWordOp; intros.

    Ltac kill_preds :=
      repeat match goal with
      | [|- (N.pred _ < _)%N] =>
        rewrite <- (N.pred_succ (Npow2 n));
          apply -> N.pred_lt_mono; instantiate;
          rewrite N.pred_succ;
        [ apply N.lt_succ_diag_r
        | apply N.neq_0_lt_0; apply Npow2_gt0]
      | [|- (wordToN _ <= N.pred _)%N] => apply N.lt_le_pred
      end.

    destruct (Nge_dec high0 (Npow2 n)),
             (Nge_dec high1 (Npow2 n)),
             (Nge_dec low0 high1);
      repeat split; kill_preds;
      repeat match goal with
      | [|- (wordToN _ < Npow2 _)%N] => apply word_size_bound
      | [|- (?x - _ < Npow2)%N] => transitivity x; [nomega|]
      | [|- (_ - ?x <= wordToN _)%N] => apply bWSub_lem
      | [|- (wordToN _ <= _ - _)%N] => eapply wminus_bound
      | [|- (0 <= _)%N] => apply N_ge_0
      end; try eassumption.

    - apply N.le_ge.
      transitivity high1; [assumption|].
      transitivity low0; [|assumption].
      apply N.ge_le; assumption.

    - apply (N.le_lt_trans _ high0 _); [|assumption].
      replace high0 with (high0 - 0)%N by nomega.
      replace' (high0 - 0)%N with high0 at 1 by nomega.
      apply N.sub_le_mono_l.
      apply N.ge_le; nomega.
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
        apply -> N.pred_lt_mono; instantiate;
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
           Some (range N 0%N (if (Nge_dec upper (Npow2 n)) then (N.pred (Npow2 n)) else upper))
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
      apply -> N.pred_lt_mono; instantiate;
        rewrite (N.pred_succ (Npow2 n));
        [nomega|].
      apply N.neq_0_lt_0.
      apply Npow2_gt0.
  Qed.
End RangeUpdate.

Section BoundedWord.
  Context {n: nat}.

  Definition BW := @BoundedWord n.
  Transparent BW.

  Definition bapp {rangeF wordF}
      (op: @validBinaryWordOp n rangeF wordF)
      (X Y: BW): option BW.

    refine (
      let op' := op _ _ _ _ _ _
        (ge_low X) (le_high X) (high_bound X)
        (ge_low Y) (le_high Y) (high_bound Y) in

      let result := rangeF
        (range N (bw_low X) (bw_high X))
        (range N (bw_low Y) (bw_high Y)) in

      match result as r' return result = r' -> _ with
      | Some (range low high) => fun e =>
        Some (@bounded n low (wordF (bw_value X) (bw_value Y)) high _ _ _)
      | None => fun _ => None
      end eq_refl); abstract (

      pose proof op' as p; clear op';
      unfold result in *;
      rewrite e in p;
      destruct p as [p0 p1]; destruct p1 as [p1 p2];
      assumption).
  Defined.

  Definition rapp {rangeF wordF}
      (op: @validBinaryWordOp n rangeF wordF)
      (X Y: Range N): option (Range N) :=
    rangeF X Y.

  Definition vapp {rangeF wordF}
      (op: @validBinaryWordOp n rangeF wordF)
      (X Y: word n): option (word n) :=
    Some (wordF X Y).

  Definition bwToRWV (w: BW): RangeWithValue :=
    rwv (bw_low w) (wordToN (bw_value w)) (bw_high w).

  Definition bwFromRWV (r: RangeWithValue): option BW.
    refine
      match r with
      | rwv l v h =>
        match (Nge_dec h v, Nge_dec v l, Nge_dec (N.pred (Npow2 n)) h) with
        | (left p0, left p1, left p2) => Some (@bounded n l (NToWord n l) h _ _ _)
        | _ => None
        end
      end; try rewrite wordToN_NToWord;

      assert (N.succ h <= Npow2 n)%N by abstract (
        apply N.ge_le in p2;
        rewrite <- (N.pred_succ h) in p2;
        apply -> N.le_pred_le_succ in p2;
        rewrite N.succ_pred in p2; [assumption |];
        apply N.neq_0_lt_0;
        apply Npow2_gt0);

      try abstract (apply (N.lt_le_trans _ (N.succ h) _);
        [nomega|assumption]);

      [reflexivity| etransitivity; apply N.ge_le; eassumption].
  Defined.

  Definition bwToRange (w: BW): Range N :=
    range N (bw_low w) (bw_high w).

  Definition bwFromRange (r: Range N): option BW.
    refine
      match r with
      | range l h =>
        match (Nge_dec h l, Nge_dec (N.pred (Npow2 n)) h) with
        | (left p0, left p1) => Some (@bounded n l (NToWord n l) h _ _ _)
        | _ => None
        end
      end; try rewrite wordToN_NToWord;

      assert (N.succ h <= Npow2 n)%N by abstract (
        apply N.ge_le in p1;
        rewrite <- (N.pred_succ h) in p1;
        apply -> N.le_pred_le_succ in p1;
        rewrite N.succ_pred in p1; [assumption |];
        apply N.neq_0_lt_0;
        apply Npow2_gt0);

      try abstract (apply (N.lt_le_trans _ (N.succ h) _);
        [nomega|assumption]);

      [reflexivity|apply N.ge_le; assumption].
  Defined.

  Definition just (x: N): option BW.
    refine
      match Nge_dec (N.pred (Npow2 n)) x with
      | left p => Some (@bounded n x (NToWord n x) x _ _ _)
      | right _ => None
      end; try rewrite wordToN_NToWord; try reflexivity;

    assert (N.succ x <= Npow2 n)%N by abstract (
        apply N.ge_le in p;
        rewrite <- (N.pred_succ x) in p;
        apply -> N.le_pred_le_succ in p;
        rewrite N.succ_pred in p; [assumption |];
        apply N.neq_0_lt_0;
        apply Npow2_gt0);

    try abstract (
      apply (N.lt_le_trans _ (N.succ x) _);
        [nomega|assumption]).
  Defined.

  Lemma just_None_spec: forall x, just x = None -> (x >= Npow2 n)%N.
  Proof.
    intros x H; unfold just in *.
    destruct (Nge_dec (N.pred (Npow2 n)) x) as [p|p]; [inversion H |].
    rewrite <- (N.pred_succ x) in p.
    apply N.lt_pred_lt_succ in p.
    rewrite N.succ_pred in p; [|apply N.neq_0_lt_0; nomega].
    apply N.le_succ_l in p.
    apply N.le_ge; apply N.succ_le_mono; assumption.
  Qed.

  Lemma just_value_spec: forall x b, just x = Some b -> bw_value b = NToWord n x.
  Proof.
    intros x b H; destruct b; unfold just in *;
    destruct (Nge_dec (N.pred (Npow2 n)) x);
    simpl in *; inversion H; subst; reflexivity.
  Qed.

  Lemma just_low_spec: forall x b, just x = Some b -> bw_low b = x.
  Proof.
    intros x b H; destruct b; unfold just in *;
    destruct (Nge_dec (N.pred (Npow2 n)) x);
    simpl in *; inversion H; subst; reflexivity.
  Qed.

  Lemma just_high_spec: forall x b, just x = Some b -> bw_high b = x.
  Proof.
    intros x b H; destruct b; unfold just in *;
    destruct (Nge_dec (N.pred (Npow2 n)) x);
    simpl in *; inversion H; subst; reflexivity.
  Qed.

  Definition any: BW.
    refine (@bounded n 0%N (wzero n) (N.pred (Npow2 n)) _ _ _);
      try rewrite wordToN_zero;
      try reflexivity;
      try abstract (apply N.lt_le_pred; apply Npow2_gt0).

    apply N.lt_pred_l; apply N.neq_0_lt_0; apply Npow2_gt0.
  Defined.

  Instance BoundedEvaluable : Evaluable (option BW) := {
    ezero := Some any;

    toT := fun x => omap x bwFromRWV;
    fromT := option_map bwToRWV;

    eadd := fun x y => omap x (fun X => omap y (fun Y => bapp range_add_valid X Y));
    esub := fun x y => omap x (fun X => omap y (fun Y => bapp range_sub_valid X Y));
    emul := fun x y => omap x (fun X => omap y (fun Y => bapp range_mul_valid X Y));
    eshiftr := fun x y => omap x (fun X => omap y (fun Y => bapp range_shiftr_valid X Y));
    eand := fun x y => omap x (fun X => omap y (fun Y => bapp range_and_valid X Y));

    eltb := fun x y =>
      orElse false (omap x (fun X => omap y (fun Y => 
        Some (N.ltb (wordToN (bw_value X)) (wordToN (bw_value Y))))));

    eeqb := fun x y =>
      orElse false (omap x (fun X => omap y (fun Y => 
        Some (N.eqb (wordToN (bw_value X)) (wordToN (bw_value Y))))))
  }.
End BoundedWord.

Section RangeWithValue.
  Context {n: nat}.

  Definition rwv_app {rangeF wordF}
    (op: @validBinaryWordOp n rangeF wordF)
    (X Y: RangeWithValue): option (RangeWithValue) :=
    omap (rangeF (range N (rwv_low X) (rwv_high X))
                 (range N (rwv_low Y) (rwv_high Y))) (fun r' =>
      match r' with
      | range l h => Some (
          rwv l (wordToN (wordF (NToWord n (rwv_value X))
                                (NToWord n (rwv_value Y)))) h)
      end).

  Definition checkRWV (x: RangeWithValue): bool :=
    match x with
    | rwv l v h =>
      match (Nge_dec h v, Nge_dec v l, Nge_dec (N.pred (Npow2 n)) h) with
      | (left p0, left p1, left p2) => true
      | _ => false
      end
    end.

  Lemma rwv_None_spec : forall {rangeF wordF}
      (op: @validBinaryWordOp n rangeF wordF)
      (X Y: RangeWithValue),
    omap (rwv_app op X Y) (bwFromRWV (n := n)) <> None.
  Proof.
  Admitted.

  Definition rwvToRange (x: RangeWithValue): Range N :=
    range N (rwv_low x) (rwv_high x).

  Definition rwvFromRange (x: Range N): RangeWithValue :=
    match x with
    | range l h => rwv l h h
    end.

  Lemma bwToFromRWV: forall x, option_map (@bwToRWV n) (omap x bwFromRWV) = x.
  Proof.
  Admitted.

  Instance RWVEvaluable : Evaluable (option RangeWithValue) := {
    ezero := None;

    toT := fun x => x;
    fromT := fun x => omap x (fun x' =>
      if (checkRWV x') then x else None);

    eadd := fun x y => omap x (fun X => omap y (fun Y =>
      rwv_app range_add_valid X Y));

    esub := fun x y => omap x (fun X => omap y (fun Y =>
      rwv_app range_sub_valid X Y));

    emul := fun x y => omap x (fun X => omap y (fun Y =>
      rwv_app range_mul_valid X Y));

    eshiftr := fun x y => omap x (fun X => omap y (fun Y =>
      rwv_app range_shiftr_valid X Y));

    eand := fun x y => omap x (fun X => omap y (fun Y =>
      rwv_app range_and_valid X Y));

    eltb := fun x y =>
      match (x, y) with
      | (Some (rwv xlow xv xhigh), Some (rwv ylow yv yhigh)) =>
          N.ltb xv yv

      | _ => false 
      end;

    eeqb := fun x y =>
      match (x, y) with
      | (Some (rwv xlow xv xhigh), Some (rwv ylow yv yhigh)) =>
          andb (andb (N.eqb xlow ylow) (N.eqb xhigh yhigh)) (N.eqb xv yv)

      | _ => false
      end;
  }.
End RangeWithValue.

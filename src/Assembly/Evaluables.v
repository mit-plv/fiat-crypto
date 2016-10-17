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
    toT     := id;
    fromT   := id;

    (* Operations *)
    eadd    := Z.add;
    esub    := Z.sub;
    emul    := Z.mul;
    eshiftr := Z.shiftr;
    eand    := Z.land;

    (* Comparisons *)
    eltb    := Z.ltb;
    eeqb    := Z.eqb;
  }.

End Z.

Section Word.
  Context {n: nat}.

  Instance WordEvaluable : Evaluable (word n) := {
    ezero := wzero n;

    (* Conversions *)
    toT := fun x => @NToWord n (Z.to_N x);
    fromT := fun x => Z.of_N (@wordToN n x);

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
          apply -> N.pred_lt_mono;
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
      apply -> N.pred_lt_mono;
        rewrite (N.pred_succ (Npow2 n));
        [nomega|].
      apply N.neq_0_lt_0.
      apply Npow2_gt0.
  Qed.
End RangeUpdate.

Section BoundedWord.
  Context {n: nat}.

  Record BoundedWord := bounded {
    low: N;
    value: word n;
    high: N;

    ge_low: (low <= wordToN value)%N;
    le_high: (wordToN value <= high)%N;
    high_bound: (high < Npow2 n)%N;
  }.

  Definition make (l: N) (v: word n) (h: N): option (BoundedWord).
    refine
      match (Nge_dec (wordToN v) l,
             Nge_dec h (wordToN v),
             Nge_dec (N.pred (Npow2 n)) h) with
      | (left p0, left p1, left p2) => Some (bounded l v h _ _ _)
      | _ => None
      end; try (apply N.ge_le; assumption); abstract (
        apply N.ge_le in p2;
        apply (N.lt_le_trans _ (N.succ h) _); [nomega|];
        rewrite <- (N.pred_succ h) in p2;
        apply -> N.le_pred_le_succ in p2;
        rewrite N.succ_pred in p2; [assumption |];
        apply N.neq_0_lt_0;
        apply Npow2_gt0).
  Defined.

  Lemma make_low_spec: forall l v h b, make l v h = Some b -> low b = l.
  Proof.
    intros l v h b H; unfold make in H; simpl;
      repeat destruct (Nge_dec _ _); inversion_clear H;
      simpl; reflexivity.
  Qed.
  
  Lemma make_value_spec: forall l v h b, make l v h = Some b -> value b = v.
  Proof.
    intros l v h b H; unfold make in H; simpl;
      repeat destruct (Nge_dec _ _); inversion_clear H;
      simpl; reflexivity.
  Qed.

  Lemma make_high_spec: forall l v h b, make l v h = Some b -> high b = h.
  Proof.
    intros l v h b H; unfold make in H; simpl;
      repeat destruct (Nge_dec _ _); inversion_clear H;
      simpl; reflexivity.
  Qed.
 
  Definition bapp {rangeF wordF}
      (op: @validBinaryWordOp n rangeF wordF)
      (X Y: BoundedWord): option BoundedWord.

    refine (
      match (rangeF (range N (low X) (high X))
                    (range N (low Y) (high Y))) as r'
          return _ = r' -> _ with
      | Some (range low high) => fun _ =>
        Some (bounded low (wordF (value X) (value Y)) high _ _ _)
      | _ => fun _ => None
      end eq_refl);

      pose proof (op _ _ _ _ _ _
            (ge_low X) (le_high X) (high_bound X)
            (ge_low Y) (le_high Y) (high_bound Y)) as p';

      rewrite e in p';
      destruct p' as [p0 p1]; destruct p1 as [p1 p2];
      assumption.
  Defined.

  Definition any: BoundedWord.
    refine (bounded 0%N (wzero n) (N.pred (Npow2 n)) _ _ _);
      try rewrite wordToN_zero;
      try reflexivity;
      try abstract (apply N.lt_le_pred; apply Npow2_gt0).

    apply N.lt_pred_l; apply N.neq_0_lt_0; apply Npow2_gt0.
  Defined.

  Definition orElse {T} (d: T) (o: option T): T :=
    match o with
    | Some v => v
    | None => d
    end.

  Instance BoundedEvaluable : Evaluable (option BoundedWord) := {
    ezero := Some any;

    toT := fun x => make (Z.to_N x) (NToWord _ (Z.to_N x)) (Z.to_N x);
    fromT := fun x => orElse 0%Z (option_map (fun x' => Z.of_N (wordToN (value x'))) x);

    eadd := fun x y => omap x (fun X => omap y (fun Y => bapp range_add_valid X Y));
    esub := fun x y => omap x (fun X => omap y (fun Y => bapp range_sub_valid X Y));
    emul := fun x y => omap x (fun X => omap y (fun Y => bapp range_mul_valid X Y));
    eshiftr := fun x y => omap x (fun X => omap y (fun Y => bapp range_shiftr_valid X Y));
    eand := fun x y => omap x (fun X => omap y (fun Y => bapp range_and_valid X Y));

    eltb := fun x y =>
      orElse false (omap x (fun X => omap y (fun Y => 
        Some (N.ltb (high X) (high Y)))));

    eeqb := fun x y =>
      orElse false (omap x (fun X => omap y (fun Y => 
        Some (andb (N.eqb (low X) (low Y)) (N.eqb (high X) (high Y))))))
  }.

End BoundedWord.

Section Range.
  Context {n: nat}.

  Definition rapp {f g} (op: @validBinaryWordOp n f g) (x y: Range N):
      option (Range N) := f x y.

  Instance RangeEvaluable : Evaluable (option (Range N)) := {
    ezero := Some (range N 0%N (N.pred (Npow2 n)));

    toT := fun x => Some (range N (Z.to_N x) (Z.to_N x));
    fromT := fun x => orElse 0%Z (omap x (fun r =>
      match r with
      | range low high => Some (Z.of_N high)
      end));

    eadd := fun x y => omap x (fun X => omap y (fun Y => rapp range_add_valid X Y));
    esub := fun x y => omap x (fun X => omap y (fun Y => rapp range_sub_valid X Y));
    emul := fun x y => omap x (fun X => omap y (fun Y => rapp range_mul_valid X Y));
    eshiftr := fun x y => omap x (fun X => omap y (fun Y => rapp range_shiftr_valid X Y));
    eand := fun x y => omap x (fun X => omap y (fun Y => rapp range_and_valid X Y));

    eltb := fun x y =>
      match (x, y) with
      | (Some (range xlow xhigh), Some (range ylow yhigh)) =>
        N.ltb xhigh yhigh

      | _ => false 
      end;

    eeqb := fun x y =>
      match (x, y) with
      | (Some (range xlow xhigh), Some (range ylow yhigh)) =>
        andb (N.eqb xlow ylow) (N.eqb xhigh yhigh)

      | _ => false
      end;
  }.
End Range.

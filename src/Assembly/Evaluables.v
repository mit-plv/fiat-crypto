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
    eshiftr: T -> nat -> T;
    emask: T -> nat -> T;

    (* Comparisons *)
    eltb: T -> T -> bool;
    eeqb: T -> T -> bool
  }.
End Evaluability.

Section Z.
  Definition Zmask := fun x k => Z.land x (Z.ones (Z.of_nat k)).
  Definition Zshiftr := fun x k => Z.shiftr x (Z.of_nat k).

  Instance ZEvaluable : Evaluable Z := {
    ezero := 0%Z;

    (* Conversions *)
    toT := id;
    fromT := id;

    (* Operations *)
    eadd := Z.add;
    esub := Z.sub;
    emul := Z.mul;
    eshiftr := Zshiftr;
    emask := Zmask;

    (* Comparisons *)
    eltb := Z.ltb;
    eeqb := Z.eqb;
  }.

  (* Some witch magic *)
  Section NatOpConversion.
    Definition getBits (x: Z) := Z.log2 (x + 1).

    Definition Zland_fail_sig: {f: Z->Z->Z | forall x y, f x y = Z.land x y}.
    Proof. exists Z.land; intros; reflexivity. Qed.

    Definition Zshiftr_fail_sig: {f: Z->Z->Z | forall x y, f x y = Z.shiftr x y}.
    Proof. exists Z.shiftr; intros; reflexivity. Qed.

    Definition Zland_fail := proj1_sig Zland_fail_sig.
    Definition Zshiftr_fail := proj1_sig Zshiftr_fail_sig.

    Lemma replace_mask : forall a b,
      Z.land a b =
        match Z.eq_dec b (Z.ones (getBits b)) with
        | left _ => Zmask a (Z.to_nat (getBits b))
        | right _ => Zland_fail a b
        end.
    Proof.
      intros; unfold Zmask, Zland_fail.
      destruct Zland_fail_sig as [f p], (Z.eq_dec _ _) as [e|];
        [| simpl; rewrite p; reflexivity ].
      f_equal.
      rewrite Z2Nat.id; [assumption|].
      apply Z.log2_nonneg.
    Qed.

    Lemma replace_shiftr : forall a b,
      Z.shiftr a b =
        match b as b' return b = b' -> _ with
        | Zpos _ => fun _ => Zshiftr a (Z.to_nat b)
        | Z0 => fun _ => a 
        | _ => fun _ => Zshiftr_fail a b
        end eq_refl.
    Proof.
      intros; unfold Zshiftr, Zshiftr_fail.
      induction Zshiftr_fail_sig as [f p], b;
        [cbv; intuition | | simpl; rewrite p; reflexivity].
      rewrite Z2Nat.id; [reflexivity|].
      cbv; intro H; inversion H.
    Qed.

    Lemma kill_eq_dec_refl: forall a,
        Z.eq_dec a a = left eq_refl.
    Proof.
      intros; destruct (Z.eq_dec a a) as [H|H];
        [ f_equal; apply proof_irrelevance | contradict H; reflexivity ].
    Qed.
  End NatOpConversion.
End Z.

(* Tactic to automagically replace_mask and replace_shiftr *)
Ltac natize_mask_and_shiftr :=
  repeat rewrite replace_mask;
  repeat rewrite replace_shiftr;
  repeat progress match goal with
  | [ |- context[Z.eq_dec ?a (Z.ones (getBits ?a))] ] =>
    replace (Z.ones (getBits a)) with a by (vm_compute; reflexivity);
      rewrite (kill_eq_dec_refl a)
  end.

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
    eshiftr := @shiftr n;
    emask := fun x k => @mask n k x;

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
    validNatWordOp
      (fun range0 k =>
         match range0 with
         | range low high =>
           Some (range N
             (N.shiftr low (N.of_nat k))
             (N.succ (N.shiftr high (N.of_nat k))))
          end)
      (fun x k => extend (Nat.eq_le_incl _ _ eq_refl) (shiftr x k)).
  Proof.
    unfold validNatWordOp; intros until x; intro H.
    destruct H as [Ha Hb]; split.

    - unfold extend; rewrite wordToN_convS.

      rewrite wordToN_zext.
      rewrite <- wordize_shiftr.
      rewrite <- Nshiftr_equiv_nat.
      repeat rewrite N.shiftr_div_pow2.
      apply N.div_le_mono; [|assumption].
      induction k.

      + cbv beta delta iota; intro Z; inversion Z.

      + rewrite <- Npow2_N.
        pose proof (Npow2_gt0 (S k)).
        nomega.

    - unfold extend; rewrite wordToN_convS.
      rewrite wordToN_zext.
      rewrite Nshiftr_equiv_nat.
      eapply N.lt_le_trans.

      + apply shiftr_bound; eassumption.

      + apply N.eq_le_incl.
        reflexivity.
  Qed.

  Lemma range_mask_valid :
    validNatWordOp
      (fun range0 k =>
         match range0 with
         | range low high =>
           Some (range N 0%N (Npow2 k))
          end)
      (fun x k => mask k x).
  Proof.
    unfold validNatWordOp; intros until x; intro H.
    destruct H as [Ha Hb]; split; [apply N_ge_0|].
    apply mask_bound.
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
    eshiftr := applyNatOp _ _ range_shiftr_valid;
    emask := applyNatOp _ _ range_mask_valid;

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

Require Import Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec.
Require Import List Omega NArith Nnat BoolEq.
Require Import QhasmUtil QhasmEvalCommon.
Require Import ProofIrrelevance FunctionalExtensionality.

Section Misc.
  Local Open Scope nword_scope.

  Lemma word_replace: forall n m, n = m -> word n = word m.
  Proof. intros; subst; intuition. Qed.

  Lemma of_nat_lt: forall x b, (x < b)%nat <-> (N.of_nat x < N.of_nat b)%N.
  Proof.
    intros x b; split; intro H.

    - unfold N.lt; rewrite N2Nat.inj_compare.
      repeat rewrite Nat2N.id.
      apply Nat.compare_lt_iff in H.
      intuition.

    - unfold N.lt in H; rewrite N2Nat.inj_compare in H.
      repeat rewrite Nat2N.id in H.
      apply Nat.compare_lt_iff in H.
      intuition.
  Qed.

  Lemma to_nat_lt: forall x b, (x < b)%N <-> (N.to_nat x < N.to_nat b)%nat.
  Proof.
    intros x b; split; intro H.

    - unfold N.lt in H; rewrite N2Nat.inj_compare in H.
      apply Nat.compare_lt_iff in H.
      intuition.

    - unfold N.lt; rewrite N2Nat.inj_compare.
      apply Nat.compare_lt_iff.
      intuition.
  Qed.

  Lemma word_size_bound : forall {n} (w: word n), (&w < Npow2 n)%N.
  Proof.
    intros; pose proof (wordToNat_bound w) as B;
      rewrite of_nat_lt in B;
      rewrite <- Npow2_nat in B;
      rewrite N2Nat.id in B;
      rewrite <- wordToN_nat in B;
      assumption.
  Qed.
End Misc.

Section Exp.
  Local Open Scope nword_scope.

  Lemma pow2_inv : forall n m, pow2 n = pow2 m -> n = m.
  Proof.
    induction n; intros; simpl in *;
        induction m; simpl in *; intuition.
  Qed.

  Lemma pow2_gt0 : forall n, (pow2 n > O)%nat.
  Proof. induction n; simpl; omega. Qed.

  Lemma pow2_N_bound: forall n j,
    (j < pow2 n)%nat -> (N.of_nat j < Npow2 n)%N.
  Proof.
    intros.
    rewrite <- Npow2_nat in H.
    unfold N.lt.
    rewrite N2Nat.inj_compare.
    rewrite Nat2N.id.
    apply Nat.compare_lt_iff in H.
    assumption.
  Qed.

  Lemma Npow2_gt0 : forall x, (0 < Npow2 x)%N.
  Proof.
    intros; induction x.

    - simpl; apply N.lt_1_r; intuition.

    - replace (Npow2 (S x)) with (2 * (Npow2 x))%N by intuition.
        apply (N.lt_0_mul 2 (Npow2 x)); left; split; apply N.neq_0_lt_0.

      + intuition; inversion H.

      + apply N.neq_0_lt_0 in IHx; intuition.
  Qed.

  Lemma Npow2_split: forall a b,
    (Npow2 (a + b) = (Npow2 a) * (Npow2 b))%N.
  Proof.
    intros; revert a.
    induction b.

    - intros; simpl; replace (a + 0) with a; try nomega.
      rewrite N.mul_1_r; intuition.

    - intros.
      replace (a + S b) with (S a + b) by intuition.
      rewrite (IHb (S a)); simpl; clear IHb.
      induction (Npow2 a), (Npow2 b); simpl; intuition.
      rewrite Pos.mul_xO_r; intuition.
  Qed.
End Exp.

Section Conversions.
  Local Open Scope nword_scope.

  Lemma NToWord_wordToN: forall sz x, NToWord sz (wordToN x) = x.
  Proof.
    intros.
    rewrite NToWord_nat.
    rewrite wordToN_nat.
    rewrite Nat2N.id.
    rewrite natToWord_wordToNat.
    intuition.
  Qed.

  Lemma wordToN_NToWord: forall sz x, (x < Npow2 sz)%N -> wordToN (NToWord sz x) = x.
  Proof.
    intros.
    rewrite NToWord_nat.
    rewrite wordToN_nat.
    rewrite <- (N2Nat.id x).
    apply Nat2N.inj_iff.
    rewrite Nat2N.id.
    apply natToWord_inj with (sz:=sz);
      try rewrite natToWord_wordToNat;
      intuition.

    - apply wordToNat_bound.
    - rewrite <- Npow2_nat; apply to_nat_lt; assumption.
  Qed.

  Lemma Npow2_ignore: forall {n} (x: word n),
    x = NToWord _ (& x + Npow2 n).
  Proof.
    intros.
    rewrite <- (NToWord_wordToN n x) at 1.
    repeat rewrite NToWord_nat.
    rewrite N2Nat.inj_add.
    rewrite Npow2_nat.
    replace (N.to_nat (&x))
       with ((N.to_nat (&x) + pow2 n) - 1 * pow2 n)
         at 1 by omega.
    rewrite drop_sub; intuition.
  Qed.
End Conversions.

Section Enumerability.
  Class Enumerable A := {
    elements : list A;
    correct : forall x: A, In x elements;
    good: NoDup elements;
    }.

  Arguments elements _ {_}.

  Definition word_elements (n: nat): list (word n) :=
    map (natToWord n) (seq O (pow2 n)).

  Lemma word_index_correct : forall n (x: word n),
    x = nth (wordToNat x) (word_elements n) (natToWord _ 0).
  Proof.
    intros; unfold word_elements.
    rewrite map_nth.
    rewrite seq_nth; try apply wordToNat_bound; simpl.
    rewrite natToWord_wordToNat.
    reflexivity.
  Qed.

  Lemma word_elements_correct: forall n (x: word n),
      In x (word_elements n).
  Proof.
    intros; unfold word_elements.
    destruct (nth_in_or_default (wordToNat x) (word_elements n) (natToWord _ 0)).

    - rewrite <- word_index_correct in i.
        assumption.

    - rewrite <- word_index_correct in e.
        apply in_map_iff.
        exists 0; split; simpl; intuition.
        apply in_seq.
        pose proof (pow2_gt0 n).
        omega.
  Qed.

  Lemma word_elements_good: forall n, NoDup (word_elements n).
  Proof.
    intros; unfold word_elements.

    apply <- (NoDup_nth (map (natToWord n) (seq 0 (pow2 n))) (natToWord _ 0)).

    intros; repeat rewrite map_nth in H1.

    rewrite map_length in H, H0.
    rewrite seq_length in H, H0.

    replace (nth i (seq 0 (pow2 n)) 0) with i in H1
        by (rewrite seq_nth; simpl; intuition).
    replace (nth j (seq 0 (pow2 n)) 0) with j in H1
        by (rewrite seq_nth; simpl; intuition).

    rewrite <- (@wordToNat_natToWord_idempotent n i);
        try apply pow2_N_bound; intuition
    rewrite <- (@wordToNat_natToWord_idempotent n j);
        try apply pow2_N_bound; intuition
    rewrite H1; intuition.

  Qed.

  Instance word_enumerable: forall n, Enumerable (word n) := {
    elements := word_elements n;
    correct := word_elements_correct n;
    good := word_elements_good n
  }.

  Lemma word_enum_correct: forall n e, length (@elements (word n) e) = pow2 n.
  Proof.
    intros.
    destruct e as [nelem ncorrect ngood].
    induction n.

    - simpl; inversion ngood.

      + rewrite <- H in ncorrect.
        pose proof (ncorrect WO).
        inversion H0.

      + rewrite (shatter_word_0 x) in *.
        destruct (list_eq_dec (@weq 0) l nil); subst; intuition.
        contradict H.
        induction l.

        * apply n; intuition.

        * rewrite (shatter_word_0 a).
          intuition.

    - replace (pow2 (S n)) with (2 * pow2 n) by (simpl; intuition).
      unfold elements; cbv zeta.

      assert (exists l1 l2, partition (@whd _) nelem = (l1, l2)) as H by (
        destruct (partition (@whd _) nelem) as [l l0];
                  exists l; exists l0; intuition).

      destruct H as [l1 H].
      destruct H as [l2 H].

      assert (forall x : word n, In x (map (split2 1 n) l1))
          as ncorrect1. {
        intro. clear ngood IHn.

        replace x with (split2 1 n (WS true x)) by (simpl; intuition).
        apply in_map.

        pose proof (ncorrect (WS true x)) as ncorrect'; clear ncorrect.

        revert ncorrect'; revert x H; revert l1 l2; induction nelem; intros.

        - inversion ncorrect'.

        - destruct ncorrect'; subst.

          + simpl in H.
            destruct (partition (whd (sz:=n)) nelem) as [g d].
            inversion H.
            intuition.

          + simpl in H; destruct (whd a); simpl in H;
              destruct (partition (whd (sz:=n)) nelem) as [g d];
              inversion H; subst; clear H.

            * right; apply (IHnelem g l2); intuition.

            * apply (IHnelem l1 d); intuition.
      }

      assert (forall x : word n, In x (map (split2 1 n) l2))
          as ncorrect2. {
        intro. clear ngood IHn ncorrect1.

        replace x with (split2 1 n (WS false x)) by (simpl; intuition).
        apply in_map.

        pose proof (ncorrect (WS false x)) as ncorrect'; clear ncorrect.

        revert ncorrect'; revert x H; revert l1 l2; induction nelem; intros.

        - inversion ncorrect'.

        - destruct ncorrect'; subst.

          + simpl in H.
            destruct (partition (whd (sz:=n)) nelem) as [g d].
            inversion H.
            intuition.

          + simpl in H; destruct (whd a); simpl in H;
              destruct (partition (whd (sz:=n)) nelem) as [g d];
              inversion H; subst; clear H.

            * apply (IHnelem g); intuition.

            * right; apply (IHnelem l1); intuition.
      }

      assert (NoDup (map (split2 1 n) l1)) as ngood1. {
        clear ncorrect1 ncorrect2 IHn ncorrect.
        revert ngood H; revert l1 l2; induction nelem; intros.

        - simpl in H; inversion H; subst; clear H.
            simpl; constructor.

        - inversion ngood; subst; clear ngood.

          assert (exists g d, partition (@whd n) nelem = (g, d)) as E by (
                destruct (partition _ _) as [g d]; exists g; exists d; intuition);
          destruct E as [g E]; destruct E as [d E].

          pose proof (elements_in_partition _ _ E) as I.

          destruct (shatter_word_S a) as [b Q].
          destruct Q as [a' Ha].
          rewrite Ha in *; simpl in H.

          simpl in H; destruct b; rewrite E in *;
            inversion H; subst; clear H.

          + constructor. 

            * intro H; clear IHnelem.

              pose proof (@in_map_iff (word (S n)) (word n) (@wtl n) g a') as M.
              apply M in H; clear M; destruct H; destruct H as [Ha Hb].
              assert (whd x = true) as Hhd. {
                clear I H2 H3 Ha a'.
                destruct (shatter_word_S x) as [b H];
                  destruct H as [x' H]; rewrite H in *; clear H x; simpl.

                revert Hb E. revert x' b g l2.
                induction nelem; intros; simpl in E.

                - inversion E; subst.
                    inversion Hb.

                - simpl in E;
                    destruct (bool_dec (whd a) true) as [B|B];
                    destruct (partition (whd (sz:=n)) nelem) as [g' d'].

                  + rewrite B in E; inversion E; subst; clear E;
                      destruct Hb.

                    * rewrite H in *; simpl in B; intuition.

                    * apply (IHnelem x' b g' l2); intuition.

                  + assert (whd a = false) as B' by (
                      induction (whd a); intuition); clear B.

                    rewrite B' in E. inversion E. subst. clear E.
                    apply (IHnelem x' b g d'); intuition.
              }

              destruct (shatter_word_S x) as [b H].
              destruct H as [x' H].
              rewrite H in *; simpl in *; clear H.
              rewrite Hhd in Hb.
              rewrite Ha in Hb.
              assert (In (a'~1) g \/ In (a'~1) l2) as Q by intuition.
              apply I in Q.
              intuition.

            * apply (IHnelem g l2); intuition.

            + apply (IHnelem _ d); intuition.
      }

      assert (NoDup (map (split2 1 n) l2)) as ngood2. {
        clear ncorrect1 ncorrect2 IHn ncorrect ngood1.
        revert ngood H; revert l1 l2; induction nelem; intros.

        - simpl in H; inversion H; subst; clear H.
          simpl; constructor.

        - inversion ngood; subst; clear ngood.

          assert (exists g d, partition (@whd n) nelem = (g, d)) as E by (
              destruct (partition _ _) as [g d]; exists g; exists d; intuition);
            destruct E as [g E];
            destruct E as [d E].

          pose proof (elements_in_partition _ _ E) as I.

          destruct (shatter_word_S a) as [b Q].
          destruct Q as [a' Ha].
          rewrite Ha in *; simpl in H.

          simpl in H; destruct b; rewrite E in *;
          inversion H; subst; clear H.

          + apply (IHnelem g l2); intuition.

          + constructor. 

            * intro H; clear IHnelem.

              pose proof (@in_map_iff (word (S n)) (word n) (@wtl n) d a') as M.
              apply M in H; clear M; destruct H; destruct H as [Ha Hb].
              assert (whd x = false) as Hhd. {
                clear I H2 H3 Ha a'.
                destruct (shatter_word_S x) as [b H];
                    destruct H as [x' H]; rewrite H in *; clear H x; simpl.

                revert Hb E. revert x' b d l1.
                induction nelem; intros; simpl in E.

                - inversion E; subst.
                    inversion Hb.

                - simpl in E;
                    destruct (bool_dec (whd a) false) as [B|B];
                    destruct (partition (whd (sz:=n)) nelem) as [g' d'].

                  + rewrite B in E; inversion E; subst; clear E;
                      destruct Hb.

                    * rewrite H in *; simpl in B; intuition.

                    * apply (IHnelem x' b d' l1); intuition.

                    + assert (whd a = true) as B' by (
                        induction (whd a); intuition); clear B.
                  rewrite B' in E. inversion E. subst. clear E.
                  apply (IHnelem x' b d g'); intuition.
              }

              destruct (shatter_word_S x) as [b H].
              destruct H as [x' H].
              rewrite H in *; simpl in *; clear H.
              rewrite Hhd in Hb.
              rewrite Ha in Hb.
              assert (In (a'~0) l1 \/ In (a'~0) d) as Q by intuition.
              apply I in Q.
              intuition.

            * apply (IHnelem l1 d); intuition.
      }

      pose proof (IHn _ ncorrect1 ngood1) as H1;
        unfold elements in H1; rewrite map_length in H1.

      pose proof (IHn _ ncorrect2 ngood2) as H2;
        unfold elements in H2; rewrite map_length in H2.

      rewrite (partition_length _ _ H); simpl in *.
      rewrite H1, H2.
      omega.
  Qed.

  Lemma word_equiv_correct: forall n m, word n = word m -> n = m.
  Proof.
    intros n m H.
    apply pow2_inv.

    pose proof (word_enum_correct n) as Hn.
    pose proof (word_enum_correct m) as Hm.

    rewrite H in Hn.
    rewrite <- (Hn (word_enumerable m)).
    rewrite <- (Hm (word_enumerable m)).

    reflexivity.
  Qed.
End Enumerability.

Section SpecialFunctions.
  Local Open Scope nword_scope.

  Lemma convS_id: forall A x p, (@convS A A x p) = x.
  Proof.
    intros; unfold convS; vm_compute.
    replace p with (eq_refl A); intuition.
    apply proof_irrelevance.
  Qed.

  Lemma wordToN_convS: forall {n m} x p,
    wordToN (@convS (word n) (word m) x p) = wordToN x.
  Proof.
    intros.
    pose proof (word_equiv_correct _ _ p) as H.
    revert x p; rewrite H; intros.
    rewrite convS_id; reflexivity.
  Qed.

  Lemma wordToN_zext: forall {n m} (x: word n),
    wordToN (@zext n x m) = wordToN x.
  Proof.
    intros; induction x; simpl; intuition.

    - unfold zext, Word.combine.
      rewrite wordToN_nat.
      unfold wzero.
      rewrite (@wordToNat_natToWord_idempotent m 0); simpl; intuition.
      apply Npow2_gt0.

    - unfold zext in IHx; rewrite IHx; clear IHx;
        destruct b; intuition.
  Qed.

  Lemma wordToN_split1: forall {n m} x,
    & (@split1 n m x) = N.shiftr_nat (& x) m.
  Proof.
    intros; induction n; simpl in *.
    pose proof (word_size_bound x).

    - induction m; simpl in *; try nomega;
        pose proof (shatter_word x) as H0;
        simpl in H0; rewrite H0 in *; clear H0;
        rewrite (IHm (wtl x)).

      + admit.

      + admit.

    - admit.
  
  Admitted.

  Lemma wordToN_split2: forall {n m} x,
    & (@split2 n m x) = N.land (& x) (N.ones (N.of_nat m)).
  Proof. Admitted.

  Lemma wordToN_combine: forall {n m} x y,
    (& (@Word.combine n x m y) = (& x) * Npow2 m + & y)%N.
  Proof. Admitted.

  Lemma break_spec: forall (m n: nat) (x: word n) low high,
      (low, high) = break m x
    -> &x = (&high * Npow2 m + &low)%N.
  Proof. Admitted.

  Lemma extend_bound: forall k n (p: (k <= n)%nat) (w: word k),
    (& (extend p w) < Npow2 k)%N.
  Proof.
    intros.
    assert (n = k + (n - k)) by abstract omega.
    replace (& (extend p w)) with (& w); try apply word_size_bound.
    unfold extend.
    rewrite wordToN_convS.
    rewrite wordToN_zext.
    reflexivity.
  Qed.

  Lemma mask_wand : forall (n: nat) (x: word n) m b,
      (& (mask (N.to_nat m) x) < b)%N
    -> (& (x ^& (@NToWord n (N.ones m))) < b)%N.
  Proof. Admitted.

End SpecialFunctions.

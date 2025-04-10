Require Import Coq.PArith.BinPosDef. Local Open Scope positive_scope.
Require Import Coq.NArith.BinNat.
From Coq.Classes Require Import Morphisms.
Require Import Spec.ModularArithmetic.
Require Import Arithmetic.ModularArithmeticTheorems.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import NTT.Polynomial NTT.NTT.
Require PrimeFieldTheorems.

Section Gallina.
  (* Lower-level Gallina code for implementing NTT *)

  Local Coercion N.of_nat: nat >-> N.
  Context {q: positive} {prime_q: prime q}.
  Local Notation F := (F q).
  Local Open Scope F_scope.
  Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
    {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.
  Context {P} {poly_ops: @Polynomial.polynomial_ops F P}.
  Context {poly_defs: @Polynomial.polynomial_defs F eq F.zero F.one F.opp F.add F.sub F.mul P _}.
  Context {zeta: F} {m: nat} {Hm: zeta ^ (N.pow 2 m) = F.opp 1}.

  Local Notation nttl' := (@nttl' q field P poly_ops poly_defs zeta m Hm).
  Local Notation nttl := (@nttl q field P poly_ops poly_defs zeta m Hm).
  Local Notation Pmod_cyclotomic_list := (@PolynomialCRT.Pmod_cyclotomic_list F F.zero F.add F.sub F.mul).
  Local Notation inttl' := (@inttl' q field P poly_ops poly_defs zeta m Hm).
  Local Notation recompose_cyclotomic_list := (@PolynomialCRT.recompose_cyclotomic_list F F.zero F.add F.sub F.mul).

  Section Unopt.
    (* No optimization *)

    Fixpoint nttl_gallina r k l (p: list F) :=
      match r with
      | O => p
      | S r' =>
          let p' := Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (zeta ^ N.of_nat (Nat.div l 2)) p in
          (nttl_gallina r' (k - 1)%nat (Nat.div l 2) (firstn (Nat.pow 2 (k - 1)) p')) ++
            (nttl_gallina r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat (skipn (Nat.pow 2 (k - 1)) p'))
      end.

    Lemma nttl_gallina_spec:
      forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat) p,
        proj1_sig (nttl' r k l Hr_leq_k Hr_leq_m Hr_leq_l p) = nttl_gallina r k l (proj1_sig p).
    Proof.
      induction r; intros.
      - reflexivity.
      - cbn -[ntt_bodyl]. cbn [ntt_bodyl].
        erewrite proj1_sig_ntt_bodyl_eq; eauto.
    Qed.

    Fixpoint inttl_gallina r k l (p: list F) :=
      match r with
      | O => p
      | S r' =>
          map (F.mul (F.inv (1 + 1)))
            (recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.inv (zeta ^ N.of_nat (Nat.div l 2)))
               ((inttl_gallina r' (k - 1)%nat (Nat.div l 2) (firstn (Nat.pow 2 (k - 1)) p)) ++
                  (inttl_gallina r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat (skipn (Nat.pow 2 (k - 1)) p))))
      end.

    Lemma inttl_gallina_spec:
      forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat) p,
        proj1_sig (inttl' r k l Hr_leq_k Hr_leq_m Hr_leq_l p) = inttl_gallina r k l (proj1_sig p).
    Proof.
      induction r; intros.
      - reflexivity.
      - cbn -[F.inv Nat.div intt_bodyl].
        unfold intt_bodyl.
        erewrite proj1_sig_intt_bodyl_eq; eauto.
        apply length_decompose.
    Qed.
  End Unopt.

  Section Delayed_mul.
    (* Delay the multiplications by F.inv (1 + 1) to the end *)
    Fixpoint inttl_nomul_gallina r k l (p: list F) :=
      match r with
      | O => p
      | S r' =>
            (recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.inv (zeta ^ N.of_nat (Nat.div l 2)))
               ((inttl_nomul_gallina r' (k - 1)%nat (Nat.div l 2) (firstn (Nat.pow 2 (k - 1)) p)) ++
                  (inttl_nomul_gallina r' (k - 1)%nat (Nat.pow 2 m + Nat.div l 2)%nat (skipn (Nat.pow 2 (k - 1)) p))))
      end.

    Lemma inttl_nomul_gallina_length:
      forall r k l p,
        length (inttl_nomul_gallina r k l p) = length p.
    Proof.
      induction r; [reflexivity|].
      intros; cbn [inttl_nomul_gallina].
      rewrite PolynomialCRT.recompose_cyclotomic_list_length.
      rewrite length_app, IHr, IHr.
      rewrite <- length_app, firstn_skipn. reflexivity.
    Qed.

    Lemma inttl_nomul_gallina_spec:
      forall r k l p (Hr_leq_k: (r <= k)%nat) (Hp: length p >= Nat.pow 2 k),
        inttl_gallina r k l p = List.map (F.mul (F.inv (F.pow (1 + 1) r))) (inttl_nomul_gallina r k l p).
    Proof.
      induction r; intros.
      - rewrite (map_ext _ (fun x => x)), map_id; [reflexivity|].
        intro. rewrite F.pow_0_r, Hierarchy.commutative, <- Hierarchy.field_div_definition.
        apply Field.div_one.
      - cbn [inttl_gallina inttl_nomul_gallina].
        assert (Hp': length p >= 2 * Nat.pow 2 (k - 1)) by (rewrite <- PeanoNat.Nat.pow_succ_r'; assert (S (k - 1) = k) as -> by Lia.lia; assumption).
        rewrite IHr by (try rewrite length_firstn; Lia.lia).
        rewrite IHr by (try rewrite length_skipn; Lia.lia).
        rewrite <- map_app.
        match goal with
        | |- context [recompose_cyclotomic_list ?k ?a (map ?f ?l)] =>
            assert (recompose_cyclotomic_list k a (map f l) = map f (recompose_cyclotomic_list k a l)) as ->
        end; [|rewrite map_map; apply map_ext].
        2:{ intros. rewrite Hierarchy.associative. f_equal.
            apply Field.left_inv_unique.
            assert (N.of_nat (S r) = N.succ (N.of_nat r)) as -> by Lia.lia.
            rewrite F.pow_succ_r.
            rewrite (Hierarchy.commutative (1 + 1)), Hierarchy.associative, <- (Hierarchy.associative (F.inv (1 + 1))), Hierarchy.left_multiplicative_inverse, Hierarchy.right_identity, Hierarchy.left_multiplicative_inverse; auto.
            - pose proof (char_ge_3 (BinNums.xO BinNums.xH) ltac:(cbv; reflexivity)) as Hchar.
              simpl in Hchar. rewrite Hierarchy.left_identity in Hchar. exact Hchar.
            - clear -field char_ge_3. induction r.
              + rewrite F.pow_0_r. symmetry.
                apply Hierarchy.integral_domain_is_zero_neq_one.
              + assert (N.of_nat (S r) = N.succ (N.of_nat r)) as -> by Lia.lia.
                rewrite F.pow_succ_r. intro X.
                apply Hierarchy.integral_domain_is_zero_product_zero_factor in X.
                destruct X; [|contradiction].
                pose proof (char_ge_3 (BinNums.xO BinNums.xH) ltac:(cbv; reflexivity)) as Hchar.
                simpl in Hchar. rewrite Hierarchy.left_identity in Hchar. contradiction. }
        assert (X: forall (A: Type) (l1 l2: list A), Forall2 eq l1 l2 -> l1 = l2); [|apply X].
        { induction 1; simpl; congruence. }
        rewrite ListUtil.Forall2_forall_iff by (rewrite PolynomialCRT.recompose_cyclotomic_list_length, length_map, length_map, PolynomialCRT.recompose_cyclotomic_list_length; reflexivity).
        rewrite PolynomialCRT.recompose_cyclotomic_list_length, length_map. intros.
        rewrite ListUtil.map_nth_default_always.
        rewrite PolynomialCRT.recompose_cyclotomic_list_nth_default by (rewrite length_map, length_app, inttl_nomul_gallina_length, inttl_nomul_gallina_length, <- length_app, firstn_skipn; assumption).
        rewrite PolynomialCRT.recompose_cyclotomic_list_nth_default by (rewrite length_app, inttl_nomul_gallina_length, inttl_nomul_gallina_length, <- length_app, firstn_skipn; assumption).
        repeat rewrite ListUtil.map_nth_default_always.
        assert (0 = F.mul (F.inv ((1 + 1) ^ N.of_nat r)) 0) as -> by (rewrite Ring.mul_0_r; reflexivity).
        repeat rewrite ListUtil.map_nth_default_always.
        assert (F.mul (F.inv ((1 + 1) ^ N.of_nat r)) 0 = 0) as -> by (rewrite Ring.mul_0_r; reflexivity).
        destruct (Decidable.dec_lt_nat i _).
        + cbn zeta. rewrite <- Hierarchy.left_distributive. reflexivity.
        + destruct (Decidable.dec_lt_nat i _); [|reflexivity].
          cbn zeta. rewrite <- Hierarchy.left_distributive.
          repeat rewrite Hierarchy.associative. rewrite (Hierarchy.commutative (F.inv _) (F.inv _)). reflexivity.
          Unshelve. exact 0.
    Qed.
  End Delayed_mul.

End Gallina.

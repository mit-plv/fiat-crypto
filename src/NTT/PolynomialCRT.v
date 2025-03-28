From Crypto.Algebra Require Import Hierarchy Ring Field.
From Crypto.NTT Require Import Polynomial.
From Coq.Classes Require Import Morphisms.

Section Theorems.
  Context {F:Type}{Feq:F->F->Prop}{Fzero Fone:F}{Fopp:F->F}{Fadd Fsub Fmul:F->F->F}
    {Feq_dec:DecidableRel Feq}.
  Context {Finv: F -> F}{Fdiv: F -> F -> F}
    {field: @field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
    {char_ge_3: @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
  Local Infix "/" := Fdiv.

  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero. Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "-" := Fsub.
  Local Infix "*" := Fmul.

  Context {P} {poly_ops: @polynomial_ops F P} {poly_defs: @polynomial_defs F Feq Fzero Fone Fopp Fadd Fsub Fmul P poly_ops}.

  Local Notation Peq := (Peq (Feq:=Feq)).
  Local Notation Peq_dec := (Peq_dec (poly_ops:=poly_ops)).
  Local Notation Pdivmod := (Pdivmod (poly_ops:=poly_ops)(Fzero:=Fzero)(Fdiv:=Fdiv)).
  Local Notation Pdiv := (Pdiv (poly_ops:=poly_ops)(Fzero:=Fzero)(Fdiv:=Fdiv)).
  Local Notation Pmod := (Pmod (poly_ops:=poly_ops)(Fzero:=Fzero)(Fdiv:=Fdiv)).
  Local Notation Pgcd := (Pgcd (poly_ops:=poly_ops)(Fzero:=Fzero)(Fdiv:=Fdiv)).
  Local Notation Pegcd := (Pegcd (poly_ops:=poly_ops)(Fzero:=Fzero)(Fdiv:=Fdiv)).
  Local Notation Pdivides := (Pdivides (poly_ops:=poly_ops)(Fzero:=Fzero)(Fdiv:=Fdiv)(Feq:=Feq)).
  Local Notation coprime := (coprime (poly_ops:=poly_ops)(Fdiv:=Fdiv)).
  Local Notation Pquot := (Pquot (Feq:=Feq) (Fzero:=Fzero) (Fdiv:=Fdiv)).

  Section CRT2.
    (* Chinese Remainder Theorem (Algebraic form), base case *)
    Variable (p p1 p2: P) (Hcoprime: coprime p1 p2) (Hp_eq: Peq p (Pmul p1 p2)).

    Definition phi2 (x: Pquot p): (Pquot p1 * Pquot p2) :=
      (of_P (to_P x), of_P (to_P x)).

    Definition psi2 (xy: Pquot p1 * Pquot p2): Pquot p :=
      let x := to_P (fst xy) in
      let y := to_P (snd xy) in
      let u := fst (Pegcd p1 p2) in
      let v := snd (Pegcd p1 p2) in
      of_P (Padd (Pmul y (Pmul (Pdiv u (Pgcd p1 p2)) p1)) (Pmul x (Pmul (Pdiv v (Pgcd p1 p2)) p2))).

    Definition EQ2 (x y: Pquot p1 * Pquot p2) :=
      eq1 (fst x) (fst y) /\ eq1 (snd x) (snd y).

    Global Instance EQ_proper_psi2: Proper (EQ2 ==> eq1) psi2.
    Proof.
      intros x y. unfold EQ2, eq1, psi2; simpl. intros (HEQ1 & HEQ2).
      destruct x as [x1 x2]. destruct y as [y1 y2].
      simpl in *.
      rewrite HEQ1, HEQ2. reflexivity.
    Qed.

    Global Instance eq_proper_phi2: Proper (eq1 ==> EQ2) phi2.
    Proof.
      intros x y. unfold EQ2, eq1, phi2; simpl. intro HEQ.
      split; rewrite HEQ; reflexivity.
    Qed.

    Definition ZERO2: Pquot p1 * Pquot p2 := (zero, zero).

    Lemma ZERO_def2: EQ2 (phi2 zero) ZERO2.
    Proof. unfold phi2, ZERO2, EQ2, eq1; simpl; split; rewrite Pmod_0_l; reflexivity. Qed.

    Definition ONE2: Pquot p1 * Pquot p2 := (one, one).

    Lemma ONE_def2: EQ2 (phi2 one) ONE2.
    Proof.
      unfold phi2, ONE2, EQ2, eq1; simpl.
      assert (Peq (Pmod (Pmod Pone p) p1) (Pmod (Pmod Pone (Pmul p1 p2)) p1)) as ->.
      { apply peq_mod_proper; [|reflexivity].
        apply peq_mod_proper; [reflexivity|apply Hp_eq]. }
      assert (Peq (Pmod (Pmod Pone p) p2) (Pmod (Pmod Pone (Pmul p1 p2)) p2)) as ->.
      { apply peq_mod_proper; [|reflexivity].
        apply peq_mod_proper; [reflexivity|apply Hp_eq]. }
      destruct (Peq_dec p1 Pzero) as [Hp1z|Hp1nz].
      { assert (Peq (Pmod (Pmod Pone _) _) (Pmod (Pmod Pone Pzero) Pzero)) as ->.
        { apply peq_mod_proper; auto.
          apply peq_mod_proper; [reflexivity|].
          rewrite Hp1z. rewrite mul_0_l. reflexivity. }
        assert (Peq (Pmod Pone p1) (Pmod Pone Pzero)) as -> by (apply peq_mod_proper; auto; reflexivity).
        assert (Peq (Pmod (Pmod Pone (Pmul p1 p2)) p2) (Pmod (Pmod Pone Pzero) p2)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          apply peq_mod_proper; [reflexivity|].
          rewrite Hp1z, mul_0_l. reflexivity. }
        rewrite Pmod_0_r, Pmod_0_r.
        split; reflexivity. }
      destruct (Peq_dec p2 Pzero) as [Hp2z|Hp2nz].
      {  assert (Peq (Pmod (Pmod Pone _) p2) (Pmod (Pmod Pone Pzero) Pzero)) as ->.
        { apply peq_mod_proper; auto.
          apply peq_mod_proper; [reflexivity|].
          rewrite Hp2z. rewrite mul_0_r. reflexivity. }
        assert (Peq (Pmod Pone p2) (Pmod Pone Pzero)) as -> by (apply peq_mod_proper; auto; reflexivity).
        assert (Peq (Pmod (Pmod Pone (Pmul p1 p2)) p1) (Pmod (Pmod Pone Pzero) p1)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          apply peq_mod_proper; [reflexivity|].
          rewrite Hp2z, mul_0_r. reflexivity. }
        split; (apply peq_mod_proper; [|reflexivity]); rewrite Pmod_0_r; reflexivity. }
      destruct (degree p1) as [np1|] eqn:Hp1; [|apply zero_degree in Hp1; contradiction].
      destruct (degree p2) as [np2|] eqn:Hp2; [|apply zero_degree in Hp2; contradiction].
      generalize (mul_degree_eq (poly_ops:=poly_ops) p1 p2); rewrite Hp1, Hp2; simpl. intro Hp12.
      assert (np1 + np2 = 0%nat :> _ \/ (np1 + np2 > 0))%nat as [He|Hn] by Lia.lia.
      - assert (np1 = 0 :> _)%nat as He1 by Lia.lia.
        assert (np2 = 0 :> _)%nat as He2 by Lia.lia.
        rewrite He1 in Hp1; rewrite He2 in Hp2; rewrite He in Hp12.
        generalize (Pdivides_degree_zero (poly_ops:=poly_ops) _ Pone Hp1).
        generalize (Pdivides_degree_zero (poly_ops:=poly_ops) _ Pone Hp2).
        generalize (Pdivides_degree_zero (poly_ops:=poly_ops) _ Pone Hp12).
        unfold Pdivides. intros A1 A2 A12.
        split; [rewrite A1, A12, Pmod_0_l|rewrite A1, A2, Pmod_0_l]; reflexivity.
      - split; rewrite (Pmod_small (poly_ops:=poly_ops) Pone (Pmul p1 p2) ltac:(rewrite degree_one, Hp12; cbv -[Nat.add]; Lia.lia)); reflexivity.
    Qed.

    Definition OPP2 (x: Pquot p1 * Pquot p2): Pquot p1 * Pquot p2 :=
      (opp (fst x), opp (snd x)).

    Definition ADD2 (x y: Pquot p1 * Pquot p2): Pquot p1 * Pquot p2 :=
      (add (fst x) (fst y), add (snd x) (snd y)).

    Definition SUB2 (x y: Pquot p1 * Pquot p2): Pquot p1 * Pquot p2 :=
      (sub (fst x) (fst y), sub (snd x) (snd y)).

    Definition MUL2 (x y: Pquot p1 * Pquot p2): Pquot p1 * Pquot p2 :=
      (mul (fst x) (fst y), mul (snd x) (snd y)).

    Lemma SUB_def2 x y:
      EQ2 (SUB2 x y) (ADD2 x (OPP2 y)).
    Proof.
      destruct x as [[x1 Hx1] [x2 Hx2]].
      destruct y as [[y1 Hy1] [y2 Hy2]].
      unfold EQ2, SUB2, OPP2, eq1; simpl.
      repeat rewrite Pmod_opp. split; reflexivity.
    Qed.

    Lemma phi_injective2:
      forall x y, eq1 (fst (phi2 x)) (fst (phi2 y)) ->
             eq1 (snd (phi2 x)) (snd (phi2 y)) ->
             eq1 x y.
    Proof.
      intros x y Heq1 Heq2.
      destruct x, y. unfold phi2, eq1 in *; simpl in *.
      assert (Hdiv: Pdivides (Pmul p1 p2) (Psub x x0)).
      { apply coprime_divides; auto.
        - rewrite (Pdivmod_eq_spec (poly_ops:=poly_ops) x p1), (Pdivmod_eq_spec (poly_ops:=poly_ops) x0 p1), ring_sub_definition.
          rewrite <- Heq1, Group.inv_op.
          rewrite <- (associative (Pmul _ _) (Pmod _ _)).
          rewrite (associative (Pmod x p1)).
          rewrite right_inverse, left_identity.
          rewrite <- mul_opp_l, <- right_distributive.
          apply Pdivides_iff. eexists; reflexivity.
        - rewrite (Pdivmod_eq_spec (poly_ops:=poly_ops) x p2), (Pdivmod_eq_spec (poly_ops:=poly_ops) x0 p2), ring_sub_definition.
          rewrite <- Heq2, Group.inv_op.
          rewrite <- (associative (Pmul _ _) (Pmod _ _)).
          rewrite (associative (Pmod x p2)).
          rewrite right_inverse, left_identity.
          rewrite <- mul_opp_l, <- right_distributive.
          apply Pdivides_iff. eexists; reflexivity. }
      apply sub_zero_iff. apply Pdivides_iff in Hdiv.
      assert (Peq x (Pmod x (Pmul p1 p2))) as p0'.
      { rewrite p0. apply peq_mod_proper; auto. }
      assert (Peq x0 (Pmod x0 (Pmul p1 p2))) as p3'.
      { rewrite p3. apply peq_mod_proper; auto. }
      destruct Hdiv as (c & Hdiv).
      destruct (Peq_dec (Pmul p1 p2) Pzero) as [Hz|Hnz]; [rewrite Hdiv, Hz, mul_0_r; reflexivity|].
      generalize (Pmod_degree_lt x (Pmul p1 p2) Hnz).
      assert (degree (Pmod x (Pmul p1 p2)) = degree x :> _) as -> by (apply peq_proper_degree; symmetry; auto).
      intro Hltx0.
      generalize (Pmod_degree_lt x0 (Pmul p1 p2) Hnz).
      assert (degree (Pmod x0 (Pmul p1 p2)) = degree x0 :> _) as -> by (apply peq_proper_degree; symmetry; auto).
      intro Hltx3.
      apply IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors in Hnz.
      destruct Hnz as (Hnz1 & Hnz2).
      destruct (degree p1) as [np1|] eqn:Hp1; [|apply zero_degree in Hp1; contradiction].
      destruct (degree p2) as [np2|] eqn:Hp2; [|apply zero_degree in Hp2; contradiction].
      generalize (mul_degree_eq (poly_ops:=poly_ops) p1 p2).
      rewrite Hp1, Hp2; simpl; intro Hp12.
      assert (Hlt: degree_lt (degree (Psub x x0)) (degree (Pmul p1 p2))).
      { eapply degree_le_lt_trans; [apply sub_degree|].
        apply degree_max_lub_lt; eauto. }
      replace (degree (Psub x x0)) with (degree (Pmul c (Pmul p1 p2))) in Hlt by (apply peq_proper_degree; symmetry; auto).
      rewrite (mul_degree_eq (poly_ops:=poly_ops) c), Hp12 in Hlt.
      rewrite Hdiv. destruct (degree c) as [nc|] eqn:Hc; [|apply zero_degree in Hc; rewrite Hc, mul_0_l; reflexivity].
      cbv -[Nat.add] in Hlt. Lia.lia.
    Qed.

    Lemma psi_phi_id2 x:
      eq1 (psi2 (phi2 x)) x.
    Proof.
      generalize (Pegcd_bezout_coprime _ _ Hcoprime).
      pose (u := (Pdiv (fst (Pegcd p1 p2)) (Pgcd p1 p2))).
      pose (v := (Pdiv (snd (Pegcd p1 p2)) (Pgcd p1 p2))).
      fold u v. intro Huv.
      assert (Hu: Peq (Pmul u p1) (Psub Pone (Pmul v p2))).
      { rewrite <- Huv, ring_sub_definition, <- associative, right_inverse.
        rewrite right_identity; reflexivity. }
      assert (Hv: Peq (Pmul v p2) (Psub Pone (Pmul u p1))).
      { rewrite <- Huv, ring_sub_definition, <- associative, (commutative (Pmul v p2)), associative, right_inverse.
        rewrite left_identity; reflexivity. }
      destruct x as (x & Hx).
      pose (a1 := Pmod x p1). pose (a2 := Pmod x p2).
      destruct (Peq_dec p1 Pzero) as [Hp1|Hp1nz].
      { unfold eq1; simpl; fold u v.
        assert (Peq (Pmod (Padd (Pmul (Pmod x p2) (Pmul u p1)) (Pmul (Pmod x p1) (Pmul v p2))) p) (Pmod (Padd (Pmul (Pmod x p2) Pzero) (Pmul (Pmod x Pzero) (Pmul v p2))) p)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          apply monoid_op_Proper.
          - apply ring_mul_Proper; [reflexivity|].
            rewrite Hp1, mul_0_r. reflexivity.
          - apply ring_mul_Proper; [|reflexivity].
            apply peq_mod_proper; auto; reflexivity. }
        rewrite Pmod_0_r, mul_0_r, left_identity.
        transitivity (Pmod x p); [|symmetry; assumption].
        apply peq_mod_proper; [|reflexivity].
        assert (Peq (Pmul v p2) Pone) as ->; [|rewrite right_identity; reflexivity].
        rewrite <- Huv. rewrite Hp1, mul_0_r, left_identity. reflexivity. }
      destruct (Peq_dec p2 Pzero) as [Hp2|Hp2nz].
      { unfold eq1; simpl; fold u v.
        transitivity (Pmod x p); [|symmetry; assumption].
        apply peq_mod_proper; [|reflexivity].
        assert (Peq (Pmod x p2) (Pmod x Pzero)) as -> by (apply peq_mod_proper; auto; reflexivity).
        rewrite Pmod_0_r, Hp2, mul_0_r, mul_0_r, right_identity.
        assert (Peq (Pmul u p1) Pone) as ->; [|rewrite right_identity; reflexivity].
        rewrite <- Huv. rewrite Hp2, mul_0_r, right_identity. reflexivity. }
      destruct (degree p1) as [np1|] eqn:Hp1; [|apply zero_degree in Hp1; contradiction].
      destruct (degree p2) as [np2|] eqn:Hp2; [|apply zero_degree in Hp2; contradiction].
      assert (Ha1: degree_lt (degree a1) (degree (Pmul p1 p2))).
      { generalize (Pmod_degree_lt x p1 Hp1nz); intro.
        eapply degree_lt_le_trans; eauto.
        rewrite mul_degree_eq, Hp1, Hp2.
        cbv -[Nat.add]. Lia.lia. }
      assert (Ha2: degree_lt (degree a2) (degree (Pmul p1 p2))).
      { generalize (Pmod_degree_lt x p2 Hp2nz); intro.
        eapply degree_lt_le_trans; eauto.
        rewrite mul_degree_eq, Hp1, Hp2.
        cbv -[Nat.add]. Lia.lia. }
      apply phi_injective2; unfold eq1; simpl; fold u v.
      - rewrite Hv. fold a1 a2.
        assert (Peq (Padd (Pmul a2 (Pmul u p1)) (Pmul a1 (Psub Pone (Pmul u p1)))) (Padd a1 (Pmul (Pmul (Psub a2 a1) u) p1))) as ->.
        { rewrite ring_sub_definition, (left_distributive a1), right_identity, associative, (commutative _ a1), <- associative, mul_opp_r, <- mul_opp_l, <- right_distributive, <- ring_sub_definition, associative.
          reflexivity. }
        assert (Peq (Pmod (Pmod (Padd a1 (Pmul (Pmul (Psub a2 a1) u) p1)) p) p1) (Pmod (Padd (Pmod a1 (Pmul p2 p1)) (Pmod (Pmul (Pmul (Psub a2 a1) u) p1) (Pmul p2 p1))) p1)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          rewrite <- Pmod_distr.
          apply peq_mod_proper; [reflexivity|rewrite commutative; assumption]. }
        rewrite Pmul_mod_distr_r.
        rewrite (Pmod_small a1) by (assert (degree (Pmul p1 p2) = degree (Pmul p2 p1) :> _) as <- by (apply peq_proper_degree; apply commutative); assumption).
        rewrite Pmod_add_r. unfold a1. rewrite Pmod_mod_eq. reflexivity.
      - rewrite Hu. fold a1 a2.
        assert (Peq (Padd (Pmul a2 (Psub Pone (Pmul v p2))) (Pmul a1 (Pmul v p2))) (Padd a2 (Pmul (Pmul (Psub a1 a2) v) p2))) as ->.
        { rewrite ring_sub_definition, (left_distributive a2), right_identity, associative, mul_opp_r, <- mul_opp_l, associative, <- (associative a2), <- right_distributive, <- right_distributive, (commutative _ a1), <- ring_sub_definition.
          reflexivity. }
        assert (Peq (Pmod (Pmod (Padd a2 (Pmul (Pmul (Psub a1 a2) v) p2)) p) p2) (Pmod (Padd (Pmod a2 (Pmul p1 p2)) (Pmod (Pmul (Pmul (Psub a1 a2) v) p2) (Pmul p1 p2))) p2)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          rewrite <- Pmod_distr. apply peq_mod_proper; [reflexivity|assumption]. }
        rewrite Pmul_mod_distr_r.
        rewrite (Pmod_small a2) by assumption.
        rewrite Pmod_add_r. unfold a2. rewrite Pmod_mod_eq. reflexivity.
    Qed.

    Lemma phi_psi_id2 x:
      EQ2 (phi2 (psi2 x)) x.
    Proof.
      destruct x as [[x1 Hx1] [x2 Hx2]]. unfold phi2, psi2, EQ2, eq1; simpl.
      generalize (Pegcd_bezout_coprime p1 p2 Hcoprime).
      pose (u := (Pdiv (fst (Pegcd p1 p2)) (Pgcd p1 p2))).
      pose (v := (Pdiv (snd (Pegcd p1 p2)) (Pgcd p1 p2))).
      fold u v. intro Huv.
      assert (Hu: Peq (Pmul u p1) (Psub Pone (Pmul v p2))).
      { rewrite <- Huv, ring_sub_definition, <- associative, right_inverse.
        rewrite right_identity; reflexivity. }
      assert (Hv: Peq (Pmul v p2) (Psub Pone (Pmul u p1))).
      { rewrite <- Huv, ring_sub_definition, <- associative, (commutative (Pmul v p2)), associative, right_inverse.
        rewrite left_identity; reflexivity. }
      destruct (Peq_dec p1 Pzero) as [Hp1|Hp1nz].
      { rewrite Hp1, mul_0_r, ring_sub_definition, Group.inv_id, right_identity in Hv.
        assert (Peq (Pmod (Pmod (Padd (Pmul x2 (Pmul u p1)) (Pmul x1 (Pmul v p2))) p) p1) (Pmod (Pmod (Pmul x1 (Pmul v p2)) Pzero) Pzero)) as ->.
        { apply peq_mod_proper; auto.
          apply peq_mod_proper; [|rewrite Hp_eq, Hp1, mul_0_l; reflexivity].
          rewrite Hp1, mul_0_r, mul_0_r, left_identity. reflexivity. }
        rewrite Pmod_0_r, Pmod_0_r, Hv, right_identity. split; [reflexivity|].
        assert (Peq (Pmod (Pmod (Padd (Pmul x2 (Pmul u p1)) x1) p) p2) (Pmod x1 p2)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          transitivity (Pmod x1 Pzero); [|apply Pmod_0_r].
          apply peq_mod_proper; [|rewrite Hp_eq, Hp1, mul_0_l; reflexivity].
          rewrite Hp1, mul_0_r, mul_0_r, left_identity. reflexivity. }
        unfold coprime in Hcoprime.
        replace (degree (Pgcd p1 p2)) with (degree p2) in Hcoprime.
        2: apply peq_proper_degree; rewrite Hp1, Pgcd_0_l; reflexivity.
        generalize (Pdivides_degree_zero p2 x1 Hcoprime).
        unfold Pdivides; intro A. rewrite A, Hx2.
        symmetry; apply (Pdivides_degree_zero p2 x2 Hcoprime). }
      destruct (Peq_dec p2 Pzero) as [Hp2|Hp2nz].
      { unfold eq1; simpl; fold u v.
        rewrite Hp2, mul_0_r, ring_sub_definition, Group.inv_id, right_identity in Hu.
        assert (Peq (Pmod (Pmod (Padd (Pmul x2 (Pmul u p1)) (Pmul x1 (Pmul v p2))) p) p1) (Pmod x2 p1)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          transitivity (Pmod x2 Pzero); [|apply Pmod_0_r].
          apply peq_mod_proper; [|rewrite Hp_eq, Hp2, mul_0_r; reflexivity].
          rewrite Hp2, mul_0_r, mul_0_r, right_identity, Hu, right_identity. reflexivity. }
        unfold coprime in Hcoprime.
        replace (degree (Pgcd p1 p2)) with (degree p1) in Hcoprime.
        2: apply peq_proper_degree; rewrite Hp2, Pgcd_0_r; reflexivity.
        generalize (Pdivides_degree_zero p1 x2 Hcoprime).
        unfold Pdivides; intro A. split.
        - rewrite A, Hx1.
          symmetry; apply (Pdivides_degree_zero p1 x1 Hcoprime).
        - transitivity (Pmod x2 Pzero); [|apply Pmod_0_r].
          apply peq_mod_proper; [|assumption].
          transitivity (Pmod x2 Pzero); [|apply Pmod_0_r].
          apply peq_mod_proper; [|rewrite Hp_eq, Hp2, mul_0_r; reflexivity].
          rewrite Hp2, mul_0_r, mul_0_r, right_identity, Hu, right_identity; reflexivity. }
      destruct (degree p1) as [np1|] eqn:Hp1; [|apply zero_degree in Hp1; contradiction].
      destruct (degree p2) as [np2|] eqn:Hp2; [|apply zero_degree in Hp2; contradiction].
      assert (Ha1: degree_lt (degree x1) (degree (Pmul p1 p2))).
      { generalize (Pmod_degree_lt x1 p1 Hp1nz); intro.
        assert (degree x1 = degree (Pmod x1 p1) :> _) as -> by (apply peq_proper_degree; auto).
        eapply degree_lt_le_trans; eauto.
        rewrite mul_degree_eq, Hp1, Hp2.
        cbv -[Nat.add]. Lia.lia. }
      assert (Ha2: degree_lt (degree x2) (degree (Pmul p1 p2))).
      { generalize (Pmod_degree_lt x2 p2 Hp2nz); intro.
        assert (degree x2 = degree (Pmod x2 p2) :> _) as -> by (apply peq_proper_degree; auto).
        eapply degree_lt_le_trans; eauto.
        rewrite mul_degree_eq, Hp1, Hp2.
        cbv -[Nat.add]. Lia.lia. }
      split; rewrite Pmod_distr.
      - assert (Peq (Pmod (Padd _ _) _) (Pmod (Pmod (Padd x1 (Pmul p1 (Padd (Pmul x2 u) (Pmul x1 (Popp u))))) (Pmul p1 p2)) p1)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          rewrite <- Pmod_distr.
          apply peq_mod_proper; [|assumption].
          rewrite Hv, ring_sub_definition, (left_distributive x1), right_identity.
          rewrite <- mul_opp_l. repeat rewrite (associative _ _ p1).
          rewrite (associative _ x1), (commutative _ x1), <- (associative x1).
          rewrite <- right_distributive, (commutative _ p1). reflexivity. }
        assert (Peq (Pmod (Pmod _ _) _) (Pmod (Padd x1 (Pmul (Pmod (Padd (Pmul x2 u) (Pmul x1 (Popp u))) p2) p1)) p1)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          rewrite Pmod_distr, (Pmod_small x1) by assumption.
          rewrite Pmul_mod_distr_l, (commutative p1). reflexivity. }
        rewrite Pmod_add_r. symmetry; assumption.
      - assert (Peq (Pmod _ _) (Pmod (Pmod (Padd x2 (Pmul (Padd (Pmul x2 (Popp v)) (Pmul x1 v)) p2)) (Pmul p1 p2)) p2)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          rewrite <- Pmod_distr.
          apply peq_mod_proper; [|assumption].
          rewrite Hu, ring_sub_definition, (left_distributive x2), right_identity.
          rewrite <- mul_opp_l. repeat rewrite (associative _ _ p2).
          rewrite <- (associative x2), <- right_distributive. reflexivity. }
        assert (Peq (Pmod (Pmod _ _) _) (Pmod (Padd x2 (Pmul (Pmod (Padd (Pmul x2 (Popp v)) (Pmul x1 v)) p1) p2)) p2)) as ->.
        { apply peq_mod_proper; [|reflexivity].
          rewrite Pmod_distr, (Pmod_small x2) by assumption.
          rewrite Pmul_mod_distr_r. reflexivity. }
        rewrite Pmod_add_r. symmetry; assumption.
    Qed.

    Lemma psi_EQ2 a b:
      eq1 (psi2 a) (psi2 b) <-> EQ2 a b.
    Proof.
      split; [intro A|intro A; rewrite A; reflexivity].
      rewrite <- (phi_psi_id2 a), A, phi_psi_id2. reflexivity.
    Qed.

    Lemma psi_ZERO2:
      eq1 (psi2 ZERO2) (zero: Pquot p).
    Proof. rewrite <- ZERO_def2. apply psi_phi_id2. Qed.

    Lemma psi_ONE2:
      eq1 (psi2 ONE2) (one : Pquot p).
    Proof. rewrite <- ONE_def2. apply psi_phi_id2. Qed.

    Lemma psi_OPP2 a:
      eq1 (psi2 (OPP2 a)) (opp (psi2 a)).
    Proof.
      destruct a as [[a1 Ha1] [a2 Ha2]]. unfold OPP2, psi2, eq1; simpl.
      rewrite Pmod_opp, Pmod_opp, mul_opp_l, mul_opp_l, <- Group.inv_op, Pmod_opp, Pmod_opp, Pmod_mod_eq.
      rewrite <- Ha1, <- Ha2, (commutative (Pmul a1 _)). reflexivity.
    Qed.

    Lemma psi_ADD2 a b:
      eq1 (psi2 (ADD2 a b)) (add (psi2 a) (psi2 b)).
    Proof.
      destruct a as [[a1 Ha1] [a2 Ha2]].
      destruct b as [[b1 Hb1] [b2 Hb2]].
      unfold ADD2, psi2, eq1; simpl.
      rewrite (Pmod_distr a1 b1), (Pmod_distr a2 b2), <- (Pmod_distr _ _ p), Pmod_mod_eq.
      rewrite <- Ha1, <- Ha2, <- Hb1, <- Hb2.
      rewrite <- (associative (Pmul a2 _) (Pmul a1 _)), (associative (Pmul a1 _) (Pmul b2 _)), (commutative (Pmul a1 _) (Pmul b2 _)), <- (associative (Pmul b2 _)), <- right_distributive, (associative (Pmul a2 _)), <- right_distributive.
      reflexivity.
    Qed.

    Lemma psi_SUB2 a b:
      eq1 (psi2 (SUB2 a b)) (sub (psi2 a) (psi2 b)).
    Proof.
      rewrite ring_sub_definition, SUB_def2, psi_ADD2.
      apply monoid_op_Proper; [reflexivity|]. apply psi_OPP2.
    Qed.

    Lemma psi_MUL2 a b:
      eq1 (psi2 (MUL2 a b)) (mul (psi2 a) (psi2 b)).
    Proof.
      generalize (phi_psi_id2 (MUL2 a b)); intros [A B].
      generalize (Pegcd_bezout_coprime p1 p2 Hcoprime).
      pose (u := (Pdiv (fst (Pegcd p1 p2)) (Pgcd p1 p2))).
      pose (v := (Pdiv (snd (Pegcd p1 p2)) (Pgcd p1 p2))).
      fold u v. intro Huv.
      assert (Hu: Peq (Pmul u p1) (Psub Pone (Pmul v p2))).
      { rewrite <- Huv, ring_sub_definition, <- associative, right_inverse.
        rewrite right_identity; reflexivity. }
      assert (Hv: Peq (Pmul v p2) (Psub Pone (Pmul u p1))).
      { rewrite <- Huv, ring_sub_definition, <- associative, (commutative (Pmul v p2)), associative, right_inverse.
        rewrite left_identity; reflexivity. }
      destruct (Peq_dec p1 Pzero) as [Hp1|Hp1nz].
      { destruct a as [[a1 Ha1] [a2 Ha2]].
        destruct b as [[b1 Hb1] [b2 Hb2]].
        unfold MUL2, psi2, eq1; simpl. clear A B.
        rewrite Hp1, mul_0_r, left_identity in Huv.
        fold u v. apply peq_mod_proper; [|reflexivity].
        transitivity (Pmul a1 b1).
        { rewrite Huv. rewrite Hp1 at 1.
          rewrite mul_0_r, mul_0_r, right_identity, left_identity.
          transitivity (Pmod (Pmul a1 b1) Pzero); [|apply Pmod_0_r].
          apply peq_mod_proper; [reflexivity|auto]. }
        symmetry. transitivity (Pmul (Pmod (Padd (Pmul a2 (Pmul u p1)) (Pmul a1 (Pmul v p2))) Pzero) (Pmod (Padd (Pmul b2 (Pmul u p1)) (Pmul b1 (Pmul v p2))) Pzero)).
        { apply ring_mul_Proper; apply peq_mod_proper; try reflexivity; rewrite Hp_eq, Hp1, mul_0_l; reflexivity. }
        rewrite Pmod_0_r, Pmod_0_r, Huv, Hp1, mul_0_r, mul_0_r, right_identity, right_identity, mul_0_r, left_identity, left_identity.
        reflexivity. }
      destruct (Peq_dec p2 Pzero) as [Hp2|Hp2nz].
      { destruct a as [[a1 Ha1] [a2 Ha2]].
        destruct b as [[b1 Hb1] [b2 Hb2]].
        unfold MUL2, psi2, eq1; simpl. clear A B.
        rewrite Hp2, mul_0_r, right_identity in Huv.
        fold u v. apply peq_mod_proper; [|reflexivity].
        transitivity (Pmul a2 b2).
        { rewrite Huv. rewrite Hp2 at 2.
          rewrite mul_0_r, mul_0_r, right_identity, right_identity.
          transitivity (Pmod (Pmul a2 b2) Pzero); [|apply Pmod_0_r].
          apply peq_mod_proper; [reflexivity|auto]. }
        symmetry. transitivity ((Pmul (Pmod (Padd (Pmul a2 (Pmul u p1)) (Pmul a1 (Pmul v p2))) Pzero) (Pmod (Padd (Pmul b2 (Pmul u p1)) (Pmul b1 (Pmul v p2))) Pzero))).
        { apply ring_mul_Proper; apply peq_mod_proper; try reflexivity; rewrite Hp_eq, Hp2, mul_0_r; reflexivity. }
        rewrite Pmod_0_r, Pmod_0_r, Huv, Hp2, mul_0_r, mul_0_r, right_identity, right_identity, mul_0_r, right_identity, right_identity.
        reflexivity. }
      destruct (degree p1) as [np1|] eqn:Hp1; [|apply zero_degree in Hp1; contradiction].
      destruct (degree p2) as [np2|] eqn:Hp2; [|apply zero_degree in Hp2; contradiction].
      destruct a as [[a1 Ha1] [a2 Ha2]].
      destruct b as [[b1 Hb1] [b2 Hb2]].
      apply phi_injective2; [rewrite A|rewrite B]; clear A B.
      - unfold MUL2, psi2, eq1; simpl. fold u v.
        symmetry; etransitivity.
        { apply peq_mod_proper; [|reflexivity].
          apply peq_mod_proper; eauto.
          apply ring_mul_Proper; apply peq_mod_proper; eauto; reflexivity. }
        rewrite Pmod_mul_mod_l, <- (Pmul_mod_idemp (Pmod _ _) (Pmod _ _) p1).
        rewrite Pmod_mul_mod_l, Pmod_mul_mod_l.
        rewrite (associative a2 u), Pmod_add_l.
        rewrite (associative b2 u), Pmod_add_l.
        apply peq_mod_proper; [|reflexivity].
        apply ring_mul_Proper.
        + etransitivity.
          { apply peq_mod_proper; [|reflexivity].
            rewrite Hv, ring_sub_definition, (left_distributive a1), right_identity, <- mul_opp_l.
            rewrite (associative _ _ p1). reflexivity. }
          rewrite Pmod_add_r. symmetry; assumption.
        + etransitivity.
          { apply peq_mod_proper; [|reflexivity].
            rewrite Hv, ring_sub_definition, (left_distributive b1), right_identity, <- mul_opp_l.
            rewrite (associative _ _ p1). reflexivity. }
          rewrite Pmod_add_r. symmetry; assumption.
      - unfold MUL2, psi2, eq1; simpl. fold u v.
        symmetry; etransitivity.
        { apply peq_mod_proper; [|reflexivity].
          apply peq_mod_proper; eauto.
          apply ring_mul_Proper; apply peq_mod_proper; eauto; reflexivity. }
        rewrite Pmod_mul_mod_r, <- (Pmul_mod_idemp (Pmod _ _) (Pmod _ _) p2).
        rewrite Pmod_mul_mod_r, Pmod_mul_mod_r.
        rewrite (associative a1 v), Pmod_add_r.
        rewrite (associative b1 v), Pmod_add_r.
        apply peq_mod_proper; [|reflexivity].
        apply ring_mul_Proper.
        + etransitivity.
          { apply peq_mod_proper; [|reflexivity].
            rewrite Hu, ring_sub_definition, (left_distributive a2), right_identity, <- mul_opp_l.
            rewrite (associative _ _ p2). reflexivity. }
          rewrite Pmod_add_r. symmetry; assumption.
        + etransitivity.
          { apply peq_mod_proper; [|reflexivity].
            rewrite Hu, ring_sub_definition, (left_distributive b2), right_identity, <- mul_opp_l.
            rewrite (associative _ _ p2). reflexivity. }
          rewrite Pmod_add_r. symmetry; assumption.
    Qed.

    Lemma CRT_ring_by_isomorphism:
      @ring _ EQ2 ZERO2 ONE2 OPP2 ADD2 SUB2 MUL2
      /\ @Ring.is_homomorphism _ eq1 one add mul _ EQ2 ONE2 ADD2 MUL2 phi2
      /\ @Ring.is_homomorphism _ EQ2 ONE2 ADD2 MUL2 _ eq1 one add mul psi2.
    Proof.
      apply Ring.ring_by_isomorphism.
      - apply psi_phi_id2.
      - apply psi_EQ2.
      - apply psi_ZERO2.
      - apply psi_ONE2.
      - apply psi_OPP2.
      - apply psi_ADD2.
      - apply psi_SUB2.
      - apply psi_MUL2.
    Qed.

    Lemma CRT_isomorphism2:
      @Ring.is_isomorphism
        (Pquot p) eq1 one add mul
        (Pquot p1 * Pquot p2) EQ2 ONE2 ADD2 MUL2
        phi2 psi2.
    Proof.
      constructor.
      - apply CRT_ring_by_isomorphism.
      - apply phi_psi_id2.
      - intros a b Hab. destruct Hab.
        apply phi_injective2; auto.
    Qed.
  End CRT2.
  Section Negacyclic.
    (* Negacyclic polynomials X^n + a *)
    Definition negacyclic (n: nat) (a: F): P := (Padd (base n) (Pconst a)).
    Definition posicyclic (n: nat) (a: F): P := negacyclic n (Fopp a).
      Global Instance peq_negacyclic_proper n: Proper (Feq ==> Peq) (negacyclic n).
      Proof.
        intros a1 a2 Ha; unfold negacyclic.
        apply monoid_op_Proper; [reflexivity|].
        apply eq_proper_const; auto. Qed.
      Global Instance peq_posicyclic_proper n: Proper (Feq ==> Peq) (posicyclic n).
      Proof. intros a1 a2 Ha; unfold posicyclic. rewrite Ha. reflexivity. Qed.
      Lemma negacyclic_degree n a (Hngt0: (n > 0)%nat):
        degree (negacyclic n a) = Some n :> _.
      Proof.
        assert (X: coeff (negacyclic n a) n = 1).
        { unfold negacyclic.
          rewrite add_definition, base_definition, const_definition.
          destruct (dec_eq_nat n n); [|congruence]. destruct n; [Lia.lia|].
          apply right_identity. }
        generalize (degree_definition (negacyclic n a)).
        destruct (degree (negacyclic n a)) as [np1|] eqn:Hnp1.
        - intros [A B]. unfold negacyclic in A.
          unfold negacyclic in A. rewrite add_definition, base_definition, const_definition in A.
          destruct (dec_eq_nat n np1); [auto|].
          destruct np1; [|elim A; apply right_identity].
          rewrite B in X by Lia.lia. elim (zero_neq_one X).
        - intros A. rewrite A in X. elim (zero_neq_one X).
      Qed.
      Lemma posicyclic_degree n a (Hngt0: (n > 0)%nat):
        degree (posicyclic n a) = Some n :> _.
      Proof. apply negacyclic_degree. auto. Qed.
      Lemma negacyclic_opp n a:
        Peq (negacyclic n (Fopp a)) (posicyclic n a).
      Proof. unfold negacyclic, posicyclic; reflexivity. Qed.
      Lemma posicyclic_opp n a:
        Peq (posicyclic n (Fopp a)) (negacyclic n a).
      Proof. rewrite (peq_negacyclic_proper _ a (Fopp (Fopp a)) ltac:(symmetry; apply Group.inv_inv)), negacyclic_opp. reflexivity. Qed.
      Lemma posicyclic_decomposition n a:
        Peq (posicyclic (2 * n)%nat (a * a)) (Pmul (posicyclic n a) (negacyclic n a)).
      Proof.
        unfold posicyclic, negacyclic.
        rewrite right_distributive, left_distributive, left_distributive.
        rewrite base_mul_base, const_mul_const, (commutative (base n) (Pconst a)).
        assert (n + n = 2 * n :> _)%nat as -> by Lia.lia.
        rewrite <- (associative (base _)).
        apply monoid_op_Proper; [reflexivity|].
        repeat rewrite <- opp_const.
        rewrite mul_opp_l, associative, right_inverse, left_identity.
        rewrite opp_const. apply eq_proper_const.
        rewrite mul_opp_l. reflexivity.
      Qed.
      Lemma posicyclic_decomposition_coprime n a (Hngt0: (n > 0)%nat) (Hanz: a <> 0):
        coprime (posicyclic n a) (negacyclic n a).
      Proof.
        assert (A: a + a <> 0).
        { rewrite <- (ring_monoid_mul.(monoid_is_right_identity).(right_identity) a).
          rewrite <- left_distributive.
          apply IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors.
          split; auto.
          generalize (char_ge_3 (BinPosDef.Pos.of_nat 2%nat) ltac:(simpl; Lia.lia)); simpl.
          rewrite left_identity; auto. }
        assert (Hnz: not (Peq (negacyclic n a) Pzero)).
        { intro X. generalize (negacyclic_degree n a Hngt0).
          intro. assert (degree (negacyclic n a) = degree Pzero :> _) as Z by (apply peq_proper_degree; auto).
          rewrite degree_zero in Z. congruence. }
        assert (Hmod12: Peq (Pmod (posicyclic n a) (negacyclic n a)) (Pconst (Fopp (a + a)))).
        { symmetry; eapply (Pdivmod_eq_iff (posicyclic n a) (negacyclic n a) Hnz Pone).
          - rewrite left_identity. unfold negacyclic.
            rewrite <- associative, const_add_const.
            unfold posicyclic, negacyclic. apply monoid_op_Proper; [reflexivity|].
            apply eq_proper_const.
            rewrite Group.inv_op, associative, right_inverse, left_identity; reflexivity.
          - rewrite degree_const, negacyclic_degree; auto.
            destruct (Feq_dec (Fopp _) 0); cbv; auto; Lia.lia. }
        unfold coprime.
        etransitivity.
        { eapply peq_proper_degree. rewrite Pgcd_mod.
          apply Pdivides_gcd.
          apply Pdivides_degree_zero.
          etransitivity; [apply peq_proper_degree; apply Hmod12|].
          rewrite degree_const. destruct (Feq_dec (Fopp (a + a)) 0); auto.
          apply (proj1 (Group.inv_id_iff _)) in f; contradiction. }
        etransitivity; [apply peq_proper_degree; apply Hmod12|].
        rewrite degree_const. destruct (Feq_dec (Fopp (a + a)) 0); auto.
        apply (proj1 (Group.inv_id_iff _)) in f; contradiction.
      Qed.
  End Negacyclic.
End Theorems.

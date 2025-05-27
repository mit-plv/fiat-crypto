Require Import Coq.PArith.BinPosDef. Local Open Scope positive_scope.
Require Import Coq.NArith.BinNat.
From Coq.Classes Require Import Morphisms.
Require Import Spec.ModularArithmetic.
Require Import Arithmetic.ModularArithmeticTheorems.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.List.
Require Import NTT.Polynomial NTT.NTT.
Require PrimeFieldTheorems.

(** This file provides equivalent (but more efficient and closer to imperative code) ways to compute the (inverse) NTT, i.e., [nttl] and [inttl] in NTT.v

    The following optimizations are proved:
    - Use the same precomputed array of ζ^k for the NTT and iNTT
    - Delayed multiplicative inversion in the iNTT

    TODO: delayed reduction for inverse NTT
*)

Section Utils.
  Lemma firstn_enumerate {A} k n (l: list A):
    firstn k (enumerate n l) = enumerate n (firstn k l).
  Proof.
    unfold enumerate. rewrite ListUtil.firstn_combine, firstn_seq, length_firstn. reflexivity.
  Qed.

  Lemma skipn_enumerate {A} k n (l: list A):
    skipn k (enumerate n l) = enumerate (n + k) (skipn k l).
  Proof.
    unfold enumerate. rewrite ListUtil.skipn_combine, ListUtil.skipn_seq, length_skipn.
    f_equal. f_equal. Lia.lia.
  Qed.
End Utils.

Section Zetas.
  (** One optimization consists in using an array of precomputed ζ^k stored in a specific order.
      This section defines this array. *)

  Local Coercion N.of_nat: nat >-> N.
  Context {q: positive} {prime_q: prime q}.
  Local Notation F := (F q).
  Local Open Scope F_scope.
  Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
    {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.

  Context {zeta: F} {m: nat} {Hm: zeta ^ (N.pow 2 m) = F.opp 1}.

  (* We only keep one half of the coefficients since the other half can be recovered from it *)
  Fixpoint zeta_powers (l i: nat) :=
    match i with
    | O => @decompose m O l
    | S i => (zeta_powers l i) ++ (List.map (fun k => nth_default 0%nat (@decompose m (S i) l) (2 * k)%nat) (seq 0%nat (Nat.pow 2 i)))
    end.

  Lemma zeta_powers_length (l i: nat):
    length (zeta_powers l i) = Nat.pow 2 i.
  Proof.
    induction i; [reflexivity|].
    simpl; rewrite length_app, length_map, length_seq, IHi.
    Lia.lia.
  Qed.

  Lemma decompose_zeta_powers_nth:
    forall i j k l, (S i <= j)%nat ->
               (k < Nat.pow 2 i)%nat ->
               exists v, nth_error (zeta_powers l j) (Nat.pow 2 i + k) = Some v /\
                    nth_error (@decompose m (S i) l) (2 * k)%nat = Some v.
  Proof.
    assert (IH: forall l j i, (S i <= j)%nat -> exists tl, zeta_powers l j = zeta_powers l i ++ (map (fun k : nat => nth_default 0%nat (@decompose m (S i) l) (2 * k)) (seq 0 (Nat.pow 2 i))) ++ tl).
    { induction j; intros i Hi; [Lia.lia|].
      assert (S i <= j \/ i = j)%nat as [Hlt|<-] by Lia.lia.
      - simpl. destruct (IHj _ Hlt) as [tl Heq].
        rewrite Heq. repeat rewrite <- List.app_assoc.
        eexists; f_equal.
      - exists nil. rewrite List.app_nil_r. reflexivity. }
    intros i j k l Hj Hk.
    pose proof (zeta_powers_length l j) as Hlenj.
    pose proof (PeanoNat.Nat.pow_le_mono_r 2%nat _ _ ltac:(Lia.lia) Hj) as Hle.
    rewrite PeanoNat.Nat.pow_succ_r' in Hle.
    destruct (ListUtil.nth_error_length_exists_value (Nat.pow 2 i + k) (zeta_powers l j) ltac:(Lia.lia)) as [x Hx].
    eexists; split; eauto.
    destruct (IH l _ _ Hj) as [tl Heq].
    rewrite Heq, nth_error_app2 in Hx by (rewrite zeta_powers_length; Lia.lia).
    rewrite zeta_powers_length in Hx.
    rewrite nth_error_app1 in Hx by (rewrite length_map, length_seq; Lia.lia).
    rewrite nth_error_map in Hx.
    replace (Nat.pow 2 i + k - _)%nat with k in Hx by Lia.lia.
    rewrite ListUtil.nth_error_seq in Hx.
    destruct (Compare_dec.lt_dec k (Nat.pow 2 i)) as [_|]; [|Lia.lia].
    rewrite PeanoNat.Nat.add_0_l in Hx. cbn [option_map] in Hx.
    erewrite ListUtil.nth_error_Some_nth_default; eauto.
    rewrite length_decompose, PeanoNat.Nat.pow_succ_r'. Lia.lia.
  Qed.

  Lemma decompose_nth:
    forall i k l,
      (2 * k + 1 < Nat.pow 2 i)%nat ->
      exists v, nth_error (@NTT.decompose m i l) (2 * k) = Some v /\
           nth_error (@NTT.decompose m i l) (2 * k + 1) = Some (Nat.pow 2 m + v)%nat.
  Proof.
    induction i; intros k l Hk.
    - rewrite PeanoNat.Nat.pow_0_r in Hk; Lia.lia.
    - cbn [NTT.decompose decompose_body].
      unfold decompose_body'.
      rewrite PeanoNat.Nat.pow_succ_r' in Hk.
      destruct (Decidable.dec_lt_nat (2 * k + 1) (Nat.pow 2 i)) as [Hlt|Hnlt].
      + rewrite nth_error_app1 by (rewrite length_decompose; Lia.lia).
        rewrite nth_error_app1 by (rewrite length_decompose; Lia.lia).
        apply IHi; auto.
      + destruct (Decidable.dec_lt_nat (Nat.pow 2 i) (2 * k + 1)) as [Hlt'|Hnlt'].
        * assert (Nat.pow 2 i <= 2 * k) as Hle by Lia.lia.
          rewrite nth_error_app2 by (rewrite length_decompose; Lia.lia).
          rewrite nth_error_app2 by (rewrite length_decompose; Lia.lia).
          rewrite length_decompose. destruct i; [simpl in *; Lia.lia|].
          rewrite PeanoNat.Nat.pow_succ_r' in *.
          assert (2 * k - 2 * Nat.pow 2 i = 2 * (k - Nat.pow 2 i))%nat as -> by Lia.lia.
          assert (2 * k + 1 - 2 * Nat.pow 2 i = 2 * (k - Nat.pow 2 i) + 1)%nat as -> by Lia.lia.
          apply IHi. Lia.lia.
        * assert (Nat.pow 2 i = 2 * k + 1)%nat as Heq by Lia.lia.
          clear -Heq Hk. destruct i.
          { simpl in *. assert (k = 0)%nat as -> by Lia.lia.
            simpl. eauto. }
          { assert (Nat.even (Nat.pow 2 (S i)) = true) as HX by (rewrite PeanoNat.Nat.even_pow by congruence; reflexivity).
            rewrite Heq, PeanoNat.Nat.even_odd in HX. congruence. }
  Qed.

  Lemma decompose_S_eq:
    forall i l,
      @NTT.decompose m (S i) l = flat_map (fun v => [Nat.div v 2; Nat.pow 2 m + Nat.div v 2]%nat) (@NTT.decompose m i l).
  Proof.
    induction i; intros; [reflexivity|].
    assert (decompose (S i) l = @decompose m i (Nat.div l 2) ++ @decompose m i (Nat.pow 2 m + Nat.div l 2))%nat as -> by reflexivity.
    rewrite flat_map_app. repeat rewrite <- IHi.
    reflexivity.
  Qed.

  Lemma decompose_mod:
    forall i, (i <= m)%nat ->
         forall x, In x (@NTT.decompose m i (Nat.pow 2 m)) ->
              (Nat.modulo x (Nat.pow 2 (m - i)) = 0)%nat.
  Proof.
    induction i; intros Hi p Hin.
    - cbn in Hin. destruct Hin as [<-|Hin]; [|elim Hin].
      rewrite PeanoNat.Nat.sub_0_r. apply PeanoNat.Nat.Div0.mod_same.
    - rewrite decompose_S_eq in Hin.
      apply In_nth_error in Hin. destruct Hin as [k Hin].
      cbn -[Nat.div] in Hin. eapply ListUtil.flat_map_constant_nth_error in Hin; [|simpl; reflexivity].
      destruct Hin as (n1 & (Hn1 & Hn2)).
      pose proof (IHi ltac:(Lia.lia) n1 ltac:(eapply nth_error_In; eauto)) as A.
      assert (m - i = S (m - S i))%nat as C by Lia.lia.
      rewrite C, PeanoNat.Nat.pow_succ_r' in A.
      assert (Nat.modulo (Nat.div n1 2) (Nat.pow 2 (m - S i)) = 0)%nat as Hmod1.
      { apply PeanoNat.Nat.Div0.div_exact.
        apply PeanoNat.Nat.Div0.div_exact in A.
        rewrite A at 1.
        assert (2 * _ * _ = (Nat.div n1 (2 * Nat.pow 2 (m - S i)) * Nat.pow 2 (m - S i)) * 2)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.div_mul by congruence.
        rewrite <- PeanoNat.Nat.Div0.div_div. Lia.lia. }
      assert (Nat.modulo (Nat.pow 2 m + Nat.div n1 2) (Nat.pow 2 (m - S i)) = 0)%nat as Hmod2.
      { rewrite PeanoNat.Nat.Div0.add_mod, Hmod1.
        rewrite PeanoNat.Nat.add_0_r, PeanoNat.Nat.Div0.mod_mod.
        assert (Nat.pow 2 m = Nat.pow 2 (S i) * Nat.pow 2 (m - S i))%nat as ->; [|apply PeanoNat.Nat.Div0.mod_mul].
        rewrite <- PeanoNat.Nat.pow_add_r. f_equal; Lia.lia. }
      assert (Nat.modulo k 2 = 0 \/ Nat.modulo k 2 = 1)%nat as X by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
      destruct X as [X|X]; rewrite X in Hn2; cbn -[Nat.div] in Hn2; inversion Hn2; subst p; clear Hn2; auto.
  Qed.

  Lemma decompose_inv_nth:
    forall i, (i <= m)%nat ->
         forall k, (k < Nat.pow 2 i)%nat ->
              forall a b,
                nth_error (@NTT.decompose m i (Nat.pow 2 m)) k = Some a ->
                nth_error (@NTT.decompose m i (Nat.pow 2 m)) (Nat.pow 2 i - 1 - k) = Some b ->
                (a + b = Nat.pow 2 (S m))%nat.
  Proof.
    induction i; intros Hi k Hk a b Ha Hb.
    - destruct k; cbn in Ha, Hb, Hk; [|Lia.lia].
      inversion Ha; inversion Hb; subst a; subst b; clear Ha Hb.
      assert (_ + _ = 2 * Nat.pow 2 m)%nat as -> by Lia.lia.
      rewrite <- PeanoNat.Nat.pow_succ_r'. reflexivity.
    - rewrite decompose_S_eq in Ha, Hb.
      apply (ListUtil.flat_map_constant_nth_error 2%nat) in Ha, Hb; try reflexivity.
      destruct Ha as (ya & Hya & Ha). destruct Hb as (yb & Hyb & Hb).
      rewrite PeanoNat.Nat.pow_succ_r' in Hk.
      apply PeanoNat.Nat.Div0.div_lt_upper_bound in Hk.
      assert (Nat.modulo k 2 = 0 \/ Nat.modulo k 2 = 1)%nat as Hkmod by (generalize (NatUtil.mod_bound_lt k 2 ltac:(Lia.lia)); Lia.lia).
      assert (Nat.div (Nat.pow 2 (S i) - 1 - k) 2 = Nat.pow 2 i - 1 - Nat.div k 2)%nat as Hdivk2.
      { rewrite (PeanoNat.Nat.div_mod_eq k 2) at 1.
        rewrite PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.sub_add_distr.
        assert (2 * PeanoNat.Nat.pow 2 i - 1 - 2 * PeanoNat.Nat.div k 2 - PeanoNat.Nat.modulo k 2 = 2 * (PeanoNat.Nat.pow 2 i - PeanoNat.Nat.div k 2 - 1) + (1 - PeanoNat.Nat.modulo k 2))%nat as -> by Lia.lia.
        rewrite NatUtil.div_add_l' by Lia.lia.
        rewrite (PeanoNat.Nat.div_small (1 - _)) by Lia.lia.
        Lia.lia. }
      rewrite Hdivk2 in Hyb.
      pose proof (IHi ltac:(Lia.lia) _ Hk _ _ Hya Hyb) as Hy.
      assert (PeanoNat.Nat.modulo (PeanoNat.Nat.pow 2 (S i) - 1 - k) 2 = 1 - Nat.modulo k 2)%nat as Hmodk2.
      { rewrite PeanoNat.Nat.pow_succ_r', (PeanoNat.Nat.div_mod_eq k 2) at 1.
        assert (2 * PeanoNat.Nat.pow 2 i - 1 - _ = 2 * (PeanoNat.Nat.pow 2 i - 1 - Nat.div k 2) + (1 - Nat.modulo k 2))%nat as -> by Lia.lia.
        rewrite NatUtil.mod_add_l' by Lia.lia.
        apply PeanoNat.Nat.mod_small. Lia.lia. }
      rewrite Hmodk2 in Hb.
      assert (Nat.div ya 2 + Nat.div yb 2 = Nat.pow 2 m)%nat as Hyab.
      { rewrite (PeanoNat.Nat.div_mod_eq ya 2) in Hy.
        rewrite (PeanoNat.Nat.div_mod_eq yb 2) in Hy.
        rewrite PeanoNat.Nat.pow_succ_r' in Hy.
        assert (2 * (Nat.div ya 2 + Nat.div yb 2) + Nat.modulo ya 2 + Nat.modulo yb 2 = 2 * Nat.pow 2 m)%nat as Hy2 by Lia.lia.
        apply nth_error_In in Hya, Hyb.
        pose proof (decompose_mod i ltac:(Lia.lia) _ Hya) as Hmodya.
        pose proof (decompose_mod i ltac:(Lia.lia) _ Hyb) as Hmodyb.
        assert (forall x y, 2 * x = 2 * y -> x = y)%nat as Z by Lia.lia; apply Z.
        rewrite <- Hy.
        assert (Nat.modulo ya 2 = 0)%nat as ->.
        { apply PeanoNat.Nat.Div0.mod_divides in Hmodya.
          destruct Hmodya as (? & ->). apply PeanoNat.Nat.Div0.mod_divides.
          assert (m - i = S (m - S i))%nat as -> by Lia.lia.
          rewrite PeanoNat.Nat.pow_succ_r'. exists (Nat.pow 2 (m - S i) * x)%nat; Lia.lia. }
        assert (Nat.modulo yb 2 = 0)%nat as ->.
        { apply PeanoNat.Nat.Div0.mod_divides in Hmodyb.
          destruct Hmodyb as (? & ->). apply PeanoNat.Nat.Div0.mod_divides.
          assert (m - i = S (m - S i))%nat as -> by Lia.lia.
          rewrite PeanoNat.Nat.pow_succ_r'. exists (Nat.pow 2 (m - S i) * x)%nat; Lia.lia. }
        Lia.lia. }
      assert (a + b = Nat.div ya 2 + Nat.div yb 2 + Nat.pow 2 m)%nat as ->.
      { destruct Hkmod as [e|e]; rewrite e in Ha, Hb; inversion Ha; inversion Hb; subst a; subst b; cbn in *; Lia.lia. }
      rewrite Hyab. rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia.
  Qed.

  Lemma decompose_S_nth:
    forall i k l,
      forall v, nth_error (@NTT.decompose m i l) k = Some v ->
           nth_error (@NTT.decompose m (S i) l) (2 * k) = Some (Nat.div v 2) /\
           nth_error (@NTT.decompose m (S i) l) (2 * k + 1) = Some (Nat.pow 2 m + Nat.div v 2)%nat.
  Proof.
    intros i k l v Hv. rewrite decompose_S_eq.
    pose proof (nth_error_Some_bound_index _ _ _ Hv) as Hk.
    rewrite length_decompose in Hk.
    assert (Hk': 2 * k + 1 < 2 * Nat.pow 2 i) by Lia.lia.
    assert (Nat.div (2 * k) 2 = k)%nat as X1 by (symmetry; apply (PeanoNat.Nat.div_unique _ 2 k 0); Lia.lia).
    assert (Nat.div (2 * k + 1) 2 = k)%nat as X2 by (symmetry; apply (PeanoNat.Nat.div_unique _ 2 k 1); Lia.lia).
    split.
    all: match goal with
         | |- nth_error ?ll ?ii = _ =>
             assert (Hll: (length ll = 2 * Nat.pow 2 i)%nat) by (rewrite (flat_map_const_length _ 2%nat) by reflexivity; rewrite length_decompose; reflexivity);
             destruct (ListUtil.nth_error_length_exists_value ii ll ltac:(Lia.lia)) as [v' Hv'];
             rewrite Hv';
             apply (ListUtil.flat_map_constant_nth_error 2%nat) in Hv'; try reflexivity;
             destruct Hv' as (y & Hy & <-);
             assert (y = v) as -> by congruence
         end.
    - rewrite (PeanoNat.Nat.mul_comm 2), PeanoNat.Nat.Div0.mod_mul.
      reflexivity.
    - assert (Nat.modulo _ _ = 1)%nat as ->; [|reflexivity].
      symmetry; apply (PeanoNat.Nat.mod_unique _ 2 k 1); Lia.lia.
  Qed.

  Definition zetas (l i: nat) := List.map (fun k => F.pow zeta (N.of_nat k)) (zeta_powers l i).

End Zetas.

Section Gallina.
  (* Lower-level Gallina code for implementing (inverse) NTT *)

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
  Local Notation inttl := (@inttl q field P poly_ops poly_defs zeta m Hm).
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
    (* Delay the multiplications by F.inv (1 + 1) to the end for the inverse ntt *)
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
      forall r k l p (Hr_leq_k: (r <= k)%nat) (Hp: (length p >= Nat.pow 2 k)%nat),
        inttl_gallina r k l p = List.map (F.mul (F.inv (F.pow (1 + 1) r))) (inttl_nomul_gallina r k l p).
    Proof.
      induction r; intros.
      - rewrite (map_ext _ (fun x => x)), map_id; [reflexivity|].
        intro. rewrite F.pow_0_r, Hierarchy.commutative, <- Hierarchy.field_div_definition.
        apply Field.div_one.
      - cbn [inttl_gallina inttl_nomul_gallina].
        assert (Hp': (length p >= 2 * Nat.pow 2 (k - 1))%nat) by (rewrite <- PeanoNat.Nat.pow_succ_r'; assert (S (k - 1) = k) as -> by Lia.lia; assumption).
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

  Section PrecomputedZetas.
    (* Use precomputed zetas *)
    Variable (precomp_zetas: list F).
    Hypothesis (precomp_zetas_eq: precomp_zetas = @zetas q zeta m (Nat.pow 2 m) m).

    Section Forward.
      Fixpoint nttl_precomp (r k u v: nat) (p: list F) :=
        match r with
        | O => p
        | S r' =>
            let p' := Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (nth_default 0%F precomp_zetas (Nat.pow 2 u + v)) p in
            (nttl_precomp r' (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p')) ++
            (nttl_precomp r' (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p'))
        end.

      Lemma nttl_precomp_length:
        forall r k u v p,
          length (nttl_precomp r k u v p) = length p.
      Proof.
        induction r; [reflexivity|].
        intros k u v p. cbn.
        rewrite length_app, IHr, IHr, <- length_app, firstn_skipn, PolynomialCRT.Pmod_cyclotomic_list_length.
        reflexivity.
      Qed.

      Lemma nttl_precomp_spec:
        forall r k u v l p,
          (r + u <= m)%nat ->
          (v < Nat.pow 2 u)%nat ->
          nth_default 0%nat (@NTT.decompose m u (Nat.pow 2 m)) v = l ->
          nttl_precomp r k u v p = nttl_gallina r k l p.
      Proof.
        induction r; [reflexivity|].
        cbn -[decompose Nat.div Nat.mul]; intros k u v l p Hru Hv Heq.
        pose proof (ListUtil.nth_error_Some_nth_default v 0%nat (@decompose m u (Nat.pow 2 m)) ltac:(rewrite length_decompose; assumption)) as Hl.
        rewrite Heq in Hl.
        pose proof (@decompose_S_nth m u v (Nat.pow 2 m) l Hl) as (Hll & Hlr).
        rewrite precomp_zetas_eq; unfold zetas.
        assert (Hlt: (Nat.pow 2 u + v < Nat.pow 2 m)%nat).
        { apply (PeanoNat.Nat.lt_le_trans _ (Nat.pow 2 (S u))).
          - rewrite PeanoNat.Nat.pow_succ_r'.
            Lia.lia.
          - apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
        rewrite (ListUtil.map_nth_default _ _ _ _ 0%nat) by (rewrite zeta_powers_length; auto).
        destruct (@decompose_zeta_powers_nth m u m v (Nat.pow 2 m) ltac:(Lia.lia) Hv) as (x & Hx1 & Hx2).
        rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hx1).
        assert (x = Nat.div l 2) as -> by congruence.
        assert (Hv': 2 * v + 1 < Nat.pow 2 (S u)) by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
        f_equal; apply IHr; try Lia.lia.
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hll).
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hlr).
      Qed.

      Lemma nttl_precomp_S_eq:
        forall r k u v p,
          (S r <= k)%nat ->
          length p = Nat.pow 2 k ->
          nttl_precomp (S r) k u v p =
          concat
            (map (fun '(i, chk) => Pmod_cyclotomic_list (Nat.pow 2 (k - S r)) (nth_default 0%F precomp_zetas (Nat.pow 2 (u + r) + i)) chk)
               (enumerate ((Nat.pow 2 r) * v) (chunk (Nat.pow 2 (k - r)) (nttl_precomp r k u v p)))).
      Proof.
        induction r; intros k u v p Hr_leq_l Hlength.
        - cbn -[chunk]. rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.add_0_r.
          pose proof (NatUtil.pow_nonzero 2 k ltac:(congruence)) as Hnz.
          rewrite chunk_small by Lia.lia.
          cbn. rewrite app_nil_r, firstn_skipn, PeanoNat.Nat.add_0_r. reflexivity.
        - assert (nttl_precomp (S (S r)) k u v p = let p' := Pmod_cyclotomic_list (Nat.pow 2 (k - 1)) (nth_default 0%F precomp_zetas (Nat.pow 2 u + v)) p in
            (nttl_precomp (S r) (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p')) ++
            (nttl_precomp (S r) (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p'))) as -> by reflexivity.
          assert (Nat.pow 2 k = 2 * (Nat.pow 2 (k - 1)))%nat as Hlength' by (rewrite <- PeanoNat.Nat.pow_succ_r'; f_equal; Lia.lia).
          cbn zeta. rewrite (IHr (k - 1)%nat), (IHr (k - 1)%nat); try Lia.lia.
          2: rewrite length_skipn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength; Lia.lia.
          2: rewrite length_firstn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength, PeanoNat.Nat.min_l by Lia.lia; reflexivity.
          rewrite <- concat_app, <- map_app.
          match goal with
          | |- context [enumerate _ ?l ++ enumerate _ _] =>
              assert (Nat.pow 2 r * (2 * v + 1) = (Nat.pow 2 r * (2 * v)) + length l)%nat as ->
          end.
          { rewrite length_chunk by (apply NatUtil.pow_nonzero; Lia.lia).
            rewrite nttl_precomp_length, length_firstn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength.
            rewrite PeanoNat.Nat.min_l by Lia.lia.
            assert (Nat.pow 2 (k - 1) = Nat.pow 2 r * Nat.pow 2 (k - 1 - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
            rewrite Nat.div_up_exact by (apply NatUtil.pow_nonzero; Lia.lia). Lia.lia. }
          rewrite <- enumerate_app, <- chunk_app.
          2: apply NatUtil.pow_nonzero; congruence.
          2:{ rewrite nttl_precomp_length, length_firstn, PolynomialCRT.Pmod_cyclotomic_list_length, Hlength, PeanoNat.Nat.min_l by Lia.lia.
              assert (Nat.pow 2 (k - 1) = Nat.pow 2 r * Nat.pow 2 (k - 1 - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
              apply PeanoNat.Nat.Div0.mod_mul. }
          f_equal. match goal with | |- map ?f ?x = map ?g ?y => assert (x = y) as -> end.
          { f_equal.
            - rewrite PeanoNat.Nat.mul_assoc, (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r'; reflexivity.
            - assert (k - 1 - r = k - S r)%nat as -> by Lia.lia.
              reflexivity. }
          apply map_ext; intros.
          assert (k - 1 - (S r) = k - S (S r))%nat as -> by Lia.lia.
          assert (S u + r = u + S r)%nat as -> by Lia.lia.
          reflexivity.
      Qed.
    End Forward.
    Section Backward.
      Fixpoint inttl_precomp (r k u v: nat) (p: list F) :=
        match r with
        | O => p
        | S r' =>
            recompose_cyclotomic_list
              (Nat.pow 2 (k - 1))
              (F.opp (nth_default 0%F precomp_zetas (Nat.pow 2 (S u) - 1 - v)))
              ((inttl_precomp r' (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p)) ++
               (inttl_precomp r' (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p)))
        end.

      Lemma inttl_precomp_length:
        forall r k u v p,
          length (inttl_precomp r k u v p) = length p.
      Proof.
        induction r; [reflexivity|].
        intros k u v p. cbn.
        rewrite PolynomialCRT.recompose_cyclotomic_list_length, length_app, IHr, IHr, <- length_app, firstn_skipn.
        reflexivity.
      Qed.

      Lemma inttl_precomp_spec:
        forall r k u v l p,
          (r + u <= m)%nat ->
          (v < Nat.pow 2 u)%nat ->
          nth_default 0%nat (@NTT.decompose m u (Nat.pow 2 m)) v = l ->
          inttl_precomp r k u v p = inttl_nomul_gallina r k l p.
      Proof.
        induction r; [reflexivity|].
        cbn -[decompose Nat.div Nat.mul F.inv]; intros k u v l p Hru Hv Heq.
        pose proof (ListUtil.nth_error_Some_nth_default v 0%nat (@decompose m u (Nat.pow 2 m)) ltac:(rewrite length_decompose; assumption)) as Hl.
        rewrite Heq in Hl.
        destruct (ListUtil.nth_error_length_exists_value (Nat.pow 2 (S u) - 1 - (2 * v)) (@decompose m (S u) (Nat.pow 2 m)) ltac:(rewrite length_decompose, PeanoNat.Nat.pow_succ_r'; Lia.lia)) as (b & Hb).
        pose proof (@decompose_S_nth m u v (Nat.pow 2 m) l Hl) as (Hll & Hlr).
        pose proof (@decompose_inv_nth m (S u) ltac:(Lia.lia) (2 * v) ltac:(rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia) _ _ Hll Hb) as Hlb.
        assert (F.inv _ = F.pow zeta (N.of_nat b)) as ->.
        { symmetry; apply Field.right_inv_unique.
          rewrite <- F.pow_add_r, <- Nnat.Nat2N.inj_add, Hlb, Nnat.Nat2N.inj_pow.
          assert (N.of_nat _ ^ _ = 2 ^ N.succ (N.of_nat m))%N as -> by Lia.lia.
          apply (zeta_pow_succ_m (Hm:=Hm)). }
        rewrite precomp_zetas_eq; unfold zetas.
        assert (Hlt: (2 * Nat.pow 2 u - 1 - v < Nat.pow 2 m)%nat).
        { apply (PeanoNat.Nat.lt_le_trans _ (Nat.pow 2 (S u))).
          - rewrite PeanoNat.Nat.pow_succ_r'.
            Lia.lia.
          - apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
        rewrite (ListUtil.map_nth_default _ _ _ _ 0%nat) by (rewrite zeta_powers_length; Lia.lia).
        destruct (@decompose_zeta_powers_nth m u m (Nat.pow 2 u - 1 - v) (Nat.pow 2 m) ltac:(Lia.lia) ltac:(Lia.lia)) as (x & Hx1 & Hx2).
        assert (2 * Nat.pow 2 u - 1 - v = Nat.pow 2 u + (Nat.pow 2 u - 1 - v))%nat as -> by Lia.lia.
        rewrite (ListUtil.nth_error_value_eq_nth_default _ _ _ Hx1).
        destruct (@decompose_nth m (S u) (Nat.pow 2 u - 1 - v)%nat (Nat.pow 2 m) ltac:(rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia)) as (? & Hv1 & Hv2).
        rewrite Hv1 in Hx2; inversion Hx2; subst x; clear Hx2.
        replace (Nat.pow 2 (S u) - 1 - 2 * v)%nat with (2 * (Nat.pow 2 u - 1 - v) + 1)%nat in Hb by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
        rewrite Hb in Hv2; inversion Hv2; subst b; clear Hv2.
        rewrite (@neg_zeta_power_eq q _ zeta m Hm).
        rewrite Nnat.Nat2N.inj_add, Nnat.Nat2N.inj_pow.
        assert (Hv': 2 * v + 1 < Nat.pow 2 (S u)) by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
        f_equal. f_equal; apply IHr; try Lia.lia.
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hll).
        - apply (ListUtil.nth_error_value_eq_nth_default _ _ _ Hlr).
      Qed.

      Lemma inttl_precomp_S_eq:
        forall r k u v p,
          (S r <= k)%nat ->
          length p = Nat.pow 2 k ->
          inttl_precomp (S r) k u v p =
          inttl_precomp r k u v
            (concat
               (map (fun '(i, chk) => recompose_cyclotomic_list (Nat.pow 2 (k - S r)) (F.opp (nth_default 0%F precomp_zetas (Nat.pow 2 (S u + r) - 1 - i))) chk)
                  (enumerate ((Nat.pow 2 r) * v) (chunk (Nat.pow 2 (k - r)) p)))).
      Proof.
        induction r; intros k u v p Hr Hp.
        - rewrite PeanoNat.Nat.add_0_r, PeanoNat.Nat.sub_0_r, PeanoNat.Nat.pow_0_r, PeanoNat.Nat.mul_1_l.
          cbn [inttl_precomp]. pose proof (NatUtil.pow_nonzero 2 k ltac:(congruence)) as Hnz.
          rewrite chunk_small by Lia.lia.
          rewrite firstn_skipn.
          cbn -[Nat.pow]. rewrite app_nil_r. reflexivity.
        - assert (inttl_precomp (S (S r)) k u v p = recompose_cyclotomic_list (Nat.pow 2 (k - 1)) (F.opp (nth_default 0%F precomp_zetas (Nat.pow 2 (S u) - 1 - v))) ((inttl_precomp (S r) (k - 1)%nat (S u) (2 * v) (firstn (Nat.pow 2 (k - 1)) p)) ++ (inttl_precomp (S r) (k - 1)%nat (S u) (2 * v + 1) (skipn (Nat.pow 2 (k - 1)) p)))) as -> by reflexivity.
          assert (length (firstn (Nat.pow 2 (k - 1)) p) = Nat.pow 2 (k - 1))%nat as Hlenl.
          { rewrite length_firstn, PeanoNat.Nat.min_l; [reflexivity|].
            rewrite Hp. apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          assert (length (skipn (Nat.pow 2 (k - 1)) p) = Nat.pow 2 (k - 1))%nat as Hlenr.
          { rewrite length_skipn, Hp. assert (Nat.pow 2 k = 2 * Nat.pow 2 (k - 1))%nat; [|Lia.lia].
            rewrite <- PeanoNat.Nat.pow_succ_r'. f_equal. Lia.lia. }
          rewrite (IHr (k - 1)%nat), (IHr (k - 1)%nat) by Lia.lia.
          cbn [inttl_precomp]. f_equal.
          assert (Nat.pow 2 (k - 1) = Nat.pow 2 r * (Nat.pow 2 (k - 1 - r)))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
          rewrite <- firstn_chunk by (apply NatUtil.pow_nonzero; congruence).
          rewrite <- skipn_chunk by (apply NatUtil.pow_nonzero; congruence).
          rewrite <- firstn_enumerate, <- firstn_map.
          assert (Nat.pow 2 r * (2 * v + 1) = Nat.pow 2 r * (2 * v) + Nat.pow 2 r)%nat as -> by Lia.lia.
          rewrite <- skipn_enumerate, <- skipn_map.
          assert (k - 1 - r = k - (S r))%nat as -> by Lia.lia.
          assert (k - 1 - S r = k - S (S r))%nat as -> by Lia.lia.
          assert (Nat.pow 2 r * (2 * v) = Nat.pow 2 (S r) * v)%nat as -> by (rewrite PeanoNat.Nat.pow_succ_r'; Lia.lia).
          assert (S (S u) + r = S u + S r)%nat as -> by Lia.lia.
          assert (Forall (fun x : list F => length x = Nat.pow 2 (k - S r)) (map (fun '(i, chk) => recompose_cyclotomic_list (Nat.pow 2 (k - S (S r))) (F.opp (nth_default 0 precomp_zetas (Nat.pow 2 (S u + S r) - 1 - i))) chk) (enumerate (Nat.pow 2 (S r) * v) (chunk (Nat.pow 2 (k - S r)) p)))) as HF.
          { apply Forall_map. rewrite Forall_forall.
            intros x Hx. destruct x as (x & y). apply in_combine_r in Hx.
            rewrite PolynomialCRT.recompose_cyclotomic_list_length.
            apply In_nth_error in Hx. destruct Hx as [i Hi].
            pose proof (nth_error_Some_bound_index _ _ _ Hi) as Hlen.
            rewrite length_chunk in Hlen by (apply NatUtil.pow_nonzero; congruence).
            rewrite (nth_error_chunk (Nat.pow 2 _) ltac:(apply NatUtil.pow_nonzero; Lia.lia) _ _ Hlen) in Hi.
            inversion Hi; subst y. rewrite length_firstn, length_skipn, Hp.
            rewrite Hp in Hlen. apply PeanoNat.Nat.min_l.
            replace (Nat.pow 2 k) with (Nat.pow 2 (S r) * Nat.pow 2 (k - S r))%nat in * by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
            rewrite Nat.div_up_exact in Hlen by (apply NatUtil.pow_nonzero; Lia.lia).
            Lia.nia. }
          symmetry; f_equal; f_equal; [apply ListUtil.firstn_concat_same_length|apply ListUtil.skipn_concat_same_length]; auto.
      Qed.
    End Backward.
  End PrecomputedZetas.

  Section Loops.
    (* Gallina code closer to loops *)

    (* [fold_left f (seq start len) state] is roughly equivalent to
       [for (i = start; i < start + len; i++) { f i; }]
       where [f] transforms the state *)

    (* Assume we have a precomputed array of powers of zeta *)
    Variable (precomp_zetas: list F).
    Hypothesis (precomp_zetas_eq: precomp_zetas = @zetas q zeta m (Nat.pow 2 m) m).

    Section ForwardNTT.
      (* Decompose one polynomial of size [2 * len] *)
      Definition polynomial_decompose_loop (start len: nat) (z: F) (p: list F) :=
        List.fold_left
          (fun (p: list F) (i: nat) =>
             let t0 := nth_default 0 p (i + len) in
             let t1 := z * t0 in
             let t2 := nth_default 0 p i in
             let p' := ListUtil.set_nth (i + len) (t2 - t1) p in
             ListUtil.set_nth i (t2 + t1) p')
          (seq start len)
          p.

      Lemma polynomial_decompose_loop_spec:
        forall start len z p,
          polynomial_decompose_loop start len z p = (firstn start p) ++ Pmod_cyclotomic_list len z (skipn start p).
      Proof.
        intros. destruct (Decidable.dec_le_nat (length p) start).
        - rewrite firstn_all2 by Lia.lia.
          rewrite skipn_all by Lia.lia.
          assert (Pmod_cyclotomic_list _ _ _ = nil) as ->.
          { apply ListUtil.length0_nil.
            rewrite PolynomialCRT.Pmod_cyclotomic_list_length. reflexivity. }
          rewrite app_nil_r.
          unfold polynomial_decompose_loop.
          match goal with
          | |- fold_left ?f _ _ = _ =>
              assert (forall k, fold_left f (seq start k) p = p) as ->; [|reflexivity]
          end.
          induction k.
          + reflexivity.
          + rewrite seq_S, fold_left_app, IHk.
            cbn. apply nth_error_ext. intro i.
            do 2 rewrite ListUtil.nth_set_nth.
            rewrite ListUtil.length_set_nth.
            destruct (Compare_dec.lt_dec i (length p)).
            * do 2 (destruct (PeanoNat.Nat.eq_dec _ _); [Lia.lia|]).
              reflexivity.
            * repeat rewrite ListUtil.nth_error_length_error by Lia.lia.
              repeat (destruct (PeanoNat.Nat.eq_dec _ _)); reflexivity.
        - unfold polynomial_decompose_loop, Pmod_cyclotomic_list.
          apply nth_error_ext; intros i.
          destruct (Decidable.dec_lt_nat i start).
          + rewrite nth_error_app1 by (rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia).
            rewrite nth_error_firstn by assumption.
            match goal with
            | |- context [fold_left ?f _ _] =>
                assert (forall k, nth_error (fold_left f (seq start k) p) i = nth_error p i) as ->; [|reflexivity]
            end.
            induction k; [reflexivity|].
            rewrite seq_S, fold_left_app.
            cbn [fold_left].
            repeat rewrite ListUtil.nth_set_nth.
            repeat rewrite ListUtil.length_set_nth.
            destruct (PeanoNat.Nat.eq_dec i _); [Lia.lia|].
            destruct (PeanoNat.Nat.eq_dec i _); [Lia.lia|].
            apply IHk.
          + rewrite nth_error_app2 by (rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia).
            rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
            match goal with
            | |- nth_error (fold_left ?f _ _) i = nth_error (fold_left ?g _ _) _ =>
                assert (forall k i, (i >= start)%nat -> nth_error (fold_left f (seq start k) p) i = nth_error (fold_left g (seq 0 k) (skipn start p)) (i - start)) as ->; [|reflexivity|Lia.lia]
            end.
            clear. induction k; intros i Hi.
            * cbn. rewrite nth_error_skipn. f_equal; Lia.lia.
            * do 2 (rewrite seq_S, fold_left_app).
              rewrite PeanoNat.Nat.add_0_l.
              cbn [fold_left].
              repeat rewrite ListUtil.nth_set_nth.
              repeat rewrite ListUtil.length_set_nth.
              pose proof (IHk (start + k)%nat ltac:(Lia.lia)) as IHk1.
              pose proof (IHk (start + k + len)%nat ltac:(Lia.lia)) as IHk2.
              match goal with
              | |- context [length (fold_left ?f ?l ?x)] =>
                  assert (length (fold_left f l x) = length x) as Hl1
              end; [|rewrite Hl1].
              { clear; induction k; [reflexivity|].
                rewrite seq_S, fold_left_app.
                cbn [fold_left]. repeat rewrite ListUtil.length_set_nth.
                rewrite IHk. reflexivity. }
              match goal with
              | |- context [length (fold_left ?f ?l ?x)] =>
                  assert (length (fold_left f l x) = length x) as Hl2
              end; [|rewrite Hl2].
              { clear; induction k; [reflexivity|].
                rewrite seq_S, fold_left_app.
                cbn [fold_left]. repeat rewrite ListUtil.length_set_nth.
                rewrite IHk. reflexivity. }
              rewrite length_skipn.
              replace (start + k - start)%nat with k in IHk1 by Lia.lia.
              replace (start + k + len - start)%nat with (k + len)%nat in IHk2 by Lia.lia.
              destruct (PeanoNat.Nat.eq_dec i (start + k)) as [->|].
              { destruct (PeanoNat.Nat.eq_dec _ _) as [->|]; [|Lia.lia].
                do 2 (destruct (Compare_dec.lt_dec _ _)); try Lia.lia; auto.
                f_equal.
                rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl1; auto).
                rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl2, length_skipn; auto).
                f_equal; try congruence.
                f_equal.
                destruct (Compare_dec.lt_dec (start + k + len) (length p)).
                - rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl1; auto).
                  rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl2, length_skipn; Lia.lia).
                  congruence.
                - rewrite ListUtil.nth_default_out_of_bounds by (rewrite Hl1; Lia.lia).
                  rewrite ListUtil.nth_default_out_of_bounds by (rewrite Hl2, length_skipn; Lia.lia).
                  reflexivity. }
              destruct (PeanoNat.Nat.eq_dec (i - start) k); [Lia.lia|].
              destruct (PeanoNat.Nat.eq_dec i _); destruct (PeanoNat.Nat.eq_dec (i - start) _); try Lia.lia; [|apply IHk; Lia.lia].
              do 2 (destruct (Compare_dec.lt_dec _ _)); try Lia.lia; auto.
              f_equal.
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl1; Lia.lia).
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk1 by (rewrite Hl2, length_skipn; Lia.lia).
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl1; Lia.lia).
              rewrite (ListUtil.nth_error_Some_nth_default _ 0) in IHk2 by (rewrite Hl2, length_skipn; Lia.lia).
              congruence.
      Qed.

      (* One layer decomposition *)
      Definition polynomial_list_loop (k old_len len: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state _ =>
             let '(l, start, p) := state in
             let l := (l + 1)%nat in
             let z := nth_default 0 precomp_zetas l in
             let p := polynomial_decompose_loop start len z p in
             let start := (start + old_len)%nat in
             (l, start, p))
          (seq 0 k)
          state.

      Lemma polynomial_list_loop_spec:
        forall k old_len len l start p,
          (0 < 2 * len <= old_len)%nat ->
          (start + k * old_len <= length p)%nat ->
          polynomial_list_loop k old_len len (l, start, p) = (l + k, start + k * old_len, firstn start p ++ concat (map (fun '(i, chk) => Pmod_cyclotomic_list len (nth_default 0%F precomp_zetas (l + 1 + i)) chk) (enumerate 0 (firstn k (chunk old_len (skipn start p))))) ++ skipn (start + k * old_len) p)%nat.
      Proof.
        unfold polynomial_list_loop.
        induction k; intros old_len len l start p Hold_len Hp.
        - cbn. repeat rewrite PeanoNat.Nat.add_0_r.
          rewrite firstn_skipn. reflexivity.
        - rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l.
          cbn [fold_left].
          rewrite IHk by Lia.lia.
          rewrite polynomial_decompose_loop_spec.
          f_equal; [f_equal; Lia.lia|].
          rewrite firstn_app, List.firstn_firstn.
          rewrite PeanoNat.Nat.min_r by Lia.lia.
          rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          rewrite skipn_app, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          assert (start + k * old_len - start = k * old_len)%nat as -> by Lia.lia.
          rewrite (skipn_all (start + k * old_len) (firstn _ _)) by (rewrite length_firstn; Lia.lia).
          rewrite app_nil_l. rewrite firstn_app.
          assert (k < (length (chunk old_len (skipn start p))))%nat as Hk.
          { rewrite length_chunk, length_skipn by Lia.lia.
            apply (PeanoNat.Nat.lt_le_trans _ (Nat.div_up (S k * old_len) old_len)).
            - rewrite Nat.div_up_exact by Lia.lia. Lia.lia.
            - apply PeanoNat.Nat.Div0.div_le_mono. Lia.lia. }
          match goal with | |- context [length (concat ?l)] => assert (length (concat l) = k * old_len)%nat as Hco end.
          { rewrite length_concat.
            assert (forall c l, (forall x, In x l -> x = c) -> list_sum l = c * length l)%nat as Hl.
            { clear. induction l; intros; simpl.
              - rewrite PeanoNat.Nat.mul_0_r. reflexivity.
              - rewrite IHl by (intros; apply H; right; auto).
                rewrite (H a ltac:(left; reflexivity)). Lia.lia. }
            rewrite (Hl old_len).
            2:{ intros x Hx. rewrite in_map_iff in Hx.
                destruct Hx as (y & Hy & Hin).
                subst x. rewrite in_map_iff in Hin.
                destruct Hin as ((i & chk) & Hz & Hzz).
                subst y. rewrite PolynomialCRT.Pmod_cyclotomic_list_length.
                apply in_combine_r in Hzz.
                rewrite firstn_chunk in Hzz by Lia.lia.
                apply In_nth_error in Hzz. destruct Hzz as (j & Hj).
                pose proof (ListUtil.nth_error_value_length _ _ _ _ Hj) as Hjj.
                rewrite length_chunk in Hjj by Lia.lia.
                rewrite (nth_error_chunk old_len ltac:(Lia.lia) _ _ Hjj) in Hj.
                inversion Hj; subst chk; clear Hj.
                rewrite length_firstn, length_skipn, length_firstn, length_skipn.
                rewrite (PeanoNat.Nat.min_l (k * _)) by Lia.lia.
                rewrite length_firstn, length_skipn in Hjj.
                rewrite PeanoNat.Nat.min_l in Hjj by Lia.lia.
                rewrite Nat.div_up_exact in Hjj by Lia.lia.
                apply PeanoNat.Nat.min_l.
                rewrite <- PeanoNat.Nat.mul_sub_distr_r.
                transitivity (1 * old_len)%nat; try Lia.lia.
                apply PeanoNat.Nat.mul_le_mono_r. Lia.lia. }
            rewrite length_map, length_map.
            unfold enumerate. rewrite length_combine, length_seq, PeanoNat.Nat.min_id.
            rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia. }
          rewrite Hco, PeanoNat.Nat.sub_diag, firstn_O, app_nil_r.
          rewrite (ListUtil.firstn_all (k * old_len)) by Lia.lia.
          rewrite skipn_app. rewrite Hco, PeanoNat.Nat.sub_diag, skipn_O.
          rewrite (skipn_all (k * old_len)) by Lia.lia.
          rewrite app_nil_l. rewrite (ListUtil.firstn_succ nil) by Lia.lia.
          rewrite enumerate_app, length_firstn.
          rewrite PeanoNat.Nat.min_l by Lia.lia.
          rewrite map_app, concat_app. repeat rewrite <- app_assoc. f_equal.
          f_equal. cbn. assert (l + k + 1 = l + S k)%nat as -> by Lia.lia.
          rewrite app_nil_r, (nth_default_eq _ _ nil).
          rewrite length_chunk in Hk by Lia.lia.
          rewrite nth_chunk by Lia.lia.
          rewrite skipn_skipn. assert (start + k * old_len = k * old_len + start)%nat as <- by Lia.lia.
          assert (forall n1 n2 a l, (2 * n1 <= n2)%nat -> Pmod_cyclotomic_list n1 a l = Pmod_cyclotomic_list n1 a (firstn n2 l) ++ (skipn n2 l)) as X.
          { clear. unfold Pmod_cyclotomic_list.
            set (f a n1 := (fun (l0 : list F) (i : nat) => ListUtil.set_nth i (nth_default 0 l0 i + a * nth_default 0 l0 (i + n1)) (ListUtil.set_nth (i + n1) (nth_default 0 l0 i - a * nth_default 0 l0 (i + n1)) l0))).
            assert (forall k n1 n2 a l, (k <= n1)%nat -> (2 * n1 <= n2)%nat -> fold_left (f a n1) (seq 0 k) l = fold_left (f a n1) (seq 0 k) (firstn n2 l) ++ skipn n2 l) as X; [|intros; apply X; auto].
            induction k; intros n1 n2 a l Hk Hl.
            - cbn. rewrite firstn_skipn. reflexivity.
            - destruct (Decidable.dec_lt_nat n2 (length l)) as [Hlt|Hnlt].
              + rewrite seq_S, fold_left_app, fold_left_app, PeanoNat.Nat.add_0_l.
                rewrite (IHk n1 n2) by Lia.lia. cbn. unfold f.
                repeat rewrite ListUtil.nth_default_app.
                assert (length (fold_left (f a n1) (seq 0 k) (firstn n2 l)) = length (firstn n2 l)) as Y; [|unfold f in Y; repeat rewrite Y].
                { clear. induction k; [reflexivity|].
                  rewrite seq_S, fold_left_app.
                  simpl; unfold f in *; repeat rewrite ListUtil.length_set_nth. auto. }
                rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
                destruct (Compare_dec.lt_dec _ n2); [|Lia.lia].
                destruct (Compare_dec.lt_dec _ n2); [|Lia.lia].
                assert (forall A k (x: A) l1 l2, (k < length l1)%nat -> ListUtil.set_nth k x (l1 ++ l2) = ListUtil.set_nth k x l1 ++ l2) as Z; [|repeat rewrite Z; auto; [rewrite ListUtil.length_set_nth|]; rewrite Y, length_firstn; Lia.lia].
                clear. intros.
                apply nth_error_ext; intros.
                rewrite ListUtil.nth_set_nth, ListUtil.nth_error_app, ListUtil.nth_error_app, length_app, ListUtil.length_set_nth, ListUtil.nth_set_nth.
                destruct (PeanoNat.Nat.eq_dec i k) as [->|Hn]; auto.
                destruct (Compare_dec.lt_dec k _); [|Lia.lia].
                destruct (Compare_dec.lt_dec _ _); [reflexivity|Lia.lia].
              + rewrite skipn_all by Lia.lia.
                rewrite firstn_all2 by Lia.lia.
                rewrite app_nil_r; reflexivity. }
          rewrite (X len old_len) by Lia.lia.
          assert (l + 1 + k = l + S k)%nat as -> by Lia.lia.
          rewrite skipn_skipn. f_equal. f_equal. Lia.lia.
      Qed.

      (* Iterate the layer decomposition n times *)
      Definition polynomial_layer_decomposition_loop (start n: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state i =>
             let '(l, len, p) := state in
             let old_len := len in
             let len := Nat.shiftr len 1 in
             let start := 0%nat in
             let '(l, start, p) := polynomial_list_loop (Nat.shiftl 1 i) old_len len (l, start, p) in
             (l, len, p))
          (seq start n)
          state.

      Definition ntt_loop (r n: nat) (p: list F) :=
        let l := 0%nat in
        let len := Nat.pow 2 n in
        let '(_, _, p) := polynomial_layer_decomposition_loop 0 r (l, len, p)
        in p.

      Lemma ntt_loop_spec:
        forall r n p (Hr_leq_n: (r <= n)%nat) (Hr_leq_m: (r <= m)%nat) (Hp: length p = Nat.pow 2 n),
          ntt_loop r n p = nttl_gallina r n (Nat.pow 2 m) p.
      Proof.
        unfold ntt_loop.
        intros. rewrite <- (@nttl_precomp_spec precomp_zetas precomp_zetas_eq r n 0 0); try Lia.lia; try reflexivity; [|cbv; Lia.lia].
        do 2 rewrite (surjective_pairing _).
        revert r n p Hr_leq_n Hr_leq_m Hp.
        assert (IH: forall r n p (Hr_leq_n: (r <= n)%nat) (Hr_leq_m: (r <= m)%nat) (Hp: length p = Nat.pow 2 n), polynomial_layer_decomposition_loop 0 r (0%nat, Nat.pow 2 n, p) = ((Nat.pow 2 r) - 1, Nat.pow 2 (n - r), nttl_precomp precomp_zetas r n 0 0 p)%nat).
        { induction r; intros.
          - cbv -[Nat.pow Nat.sub].
            rewrite PeanoNat.Nat.sub_0_r. reflexivity.
          - unfold polynomial_layer_decomposition_loop.
            match goal with
            | |- context [fold_left ?f ?l ?state] =>
                assert (fold_left f l state = f (polynomial_layer_decomposition_loop 0 r state) r) as ->
            end.
            { rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l. reflexivity. }
            rewrite nttl_precomp_S_eq by Lia.lia.
            rewrite IHr by Lia.lia.
            assert (Nat.shiftr (Nat.pow 2 (n - r)) 1 = Nat.pow 2 (n - S r)) as ->.
            { rewrite PeanoNat.Nat.shiftr_div_pow2.
              rewrite <- PeanoNat.Nat.pow_sub_r by Lia.lia.
              f_equal; Lia.lia. }
            clear IHr.
            rewrite PeanoNat.Nat.shiftl_1_l.
            rewrite polynomial_list_loop_spec.
            3:{ rewrite nttl_precomp_length.
                rewrite <- PeanoNat.Nat.pow_add_r.
                assert (r + (n - r) = n)%nat as ->; Lia.lia. }
            2:{ rewrite <- PeanoNat.Nat.pow_succ_r'.
                assert (S (n - S r) = n - r)%nat as -> by Lia.lia.
                pose proof (NatUtil.pow_nonzero 2 (n - r) ltac:(Lia.lia)); Lia.lia. }
            assert (Nat.pow 2 r - 1 + _ = 2 * Nat.pow 2 r - 1)%nat as -> by Lia.lia.
            rewrite <- PeanoNat.Nat.pow_succ_r'.
            rewrite <- PeanoNat.Nat.pow_add_r.
            assert (r + (n - r) = n)%nat as -> by Lia.lia.
            rewrite firstn_O, app_nil_l, PeanoNat.Nat.mul_0_r, skipn_O, skipn_all by (rewrite nttl_precomp_length; Lia.lia).
            rewrite app_nil_r, PeanoNat.Nat.add_0_l, firstn_all2.
            2:{ rewrite length_chunk by (apply NatUtil.pow_nonzero; congruence).
                rewrite nttl_precomp_length, Hp.
                assert (Nat.pow 2 n = Nat.pow 2 r * Nat.pow 2 (n - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
                rewrite Nat.div_up_exact; [|apply NatUtil.pow_nonzero]; Lia.lia. }
            f_equal. f_equal. apply map_ext; intros a; destruct a.
            f_equal. f_equal. pose proof (NatUtil.pow_nonzero 2 r ltac:(congruence)); Lia.lia. }
        intros; rewrite IH; auto.
      Qed.
    End ForwardNTT.
    Section BackwardNTT.
      (* Multiply coefficients by c, will be instantiated with c = F.inv (2 ^ n) for some n *)
      Definition div_loop (n: nat) (c: F) (p: list F): list F :=
        fold_left
          (fun l i =>
             let x := nth_default 0%F l i in
             ListUtil.set_nth i (c * x) l)
          (seq 0 n)
          p.

      Lemma div_loop_spec:
        forall n c p, div_loop n c p = (List.map (F.mul c) (firstn n p)) ++ (skipn n p).
      Proof.
        unfold div_loop. induction n; [reflexivity|].
        intros c p. rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l.
        rewrite IHn. cbn [fold_left]. apply nth_error_ext; intros i.
        destruct (Decidable.dec_lt_nat n (length p)) as [Hlt|Hnlt].
        - rewrite ListUtil.nth_error_app, ListUtil.nth_set_nth, nth_error_map, ListUtil.nth_error_app, nth_error_map, length_map.
          rewrite length_map, length_app, length_map, <- length_app, firstn_skipn, ListUtil.nth_default_app, length_map.
          repeat rewrite length_firstn. repeat (rewrite PeanoNat.Nat.min_l by Lia.lia).
          destruct (Compare_dec.lt_dec n n) as [|_]; [Lia.lia|].
          rewrite ListUtil.nth_default_skipn. assert (n + (_ - _) = n)%nat as -> by Lia.lia.
          destruct (PeanoNat.Nat.eq_dec i n) as [->|].
          + destruct (Compare_dec.lt_dec n (length p)) as [_|]; [|Lia.lia].
            destruct (Compare_dec.lt_dec _ _) as [_|]; [|Lia.lia].
            rewrite nth_error_firstn by Lia.lia.
            rewrite (ListUtil.nth_error_Some_nth_default _ 0%F _ Hlt). reflexivity.
          + destruct (Compare_dec.lt_dec i n).
            * destruct (Compare_dec.lt_dec i _); [|Lia.lia].
              do 2 (rewrite nth_error_firstn by Lia.lia).
              reflexivity.
            * destruct (Compare_dec.lt_dec i (S n)); [Lia.lia|].
              do 2 rewrite nth_error_skipn.
              f_equal. Lia.lia.
        - repeat (rewrite skipn_all by Lia.lia). rewrite app_nil_r, app_nil_r.
          repeat (rewrite firstn_all2 by Lia.lia).
          rewrite ListUtil.nth_set_nth.
          destruct (PeanoNat.Nat.eq_dec i n); [subst i|]; auto.
          rewrite length_map. destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|].
          rewrite nth_error_map, ListUtil.nth_error_length_error; [reflexivity|Lia.lia].
      Qed.

      (* Recompose the two polynomials represented by p[start..start+old_len) and p[start+old_en..start+2*old_len) *)
      Definition inverse_polynomial_recompose_loop (i start old_len: nat) (z: F) (p: list F) :=
        List.fold_left
          (fun p j =>
             let tmp := nth_default 0%F p j in
             let x := nth_default 0%F p (j + old_len)%nat in
             let p := ListUtil.set_nth j (tmp + x) p in
             let x := (x - tmp)%F in
             let p := ListUtil.set_nth (j + old_len)%nat (z * x)%F p in
             p
          )
          (seq start i)
          p.

      Lemma inverse_polynomial_recompose_loop_spec:
        forall n start z p,
          inverse_polynomial_recompose_loop n start n z p = (firstn start p) ++ (recompose_cyclotomic_list n (F.opp z) (skipn start p)).
      Proof.
        intros n start z p.
        destruct (Decidable.dec_le_nat (length p) start) as [Hle|Hnle].
        - rewrite firstn_all2 by Lia.lia.
          rewrite skipn_all by Lia.lia.
          assert (recompose_cyclotomic_list _ _ _ = []) as ->.
          { apply ListUtil.length0_nil. rewrite <- (@length_nil F).
            apply PolynomialCRT.recompose_cyclotomic_list_length. }
          rewrite app_nil_r.
          unfold inverse_polynomial_recompose_loop.
          match goal with
          | |- fold_left ?f _ _ = _ =>
              assert (forall k, fold_left f (seq start k) p = p) as ->; [|reflexivity]
          end.
          clear -Hle. induction k; [reflexivity|].
          rewrite seq_S, fold_left_app, IHk. cbn.
          rewrite ListUtil.set_nth_equiv_splice_nth, ListUtil.length_set_nth, ListUtil.set_nth_equiv_splice_nth.
          destruct (Compare_dec.lt_dec _ (length p)); [Lia.lia|].
          destruct (Compare_dec.lt_dec _ (length p)); [Lia.lia|].
          reflexivity.
        - unfold inverse_polynomial_recompose_loop, recompose_cyclotomic_list.
          erewrite (ListUtil.fold_left_ext _ _ _ _ _ (skipn start p)).
          2:{ intros. assert (forall A (l: list A) i x y, ListUtil.set_nth i x (ListUtil.set_nth i y l) = ListUtil.set_nth i x l) as ->.
              { intros. apply nth_error_ext. intro k.
                repeat rewrite ListUtil.nth_set_nth.
                destruct (PeanoNat.Nat.eq_dec k i); auto.
                rewrite ListUtil.length_set_nth. reflexivity. }
              reflexivity. }
          rewrite <- (firstn_skipn start p) at 1.
          match goal with
          | |- fold_left ?f _ _ = _ =>
              assert (forall k l1 l2, length l1 = start -> fold_left f (seq start k) (l1 ++ l2) = l1 ++ (fold_left f (seq 0 k) l2)) as ->
          end.
          3: rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia.
          2:{ f_equal. apply ListUtil.fold_left_ext.
              intros l j. repeat rewrite ListUtil.set_nth_nth_default_full.
              repeat rewrite ListUtil.length_set_nth.
              destruct (PeanoNat.Nat.eq_dec _ _) as [_|]; [|congruence].
              destruct (Compare_dec.lt_dec _ _) as [Hlt|Hnlt].
              + f_equal. rewrite Ring.mul_opp_l, <- Ring.mul_opp_r.
                do 2 rewrite Hierarchy.ring_sub_definition.
                rewrite Group.inv_op, Group.inv_inv. reflexivity.
              + repeat rewrite (ListUtil.set_nth_equiv_splice_nth (j + n)).
                repeat rewrite ListUtil.length_set_nth.
                destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|]. reflexivity. }
          induction k; intros l1 l2 Hl1; [reflexivity|].
          rewrite seq_S, fold_left_app, IHk; auto.
          rewrite seq_S, fold_left_app. rewrite PeanoNat.Nat.add_0_l.
          cbn [fold_left].
          rewrite ListUtil.nth_default_app.
          destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|].
          assert (start + k + n - length l1 = k + n)%nat as -> by Lia.lia.
          rewrite ListUtil.nth_default_app.
          destruct (Compare_dec.lt_dec _ _) as [|_]; [Lia.lia|].
          assert (start + k - length l1 = k)%nat as -> by Lia.lia.
          assert (forall A k (x: A) l1 l2, (length l1 <= k)%nat -> ListUtil.set_nth k x (l1 ++ l2) = l1 ++ ListUtil.set_nth (k - length l1) x l2) as Z; [|repeat rewrite Z; try Lia.lia; repeat (f_equal; try Lia.lia)].
          clear. induction k; intros x l1 l2 Hk.
          + destruct l1; [|cbn in Hk; Lia.lia].
            reflexivity.
          + destruct l1; [reflexivity|].
            cbn in Hk. rewrite <- app_comm_cons, <- ListUtil.cons_set_nth.
            rewrite IHk by Lia.lia.
            cbn [length]. assert (S k - S _ = k - length l1)%nat as -> by Lia.lia.
            rewrite app_comm_cons. reflexivity.
      Qed.

      (* Iterate once over the whole array and recompose all polynomials *)
      Definition inverse_polynomial_list_loop (k old_len len: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state _ =>
             let '(l, start, p) := state in
             let l := (l - 1)%nat in
             let z := nth_default 0%F precomp_zetas l in
             let p := inverse_polynomial_recompose_loop old_len start old_len z p in
             let start := (start + len)%nat in
             (l, start, p))
          (seq 0 k)
          state.

      Lemma inverse_polynomial_list_loop_spec:
        forall k old_len len l start p,
          (k <= l)%nat ->
          (0 < 2 * old_len <= len)%nat ->
          (start + k * len <= length p)%nat ->
          inverse_polynomial_list_loop k old_len len (l, start, p) =
            (l - k, start + k * len, firstn start p ++ concat (map (fun '(i, chk) => recompose_cyclotomic_list old_len (F.opp (nth_default 0%F precomp_zetas (l - 1 - i))) chk) (enumerate 0 (firstn k (chunk len (skipn start p))))) ++ skipn (start + k * len) p)%nat.
      Proof.
        unfold inverse_polynomial_list_loop.
        induction k; intros old_len len l start p Hl Hlen Hp.
        - cbn. rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.add_0_r.
          rewrite firstn_skipn. reflexivity.
        - rewrite seq_S, fold_left_app, PeanoNat.Nat.add_0_l, IHk by Lia.lia.
          cbn [fold_left]. f_equal; [f_equal; Lia.lia|].
          rewrite inverse_polynomial_recompose_loop_spec.
          rewrite firstn_app, List.firstn_firstn, PeanoNat.Nat.min_r by Lia.lia.
          rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          assert (start + k * len - start = k * len)%nat as -> by Lia.lia.
          rewrite firstn_app.
          assert (k < (length (chunk len (skipn start p))))%nat as Hk.
          { rewrite length_chunk, length_skipn by Lia.lia.
            apply (PeanoNat.Nat.lt_le_trans _ (Nat.div_up (S k * len) len)).
            - rewrite Nat.div_up_exact by Lia.lia. Lia.lia.
            - apply PeanoNat.Nat.Div0.div_le_mono. Lia.lia. }
          match goal with | |- context [length (concat ?l)] => assert (length (concat l) = k * len)%nat as Hco end.
          { rewrite length_concat.
            assert (forall c l, (forall x, In x l -> x = c) -> list_sum l = c * length l)%nat as Hcl.
            { clear. induction l; intros; simpl.
              - rewrite PeanoNat.Nat.mul_0_r. reflexivity.
              - rewrite IHl by (intros; apply H; right; auto).
                rewrite (H a ltac:(left; reflexivity)). Lia.lia. }
            rewrite (Hcl len).
            2:{ intros x Hx. rewrite in_map_iff in Hx.
                destruct Hx as (y & Hy & Hin).
                subst x. rewrite in_map_iff in Hin.
                destruct Hin as ((i & chk) & Hz & Hzz).
                subst y. rewrite PolynomialCRT.recompose_cyclotomic_list_length.
                apply in_combine_r in Hzz.
                rewrite firstn_chunk in Hzz by Lia.lia.
                apply In_nth_error in Hzz. destruct Hzz as (j & Hj).
                pose proof (ListUtil.nth_error_value_length _ _ _ _ Hj) as Hjj.
                rewrite length_chunk in Hjj by Lia.lia.
                rewrite (nth_error_chunk len ltac:(Lia.lia) _ _ Hjj) in Hj.
                inversion Hj; subst chk; clear Hj.
                rewrite length_firstn, length_skipn, length_firstn, length_skipn.
                rewrite (PeanoNat.Nat.min_l (k * _)) by Lia.lia.
                rewrite length_firstn, length_skipn in Hjj.
                rewrite PeanoNat.Nat.min_l in Hjj by Lia.lia.
                rewrite Nat.div_up_exact in Hjj by Lia.lia.
                apply PeanoNat.Nat.min_l.
                rewrite <- PeanoNat.Nat.mul_sub_distr_r.
                transitivity (1 * len)%nat; try Lia.lia.
                apply PeanoNat.Nat.mul_le_mono_r. Lia.lia. }
            rewrite length_map, length_map.
            unfold enumerate. rewrite length_combine, length_seq, PeanoNat.Nat.min_id.
            rewrite length_firstn, PeanoNat.Nat.min_l; Lia.lia. }
          rewrite (@firstn_all2 _ (k * len)%nat) by Lia.lia.
          rewrite Hco, PeanoNat.Nat.sub_diag, firstn_O, app_nil_r.
          rewrite skipn_app, (skipn_all (start + k * len)) by (rewrite length_firstn; Lia.lia).
          rewrite app_nil_l, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          assert (start + k * len - start = k * len)%nat as -> by Lia.lia.
          rewrite skipn_app, Hco, PeanoNat.Nat.sub_diag, skipn_O.
          rewrite (ListUtil.firstn_succ nil), enumerate_app, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
          rewrite map_app, PeanoNat.Nat.add_0_l. cbn.
          rewrite concat_app, (nth_default_eq _ _ []), nth_chunk by (rewrite length_chunk in Hk; Lia.lia).
          rewrite skipn_skipn, (skipn_all (k * len)) by Lia.lia.
          rewrite app_nil_l. cbn [concat]. rewrite app_nil_r.
          assert (forall n1 n2 a l, (2 * n1 <= n2)%nat -> recompose_cyclotomic_list n1 a l = recompose_cyclotomic_list n1 a (firstn n2 l) ++ (skipn n2 l)) as X.
          { clear. unfold recompose_cyclotomic_list.
            set (f a n1 := (fun (l0 : list F) (i : nat) => ListUtil.set_nth (i + n1) (a *nth_default 0(ListUtil.set_nth (i + n1) (nth_default 0 l0 i - nth_default 0 l0 (i + n1)) (ListUtil.set_nth i (nth_default 0 l0 i + nth_default 0 l0 (i + n1)) l0)) (i + n1)) (ListUtil.set_nth (i + n1) (nth_default 0 l0 i - nth_default 0 l0 (i + n1)) (ListUtil.set_nth i (nth_default 0 l0 i + nth_default 0 l0 (i + n1)) l0)))).
            assert (forall k n1 n2 a l, (k <= n1)%nat -> (2 * n1 <= n2)%nat -> fold_left (f a n1) (seq 0 k) l = fold_left (f a n1) (seq 0 k) (firstn n2 l) ++ skipn n2 l) as X; [|intros; apply X; auto].
            assert (forall A g k n2 (l: list A), (forall l i, (i < k)%nat -> g l i = g (firstn n2 l) i ++ skipn n2 l) -> (forall l i, length (g l i) = length l)%nat -> fold_left g (seq 0 k) l = fold_left g (seq 0 k) (firstn n2 l) ++ skipn n2 l) as Z.
            2: { intros; apply Z.
                 - intros. unfold f.
                   repeat rewrite ListUtil.set_nth_set_nth.
                   destruct (Decidable.dec_le_nat (length l0) n2).
                   { rewrite firstn_all2 by Lia.lia.
                     rewrite skipn_all by Lia.lia.
                     rewrite app_nil_r. reflexivity. }
                   rewrite <- ListUtil.set_nth_app_l by (rewrite ListUtil.length_set_nth, length_firstn; Lia.lia).
                   rewrite <- ListUtil.set_nth_app_l by (rewrite length_firstn; Lia.lia).
                   rewrite firstn_skipn. repeat rewrite ListUtil.nth_default_firstn.
                   destruct (Compare_dec.le_dec n2 (length l0)); [|Lia.lia].
                   do 2 (destruct (Compare_dec.lt_dec _ _); [|Lia.lia]).
                   f_equal. f_equal.
                   repeat rewrite ListUtil.set_nth_nth_default_full.
                   repeat rewrite ListUtil.length_set_nth.
                   rewrite length_firstn, PeanoNat.Nat.min_l by Lia.lia.
                   destruct (PeanoNat.Nat.eq_dec _ (i + n1)) as [_|]; [|Lia.lia].
                   do 2 destruct (Compare_dec.lt_dec _ _); auto; Lia.lia.
                 - intros; unfold f; repeat rewrite ListUtil.length_set_nth. reflexivity. }
            clear f. induction k; intros n2 l Hg Hlen; [cbn; rewrite firstn_skipn; reflexivity|].
            destruct (Decidable.dec_le_nat (length l) n2) as [Hle|Hnle].
            { rewrite firstn_all2, skipn_all by Lia.lia.
              rewrite app_nil_r. reflexivity. }
            rewrite seq_S, fold_left_app, fold_left_app, PeanoNat.Nat.add_0_l, (IHk n2); auto.
            cbn [fold_left]. assert (forall l z, length (fold_left g l z) = length z) as W.
            { clear -Hlen. induction l; intros; cbn; [|rewrite IHl, Hlen]; reflexivity. }
            rewrite (Hg (_ ++ _)) by Lia.lia.
            rewrite firstn_app. rewrite W, length_firstn, PeanoNat.Nat.min_l by Lia.lia.
            rewrite PeanoNat.Nat.sub_diag, firstn_O, app_nil_r.
            rewrite ListUtil.skipn_app_sharp by (rewrite W, length_firstn; apply PeanoNat.Nat.min_l; Lia.lia).
            rewrite firstn_all2 by (rewrite W, length_firstn, PeanoNat.Nat.min_l; Lia.lia).
            reflexivity. }
          rewrite (X old_len len) by Lia.lia.
          rewrite skipn_skipn. repeat rewrite <- app_assoc.
          repeat (f_equal; try Lia.lia).
      Qed.

      (* Iterate r times the polynomial recomposition *)
      Definition inverse_layer_recomposition_loop (r: nat) (state: nat * nat * list F) :=
        List.fold_left
          (fun state i =>
             let '(l, len, p) := state in
             let start := 0%nat in
             let old_len := len in
             let len := Nat.shiftl len 1 in
             let '(l, _, p) :=
               inverse_polynomial_list_loop (Nat.shiftl 1 ((r - 1) - i))%nat old_len len (l, start, p) in
             (l, len, p))
          (seq 0 r)
          state.

      Lemma inverse_layer_recomposition_loop_spec:
        forall r k l len p,
          (length p = Nat.pow 2 k) ->
          (r <= k)%nat ->
          (len = Nat.pow 2 (k - r))%nat ->
          (l = Nat.pow 2 r)%nat ->
          inverse_layer_recomposition_loop r (l, len, p) = (1, Nat.shiftl len r, inttl_precomp precomp_zetas r k 0 0 p)%nat.
      Proof.
        induction r; intros n l len p Hp Hrn Hlen Hl.
        - cbn. rewrite Hl. reflexivity.
        - assert (len <> 0)%nat as Hlennz by (rewrite Hlen; apply NatUtil.pow_nonzero; congruence).
          subst len. subst l.
          unfold inverse_layer_recomposition_loop in IHr.
          unfold inverse_layer_recomposition_loop.
          rewrite <- cons_seq, ListUtil.List.fold_left_cons.
          rewrite <- seq_shift, ListUtil.fold_left_map.
          rewrite PeanoNat.Nat.sub_0_r, PeanoNat.Nat.shiftl_1_l, PeanoNat.Nat.shiftl_mul_pow2, PeanoNat.Nat.pow_1_r.
          rewrite inverse_polynomial_list_loop_spec.
          2:{ apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          2:{ Lia.lia. }
          2:{ rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.add_0_l.
              rewrite <- PeanoNat.Nat.pow_add_r, Hp.
              apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          rewrite firstn_O, app_nil_l, skipn_O, PeanoNat.Nat.add_0_l, skipn_all.
          2:{ rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r'.
              rewrite <- PeanoNat.Nat.pow_add_r, Hp.
              apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          rewrite app_nil_r. rewrite inttl_precomp_S_eq by assumption.
          rewrite PeanoNat.Nat.mul_0_r. rewrite firstn_chunk by Lia.lia.
          rewrite firstn_all2.
          2:{ rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r', <- PeanoNat.Nat.pow_add_r, Hp.
              apply PeanoNat.Nat.pow_le_mono_r; Lia.lia. }
          rewrite (PeanoNat.Nat.mul_comm _ 2), <- PeanoNat.Nat.pow_succ_r'.
          assert (S (n - S r) = n - r)%nat as -> by Lia.lia.
          assert (1 + r = S r)%nat as -> by Lia.lia.
          erewrite ListUtil.fold_left_ext.
          + erewrite (IHr n); try Lia.lia.
            * f_equal. f_equal.
              do 2 rewrite PeanoNat.Nat.shiftl_mul_pow2.
              rewrite <- PeanoNat.Nat.pow_add_r, <- PeanoNat.Nat.pow_add_r.
              f_equal; Lia.lia.
            * rewrite (length_concat_same_length (Nat.pow 2 (n - r))).
              { rewrite length_map. unfold enumerate.
                rewrite length_combine, length_chunk by (apply NatUtil.pow_nonzero; congruence).
                rewrite length_seq, PeanoNat.Nat.min_id.
                rewrite Hp. assert (Nat.pow 2 n = Nat.pow 2 r * Nat.pow 2 (n - r))%nat as -> by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
                rewrite Nat.div_up_exact by (apply NatUtil.pow_nonzero; congruence).
                reflexivity. }
              apply Forall_map. rewrite Forall_forall.
              intros x Hx. destruct x as (x & y). apply in_combine_r in Hx.
              rewrite PolynomialCRT.recompose_cyclotomic_list_length.
              apply In_nth_error in Hx. destruct Hx as [i Hi].
              pose proof (nth_error_Some_bound_index _ _ _ Hi) as Hlen.
              rewrite length_chunk in Hlen by (apply NatUtil.pow_nonzero; congruence).
              rewrite (nth_error_chunk (Nat.pow 2 _) ltac:(apply NatUtil.pow_nonzero; Lia.lia) _ _ Hlen) in Hi.
              inversion Hi; subst y. rewrite length_firstn, length_skipn, Hp.
              rewrite Hp in Hlen. apply PeanoNat.Nat.min_l.
              replace (Nat.pow 2 n) with (Nat.pow 2 r * Nat.pow 2 (n - r))%nat in * by (rewrite <- PeanoNat.Nat.pow_add_r; f_equal; Lia.lia).
              rewrite Nat.div_up_exact in Hlen by (apply NatUtil.pow_nonzero; Lia.lia).
              Lia.nia.
            * assert (S r - 1 = r)%nat as -> by Lia.lia.
              rewrite PeanoNat.Nat.pow_succ_r'. Lia.lia.
          + intros ((a & b) & c) d. cbn zeta.
            assert (S r - 1 - S d = r - 1 - d)%nat as -> by Lia.lia.
            reflexivity.
      Qed.

      (* The whole thing  *)
      (* length p = 2 ^ k *)
      (* Each polynomial have size 2 ^ (k - r) at the beginning *)
      Definition inverse_ntt_loop (r k: nat) (p: list F) :=
        let l := Nat.shiftl 1 r in
        let len := Nat.shiftl 1 (k - r) in
        let '(_, _, p) :=
          inverse_layer_recomposition_loop r (l, len, p) in
        let p := div_loop (Nat.shiftl 1 k) (F.inv (F.pow (1 + 1) r)) p
        in p.

      Lemma inverse_ntt_loop_spec:
        forall r k p,
          (r <= k)%nat ->
          (r <= m)%nat ->
          length p = Nat.pow 2 k ->
          inverse_ntt_loop r k p = inttl_gallina r k (Nat.pow 2 m) p.
      Proof.
        intros r k p Hrk Hrm Hp. rewrite inttl_nomul_gallina_spec by Lia.lia.
        unfold inverse_ntt_loop.
        repeat rewrite PeanoNat.Nat.shiftl_mul_pow2.
        repeat rewrite PeanoNat.Nat.mul_1_l.
        rewrite (inverse_layer_recomposition_loop_spec _ k) by Lia.lia.
        rewrite <- (inttl_precomp_spec _ precomp_zetas_eq _ _ 0 0); try (cbn; Lia.lia).
        rewrite div_loop_spec.
        assert (Nat.pow 2 k = length (inttl_precomp precomp_zetas r k 0 0 p)) as -> by (rewrite inttl_precomp_length; auto).
        rewrite firstn_all, skipn_all by Lia.lia.
        rewrite app_nil_r. reflexivity.
      Qed.
    End BackwardNTT.

    (* Full specs relating to the dependent-type-style specifications *)
    Lemma ntt_loop_full_spec:
      forall n p,
        proj1_sig (nttl n p) = ntt_loop (Nat.min n m) n (proj1_sig p).
    Proof.
      intros. unfold nttl. rewrite nttl_gallina_spec.
      symmetry; apply ntt_loop_spec; [Lia.lia|Lia.lia|].
      rewrite (proj2_sig p), PolynomialCRT.posicyclic_measure; [Lia.lia|].
      pose proof (NatUtil.pow_nonzero 2 n ltac:(congruence)); Lia.lia.
    Qed.

    Lemma inverse_ntt_loop_full_spec:
      forall n p,
        proj1_sig (inttl n p) = inverse_ntt_loop (Nat.min n m) n (proj1_sig p).
    Proof.
      intros. unfold inttl. rewrite inttl_gallina_spec.
      symmetry; apply inverse_ntt_loop_spec; [Lia.lia|Lia.lia|].
      rewrite (proj2_sig p), map_map, (ListUtil.list_sum_constant (Nat.pow 2 (n - Nat.min n m))).
      - rewrite length_map, length_decompose, <- PeanoNat.Nat.pow_add_r.
        f_equal; Lia.lia.
      - apply Forall_map. rewrite Forall_forall.
        intros. rewrite PolynomialCRT.posicyclic_measure; [Lia.lia|].
        pose proof (NatUtil.pow_nonzero 2 (n - Nat.min n m) ltac:(congruence)); Lia.lia.
    Qed.
  End Loops.

  Section Delayed_add_sub_reduce.
    (* TODO: Parameterize over the field representation *)

    (* We delay reducing modulo q in the butterfly operation as late as possible.
       t := b * z (mod q)
       y0 := x + t (mod q)
       y1 := x - t (mod q)

       becomes

       t := b * z (mod q)
       y0 := x + t
       y1 := x + (q - t)          // assuming unsigned representation
       ...
       reduce y0, y1 at some point later *)
    Variable (precomp_zetas: list Z).
    Hypothesis (precomp_zetas_eq: precomp_zetas = List.map F.to_Z (@zetas q zeta m (Nat.pow 2 m) m)).

    Lemma precomp_zetas_eq':
      map (F.of_Z q) precomp_zetas = (@zetas q zeta m (Nat.pow 2 m) m).
    Proof.
      rewrite precomp_zetas_eq, map_map, (map_ext _ id); [apply map_id|].
      apply F.of_Z_to_Z.
    Qed.

    Lemma precomp_zetas_bounds:
      forall i, 0 <= (nth_default 0%Z precomp_zetas i) < q.
    Proof.
      intros. rewrite precomp_zetas_eq.
      rewrite <- (@F.to_Z_0 q), ListUtil.map_nth_default_always.
      apply F.to_Z_range; Lia.lia.
    Qed.

    Variables (Zreduce: Z -> Z) (Zreduce_bounds: Z).

    (* Assumes Zreduce is a modular reduction operation *)
    Hypothesis Zreduce_ok: forall x, (0 <= x <= Zreduce_bounds)%Z -> Zreduce x = Z.modulo x q.

    (* Assumes Zreduce can at least reduces the multiplication of two field elements *)
    Hypothesis Zreduce_bounds_ge_q2: (q * q <= Zreduce_bounds)%Z.

    Lemma Zreduce_0:
      Zreduce 0 = 0%Z.
    Proof. rewrite Zreduce_ok; [apply Z.mod_0_l; congruence|Lia.lia]. Qed.

    Lemma Zreduce_small:
      forall x, (0 <= x < q)%Z -> Zreduce x = x.
    Proof. intros; rewrite Zreduce_ok; [apply Z.mod_small; auto|Lia.nia]. Qed.

    Lemma Zreduce_mod:
      forall x, Zreduce (x mod q) = x mod q.
    Proof. intros; apply Zreduce_small. apply Zdiv.Z_mod_lt. Lia.lia. Qed.

    (* We can do k_iter iterations before having to reduce *)
    Local Notation k_iter := (Z.div Zreduce_bounds (q * q)).

    (* k_iter is at least 1, so worst case scenario is reducing after each iteration *)
    Local Lemma k_iter_ge_1:
      (1 <= k_iter)%Z.
    Proof.
      transitivity ((q * q) / (q * q))%Z; [|apply Div.Z.div_le_mono_nonneg; Lia.lia].
      rewrite Z.div_same; Lia.lia.
    Qed.

    Local Lemma k_iter_times_q2_le_reduce_bounds:
      (k_iter * q * q <= Zreduce_bounds)%Z.
    Proof.
      rewrite <- Z.mul_assoc, Z.mul_comm.
      apply Zdiv.Z_mult_div_ge. Lia.lia.
    Qed.

    Section Bounded_by.
      (* We are going to manipulate coefficients bounded by a multiple of q.
         This section defines this predicate and some related lemmas.
      *)
      Definition Zbounded_by (n: nat) (x: Z) :=
        (0 <= x <= n * q)%Z.

      Lemma bounded_by_monotone (i j: nat) (x: Z):
        (i <= j)%nat ->
        Zbounded_by i x ->
        Zbounded_by j x.
      Proof. unfold Zbounded_by; Lia.nia. Qed.

      Lemma bounded_by_0_r:
        forall n, Zbounded_by n 0.
      Proof. unfold Zbounded_by; Lia.lia. Qed.

      Lemma mod_bounded_by_1:
        forall x, Zbounded_by 1 (x mod q).
      Proof.
        intros. pose proof (Zdiv.Z_mod_lt x q ltac:(Lia.lia)).
        unfold Zbounded_by. Lia.lia.
      Qed.

      Lemma bounded_by_reduce_eq (n: nat) (x: Z):
        (n <= k_iter * q)%Z ->
        Zbounded_by n x ->
        Zreduce x = F.to_Z (@F.of_Z q x).
      Proof.
        unfold Zbounded_by. intros. rewrite F.to_Z_of_Z.
        apply Zreduce_ok. split; [Lia.lia|].
        etransitivity; [|apply k_iter_times_q2_le_reduce_bounds].
        Lia.nia.
      Qed.

      Lemma bounded_by_reduce (n: nat) (x: Z):
        (n <= k_iter * q)%Z ->
        Zbounded_by n x ->
        Zbounded_by 1 (Zreduce x).
      Proof.
        intros. rewrite (bounded_by_reduce_eq n); auto.
        pose proof (@F.to_Z_range q (F.of_Z q x) ltac:(Lia.lia)).
        unfold Zbounded_by; Lia.lia.
      Qed.

      Lemma bounded_by_add (n: nat) (x y: Z):
        Zbounded_by n x ->
        Zbounded_by 1 y ->
        Zbounded_by (n + 1)%nat (x + y).
      Proof. unfold Zbounded_by; intros. Lia.lia. Qed.

      Lemma bounded_by_sub (n: nat) (x y: Z):
        Zbounded_by n x ->
        Zbounded_by 1 y ->
        Zbounded_by (n + 1)%nat (x + (q - y)).
      Proof. unfold Zbounded_by; intros. Lia.lia. Qed.

      Lemma bounded_by_mul (n: nat) (x y: Z):
        Zbounded_by n x ->
        Zbounded_by 1 y ->
        Zbounded_by (n * Pos.to_nat q)%nat (x * y).
      Proof. unfold Zbounded_by; intros. Lia.nia. Qed.
    End Bounded_by.

    Section ForwardNTT.
      (* We parameterize over whether reducing is done *)
      Definition polynomial_decompose_loop_may_reduce (reduce_bool: bool) (start len: nat) (z: Z) (p: list Z) :=
        List.fold_left
          (fun (p: list Z) (i: nat) =>
             let t0 := nth_default 0%Z p (i + len) in
             let t1 := Zreduce (z * t0)%Z in
             let t2 := nth_default 0%Z p i in
             let p' := ListUtil.set_nth (i + len) ((if reduce_bool then Zreduce else id) (t2 + (q - t1)))%Z p in
             ListUtil.set_nth i ((if reduce_bool then Zreduce else id) (t2 + t1))%Z p')
          (seq start len)
          p.

      Lemma polynomial_decompose_loop_may_reduce_spec:
        forall reduce_bool start len z p (ll lr: nat),
          (0 <= z < q)%Z ->
          (ll <= k_iter * q)%Z ->
          (lr <= k_iter)%Z ->
          (1 <= ll)%nat -> (1 <= lr)%nat ->
          Forall (Zbounded_by ll) (firstn start p) ->
          Forall (Zbounded_by lr) (skipn start p) ->
          let p' := polynomial_decompose_loop_may_reduce reduce_bool start len z p in
          let p_spec' := (polynomial_decompose_loop start len (F.of_Z q z) (List.map (F.of_Z q) p)) in
          (* bounds specs *)
          Forall (Zbounded_by ll) (firstn start p') /\
          Forall (Zbounded_by (if reduce_bool then 1 else lr + 1)) (firstn (2 * len) (skipn start p')) /\
          Forall (Zbounded_by lr) (skipn (start + 2 * len) p') /\
          (* functional specs *)
          (List.map F.to_Z p_spec' = List.map Zreduce p') /\
          (if reduce_bool then firstn (2 * len) (skipn start (List.map F.to_Z p_spec')) = firstn (2 * len) (skipn start p') else True) /\
          (firstn start p' = firstn start p) /\
          (skipn (start + 2 * len) p' = skipn (start + 2 * len) p).
      Proof.
        set (f_rec := fun u (reduce_bool: bool) start len z p => List.fold_left
                                            (fun (p: list Z) (i: nat) =>
                                               let t0 := nth_default 0%Z p (i + len) in
                                               let t1 := Zreduce (z * t0)%Z in
                                               let t2 := nth_default 0%Z p i in
                                               let p' := ListUtil.set_nth (i + len) ((if reduce_bool then Zreduce else id) (t2 + (q - t1)))%Z p in
                                               ListUtil.set_nth i ((if reduce_bool then Zreduce else id) (t2 + t1))%Z p')
                                            (seq start u)
                                            p).
        set (f_spec_rec := fun u start len z p => List.fold_left
                                                 (fun (p: list F) (i: nat) =>
                                                    let t0 := nth_default 0 p (i + len) in
                                                    let t1 := z * t0 in
                                                    let t2 := nth_default 0 p i in
                                                    let p' := ListUtil.set_nth (i + len) (t2 - t1) p in
                                                    ListUtil.set_nth i (t2 + t1) p')
                                                 (seq start u)
                                                 p).
        assert (forall reduce_bool u start len z p (ll lr: nat),
                  (u <= len)%nat ->
                  (0 <= z < q)%Z ->
                  (ll <= k_iter * q)%Z ->
                  (lr <= k_iter)%Z ->
                  (1 <= ll)%nat -> (1 <= lr)%nat ->
                  Forall (Zbounded_by ll) (firstn start p) ->
                  Forall (Zbounded_by lr) (skipn start p) ->
                  let p' := f_rec u reduce_bool start len z p in
                  let p_spec' := f_spec_rec u start len (F.of_Z q z) (List.map (F.of_Z q) p) in
                  (firstn start p' = firstn start p) /\
                  Forall (Zbounded_by (if reduce_bool then 1 else lr + 1)) (firstn u (skipn start p')) /\
                  (firstn (len - u) (skipn (start + u) p') = firstn (len - u) (skipn (start + u) p)) /\
                  Forall (Zbounded_by (if reduce_bool then 1 else lr + 1)) (firstn u (skipn (start + len) p')) /\
                  (skipn (start + len + u) p' = skipn (start + len + u) p) /\
                  (List.map F.to_Z p_spec' = List.map Zreduce p') /\
                  (if reduce_bool then firstn u (skipn start (List.map F.to_Z p_spec')) = firstn u (skipn start p') /\ firstn u (skipn (start + len) (List.map F.to_Z p_spec')) = firstn u (skipn (start + len) p') else True)) as IH.
        { induction u; intros start len z p ll lr Hu Hz Hllred Hk_iter Hllpos Hlrpos Hll Hlr.
          - assert (f_rec _ _ _ _ _ _ = p) as -> by reflexivity.
            cbn. rewrite <- (firstn_skipn len (skipn start p)) in Hlr.
            rewrite skipn_skipn, Forall_app in Hlr. destruct Hlr as (Hlr1 & Hlr2).
            rewrite PeanoNat.Nat.add_0_r, PeanoNat.Nat.add_0_r, PeanoNat.Nat.sub_0_r, (PeanoNat.Nat.add_comm start len).
            repeat split; auto. 2: destruct reduce_bool; split; reflexivity.
            rewrite map_map. apply map_ext_in.
            intros x Hx. symmetry.
            assert (ll <= Nat.max ll lr)%nat as Z0 by Lia.lia.
            assert (lr <= Nat.max ll lr)%nat as Z1 by Lia.lia.
            apply (@Forall_impl _ (Zbounded_by ll) (Zbounded_by (Nat.max ll lr)%nat) ltac:(intros; apply (bounded_by_monotone ll); auto)) in Hll.
            apply (@Forall_impl _ (Zbounded_by lr) (Zbounded_by (Nat.max ll lr)%nat) ltac:(intros; apply (bounded_by_monotone lr); auto)) in Hlr1, Hlr2.
            apply (bounded_by_reduce_eq (Nat.max ll lr)); [Lia.nia|].
            rewrite <- (firstn_skipn start) in Hx.
            apply in_app_or in Hx. destruct Hx as [Hx|Hx].
            + apply (Forall_In Hll); auto.
            + rewrite <- (firstn_skipn len), skipn_skipn in Hx.
              apply in_app_or in Hx. destruct Hx as [Hx|Hx]; [apply (Forall_In Hlr1)|apply (Forall_In Hlr2)]; auto.
          - assert (Hlrred: (lr + 1 <= k_iter * q)%Z).
            { transitivity (2 * lr)%Z; [Lia.lia|].
              pose proof (prime_ge_2 q prime_q). Lia.nia. }
            assert (Hz': Zbounded_by 1 z) by (unfold Zbounded_by; Lia.lia).
            pose proof (IHu start len z p ll lr ltac:(Lia.lia) Hz Hllred Hk_iter Hllpos Hlrpos Hll Hlr) as (Hleft & Hmid1 & Hmid2 & Hmid3 & Hright & Hrec & Hrec_eq).
            unfold f_rec. rewrite seq_S, fold_left_app. cbn [fold_left].
            assert (fold_left _ _ _ = f_rec u reduce_bool start len z p) as -> by reflexivity.
            assert (Hll': Forall (Zbounded_by ll) (firstn start (f_rec u reduce_bool start len z p))) by congruence.
            assert (Hlr': Forall (Zbounded_by lr) (skipn (start + len + u) (f_rec u reduce_bool start len z p))).
            { rewrite Hright, <- (PeanoNat.Nat.add_assoc start), (PeanoNat.Nat.add_comm start), <- skipn_skipn.
              apply Forall.Forall_skipn. auto. }
            assert (Hmid: Forall (Zbounded_by lr) (firstn (len - u) (skipn (start + u) (f_rec u reduce_bool start len z p)))%Z).
            { rewrite Hmid2, (PeanoNat.Nat.add_comm start), <- skipn_skipn.
              apply Forall.Forall_firstn. apply Forall.Forall_skipn. auto. }
            assert (X1: Zbounded_by lr (nth_default 0%Z (f_rec u reduce_bool start len z p) (start + u + len))).
            { assert (start + u + len = (start + len + u) + 0)%nat as -> by Lia.lia.
              rewrite <- ListUtil.nth_default_skipn.
              apply Forall_nth_default; auto. apply bounded_by_0_r. }
            assert (X2: Zbounded_by lr (nth_default 0%Z (f_rec u reduce_bool start len z p) (start + u))).
            { rewrite <- (PeanoNat.Nat.add_0_r (start + u)), <- ListUtil.nth_default_skipn.
              assert (nth_default _ _ _ = nth_default 0 (firstn (len - u) (skipn (start + u) (f_rec u reduce_bool start len z p))) 0)%Z as ->.
              - rewrite ListUtil.nth_default_firstn; destruct (Compare_dec.lt_dec 0 _); [|Lia.lia]; destruct (Compare_dec.le_dec _ _); reflexivity.
              - apply Forall_nth_default; auto. apply bounded_by_0_r. }
            assert (Hlen: length (map F.to_Z (f_spec_rec u start len (F.of_Z q z) (map (F.of_Z q) p))) = length (map Zreduce (f_rec u reduce_bool start len z p))) by congruence.
            do 2 rewrite length_map in Hlen.
            repeat split.
            + repeat (rewrite ListUtil.firstn_set_nth_out_of_bounds by Lia.lia).
              exact Hleft.
            + repeat (rewrite ListUtil.skipn_set_nth_inbounds by Lia.lia).
              destruct (Compare_dec.lt_dec u (length (skipn start (f_rec u reduce_bool  start len z p)))) as [Hlt | Hnlt].
              * rewrite (ListUtil.firstn_succ 0%Z) by (repeat rewrite ListUtil.length_set_nth; assumption).
                repeat rewrite (ListUtil.firstn_set_nth_out_of_bounds) by Lia.lia.
                rewrite Forall_app; split; auto.
                repeat rewrite ListUtil.set_nth_nth_default_full.
                repeat rewrite ListUtil.length_set_nth.
                destruct (Compare_dec.lt_dec _ _) as [_|?]; [|Lia.lia].
                destruct (PeanoNat.Nat.eq_dec u _) as [_|?]; [|Lia.lia].
                constructor; [|constructor].
                destruct (reduce_bool); cbn [id].
                { eapply bounded_by_reduce; [|apply bounded_by_add; eauto].
                  - Lia.lia.
                  - rewrite (Z.mul_comm z).
                    eapply bounded_by_reduce; [|apply bounded_by_mul; eauto].
                    Lia.nia. }
                apply bounded_by_add; auto.
                rewrite (Z.mul_comm z). eapply bounded_by_reduce; [|apply bounded_by_mul; eauto].
                Lia.nia.
              * rewrite firstn_all2 by (repeat rewrite ListUtil.length_set_nth; Lia.lia).
                repeat rewrite ListUtil.set_nth_out_of_bounds by (repeat rewrite ListUtil.length_set_nth; Lia.lia).
                rewrite firstn_all2 in Hmid1 by Lia.lia; auto.
            + rewrite ListUtil.skipn_set_nth_out_of_bounds by Lia.lia.
              rewrite (PeanoNat.Nat.add_comm start), <- skipn_skipn, <- ListUtil.skipn_firstn.
              rewrite ListUtil.skipn_set_nth_inbounds by Lia.lia.
              rewrite ListUtil.firstn_set_nth_out_of_bounds by Lia.lia.
              assert (S u = 1 + u)%nat as -> by Lia.lia.
              rewrite <- skipn_skipn, ListUtil.skipn_firstn, skipn_skipn, (PeanoNat.Nat.add_comm u), Hmid2.
              rewrite skipn_firstn_comm, skipn_skipn; f_equal; [Lia.lia|].
              f_equal; Lia.lia.
            + rewrite ListUtil.skipn_set_nth_out_of_bounds by Lia.lia.
              rewrite ListUtil.skipn_set_nth_inbounds by Lia.lia.
              assert (start + u + len - _ = u)%nat as -> by Lia.lia.
              destruct (Compare_dec.lt_dec u (length (skipn (start + len) (f_rec u reduce_bool start len z p)))) as [Hlt|Hnlt].
              * rewrite (ListUtil.firstn_succ 0%Z) by (rewrite ListUtil.length_set_nth; Lia.lia).
                rewrite ListUtil.firstn_set_nth_out_of_bounds by Lia.lia.
                rewrite ListUtil.set_nth_nth_default by Lia.lia.
                rewrite NatUtil.eq_nat_dec_refl.
                apply Forall_app; split; auto.
                constructor; [|constructor].
                destruct reduce_bool; cbn [id].
                { eapply bounded_by_reduce; [|apply bounded_by_sub; eauto].
                  - Lia.lia.
                  - rewrite (Z.mul_comm z).
                    eapply bounded_by_reduce; [|apply bounded_by_mul; eauto].
                    Lia.nia. }
                apply bounded_by_sub; auto.
                rewrite (Z.mul_comm z).
                eapply bounded_by_reduce; [|apply bounded_by_mul; eauto]. Lia.nia.
              * rewrite firstn_all2 by (rewrite ListUtil.length_set_nth; Lia.lia).
                rewrite firstn_all2 in Hmid3 by Lia.lia.
                rewrite ListUtil.set_nth_out_of_bounds by Lia.lia.
                assumption.
            + do 2 rewrite ListUtil.skipn_set_nth_out_of_bounds by Lia.lia.
              assert (start + len + S u = 1 + (start + len + u))%nat as -> by Lia.lia.
              rewrite <- skipn_skipn, Hright, skipn_skipn. reflexivity.
            + unfold f_spec_rec. rewrite seq_S, fold_left_app.
              cbn [fold_left]. assert (fold_left _ _ _ = f_spec_rec u start len (F.of_Z q z) (map (F.of_Z q) p)) as -> by reflexivity.
              apply nth_error_ext. intros i.
              do 2 rewrite nth_error_map.
              repeat rewrite ListUtil.nth_set_nth.
              repeat rewrite ListUtil.length_set_nth.
              assert (Hcomm: forall (b: bool) e, Zreduce ((if b then Zreduce else id) e) = (if b then Zreduce else id) (Zreduce e)) by (intros; destruct b; reflexivity).
              repeat rewrite Hlen. destruct (PeanoNat.Nat.eq_dec i (start + u)).
              * destruct (Compare_dec.lt_dec i _); [|reflexivity].
                cbn -[F.of_Z]. f_equal. subst i.
                rewrite F.to_Z_add, F.to_Z_mul.
                repeat rewrite <- (ListUtil.map_nth_default_always F.to_Z).
                rewrite Hrec, F.to_Z_0, F.to_Z_of_Z.
                rewrite (Z.mod_small z) by Lia.lia.
                rewrite <- Zreduce_0 at 2.
                rewrite <- Zreduce_0 at 1.
                do 2 rewrite ListUtil.map_nth_default_always.
                rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X1).
                rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X2).
                repeat rewrite F.to_Z_of_Z.
                rewrite (Z.mul_comm z (nth_default _ _ _)), Hcomm.
                erewrite (bounded_by_reduce_eq (lr * Pos.to_nat q)%nat (_ * z) ltac:(Lia.nia)) by (apply bounded_by_mul; auto).
                rewrite F.to_Z_of_Z.
                rewrite (bounded_by_reduce_eq (lr + 1)%nat _ ltac:(Lia.lia)).
                2: apply bounded_by_add; [|apply mod_bounded_by_1]; auto.
                rewrite F.to_Z_of_Z.
                destruct reduce_bool; [rewrite Zreduce_mod|cbv [id]];
                rewrite Zdiv.Zmult_mod_idemp_r, Zdiv.Zplus_mod_idemp_r, Zdiv.Zplus_mod_idemp_r, Zdiv.Zplus_mod_idemp_l;
                f_equal; Lia.lia.
              * destruct (PeanoNat.Nat.eq_dec _ _) as [->|].
                2:{ do 2 rewrite <- nth_error_map. rewrite Hrec. reflexivity. }
                destruct (Compare_dec.lt_dec _ _); [|reflexivity].
                cbn [option_map]. f_equal.
                rewrite Hierarchy.ring_sub_definition.
                rewrite F.to_Z_add, F.to_Z_opp, F.to_Z_mul, F.to_Z_of_Z.
                rewrite (Z.mod_small z) by Lia.lia.
                repeat rewrite <- (ListUtil.map_nth_default_always F.to_Z).
                rewrite Hrec, F.to_Z_0.
                rewrite <- Zreduce_0 at 2.
                rewrite <- Zreduce_0 at 1.
                do 2 rewrite ListUtil.map_nth_default_always.
                rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X1).
                rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X2).
                repeat rewrite F.to_Z_of_Z. repeat rewrite (Z.mul_comm z).
                rewrite (bounded_by_reduce_eq (lr * Pos.to_nat q)%nat (_ * z) ltac:(Lia.nia)) by (apply bounded_by_mul; auto).
                rewrite F.to_Z_of_Z.
                rewrite Hcomm, (bounded_by_reduce_eq (lr + 1)%nat _ ltac:(Lia.lia)).
                2: apply bounded_by_sub; [|apply mod_bounded_by_1]; auto.
                rewrite F.to_Z_of_Z, Zdiv.Zmult_mod_idemp_l.
                destruct (Z.eq_dec ((nth_default 0 (f_rec u reduce_bool start len z p) (start + u + len) * z) mod q) 0)%Z as [->|Hnz].
                { destruct reduce_bool; [rewrite Zreduce_mod|cbv [id]].
                  all: rewrite Z.sub_0_r, Z.add_0_r, Z.mod_mod by Lia.lia.
                  all: rewrite <- Zdiv.Zplus_mod_idemp_r, Zdiv.Z_mod_same_full, Z.add_0_r.
                  all: reflexivity. }
                rewrite Modulo.Z.mod_opp_small.
                2: pose proof (Zdiv.Z_mod_lt ((nth_default 0%Z (f_rec u reduce_bool start len z p) (start + u + len)) * z) q ltac:(Lia.lia)); Lia.lia.
                rewrite Zdiv.Zplus_mod_idemp_l.
                destruct reduce_bool; [rewrite Zreduce_mod|cbv [id]]; reflexivity.
            + unfold f_spec_rec. rewrite seq_S, fold_left_app.
              cbn [fold_left]. assert (fold_left _ _ _ = f_spec_rec u start len (F.of_Z q z) (map (F.of_Z q) p)) as -> by reflexivity.
              destruct reduce_bool; [|exact I].
              destruct (Compare_dec.lt_dec u (length (skipn start (f_spec_rec u start len (F.of_Z q z) (map (F.of_Z q) p))))) as [Hlt|Hnlt].
              { rewrite length_skipn in Hlt.
                destruct Hrec_eq as (Hrec1 & Hrec2). split.
                - rewrite (ListUtil.firstn_succ 0%Z) by (rewrite length_skipn, length_map, ListUtil.length_set_nth, ListUtil.length_set_nth; Lia.lia).
                  rewrite (ListUtil.firstn_succ 0%Z) by (rewrite length_skipn, ListUtil.length_set_nth, ListUtil.length_set_nth; Lia.lia).
                  f_equal.
                  + rewrite firstn_skipn_comm, firstn_map.
                    do 2 rewrite ListUtil.firstn_set_nth_out_of_bounds by Lia.lia.
                    rewrite <- firstn_map, <- firstn_skipn_comm, Hrec1. symmetry.
                    rewrite firstn_skipn_comm.
                    do 2 rewrite ListUtil.firstn_set_nth_out_of_bounds by Lia.lia.
                     rewrite <- firstn_skipn_comm; auto.
                  + f_equal. do 2 rewrite ListUtil.nth_default_skipn.
                    rewrite <- (@F.to_Z_0 q) at 1.
                    rewrite ListUtil.map_nth_default_always.
                    repeat rewrite ListUtil.set_nth_nth_default_full.
                    repeat rewrite NatUtil.eq_nat_dec_refl.
                    repeat rewrite ListUtil.length_set_nth.
                    destruct (Compare_dec.lt_dec _ _) as [_|]; [|Lia.lia].
                    destruct (Compare_dec.lt_dec _ _) as [_|]; [|Lia.lia].
                    rewrite F.to_Z_add, F.to_Z_mul, F.to_Z_of_Z.
                    do 2 rewrite <- (ListUtil.map_nth_default_always F.to_Z), Hrec.
                    repeat rewrite F.to_Z_0.
                    rewrite <- Zreduce_0 at 2. rewrite <- Zreduce_0 at 1.
                    do 2 rewrite ListUtil.map_nth_default_always.
                    rewrite (Z.mod_small z) by Lia.lia.
                    rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia)); auto.
                    rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia)); auto.
                    rewrite (bounded_by_reduce_eq (lr + 1) _ ltac:(Lia.lia)).
                    2:{ apply bounded_by_add; auto.
                        rewrite Z.mul_comm.
                        eapply bounded_by_reduce; [|apply bounded_by_mul; eauto].
                        Lia.nia. }
                    rewrite (bounded_by_reduce_eq (lr * Pos.to_nat q) _ ltac:(Lia.nia)) by (rewrite Z.mul_comm; apply bounded_by_mul; auto).
                    repeat rewrite F.to_Z_of_Z.
                    rewrite Zdiv.Zplus_mod_idemp_l, Zdiv.Zmult_mod_idemp_r.
                    reflexivity.
                - rewrite skipn_map.
                  do 2 rewrite (ListUtil.skipn_set_nth_out_of_bounds (start + len) (start + u)) by Lia.lia.
                  repeat rewrite ListUtil.skipn_set_nth_inbounds by Lia.lia.
                  assert (start + u + len - _ = u)%nat as -> by Lia.lia.
                  destruct (Compare_dec.lt_dec u (length (skipn (start + len) (f_spec_rec u start len (F.of_Z q z) (map (F.of_Z q) p))))) as [Hlt2|Hnlt].
                  + rewrite (ListUtil.firstn_succ 0%Z) by (rewrite length_map, ListUtil.length_set_nth; Lia.lia).
                    rewrite firstn_map, ListUtil.firstn_set_nth_out_of_bounds by Lia.lia.
                    rewrite length_skipn in Hlt2.
                    rewrite (ListUtil.firstn_succ 0%Z) by (rewrite ListUtil.length_set_nth, length_skipn; Lia.lia).
                    rewrite ListUtil.firstn_set_nth_out_of_bounds by Lia.lia.
                    rewrite <- firstn_map, <- skipn_map, Hrec2. f_equal.
                    f_equal. rewrite <- (@F.to_Z_0 q) at 1.
                    rewrite ListUtil.map_nth_default_always.
                    repeat rewrite ListUtil.set_nth_nth_default_full.
                    repeat rewrite length_skipn.
                    repeat rewrite NatUtil.eq_nat_dec_refl.
                    rewrite Hlen. destruct (Compare_dec.lt_dec _ _) as [_|]; [|Lia.lia].
                    rewrite Hierarchy.ring_sub_definition.
                    rewrite F.to_Z_add, F.to_Z_opp, F.to_Z_mul, F.to_Z_of_Z.
                    rewrite (Z.mod_small z) by Lia.lia.
                    repeat rewrite <- (ListUtil.map_nth_default_always F.to_Z).
                    rewrite Hrec, F.to_Z_0.
                    rewrite <- Zreduce_0 at 2.
                    rewrite <- Zreduce_0 at 1.
                    do 2 rewrite ListUtil.map_nth_default_always.
                    rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X1).
                    rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X2).
                    repeat rewrite F.to_Z_of_Z. repeat rewrite (Z.mul_comm z).
                    rewrite (bounded_by_reduce_eq (lr * Pos.to_nat q)%nat (_ * z) ltac:(Lia.nia)) by (apply bounded_by_mul; auto).
                    rewrite F.to_Z_of_Z.
                    rewrite (bounded_by_reduce_eq (lr + 1)%nat).
                    2:{ transitivity (2 * lr)%Z; [Lia.lia|].
                        pose proof (prime_ge_2 q prime_q).
                        Lia.nia. }
                    2: apply bounded_by_sub; [|apply mod_bounded_by_1]; auto.
                    rewrite F.to_Z_of_Z, Zdiv.Zmult_mod_idemp_l.
                    destruct (Z.eq_dec ((nth_default 0 (f_rec u true start len z p) (start + u + len) * z) mod q) 0)%Z as [->|Hnz].
                    { rewrite Z.sub_0_r, Z.add_0_r, Z.mod_mod by Lia.lia.
                      rewrite <- Zdiv.Zplus_mod_idemp_r, Zdiv.Z_mod_same_full, Z.add_0_r.
                      reflexivity. }
                    rewrite Modulo.Z.mod_opp_small.
                    2: pose proof (Zdiv.Z_mod_lt ((nth_default 0%Z (f_rec u true start len z p) (start + u + len)) * z) q ltac:(Lia.lia)); Lia.lia.
                    rewrite Zdiv.Zplus_mod_idemp_l. reflexivity.
                  + rewrite length_skipn in Hnlt.
                    rewrite firstn_all2 by (rewrite length_map, ListUtil.length_set_nth, length_skipn; Lia.lia).
                    rewrite firstn_all2 in Hrec2 by (rewrite length_skipn, length_map; Lia.lia).
                    rewrite firstn_all2 by (rewrite ListUtil.length_set_nth, length_skipn; Lia.lia).
                    rewrite firstn_all2 in Hrec2 by (rewrite length_skipn; Lia.lia).
                    rewrite <- Hrec2. rewrite ListUtil.map_set_nth, skipn_map. f_equal.
                    rewrite Hierarchy.ring_sub_definition.
                    rewrite F.to_Z_add, F.to_Z_opp, F.to_Z_mul, F.to_Z_of_Z.
                    rewrite (Z.mod_small z) by Lia.lia.
                    repeat rewrite <- (ListUtil.map_nth_default_always F.to_Z).
                    rewrite Hrec, F.to_Z_0.
                    rewrite <- Zreduce_0 at 2.
                    rewrite <- Zreduce_0 at 1.
                    do 2 rewrite ListUtil.map_nth_default_always.
                    rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X1).
                    rewrite (bounded_by_reduce_eq lr _ ltac:(Lia.nia) X2).
                    repeat rewrite F.to_Z_of_Z. repeat rewrite (Z.mul_comm z).
                    rewrite (bounded_by_reduce_eq (lr * Pos.to_nat q)%nat (_ * z) ltac:(Lia.nia)) by (apply bounded_by_mul; auto).
                    rewrite F.to_Z_of_Z.
                    rewrite (bounded_by_reduce_eq (lr + 1)%nat).
                    2:{ transitivity (2 * lr)%Z; [Lia.lia|].
                        pose proof (prime_ge_2 q prime_q).
                        Lia.nia. }
                    2: apply bounded_by_sub; [|apply mod_bounded_by_1]; auto.
                    rewrite F.to_Z_of_Z, Zdiv.Zmult_mod_idemp_l.
                    destruct (Z.eq_dec ((nth_default 0 (f_rec u true start len z p) (start + u + len) * z) mod q) 0)%Z as [->|Hnz].
                    { rewrite Z.sub_0_r, Z.add_0_r, Z.mod_mod by Lia.lia.
                      rewrite <- Zdiv.Zplus_mod_idemp_r, Zdiv.Z_mod_same_full, Z.add_0_r.
                      reflexivity. }
                    rewrite Modulo.Z.mod_opp_small.
                    2: pose proof (Zdiv.Z_mod_lt ((nth_default 0%Z (f_rec u true start len z p) (start + u + len)) * z) q ltac:(Lia.lia)); Lia.lia.
                    rewrite Zdiv.Zplus_mod_idemp_l. reflexivity. }
              rewrite length_skipn in Hnlt.
              repeat rewrite ListUtil.set_nth_out_of_bounds by (repeat rewrite ListUtil.length_set_nth; Lia.lia).
              rewrite firstn_all2 by (rewrite length_skipn, length_map; Lia.lia).
              rewrite firstn_all2 by (rewrite length_skipn; Lia.lia).
              rewrite firstn_all2 by (rewrite length_skipn, length_map; Lia.lia).
              rewrite firstn_all2 by (rewrite length_skipn; Lia.lia).
              rewrite firstn_all2 in Hrec_eq by (rewrite length_skipn, length_map; Lia.lia).
              rewrite firstn_all2 in Hrec_eq by (rewrite length_skipn; Lia.lia).
              rewrite firstn_all2 in Hrec_eq by (rewrite length_skipn, length_map; Lia.lia).
              rewrite firstn_all2 in Hrec_eq by (rewrite length_skipn; Lia.lia).
              assumption. }
        intros reduce_bool start len z p ll lr Hz Hllred Hk_iter Hllpos Hlrpos Hl Hr p' p_spec'.
        assert (p' = f_rec len reduce_bool start len z p) as -> by reflexivity.
        assert (p_spec' = f_spec_rec len start len (F.of_Z q z) (map (F.of_Z q) p)) as -> by reflexivity.
        pose proof (IH reduce_bool len start len z p ll lr ltac:(Lia.lia) Hz Hllred Hk_iter Hllpos Hlrpos Hl Hr) as (Hleft & Hmid1 & Hmid2 & Hmid3 & Hright & Hrec & Hrec_eq).
        clear Hmid2. rewrite Hleft.
        split; auto. assert (start + 2 * len = start + len + len)%nat as -> by Lia.lia.
        rewrite Hright.
        rewrite <- (firstn_skipn len (firstn _ _)), firstn_firstn, PeanoNat.Nat.min_l by Lia.lia.
        rewrite Forall_app, ListUtil.skipn_firstn, skipn_skipn, (PeanoNat.Nat.add_comm len start).
        assert (2 * len - len = len)%nat as -> by Lia.lia. split; auto.
        rewrite <- (PeanoNat.Nat.add_assoc start), (PeanoNat.Nat.add_comm start), <- skipn_skipn.
        split; [apply Forall.Forall_skipn; auto|].
        split; auto. split; [|split; auto].
        destruct reduce_bool; [|exact I].
        rewrite <- (firstn_skipn len (firstn _ _)), firstn_firstn, PeanoNat.Nat.min_l by Lia.lia.
        rewrite ListUtil.skipn_firstn, skipn_skipn, (PeanoNat.Nat.add_comm len start).
        assert (2 * len - len = len)%nat as -> by Lia.lia.
        destruct Hrec_eq; f_equal; auto.
      Qed.

      Local Notation polynomial_decompose_loop_no_reduce := (polynomial_decompose_loop_may_reduce false).
      Local Notation polynomial_decompose_loop_with_reduce := (polynomial_decompose_loop_may_reduce true).

      Definition polynomial_list_loop_may_reduce (reduce_bool: bool) (k old_len len: nat) (state: nat * nat * list Z) :=
        List.fold_left
          (fun state _ =>
             let '(l, start, p) := state in
             let l := (l + 1)%nat in
             let z := nth_default 0%Z precomp_zetas l in
             let p := polynomial_decompose_loop_may_reduce reduce_bool start len z p in
             let start := (start + old_len)%nat in
             (l, start, p))
          (seq 0 k)
          state.

      Lemma polynomial_list_loop_may_reduce_spec:
        forall reduce_bool k old_len len l start p (ll lr: nat),
          (0 < len)%nat ->
          (old_len = 2 * len)%nat ->
          (start + k * old_len <= length p)%nat ->
          (ll <= k_iter * q)%Z ->
          (lr <= k_iter)%Z ->
          (1 <= ll)%nat -> (1 <= lr)%nat ->
          Forall (Zbounded_by ll) (firstn start p) ->
          Forall (Zbounded_by lr) (skipn start p) ->
          let '(l', start', p') := polynomial_list_loop_may_reduce reduce_bool k old_len len (l, start, p) in
          let '(l_spec', start_spec', p_spec') := polynomial_list_loop (List.map (F.of_Z q) precomp_zetas) k old_len len (l, start, map (F.of_Z q) p) in
          (l' = l + k)%nat /\ l' = l_spec' /\
          (start' = start + k * old_len)%nat /\ start' = start_spec' /\
          Forall (Zbounded_by ll) (firstn start p') /\
          Forall (Zbounded_by (if reduce_bool then 1 else lr + 1)) (firstn (k * old_len) (skipn start p')) /\
          Forall (Zbounded_by lr) (skipn (start + k * old_len) p') /\
          map F.to_Z p_spec' = map Zreduce p' /\
          (if reduce_bool then firstn (k * old_len) (skipn start (map F.to_Z p_spec')) = firstn (k * old_len) (skipn start p') else True) /\
          (firstn start p' = firstn start p) /\
          (skipn (start + k * old_len) p' = skipn (start + k * old_len) p).
      Proof.
        induction k; intros old_len len l start p ll lr Hlen_pos Hold_len Hlen_le Hllred Hk_iter Hllpos Hlrpos Hleft Hright.
        - cbn. repeat rewrite PeanoNat.Nat.add_0_r. repeat split; auto.
          + rewrite map_map. apply map_ext_in.
            intros a Ha; rewrite F.to_Z_of_Z. symmetry.
            apply (bounded_by_reduce_eq (Nat.max ll lr)); [Lia.nia|].
            rewrite <- (firstn_skipn start) in Ha. apply in_app_or in Ha.
            destruct Ha as [Ha|Ha].
            * apply (bounded_by_monotone ll (Nat.max ll lr) _ ltac:(Lia.lia)).
              eapply Forall_In; eauto.
            * apply (bounded_by_monotone lr (Nat.max ll lr) _ ltac:(Lia.lia)).
              eapply Forall_In; eauto.
          + destruct reduce_bool; auto.
        - assert (Hlrred: (lr + 1 <= k_iter * q)%Z).
          { transitivity (2 * lr)%Z; [Lia.lia|].
            pose proof (prime_ge_2 q prime_q). Lia.nia. }
          pose proof (IHk old_len len l start p ll lr Hlen_pos Hold_len ltac:(Lia.lia) Hllred Hk_iter Hllpos Hlrpos Hleft Hright) as IH.
          unfold polynomial_list_loop_may_reduce.
          rewrite seq_S, fold_left_app. cbn [fold_left].
          assert (fold_left _ _ _ = polynomial_list_loop_may_reduce reduce_bool k old_len len (l, start, p)) as -> by reflexivity.
          unfold polynomial_list_loop.
          rewrite seq_S, fold_left_app. cbn [fold_left].
          assert (fold_left _ _ _ = polynomial_list_loop (map (F.of_Z q) precomp_zetas) k old_len len (l, start, map (F.of_Z q) p)) as -> by reflexivity.
          destruct (polynomial_list_loop_may_reduce reduce_bool k old_len len (l, start, p)) as ((l' & start') & p') eqn:Hp'.
          destruct (polynomial_list_loop (map (F.of_Z q) precomp_zetas) k old_len len (l, start, map (F.of_Z q) p)) as ((l_spec' & start_spec') & p_spec') eqn:Hp_spec'.
          destruct IH as (-> & <- & -> & <- & Xleft & Xmid & Xright & Xcont_eq & Xeq & Xleft_eq & Xright_eq).
          do 4 (split; [Lia.lia|]).
          assert (Xleft': Forall (Zbounded_by (Nat.max ll (if reduce_bool then 1 else lr + 1))%nat) (firstn (start + k * old_len) p')).
          { rewrite <- (firstn_skipn start), firstn_firstn, skipn_firstn_comm, PeanoNat.Nat.min_l by Lia.lia.
            assert (_ + _ - _= k * old_len)%nat as -> by Lia.lia.
            apply Forall_app; split; eapply Forall_impl; try eassumption; intros; eapply bounded_by_monotone; try eassumption; Lia.lia. }
          pose proof (polynomial_decompose_loop_may_reduce_spec reduce_bool (start + k * old_len) len (nth_default 0%Z precomp_zetas (l + k + 1)) p' (Nat.max ll (if reduce_bool then 1 else lr + 1)) lr (precomp_zetas_bounds _) ltac:(destruct reduce_bool; Lia.lia) Hk_iter ltac:(Lia.lia) Hlrpos Xleft' Xright) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7).
          assert (firstn start _ = firstn start (firstn (start + k * old_len) (polynomial_decompose_loop_may_reduce reduce_bool  (start + k * old_len) len (nth_default 0%Z precomp_zetas (l + k + 1)) p'))) as -> by (rewrite firstn_firstn, PeanoNat.Nat.min_l by Lia.lia; reflexivity).
          rewrite Y6, firstn_firstn, PeanoNat.Nat.min_l by Lia.lia. split; [assumption|].
          assert (start + S k * old_len = start + k * old_len + 2 * len)%nat as -> by Lia.lia.
          rewrite Y7. rewrite (PeanoNat.Nat.add_comm _ (2 * len)), <- (skipn_skipn (2 * len)), <- (skipn_skipn (2 * len)), Xright_eq.
          repeat split; auto.
          + rewrite <- (firstn_skipn (k * old_len)), firstn_firstn, PeanoNat.Nat.min_l by Lia.lia.
            rewrite firstn_skipn_comm, Y6, skipn_firstn_comm.
            assert (_ + _ - _ = k * old_len)%nat as -> by Lia.lia.
            apply Forall_app; split; [assumption|].
            rewrite skipn_firstn_comm, skipn_skipn, (PeanoNat.Nat.add_comm (k * old_len)).
            assert (S k * old_len - k * old_len = 2 * len)%nat as -> by Lia.lia.
            assumption.
          + apply Forall.Forall_skipn; congruence.
          + assert (p_spec' = map (F.of_Z q) p') as ->.
            { transitivity (map (F.of_Z q) (map Zreduce p')).
              - symmetry. rewrite <- Xcont_eq, map_map.
                erewrite map_ext; [apply map_id|].
                intros; apply F.of_Z_to_Z.
              - symmetry. rewrite map_map. apply map_ext_in.
                intros a Ha. rewrite (bounded_by_reduce_eq (Nat.max ll (lr + 1)) _ ltac:(Lia.nia)).
                + rewrite F.of_Z_to_Z. reflexivity.
                + rewrite <- (firstn_skipn start) in Ha. apply in_app_or in Ha.
                  destruct Ha as [Ha|Ha]; [apply (bounded_by_monotone ll (Nat.max ll (lr + 1)) _ ltac:(Lia.lia)); eapply (Forall_In Xleft); eauto|].
                  rewrite <- (firstn_skipn (k * old_len)) in Ha.
                  rewrite skipn_skipn, (PeanoNat.Nat.add_comm (k * old_len)) in Ha.
                  apply in_app_or in Ha.
                  destruct Ha as [Ha|Ha]; [|apply (bounded_by_monotone lr (Nat.max ll (lr + 1)) _ ltac:(Lia.lia)); eapply (Forall_In Xright); eauto].
                  apply (bounded_by_monotone (if reduce_bool then 1 else (lr + 1)) (Nat.max ll (lr + 1)) _ ltac:(destruct reduce_bool; Lia.lia)).
                  apply (Forall_In Xmid). auto. }
            assert (0 = F.of_Z q 0) as -> by reflexivity.
            rewrite ListUtil.map_nth_default_always, Y4.
            reflexivity.
          + assert (p_spec' = map (F.of_Z q) p') as ->.
            { transitivity (map (F.of_Z q) (map Zreduce p')).
              - symmetry. rewrite <- Xcont_eq, map_map.
                erewrite map_ext; [apply map_id|].
                intros; apply F.of_Z_to_Z.
              - symmetry. rewrite map_map. apply map_ext_in.
                intros a Ha. rewrite (bounded_by_reduce_eq (Nat.max ll (lr + 1)) _ ltac:(Lia.nia)).
                + rewrite F.of_Z_to_Z. reflexivity.
                + rewrite <- (firstn_skipn start) in Ha. apply in_app_or in Ha.
                  destruct Ha as [Ha|Ha]; [apply (bounded_by_monotone ll (Nat.max ll (lr + 1)) _ ltac:(Lia.lia)); eapply (Forall_In Xleft); eauto|].
                  rewrite <- (firstn_skipn (k * old_len)) in Ha.
                  rewrite skipn_skipn, (PeanoNat.Nat.add_comm (k * old_len)) in Ha.
                  apply in_app_or in Ha.
                  destruct Ha as [Ha|Ha]; [|apply (bounded_by_monotone lr (Nat.max ll (lr + 1)) _ ltac:(Lia.lia)); eapply (Forall_In Xright); eauto].
                  apply (bounded_by_monotone (if reduce_bool then 1 else (lr + 1)) (Nat.max ll (lr + 1)) _ ltac:(destruct reduce_bool; Lia.lia)).
                  apply (Forall_In Xmid). auto. }
            destruct reduce_bool; [|exact I].
            assert (0 = F.of_Z q 0) as -> by reflexivity.
            rewrite ListUtil.map_nth_default_always, Y4.
            rewrite Y4 in Y5.
            assert (S k * old_len = k * old_len + 2 * len)%nat as -> by Lia.lia.
            rewrite <- (firstn_skipn (k * old_len) (firstn _ (skipn _ (map _ _)))), firstn_firstn, PeanoNat.Nat.min_l by Lia.lia.
            rewrite (firstn_skipn_comm (k * old_len)), firstn_map, Y6.
            rewrite (skipn_firstn_comm (k * old_len)), skipn_skipn, (PeanoNat.Nat.add_comm _ start).
            assert (_ + _ - _ = 2 * len)%nat as -> by Lia.lia.
            rewrite Y5.
            rewrite <- (firstn_skipn (k * old_len) (firstn (k * old_len + _) _)), firstn_firstn, PeanoNat.Nat.min_l by Lia.lia.
            rewrite (firstn_skipn_comm (k * old_len)), Y6.
            rewrite (skipn_firstn_comm (k * old_len)), skipn_skipn, (PeanoNat.Nat.add_comm _ start).
            assert (_ + _ - _ = 2 * len)%nat as -> by Lia.lia.
            f_equal. rewrite skipn_map, skipn_firstn_comm.
            assert (_ + _ - _ = k * old_len)%nat as -> by Lia.lia.
            rewrite <- Xeq, map_map.
            erewrite (map_ext (fun x => F.to_Z (F.of_Z q x))); [|apply F.to_Z_of_Z].
            rewrite skipn_map, firstn_map, map_map. apply map_ext.
            apply Zreduce_mod.
      Qed.

      Lemma polynomial_list_full_loop_may_reduce_spec:
        forall reduce_bool k old_len len l p (bound: nat),
          (0 < len)%nat ->
          (old_len = 2 * len)%nat ->
          (k * old_len = length p)%nat ->
          (1 <= bound)%nat ->
          (bound <= k_iter)%Z ->
          Forall (Zbounded_by bound) p ->
          let '(l', _, p') := polynomial_list_loop_may_reduce reduce_bool k old_len len (l, 0%nat, p) in
          let '(l_spec', _, p_spec') := polynomial_list_loop (List.map (F.of_Z q) precomp_zetas) k old_len len (l, 0%nat, map (F.of_Z q) p) in
          (l' = l + k)%nat /\ l' = l_spec' /\
          Forall (Zbounded_by (if reduce_bool then 1 else bound + 1)) p' /\
          map F.to_Z p_spec' = map Zreduce p' /\
          (if reduce_bool then (map F.to_Z p_spec') = p' else True) /\
          length p' = length p.
      Proof.
        intros reduce_bool k old_len len l p bound Hlen_pos Hold_len Hlen Hboundpos Hk_iter Hbounded.
        pose proof (polynomial_list_loop_may_reduce_spec reduce_bool k old_len len l 0%nat p bound bound Hlen_pos Hold_len ltac:(Lia.lia) ltac:(Lia.nia) Hk_iter Hboundpos Hboundpos ltac:(rewrite firstn_O; constructor) ltac:(rewrite skipn_O; assumption)) as Hspec.
        destruct (polynomial_list_loop_may_reduce reduce_bool k old_len len (l, 0%nat, p)) as ((l' & ?) & p') eqn:Hp'.
        destruct (polynomial_list_loop (map (F.of_Z q) precomp_zetas) k old_len len (l, 0%nat, map (F.of_Z q) p)) as ((l_spec' & ?) & p_spec') eqn:Hp_spec'.
        destruct Hspec as (-> & -> & _ & _ & _ & Hbounded' & _ & Hcont_eq & Heq & _ & _).
        rewrite skipn_O, Hlen in *.
        assert (length p = length p') as Hlen_eq.
        { transitivity (length (map Zreduce p')); [|apply length_map].
          rewrite <- Hcont_eq, length_map.
          rewrite polynomial_list_loop_spec in Hp_spec' by (try rewrite length_map; Lia.lia).
          inversion Hp_spec'; subst p_spec'.
          rewrite length_app, length_skipn, length_map, Hlen, PeanoNat.Nat.sub_diag, PeanoNat.Nat.add_0_r.
          rewrite (length_concat_same_length old_len).
          - unfold enumerate. rewrite length_map, length_combine, length_seq, length_firstn, length_chunk, length_map, <- Hlen, Nat.div_up_exact by Lia.lia.
            repeat rewrite PeanoNat.Nat.min_l by Lia.lia. reflexivity.
          - apply Forall_map, Forall.Forall_forall_iff_nth_error. unfold enumerate.
            intros i (j & chk) Hchk.
            rewrite PolynomialCRT.Pmod_cyclotomic_list_length.
            rewrite ListUtil.nth_error_combine in Hchk.
            destruct (nth_error (seq 0 _) i); [|congruence].
            rewrite ListUtil.nth_error_firstn in Hchk.
            destruct (Compare_dec.lt_dec i k); [|congruence].
            destruct (nth_error (chunk old_len _) i) eqn:Hnth; [|congruence].
            inversion Hchk; subst n1; subst l1; clear Hchk.
            rewrite (nth_error_chunk old_len ltac:(Lia.lia)) in Hnth by (rewrite length_map, <- Hlen, Nat.div_up_exact; Lia.lia).
            inversion Hnth; subst chk; clear Hnth.
            rewrite length_firstn, length_skipn, length_map, <- Hlen.
            rewrite PeanoNat.Nat.min_l; Lia.nia. }
        rewrite Hlen_eq, firstn_all in *.
        repeat split; auto.
        rewrite firstn_all2 in Heq; auto.
        rewrite Hcont_eq, length_map; Lia.lia.
      Qed.

      Local Notation polynomial_list_loop_no_reduce := (polynomial_list_loop_may_reduce false).

      Local Notation polynomial_list_loop_with_reduce := (polynomial_list_loop_may_reduce true).

      (* Do not reduce for n iterations, then reduce during n+1-th iteration *)
      Definition polynomial_layer_decomposition_loop_delay_reduce (start n: nat) (state: nat * nat * list Z) :=
        let '(l, len, p) :=
          List.fold_left
            (fun state i =>
               let '(l, len, p) := state in
               let old_len := len in
               let len := Nat.shiftr len 1 in
               let start := 0%nat in
               let '(l, _, p) := polynomial_list_loop_no_reduce (Nat.shiftl 1 i) old_len len (l, start, p) in
               (l, len, p))
            (seq start n)
            state in
        let old_len := len in
        let len := Nat.shiftr len 1 in
        let '(l, _, p) := polynomial_list_loop_with_reduce (Nat.shiftl 1 (start + n)) old_len len (l, 0%nat, p) in
        (l, len, p).

      Lemma polynomial_layer_decomposition_loop_delay_reduce_spec:
        forall r start n l len p,
          ((n + 1)%nat <= k_iter)%Z ->
          (S n <= r - start)%nat ->
          length p = Nat.pow 2 r ->
          len = Nat.pow 2 (r - start) ->
          let '(l', len', p') :=
            polynomial_layer_decomposition_loop_delay_reduce start n (l, len, List.map F.to_Z p) in
          let '(l_spec', len_spec', p_spec') :=
            polynomial_layer_decomposition_loop (List.map (@F.of_Z q) precomp_zetas) start (S n) (l, len, p) in
          l' = l_spec' /\ l' = (l + (Nat.pow 2 (start + S n) - Nat.pow 2 start))%nat /\
          len' = len_spec' /\ len' = Nat.shiftr len (n + 1)%nat /\
          p' = List.map F.to_Z p_spec' /\
          length p' = length p.
      Proof.
        set (f_rec := fun start n state =>
                        List.fold_left
                          (fun state i =>
                             let '(l, len, p) := state in
                             let old_len := len in
                             let len := Nat.shiftr len 1 in
                             let start := 0%nat in
                             let '(l, _, p) := polynomial_list_loop_no_reduce (Nat.shiftl 1 i) old_len len (l, start, p) in
                             (l, len, p))
                          (seq start n)
                          state).
        assert
          (IHrec: forall r start n l len p,
              ((n + 1)%nat <= k_iter)%Z ->
              (S n <= r - start)%nat ->
              length p = Nat.pow 2 r ->
              len = Nat.pow 2 (r - start) ->
              let '(l', len', p') :=
                f_rec start n (l, len, List.map F.to_Z p) in
              let '(l_spec', len_spec', p_spec') :=
                polynomial_layer_decomposition_loop (List.map (@F.of_Z q) precomp_zetas) start n (l, len, p) in
              l' = l_spec' /\ (l' = l + (Nat.pow 2 (start + n) - Nat.pow 2 start))%nat /\
              len' = len_spec' /\ len' = Nat.shiftr len n /\
              Forall (Zbounded_by (1 + n)%nat) p' /\
              map Zreduce p' = List.map F.to_Z p_spec' /\
              length p' = length p).
        { induction n; intros l len p Hk_iter Hstart Hp Hlen.
          - cbn. rewrite PeanoNat.Nat.add_0_r, PeanoNat.Nat.sub_diag, PeanoNat.Nat.add_0_r, map_map, length_map.
            repeat split; auto.
            + apply Forall_map, Forall_forall; intros.
              pose proof (F.to_Z_range x ltac:(Lia.lia)) as Hx.
              unfold Zbounded_by; Lia.lia.
            + apply map_ext; intros.
              apply Zreduce_small. apply F.to_Z_range. Lia.lia.
          - unfold f_rec. rewrite seq_S, fold_left_app. cbn [fold_left].
            assert (fold_left _ _ _ = f_rec start n (l, len, map F.to_Z p)) as -> by reflexivity.
            unfold polynomial_layer_decomposition_loop. rewrite seq_S, fold_left_app.
            cbn [fold_left].
            assert (fold_left _ _ _ = polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) start n (l, len, p)) as -> by reflexivity.
            pose proof (IHn l len p ltac:(Lia.nia) ltac:(Lia.nia) Hp Hlen) as IH.
            destruct (f_rec start n (l, len, map F.to_Z p)) as ((l' & len') & p') eqn:Hp'.
            destruct (polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) start n (l, len, p)) as ((l_spec' & len_spec') & p_spec') eqn:Hp_spec'.
            destruct IH as (<- & -> & <- & -> & IHbound & IHcont & Hlen_preserved).
            rewrite PeanoNat.Nat.shiftr_shiftr.
            assert (Hshiftr: forall i, (i <= r - start)%nat -> Nat.shiftr len i = Nat.pow 2 (r - start - i)).
            { intros. subst len. rewrite PeanoNat.Nat.shiftr_div_pow2.
              rewrite <- PeanoNat.Nat.pow_sub_r by Lia.lia. reflexivity. }
            assert (Hpow2nz: forall k, (0 < Nat.pow 2 k)%nat).
            { intros; pose proof (NatUtil.pow_nonzero 2 k ltac:(congruence)). Lia.lia. }
            repeat rewrite Hshiftr by Lia.lia.
            pose proof (polynomial_list_full_loop_may_reduce_spec false (Nat.shiftl 1 (start + n)) (Nat.pow 2 (r - start - n)) (Nat.pow 2 (r - start - (n + 1))%nat) (l + (Nat.pow 2 (start + n) - Nat.pow 2 start))%nat p' (1 + n)%nat (Hpow2nz _) ltac:(rewrite <- PeanoNat.Nat.pow_succ_r'; f_equal; Lia.lia) ltac:(rewrite PeanoNat.Nat.shiftl_mul_pow2, PeanoNat.Nat.mul_1_l, <- PeanoNat.Nat.pow_add_r, Hlen_preserved, Hp; f_equal; Lia.lia) ltac:(Lia.nia) ltac:(Lia.lia) IHbound) as HH.
            destruct (polynomial_list_loop_no_reduce (Nat.shiftl 1 (start + n)) (Nat.pow 2 (r - start - n)) (Nat.pow 2 (r - start - (n + 1))) ((l + (Nat.pow 2 (start + n) - Nat.pow 2 start))%nat, 0%nat, p')) as ((l2' & ?) & p2') eqn:Hp2'.
            assert (p_spec' = map (F.of_Z q) p') as ->.
            { transitivity (map (F.of_Z q) (map Zreduce p')).
              - rewrite IHcont, map_map, (map_ext _ id), map_id; auto.
                intros. rewrite F.of_Z_to_Z. reflexivity.
              - rewrite map_map. apply map_ext_in.
                intros a Ha. rewrite (bounded_by_reduce_eq (1 + n) _ ltac:(Lia.nia)).
                + rewrite F.of_Z_to_Z. reflexivity.
                + apply (Forall_In IHbound); auto. }
            destruct (polynomial_list_loop (map (F.of_Z q) precomp_zetas) (Nat.shiftl 1 (start + n)) (Nat.pow 2 (r - start - n)) (Nat.pow 2 (r - start - (n + 1))) ((l + (Nat.pow 2 (start + n) - Nat.pow 2 start))%nat, 0%nat, map (F.of_Z q) p')) as ((l_spec2' & ?) & p_spec2') eqn:Hp_spec2'.
            destruct HH as (-> & <- & Hbounds & Hcont_eq & _ & Hlen_eq).
            repeat split; try Lia.lia; auto.
            + assert (start + S n = S (start + n))%nat as -> by Lia.lia.
              rewrite PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.shiftl_mul_pow2, PeanoNat.Nat.mul_1_l.
              pose proof (PeanoNat.Nat.pow_le_mono_r 2 start (start + n)%nat ltac:(congruence) ltac:(Lia.lia)).
              Lia.lia.
            + f_equal; Lia.lia.
            + replace (S n) with (n + 1)%nat by Lia.lia. auto. }
        intros r start n l len p Hk_iter Hstart Hp Hlen.
        specialize (IHrec r start n l len p Hk_iter Hstart Hp Hlen).
        unfold polynomial_layer_decomposition_loop_delay_reduce.
        assert (fold_left _ _ _ = f_rec start n (l, len, map F.to_Z p)) as -> by reflexivity.
        destruct (f_rec start n (l, len, map F.to_Z p)) as ((l' & len') & p') eqn:Hp'.
        unfold polynomial_layer_decomposition_loop.
        rewrite seq_S, fold_left_app. cbn [fold_left].
        assert (fold_left _ _ _ = polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) start n (l, len, p)) as -> by reflexivity.
        destruct (polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) start n (l, len, p)) as ((l_spec' & len_spec') & p_spec') eqn:Hp_spec'.
        destruct IHrec as (<- & -> & <- & -> & Hbounds & Hcont_eq & Hlen_eq).
        rewrite PeanoNat.Nat.shiftr_shiftr.
        assert (p_spec' = map (F.of_Z q) p') as ->.
        { transitivity (map (F.of_Z q) (map Zreduce p')).
          - rewrite Hcont_eq, map_map, (map_ext _ id), map_id; auto.
            intros. rewrite F.of_Z_to_Z. reflexivity.
          - rewrite map_map. apply map_ext_in.
            intros a Ha. rewrite (bounded_by_reduce_eq (1 + n) _ ltac:(Lia.nia)).
            + rewrite F.of_Z_to_Z. reflexivity.
            + apply (Forall_In Hbounds); auto. }
        assert (Hshiftr: forall i, (i <= r - start)%nat -> Nat.shiftr len i = Nat.pow 2 (r - start - i)).
        { intros. subst len. rewrite PeanoNat.Nat.shiftr_div_pow2.
          rewrite <- PeanoNat.Nat.pow_sub_r by Lia.lia. reflexivity. }
        assert (Hpow2nz: forall k, (0 < Nat.pow 2 k)%nat).
        { intros; pose proof (NatUtil.pow_nonzero 2 k ltac:(congruence)). Lia.lia. }
        repeat rewrite Hshiftr by Lia.lia.
        pose proof (polynomial_list_full_loop_may_reduce_spec true (Nat.shiftl 1 (start + n)) (Nat.pow 2 (r - start - n)) (Nat.pow 2 (r - start - (n + 1))%nat) (l + (Nat.pow 2 (start + n) - Nat.pow 2 start))%nat p' (1 + n)%nat (Hpow2nz _) ltac:(rewrite <- PeanoNat.Nat.pow_succ_r'; f_equal; Lia.lia) ltac:(rewrite Hlen_eq, PeanoNat.Nat.shiftl_mul_pow2, PeanoNat.Nat.mul_1_l, <- PeanoNat.Nat.pow_add_r, Hp; f_equal; Lia.lia) ltac:(Lia.nia) ltac:(Lia.lia) Hbounds) as HH.
        destruct (polynomial_list_loop_with_reduce (Nat.shiftl 1 (start + n)) (Nat.pow 2 (r - start - n)) (Nat.pow 2 (r - start - (n + 1))) ((l + (Nat.pow 2 (start + n) - Nat.pow 2 start))%nat, 0%nat, p')) as ((l2' & ?) & p2') eqn:Hp2'.
        destruct (polynomial_list_loop (map (F.of_Z q) precomp_zetas) (Nat.shiftl 1 (start + n)) (Nat.pow 2 (r - start - n)) (Nat.pow 2 (r - start - (n + 1))) ((l + (Nat.pow 2 (start + n) - Nat.pow 2 start))%nat, 0%nat, map (F.of_Z q) p')) as ((l_spec2' & ?) & p_spec2') eqn:Hp_spec2'.
        destruct HH as (-> & <- & Hbounds' & _ & <- & Hlen_eq').
        repeat split; auto.
        2: transitivity (length p'); auto.
        assert (start + S n = S (start + n))%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.pow_succ_r', PeanoNat.Nat.shiftl_mul_pow2, PeanoNat.Nat.mul_1_l.
        pose proof (PeanoNat.Nat.pow_le_mono_r 2 start (start + n)%nat ltac:(congruence) ltac:(Lia.lia)).
        Lia.lia.
      Qed.

      (* Assumes length p = 2^n *)
      (* Does a * k_iter loop iterations *)
      Definition ntt_loop_delay_reduce_no_remainder (a n: nat) (p: list Z) :=
        let l := 0%nat in
        let len := Nat.pow 2 n in
        let '(_, _, p) :=
          List.fold_left
            (fun state i =>
               let '(l, len, p) := state in
               let '(l, len, p) := polynomial_layer_decomposition_loop_delay_reduce (i * Z.to_nat k_iter)%nat (Z.to_nat k_iter - 1)%nat (l, len, p) in
               (l, len, p))
            (seq 0 a)
            (l, len, p) in
        p.

      (* Assumes length p = 2^n *)
      (* Does a * k_iter + r loop iterations assuming 0 < r < k_iter *)
      Definition ntt_loop_delay_reduce_with_remainder (a r n: nat) (p: list Z) :=
        let l := 0%nat in
        let len := Nat.pow 2 n in
        let '(l, len, p) :=
          List.fold_left
            (fun state i =>
               let '(l, len, p) := state in
               let '(l, len, p) := polynomial_layer_decomposition_loop_delay_reduce (i * Z.to_nat k_iter)%nat (Z.to_nat k_iter - 1)%nat (l, len, p) in
               (l, len, p))
            (seq 0 a)
            (l, len, p) in
        let '(_, _, p) :=
          polynomial_layer_decomposition_loop_delay_reduce (a * Z.to_nat k_iter)%nat (r - 1)%nat (l, len, p) in
        p.

      Lemma ntt_loop_delay_reduce_specs:
        (forall a n p,
          length p = Nat.pow 2 n ->
          (a * Z.to_nat k_iter <= n)%nat ->
          ntt_loop_delay_reduce_no_remainder a n (List.map F.to_Z p) = List.map F.to_Z (ntt_loop (List.map (F.of_Z q) precomp_zetas) (a * Z.to_nat k_iter)%nat n p)) /\
        (forall a (r: nat) n p,
          length p = Nat.pow 2 n ->
          (a * Z.to_nat k_iter + r <= n)%nat ->
          (0 < r < k_iter)%Z ->
          ntt_loop_delay_reduce_with_remainder a r n (List.map F.to_Z p) = List.map F.to_Z (ntt_loop (List.map (F.of_Z q) precomp_zetas) (a * Z.to_nat k_iter + r)%nat n p)).
      Proof.
        set (f_rec :=
               fun a n p =>
                 List.fold_left
                   (fun state i =>
                      let '(l, len, p) := state in
                      let '(l, len, p) := polynomial_layer_decomposition_loop_delay_reduce (i * Z.to_nat k_iter)%nat (Z.to_nat k_iter - 1)%nat (l, len, p) in
                      (l, len, p))
                   (seq 0 a)
                   (0%nat, Nat.pow 2 n, p)).
        assert (forall a n p, ntt_loop_delay_reduce_no_remainder a n p = snd (f_rec a n p)) as Hf_rec_eq.
        { intros. unfold ntt_loop_delay_reduce_no_remainder, f_rec.
          do 2 rewrite (surjective_pairing _). reflexivity. }
        assert (forall a r n p, ntt_loop_delay_reduce_with_remainder a r n p = snd (polynomial_layer_decomposition_loop_delay_reduce (a * Z.to_nat k_iter)%nat (r - 1)%nat (f_rec a n p))) as Hf_rec_eq'.
        { intros. unfold ntt_loop_delay_reduce_with_remainder.
          assert (fold_left _ _ _ = f_rec a n p) as -> by reflexivity.
          do 4 (rewrite (surjective_pairing _)). reflexivity. }
        set (f_rec_spec :=
               fun r n p =>
                 polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) 0%nat r (0%nat, Nat.pow 2 n, p)).
        assert (forall r n p, ntt_loop (map (F.of_Z q) precomp_zetas) r n p = snd (f_rec_spec r n p)) as Hf_rec_spec_eq.
        { intros. unfold ntt_loop, f_rec_spec. do 2 rewrite (surjective_pairing _).
          reflexivity. }
        assert (forall a n p,
                   length p = Nat.pow 2 n ->
                   (a * Z.to_nat k_iter <= n)%nat ->
                   let '(l', len', p') :=
                     f_rec a n (map F.to_Z p) in
                   let '(l_spec', len_spec', p_spec') :=
                     f_rec_spec (a * Z.to_nat k_iter)%nat n p in
                   l' = l_spec' /\
                   len' = len_spec' /\ len' = Nat.pow 2 (n - a * Z.to_nat k_iter)%nat /\
                   p' = List.map F.to_Z p_spec' /\
                   length p' = length p) as IH.
        { induction a; intros n p Hlenp Hn.
          - cbn. repeat split; try reflexivity.
            + rewrite PeanoNat.Nat.sub_0_r; reflexivity.
            + rewrite length_map. reflexivity.
          - unfold f_rec. rewrite seq_S, fold_left_app.
            cbn [fold_left]. assert (fold_left _ _ _ = f_rec a n (map F.to_Z p)) as -> by reflexivity.
            unfold f_rec_spec, polynomial_layer_decomposition_loop.
            rewrite PeanoNat.Nat.mul_succ_l, ListUtil.seq_add, PeanoNat.Nat.add_0_l, PeanoNat.Nat.add_0_l.
            rewrite fold_left_app.
            assert (fold_left _ (seq 0 _) _ = f_rec_spec (a * Z.to_nat k_iter)%nat n p) as -> by reflexivity.
            assert (fold_left _ _ _ = polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) (a * Z.to_nat k_iter)%nat (Z.to_nat k_iter)%nat (f_rec_spec (a * Z.to_nat k_iter)%nat n p)) as -> by reflexivity.
            specialize (IHa n p Hlenp ltac:(Lia.nia)).
            destruct (f_rec a n (map F.to_Z p)) as ((l' & len') & p') eqn:Hp'.
            destruct (f_rec_spec (a * Z.to_nat k_iter)%nat n p) as ((l_spec' & len_spec') & p_spec') eqn:Hp_spec'.
            destruct IHa as (<- & <- & Hlen_eq' & -> & Hlen_eq).
            rewrite length_map in Hlen_eq.
            pose proof (polynomial_layer_decomposition_loop_delay_reduce_spec n (a * Z.to_nat k_iter)%nat (Z.to_nat k_iter - 1)%nat l' len' p_spec' ltac:(pose proof k_iter_ge_1; Lia.lia) ltac:(pose proof k_iter_ge_1; Lia.lia) ltac:(transitivity (length p); auto) Hlen_eq') as IH.
            destruct (polynomial_layer_decomposition_loop_delay_reduce (a * Z.to_nat (Zreduce_bounds / (Z.pos q * Z.pos q))) (Z.to_nat (Zreduce_bounds / (Z.pos q * Z.pos q)) - 1) (l', len', map F.to_Z p_spec')) as ((l2' & len2') & p2') eqn:Hp2'.
            rewrite PeanoNat.Nat.add_1_r, <- PeanoNat.pred_of_minus, (PeanoNat.Nat.lt_succ_pred 0) in IH by (pose proof k_iter_ge_1; Lia.lia).
            destruct (polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) (a * Z.to_nat (Zreduce_bounds / (Z.pos q * Z.pos q))) (Z.to_nat (Zreduce_bounds / (Z.pos q * Z.pos q))) (l', len', p_spec')) as ((l_spec2' & len_spec2') & p_spec2') eqn:Hp_spec2'.
            destruct IH as (<- & -> & <- & -> & -> & ->).
            repeat split; auto.
            rewrite Hlen_eq', PeanoNat.Nat.shiftr_div_pow2.
            rewrite <- PeanoNat.Nat.pow_sub_r by Lia.lia.
            f_equal. Lia.lia. }
        split.
        { intros a n p Hlenp Hn.
          rewrite Hf_rec_eq, Hf_rec_spec_eq.
          specialize (IH a n p Hlenp Hn).
          destruct (f_rec a n (map F.to_Z p)) as ((l' & len') & p') eqn:Hp'.
          destruct (f_rec_spec (a * Z.to_nat k_iter)%nat n p) as ((l_spec' & len_spec') & p_spec') eqn:Hp_spec'.
          destruct IH as (<- & <- & -> & -> & _). cbn. reflexivity. }
        { intros a r n p Hlenp Hn Hr.
          rewrite Hf_rec_eq', Hf_rec_spec_eq.
          specialize (IH a n p Hlenp ltac:(Lia.lia)).
          unfold f_rec_spec, polynomial_layer_decomposition_loop.
          rewrite ListUtil.seq_add, PeanoNat.Nat.add_0_l.
          rewrite fold_left_app.
          assert (fold_left _ (seq 0 _) _ = f_rec_spec (a * Z.to_nat k_iter)%nat n p) as -> by reflexivity.
          assert (fold_left _ _ _ = polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) (a * Z.to_nat k_iter)%nat r (f_rec_spec (a * Z.to_nat k_iter)%nat n p)) as -> by reflexivity.
          destruct (f_rec a n (map F.to_Z p)) as ((l' & len') & p') eqn:Hp'.
          destruct (f_rec_spec (a * Z.to_nat k_iter)%nat n p) as ((l_spec' & len_spec') & p_spec') eqn:Hp_spec'.
          destruct IH as (<- & <- & Hlen_eq' & -> & Hlen_eq).
          rewrite length_map in Hlen_eq.
          pose proof (polynomial_layer_decomposition_loop_delay_reduce_spec n (a * Z.to_nat k_iter)%nat (r - 1)%nat l' len' p_spec' ltac:(pose proof k_iter_ge_1; Lia.lia) ltac:(pose proof k_iter_ge_1; Lia.lia) ltac:(transitivity (length p); auto) Hlen_eq') as HH.
          destruct (polynomial_layer_decomposition_loop_delay_reduce (a * Z.to_nat (Zreduce_bounds / (Z.pos q * Z.pos q))) (r - 1)%nat (l', len', map F.to_Z p_spec')) as ((l2' & len2') & p2') eqn:Hp2'.
          replace (S (r - 1)) with r in HH by Lia.lia.
          destruct (polynomial_layer_decomposition_loop (map (F.of_Z q) precomp_zetas) (a * Z.to_nat (Zreduce_bounds / (Z.pos q * Z.pos q))) r (l', len', p_spec')) as ((l_spec2' & len_spec2') & p_spec2') eqn:Hp_spec2'.
          destruct HH as (? & ? & ? & ? & ? & ?). cbn; auto. }
      Qed.

      Lemma ntt_loop_delay_reduce_no_remainder_spec:
        forall a n p,
          length p = Nat.pow 2 n ->
          (a * Z.to_nat k_iter <= n)%nat ->
          ntt_loop_delay_reduce_no_remainder a n (List.map F.to_Z p) = List.map F.to_Z (ntt_loop (List.map (F.of_Z q) precomp_zetas) (a * Z.to_nat k_iter)%nat n p).
      Proof. exact (proj1 ntt_loop_delay_reduce_specs). Qed.

      Lemma ntt_loop_delay_reduce_with_remainder_spec:
        forall a (r: nat) n p,
          length p = Nat.pow 2 n ->
          (a * Z.to_nat k_iter + r <= n)%nat ->
          (0 < r < k_iter)%Z ->
          ntt_loop_delay_reduce_with_remainder a r n (List.map F.to_Z p) = List.map F.to_Z (ntt_loop (List.map (F.of_Z q) precomp_zetas) (a * Z.to_nat k_iter + r)%nat n p).
      Proof. exact (proj2 ntt_loop_delay_reduce_specs). Qed.

      Lemma ntt_loop_delay_reduce_full_spec:
        forall n p,
          let a := Nat.div (Nat.min n m) (Z.to_nat k_iter) in
          let r := Nat.modulo (Nat.min n m) (Z.to_nat k_iter) in
          map F.to_Z (proj1_sig (nttl n p)) =
            if PeanoNat.Nat.eq_dec r 0 then
              ntt_loop_delay_reduce_no_remainder a n (map F.to_Z (proj1_sig p))
            else
              ntt_loop_delay_reduce_with_remainder a r n (map F.to_Z (proj1_sig p)).
      Proof.
        intros. rewrite (ntt_loop_full_spec (map (F.of_Z q) precomp_zetas) precomp_zetas_eq').
        assert (Nat.min n m = a * Z.to_nat k_iter + r)%nat as Heq.
        { rewrite (PeanoNat.Nat.div_mod_eq (Nat.min n m) (Z.to_nat k_iter)).
          Lia.lia. }
        rewrite Heq.
        destruct (PeanoNat.Nat.eq_dec r 0) as [->|Hrnz].
        - rewrite PeanoNat.Nat.add_0_r in *.
          rewrite <- ntt_loop_delay_reduce_no_remainder_spec; auto.
          + rewrite (proj2_sig p), PolynomialCRT.posicyclic_measure; [Lia.lia|].
            pose proof (NatUtil.pow_nonzero 2 n ltac:(congruence)). Lia.lia.
          + rewrite <- Heq. Lia.lia.
        - rewrite <- ntt_loop_delay_reduce_with_remainder_spec; auto.
          + rewrite (proj2_sig p), PolynomialCRT.posicyclic_measure; [Lia.lia|].
            pose proof (NatUtil.pow_nonzero 2 n ltac:(congruence)). Lia.lia.
          + rewrite <- Heq; Lia.lia.
          + pose proof (NatUtil.mod_bound_lt (Nat.min n m) (Z.to_nat k_iter) ltac:(pose proof k_iter_ge_1; Lia.lia)).
            split; Lia.lia.
      Qed.
    End ForwardNTT.
  End Delayed_add_sub_reduce.
End Gallina.

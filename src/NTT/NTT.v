Require Import Coq.PArith.BinPosDef. Local Open Scope positive_scope.
Require Import Coq.NArith.BinNat.
From Coq.Classes Require Import Morphisms.
Require Import Spec.ModularArithmetic.
Require Import Arithmetic.ModularArithmeticTheorems.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Znumtheory Coq.Lists.List. Import ListNotations.
Require Import NTT.Polynomial NTT.PolynomialCRT.
Require PrimeFieldTheorems.

Require Import coqutil.Datatypes.List.

Section CyclotomicDecomposition.
  Local Coercion N.of_nat: nat >-> N.
  Context {q: positive} {prime_q: prime q}.
  Local Notation F := (F q). (* This is to have F.pow available, there is no Fpow defined for a general field *)
  Local Open Scope F_scope.
  Context {field: @Hierarchy.field F eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}
    {char_ge_3: @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos (BinNat.N.two))}.
  Context {P}{poly_ops: @Polynomial.polynomial_ops F P}.
  Context {poly_defs: @Polynomial.polynomial_defs F eq F.zero F.one F.opp F.add F.sub F.mul P _}.
  Context {zeta: F} {m: nat} {Hm: zeta ^ (N.pow 2 m) = F.opp 1}.

  (* Too many instances *)
  Remove Hints F.commutative_ring_modulo: typeclass_instances.

  Local Notation Peq := (@Polynomial.Peq F eq P _).
  Local Notation Pmod := (@Polynomial.Pmod F F.zero P _ F.div).
  Local Notation Pmul := (@Polynomial.Pmul _ _ poly_ops).
  Local Notation Pconst := (@Polynomial.Pconst _ _ poly_ops).
  Local Notation negacyclic := (@PolynomialCRT.negacyclic F P _).
  Local Notation posicyclic := (@PolynomialCRT.posicyclic F F.opp P _).
  Local Notation Pgcd := (Polynomial.Pgcd (poly_ops:=poly_ops)(poly_defs:=poly_defs)(Fdiv:=F.div)).
  Local Notation coprime := (Polynomial.coprime (poly_ops:=poly_ops)(poly_defs:=poly_defs)(Fdiv:=F.div)).
  Local Notation Pquotl := (@Polynomial.Pquotl F eq F.zero P _ F.div).
  Local Notation of_pl := (Polynomial.of_pl (poly_defs:=poly_defs) (Finv:=F.inv) (Fdiv:=F.div) (field:=field)).
  Local Notation NTT2 := (PolynomialCRT.phi2 (poly_ops:=poly_ops)).
  Local Notation iNTT2 := (PolynomialCRT.psi2 (Feq:=eq)(poly_ops:=poly_ops)).
  Local Notation Pquot := (@Polynomial.Pquot F eq F.zero P _ F.div).
  Local Notation one := (@Polynomial.one F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).
  Local Notation eq1 := (@Polynomial.eq1 F eq F.zero _ poly_ops F.div).
  Local Notation add := (@Polynomial.add F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).
  Local Notation mul := (@Polynomial.mul F eq F.zero F.one F.opp F.add F.sub F.mul _ F.eq_dec _ poly_ops poly_defs F.inv F.div _).

  Lemma zeta_pow_nz:
    forall k, zeta ^ k <> 0.
  Proof.
    apply N.peano_ind.
    - rewrite F.pow_0_r. symmetry; apply Hierarchy.zero_neq_one.
    - intros n IH. rewrite F.pow_succ_r.
      intro X. apply Hierarchy.zero_product_zero_factor in X.
      destruct X as [X|X]; [|elim IH; auto].
      rewrite X in Hm. rewrite F.pow_0_l in Hm by Lia.lia.
      symmetry in Hm. apply Group.inv_id_iff in Hm.
      rewrite Group.inv_inv in Hm.
      symmetry in Hm. apply Hierarchy.zero_neq_one in Hm; auto.
  Qed.

  Lemma zeta_pow_succ_m:
    zeta ^ (N.pow 2 (N.succ m)) = 1.
  Proof.
    rewrite N.pow_succ_r', N.mul_comm, <- F.pow_pow_l, Hm.
    rewrite F.pow_2_r, (@Ring.mul_opp_l F eq _ _ _ _ _ _ _ 1 _), (@Ring.mul_opp_r F eq _ _ _ _ _ _ _ _ 1).
    rewrite (@Group.inv_inv F _ _ _ _ _).
    apply Hierarchy.left_identity.
  Qed.

  Lemma zeta_pow_mod:
    forall k, zeta ^ k = zeta ^ (k mod (N.pow 2 (N.succ m))).
  Proof.
    intros k; rewrite (N.Div0.div_mod k (N.pow 2 (N.succ m))) at 1.
    rewrite F.pow_add_r, <- F.pow_pow_l.
    rewrite zeta_pow_succ_m, F.pow_1_l.
    apply Hierarchy.left_identity.
  Qed.

  Lemma neg_zeta_power_eq:
    forall k,
      F.opp (zeta ^ k) = zeta ^ (N.add (N.pow 2 m) k).
  Proof.
    intros k. rewrite F.pow_add_r, Hm.
    rewrite Ring.mul_opp_l, (@Hierarchy.left_identity F eq F.mul _ _ _).
    reflexivity.
  Qed.

  Section Inductive_Case.
    Context (rec_decompose: nat -> nat -> list nat).

    Let rec_decomposition := fun r' k l => List.map (fun n => posicyclic (Nat.pow 2 (k - r')) (F.pow zeta (N.of_nat n))) (rec_decompose r' l).

    Context
      (rec_ntt: forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ l)) -> Pquotl (rec_decomposition r' k l))
      (rec_intt: forall (r' k l: nat), (r' <= k)%nat -> (r' <= m)%nat -> (Nat.modulo l (Nat.pow 2 r') = 0)%nat -> Pquotl (rec_decomposition r' k l) -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ l))).

    Context (r' k l: nat) (r := S r').
    Context (r_leq_k: (r <= k)%nat).
    Context (r_leq_m: (r <= m)%nat).
    Context (r_leq_l: (Nat.modulo l (Nat.pow 2 r) = 0)%nat).

    Context
      (h_rec_ntt_isomorphism:
        forall (k: nat) (l: nat)
          (Hr_leq_k: (r' <= k)%nat)
          (Hr_leq_m: (r' <= m)%nat)
          (Hr_leq_l: (Nat.modulo l (Nat.pow 2 r') = 0)%nat),
          @Ring.is_isomorphism
            _ eq1 one add mul
            _ eql onel addl mull
            (rec_ntt r' k l Hr_leq_k Hr_leq_m Hr_leq_l)
            (rec_intt r' k l Hr_leq_k Hr_leq_m Hr_leq_l)).

    Let m0 := (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)).
    Let m1 := (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Let m2 := (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.pow 2 m + Nat.div l 2)))).

    Local Lemma r_leq_k': (r' <= k - 1)%nat. Proof. Lia.lia. Qed.
    Local Lemma r_leq_m': (r' <= m)%nat. Proof. Lia.lia. Qed.
    Local Lemma r_leq_l_lhs: (Nat.modulo (Nat.div l 2) (Nat.pow 2 r') = 0)%nat.
    Proof.
      rewrite <- PeanoNat.Nat.Div0.div_exact in r_leq_l.
      rewrite <- PeanoNat.Nat.Div0.div_exact.
      rewrite PeanoNat.Nat.Div0.div_div.
      rewrite r_leq_l at 1. unfold r; rewrite PeanoNat.Nat.pow_succ_r'.
      assert (2 * _ * _ = (PeanoNat.Nat.pow 2 r' * PeanoNat.Nat.div l (2 * PeanoNat.Nat.pow 2 r')) * 2)%nat as -> by Lia.lia.
      rewrite PeanoNat.Nat.div_mul by congruence. reflexivity.
    Qed.

    Local Lemma r_leq_l_rhs: (Nat.modulo (Nat.pow 2 m + Nat.div l 2) (Nat.pow 2 r') = 0)%nat.
    Proof.
      assert (m = r' + (m - r'))%nat as -> by Lia.lia.
      rewrite PeanoNat.Nat.pow_add_r.
      rewrite PeanoNat.Nat.add_comm, PeanoNat.Nat.mul_comm, PeanoNat.Nat.Div0.mod_add.
      apply r_leq_l_lhs.
    Qed.

    Local Lemma ok_m0:
      Peq m0 (posicyclic (2 * (Nat.pow 2 (k - 1))) ((zeta ^ (N.of_nat (Nat.div l 2))) * (zeta ^ (N.of_nat (Nat.div l 2))))%F).
    Proof.
      rewrite <- PeanoNat.Nat.pow_succ_r'.
      assert (S (k - 1) = k) as -> by Lia.lia.
      assert (_ * _ = zeta ^ l) as ->.
      { rewrite <- F.pow_2_r, F.pow_pow_l. f_equal.
        assert (2 = N.of_nat 2)%N as -> by reflexivity.
        rewrite <- Nnat.Nat2N.inj_mul, Nnat.Nat2N.inj_iff.
        rewrite <- PeanoNat.Nat.Div0.div_exact in r_leq_l.
        rewrite r_leq_l.
        unfold r. rewrite PeanoNat.Nat.pow_succ_r'.
        assert (2 * _ * _ = (PeanoNat.Nat.pow 2 r' * PeanoNat.Nat.div l (2 * PeanoNat.Nat.pow 2 r')) * 2)%nat as -> by Lia.lia.
        rewrite PeanoNat.Nat.div_mul by congruence. reflexivity. }
      reflexivity.
    Qed.

    Local Lemma ok_m1:
      Peq m1 (posicyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof. reflexivity. Qed.

    Local Lemma ok_m2:
      Peq m2 (negacyclic (Nat.pow 2 (k - 1)) (zeta ^ (N.of_nat (Nat.div l 2)))).
    Proof.
      rewrite <- posicyclic_opp, neg_zeta_power_eq.
      assert (2 ^ N.of_nat m = Nat.pow 2 m)%N as -> by (rewrite Nnat.Nat2N.inj_pow; reflexivity).
      rewrite <- Nnat.Nat2N.inj_add. reflexivity.
    Qed.

    Definition ntt2:
      Pquot m0 ->
      Pquot m1 * Pquot m2 :=
      NTT2 m0 m1 m2.

    Program Definition intt2:
      Pquot m1 * Pquot m2 ->
      Pquot m0 :=
      iNTT2 m0 m1 m2.

    Lemma ntt_isomorphism2:
      @Ring.is_isomorphism
        (Pquot m0) eq1 one add mul
        (Pquot m1 * Pquot m2) (EQ2 m1 m2) (ONE2 m1 m2) (ADD2 m1 m2) (MUL2 m1 m2)
        ntt2
        intt2.
    Proof.
      assert (Hcoprime: coprime m1 m2).
      { rewrite ok_m2. unfold m1.
        apply posicyclic_decomposition_coprime.
        - pose proof (NatUtil.pow_nonzero 2 (k - 1)%nat ltac:(congruence)); Lia.lia.
        - apply zeta_pow_nz. }
      assert (Heq: Peq m0 (Pmul m1 m2)).
      { rewrite ok_m2. unfold m1.
        rewrite <- posicyclic_decomposition. apply ok_m0. }
      apply (CRT_isomorphism2 m0 m1 m2 Hcoprime Heq).
    Qed.

    Definition decompose_body': list nat :=
      (rec_decompose r' (Nat.div l 2)) ++ (rec_decompose r' (Nat.pow 2 m + Nat.div l 2)).

    Let decomposition_body' := List.map (fun n => posicyclic (Nat.pow 2 (k - r)) (F.pow zeta (N.of_nat n))) decompose_body'.

    Lemma decomposition_body_spec':
      Forall2 Peq ((rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))) decomposition_body'.
    Proof.
      unfold decomposition_body', decompose_body'.
      rewrite List.map_app. unfold rec_decomposition.
      assert (k - 1 - r' = k - r)%nat as -> by Lia.lia.
      rewrite (ListUtil.Forall2_forall_iff _ _ _ Pzero) by reflexivity.
      intros; reflexivity.
    Qed.

    Lemma decomposition_body_spec'':
      Forall2 Peq decomposition_body' ((rec_decomposition r' (k - 1) (Nat.div l 2)) ++ (rec_decomposition r' (k - 1) (Nat.pow 2 m + Nat.div l 2))).
    Proof. symmetry; apply decomposition_body_spec'. Qed.

    Definition ntt_body' (p: Pquot m0): Pquotl decomposition_body' :=
      Pquotl_convert decomposition_body_spec' (Pquotl_app (Ring.apply_unop_pair (rec_ntt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs) (rec_ntt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs) (ntt2 p))).

    Definition intt_body' (pl: Pquotl decomposition_body'): Pquot m0 :=
      intt2 (Ring.apply_unop_pair (rec_intt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs) (rec_intt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs) (Pquotl_split (Pquotl_convert decomposition_body_spec'' pl))).

    Lemma ntt_isomorphism':
      @Ring.is_isomorphism _ eq1 one add mul _ eql onel addl mull ntt_body' intt_body'.
    Proof.
      pose proof (Hlhs_iso := h_rec_ntt_isomorphism (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs).
      pose proof (Hrhs_iso := h_rec_ntt_isomorphism (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs).
      pose proof (Hntt2 := ntt_isomorphism2).
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                (Pquotl_convert decomposition_body_spec')
                (fun pl : Pquotl _ =>
                   intt2 (Ring.apply_unop_pair
                            (rec_intt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
                            (rec_intt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
                            (Pquotl_split pl)))
                (Pquotl_convert decomposition_body_spec'')); [|apply Pquotl_convert_isomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                _
                Pquotl_app
                (fun x =>
                   intt2 (Ring.apply_unop_pair
                            (rec_intt r' (k - 1) (Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_lhs)
                            (rec_intt r' (k - 1) (Nat.pow 2 m + Nat.div l 2) r_leq_k' r_leq_m' r_leq_l_rhs)
                            x))
                Pquotl_split); [|apply PquotlAppRingIsomorphism].
      eapply (@Ring.compose_isomorphism
                _ _ _ _ _
                _ _ _ _ _
                _ _ _ _ _ _ _ _
                _
                ntt2
                _
                intt2
                _); [apply Hntt2|].
      Unshelve. 5: apply Ring.product_ring.
      apply Ring.product_isomorphism.
    Qed.
  End Inductive_Case.

  Definition decompose_body rec_decompose (r l: nat): list nat :=
    match r with
    | S r' => decompose_body' rec_decompose r' l
    | O => [l]
    end.

  Fixpoint decompose (r l: nat): list nat := decompose_body decompose r l.

  Definition decomposition (r k l: nat) :=
    List.map (fun n => posicyclic (Nat.pow 2 (k - r)%nat) (zeta ^ (N.of_nat n))) (decompose r l).

  Program Definition ntt_body rec_ntt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquot (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) -> Pquotl (decomposition r k l) :=
    match r with
    | S r' => ntt_body' decompose rec_ntt r' k l Hr_leq_k Hr_leq_m Hr_leq_l
    | O => fun p => [proj1_sig p]
    end.
  Next Obligation. constructor; [|constructor]. rewrite PeanoNat.Nat.sub_0_r. apply (proj2_sig p). Qed.

  Fixpoint ntt' (r k l: nat) :=
    ntt_body ntt' r k l.

  Lemma pow_2_mod n:
    Nat.modulo (Nat.pow 2 m) (Nat.pow 2 (Nat.min n m)) = 0%nat.
  Proof.
    replace m with ((m - (Nat.min n m)) + Nat.min n m)%nat at 1 by Lia.lia.
    rewrite PeanoNat.Nat.pow_add_r.
    rewrite <- PeanoNat.Nat.Div0.div_exact.
    rewrite PeanoNat.Nat.div_mul by (apply PeanoNat.Nat.pow_nonzero; congruence).
    apply PeanoNat.Nat.mul_comm.
  Qed.

  Program Definition ntt (n: nat) p :=
    ntt' (Nat.min n m) n (Nat.pow 2 m) (PeanoNat.Nat.le_min_l _ _) (PeanoNat.Nat.le_min_r _ _) (pow_2_mod _) p.

  Program Definition intt_body rec_intt (r k l : nat) (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat): Pquotl (decomposition r k l) -> Pquot (posicyclic (Nat.pow 2 k) (zeta ^ N.of_nat l)) :=
    match r with
    | S r' => intt_body' decompose rec_intt r' k l Hr_leq_k Hr_leq_m Hr_leq_l
    | O => fun pl => List.hd Pzero (proj1_sig pl)
    end.
  Next Obligation.
    cbv [decomposition decompose decompose_body map] in pl.
    destruct pl as [pl Hpl]. simpl.
    inversion Hpl; subst; clear Hpl. inversion H4; subst; clear H4.
    simpl. rewrite PeanoNat.Nat.sub_0_r in H3. exact H3.
  Qed.

  Fixpoint intt' (r k l: nat) :=
    intt_body intt' r k l.

  Program Definition intt (n: nat) pl :=
    intt' (Nat.min n m) n (Nat.pow 2 m) (PeanoNat.Nat.le_min_l _ _) (PeanoNat.Nat.le_min_r _ _) (pow_2_mod _) pl.

  Lemma ntt_rec_isomorphism:
    forall r k l (Hr_leq_k: (r <= k)%nat) (Hr_leq_m: (r <= m)%nat) (Hr_leq_l: Nat.modulo l (Nat.pow 2 r) = 0%nat),
      @Ring.is_isomorphism
        _ eq1 one add mul
        _ eql onel addl mull
        (ntt' r k l Hr_leq_k Hr_leq_m Hr_leq_l)
        (intt' r k l Hr_leq_k Hr_leq_m Hr_leq_l).
  Proof.
    induction r; intros.
    - split; simpl.
      + split; simpl.
        * split; simpl.
          { intros a b; destruct a as (a & Ha); destruct b as (b & Hb).
            unfold eql; simpl. repeat constructor.
            rewrite Pmod_distr, <- Ha, <- Hb. reflexivity. }
          { intros a b; destruct a as (a & Ha); destruct b as (b & Hb).
            unfold eq1, eql; simpl. intros; repeat constructor; auto. }
        * unfold eql; simpl.
          intros a b; destruct a as (a & Ha); destruct b as (b & Hb); simpl.
          rewrite PeanoNat.Nat.sub_0_r. reflexivity.
        * unfold eql; simpl. rewrite PeanoNat.Nat.sub_0_r. reflexivity.
      + intro a; destruct a as (a & Ha); unfold eql; simpl.
        inversion Ha; subst. inversion H3. simpl.
        reflexivity.
      + intros a b; destruct a as (a & Ha); destruct b as (b & Hb).
        unfold eql, eq1; simpl. inversion 1; auto.
    - apply (ntt_isomorphism' _ _ _ _ _ _ _ _ _ IHr).
  Qed.

  Lemma ntt_isomorphism:
    forall n,
      @Ring.is_isomorphism _ eq1 one add mul _ eql onel addl mull (ntt n) (intt n).
  Proof. intros; apply ntt_rec_isomorphism. Qed.
End CyclotomicDecomposition.

Section SanityCheck.
  Local Definition bitrev (n: nat) (i: nat): nat :=
    let fix aux k := match k with
                     | O => if Nat.testbit i 0%nat then PeanoNat.Nat.setbit 0%nat (n - 1)%nat else 0%nat
                     | S k' => if Nat.testbit i k then PeanoNat.Nat.setbit (aux k') (n - 1 - k)%nat else aux k'
                     end in
    aux (n - 1)%nat.

  Local Notation bitrev8 := (bitrev 8%nat). (* Dilithium *)
  Local Notation bitrev7 := (bitrev 7%nat). (* Kyber *)

  (* Making sure the decomposition returns the same order expected by ML-DSA
     aka Dilithium *)
  (* See Section 7.5 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf *)
  Local Lemma dilithium_ok:
    (@decompose 8%nat 8%nat (Nat.pow 2 8)) = List.map (fun k => (2 * (bitrev8 k) + 1)%nat) (seq 0 256%nat).
  Proof. reflexivity. Qed.

  (* Making sure the decomposition returns the same order expected by ML-KEM
     aka Kyber *)
  (* See Section 4.3 of https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.pdf *)
  Local Lemma kyber_ok:
    (@decompose 7%nat 7%nat (Nat.pow 2 7)) = List.map (fun k => (2 * (bitrev7 k) + 1)%nat) (seq 0 128%nat).
  Proof. reflexivity. Qed.
End SanityCheck.

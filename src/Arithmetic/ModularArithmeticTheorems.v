From Coq Require Import Lia Zmod.
Require Import Crypto.Spec.ModularArithmetic.

From Coq Require Import ZArith Zdiv Znumtheory NArith NArithRing. (* import Zdiv before Znumtheory *)
From Coq Require Import Morphisms Setoid.
From Coq Require Export Ring_theory Ring_tac.

Require Import Crypto.Algebra.Hierarchy Crypto.Algebra.ScalarMult.
Require Crypto.Algebra.Ring Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZUtil.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Export Crypto.Util.FixCoqMistakes.

Module Zmod.
  Global Instance eq_dec {m} : DecidableRel (@eq (Zmod m)).
  Proof.
    refine (fun x y =>
              match Zmod.eqb x y as b return Zmod.eqb x y = b -> {x = y} + {x <> y} with
              | true => fun H => left _
              | false => fun H => right _
              end eq_refl);
      abstract (revert H; case (Zmod.eqb_spec x y); intros; congruence).
  Defined.

  Global Instance commutative_ring_modulo m
    : @Algebra.Hierarchy.commutative_ring (Zmod m) Logic.eq 0%Zmod 1%Zmod Zmod.opp Zmod.add Zmod.sub Zmod.mul.
  Proof.
    repeat (split || intro); subst; try reflexivity;
      auto using Zmod.add_assoc, Zmod.add_comm, Zmod.add_0_l, Zmod.add_0_r,
        Zmod.add_opp_same_l, Zmod.add_opp_same_r, Zmod.add_opp_r,
        Zmod.mul_assoc, Zmod.mul_comm, Zmod.mul_1_l, Zmod.mul_1_r,
        Zmod.mul_add_l, Zmod.mul_add_r.
  Qed.

  Section FandZ.
    Context {m:Z}.
    Local Open Scope Zmod_scope.

    Lemma of_Z_small_nonzero z : (0 < z < m)%Z -> Zmod.of_Z m z <> 0.
    Proof using Type. intros; apply Zmod.of_Z_nz; rewrite Z.mod_small; lia. Qed.

    Lemma to_Z_nonzero_range (x : Zmod m) : (x <> 0) -> 0 < m -> (1 <= Zmod.unsigned x < m)%Z.
    Proof using Type.
      intros Hnz Hlt; pose proof (Zmod.unsigned_nz x Hnz); pose proof (Zmod.unsigned_pos_bound x Hlt); lia.
    Qed.

    Lemma square_iff (x:Zmod m) :
      (exists y : Zmod m, y * y = x) <-> (exists y : Z, y * y mod m = Zmod.unsigned x)%Z.
    Proof using Type.
      setoid_rewrite <-Zmod.unsigned_inj_iff; setoid_rewrite Zmod.unsigned_mul; split; intro H; destruct H as [x' H].
      - eauto.
      - exists (Zmod.of_Z _ x'); rewrite !Zmod.unsigned_of_Z; pull_Zmod; auto.
    Qed.

    Local Notation R_of_nat := (@Ring.of_nat (Zmod m) 0%Zmod 1%Zmod Zmod.add).
    Lemma Ring_of_nat p : R_of_nat (Pos.to_nat p) = Zmod.of_Z m (Z.pos p).
    Proof.
      induction p using Pos.peano_ind.
      { simpl. rewrite left_identity. reflexivity. }
      { rewrite Pos2Nat.inj_succ; simpl; rewrite IHp.
        rewrite <-Pos.add_1_r, Pos2Z.inj_add, Zmod.of_Z_add.
        reflexivity. }
    Qed.

    Local Notation R_of_Z := (@Ring.of_Z (Zmod m) 0%Zmod 1%Zmod Zmod.opp Zmod.add).
    Lemma Ring_of_Z x : R_of_Z x = Zmod.of_Z m x.
    Proof.
      destruct x; cbv [R_of_Z];
        rewrite ?Ring_of_nat, <-?Pos2Z.opp_pos, ?Zmod.of_Z_opp; reflexivity.
    Qed.

    Global Instance char_gt :
      @Ring.char_ge
        (Zmod m) Logic.eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub Zmod.mul
        (Z.to_pos m).
    Proof.
      cbv [Ring.char_ge Hierarchy.char_ge].
      intros p Hp.
      rewrite Ring_of_Z.
      apply Zmod.of_Z_nz.
      destruct m as [|m'|m']; cbn [Z.to_pos] in Hp; try lia.
      rewrite Z.mod_small; lia.
    Qed.
  End FandZ.
  Section FandNat.
    Import Nat.
    Local Infix "mod" := modulo : nat_scope.
    Local Open Scope nat_scope.

    Context {m:Z}.

    Lemma to_nat_of_nat (n:nat) (Hm:(0 < m)%Z) : Zmod.to_nat (Zmod.of_nat m n) = (n mod (Z.to_nat m))%nat.
    Proof using Type.
      unfold Zmod.to_nat, Zmod.of_nat.
      rewrite Zmod.unsigned_of_Z.
      pose proof (Nat2Z.inj_mod n (Z.to_nat m)) as Hmod.
      rewrite Z2Nat.id in Hmod by lia.
      rewrite <- Hmod.
      rewrite Nat2Z.id; reflexivity.
    Qed.

    Lemma of_nat_to_nat x (Hm:(0 < m)%Z) : Zmod.of_nat m (Zmod.to_nat x) = x.
    Proof using Type.
      unfold Zmod.to_nat, Zmod.of_nat.
      rewrite Z2Nat.id; [ eapply Zmod.of_Z_unsigned | eapply Zmod.unsigned_pos_bound; assumption].
    Qed.

    (* TODO: move *)
    Lemma Pos_to_nat_nonzero p : Pos.to_nat p <> 0%nat.
    Proof.
      pose proof (Pos2Nat.is_pos p); lia.
    Qed.

    Lemma of_nat_mod (n:nat) (Hm:(0 < m)%Z) : Zmod.of_nat m (n mod (Z.to_nat m)) = Zmod.of_nat m n.
    Proof using Type.
      unfold Zmod.of_nat.
      rewrite <-(Zmod.of_Z_mod (Z.of_nat n)), ?Nat2Z.inj_mod, ?Z2Nat.id; [reflexivity|].
      lia.
    Qed.

    Lemma to_nat_mod (x:Zmod m) (Hm:(0 < m)%Z) : Zmod.to_nat x mod (Z.to_nat m) = Zmod.to_nat x.
    Proof using Type.
      unfold Zmod.to_nat.
      rewrite <-Zmod.mod_unsigned at 2.
      apply Z.mod_to_nat; [assumption|].
      apply Zmod.unsigned_pos_bound; assumption.
    Qed.

    Lemma of_nat_add x y :
      Zmod.of_nat m (x + y) = (Zmod.of_nat m x + Zmod.of_nat m y)%Zmod.
    Proof using Type. unfold Zmod.of_nat; rewrite Nat2Z.inj_add, Zmod.of_Z_add; reflexivity. Qed.

    Lemma of_nat_mul x y :
      Zmod.of_nat m (x * y) = (Zmod.of_nat m x * Zmod.of_nat m y)%Zmod.
    Proof using Type. unfold Zmod.of_nat; rewrite Nat2Z.inj_mul, Zmod.of_Z_mul; reflexivity. Qed.
  End FandNat.

  Section RingTacticGadgets.
    Context (m:Z).

    Lemma pow_pow_N (x : Zmod m) : forall (n : N), (x ^ Z.of_N n)%Zmod = pow_N 1%Zmod Zmod.mul x n.
    Proof using Type.
      induction n as [|n IHn] using N.peano_ind; [apply Zmod.pow_0_r|].
      rewrite N2Z.inj_succ, Zmod.pow_succ_nonneg_r, IHn by apply N2Z.is_nonneg.
      destruct n as [|p]; cbn [N.succ pow_N pow_pos]; [apply Zmod.mul_1_r|].
      symmetry; apply (@pow_pos_succ (Zmod m) (@Zmod.mul m) eq _ ltac:(solve_proper) (@Zmod.mul_assoc m) x p).
    Qed.

    (* The exponent of [Zmod.pow] is a [Z]; the [ring]/[field] tactics only handle
       [N] exponents internally, so [Z.of_N] is the embedding the tactics see
       (as for [Z]'s own [Zpower_theory]). Together with [is_pow_constant]
       below this lets [ring] normalize [x ^ 2] and [x ^ 3]. *)
    Lemma power_theory : power_theory 1%Zmod (@Zmod.mul m) eq Z.of_N (@Zmod.pow m).
    Proof using Type. split; apply pow_pow_N. Qed.

    (***** Division Theory *****)
    Definition quotrem (a b: Zmod m): Zmod m * Zmod m :=
      (Zmod.of_Z _ (Zmod.unsigned a / Zmod.unsigned b), Zmod.of_Z _ (Zmod.unsigned a mod Zmod.unsigned b)).
    Lemma div_theory : div_theory eq (@Zmod.add m) (@Zmod.mul m) (@id _) quotrem.
    Proof using Type.
      constructor; intros a b; unfold quotrem, id.
      apply Zmod.unsigned_inj.
      rewrite Zmod.unsigned_add, Zmod.unsigned_mul, !Zmod.unsigned_of_Z.
      pull_Zmod.
      rewrite <-Z_div_mod_eq_full; symmetry; apply Zmod.mod_unsigned.
    Qed.

    (* Define a "ring morphism" between GF and Z, i.e. an equivalence
     * between 'inject (ZFunction (X))' and 'GFFunction (inject (X))'.
     *
     * Doing this allows the [ring] tactic to do coefficient
     * manipulations in Z rather than F, because we know it's equivalent
     * to inject the result afterward. *)
    Lemma ring_morph: ring_morph 0%Zmod 1%Zmod Zmod.add Zmod.mul Zmod.sub Zmod.opp   eq
                                 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb  (Zmod.of_Z m).
    Proof using Type.
      split; intros;
        auto using Zmod.of_Z_0, Zmod.of_Z_1, Zmod.of_Z_add, Zmod.of_Z_sub, Zmod.of_Z_mul, Zmod.of_Z_opp.
      match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H; subst; reflexivity end.
    Qed.

    (* Redefine our division theory under the ring morphism *)
    Lemma morph_div_theory:
      Ring_theory.div_theory eq Z.add Z.mul (Zmod.of_Z m) Z.quotrem.
    Proof using Type.
      split; intros a b.
      replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b);
        try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).
      rewrite <- (Z.quot_rem' a b); trivial.
    Qed.

  End RingTacticGadgets.

  Ltac is_constant t := match t with Zmod.of_Z _ ?x => x | _ => NotConstant end.
  (* [ring]/[field] represent exponents as [N] (see [power_theory]); a literal
     [Z] exponent [Zpos p] is handed over as [Npos p], which [Z.of_N] maps back
     to [Zpos p] by computation. *)
  Ltac is_pow_constant t :=
    match t with
    | Z0 => constr:(N0)
    | Zpos ?p =>
      match InitialRing.isPcst p with
      | true => constr:(Npos p)
      | _ => constr:(NotConstant)
      end
    | _ => constr:(NotConstant)
    end.

  Section VariousModulo.
    Context {m:Z}.
    Local Open Scope Zmod_scope.

    Add Ring _theory : (Zmod.ring_theory m)
                         (morphism (ring_morph m),
                          constants [is_constant],
                          div (morph_div_theory m),
                          power_tac (power_theory m) [is_pow_constant]).

    Lemma mul_nonzero_l : forall a b : Zmod m, a*b <> 0 -> a <> 0.
    Proof using Type. intros a b Hnz Hz. rewrite Hz in Hnz; apply Hnz; ring. Qed.

    Lemma mul_nonzero_r : forall a b : Zmod m, a*b <> 0 -> b <> 0.
    Proof using Type. intros a b Hnz Hz. rewrite Hz in Hnz; apply Hnz; ring. Qed.
  End VariousModulo.

  Section Pow.
    Context {m:Z}.
    Add Ring _theory' : (Zmod.ring_theory m)
                          (morphism (ring_morph m),
                           constants [is_constant],
                           div (morph_div_theory m),
                           power_tac (power_theory m) [is_pow_constant]).
    Local Open Scope Zmod_scope.

    (* TODO: move this somewhere? *)
    Create HintDb nat2N discriminated.
    Hint Rewrite Nat2N.inj_iff
         (eq_refl _ : (0%N = N.of_nat 0))
         (eq_refl _ : (1%N = N.of_nat 1))
         (eq_refl _ : (2%N = N.of_nat 2))
         (eq_refl _ : (3%N = N.of_nat 3))
      : nat2N.
    Hint Rewrite <- Nat2N.inj_double Nat2N.inj_succ_double Nat2N.inj_succ
         Nat2N.inj_add Nat2N.inj_mul Nat2N.inj_sub Nat2N.inj_pred
         Nat2N.inj_div2 Nat2N.inj_max Nat2N.inj_min Nat2N.id
      : nat2N.

    Lemma pow_3_r (x:Zmod m) : x^3 = x*x*x.
    Proof using Type. ring. Qed.
  End Pow.
End Zmod.

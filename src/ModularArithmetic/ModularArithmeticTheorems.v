Require Import Coq.omega.Omega.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.Pre.

Require Import Coq.ZArith.BinInt Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Export Coq.setoid_ring.Ring_theory Coq.setoid_ring.Ring_tac.

Require Import Crypto.Algebra Crypto.Algebra.Ring Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable Crypto.Util.ZUtil.
Require Export Crypto.Util.FixCoqMistakes.

Module F.
  Ltac unwrap_F :=
    intros;
    repeat match goal with [ x : F _ |- _ ] => destruct x end;
    lazy iota beta delta [F.add F.sub F.mul F.opp F.to_Z F.of_Z proj1_sig] in *;
    try apply eqsig_eq;
    pull_Zmod.
  
  (* FIXME: remove the pose proof once [monoid] no longer contains decidable equality *)
  Global Instance eq_dec {m} : DecidableRel (@eq (F m)). pose proof dec_eq_Z. exact _. Defined.
  
  Global Instance commutative_ring_modulo m
    : @Algebra.commutative_ring (F m) Logic.eq 0%F 1%F F.opp F.add F.sub F.mul.
  Proof.
    repeat (split || intro); unwrap_F;
      autorewrite with zsimplify; solve [ exact _ | auto with zarith | congruence].
  Qed.

  Lemma pow_spec {m} a : F.pow a 0%N = 1%F :> F m /\ forall x, F.pow a (1 + x)%N = F.mul a (F.pow a x).
  Proof. change (@F.pow m) with (proj1_sig (@F.pow_with_spec m)); destruct (@F.pow_with_spec m); eauto. Qed.

  Section FandZ.
    Context {m:Z}.
    Local Open Scope F_scope.

    Theorem eq_to_Z_iff (x y : F m) : x = y <-> F.to_Z x = F.to_Z y.
    Proof. destruct x, y; intuition; simpl in *; try apply (eqsig_eq _ _); congruence. Qed.

    Lemma eq_of_Z_iff : forall x y : Z, x mod m = y mod m <-> F.of_Z m x = F.of_Z m y.
    Proof. split; unwrap_F; congruence. Qed.

    
    Lemma to_Z_of_Z : forall z, F.to_Z (F.of_Z m z) = z mod m.
    Proof. unwrap_F; trivial. Qed.

    Lemma of_Z_to_Z x : F.of_Z m (F.to_Z x) = x :> F m.
    Proof. unwrap_F; congruence. Qed.

    
    Lemma of_Z_mod : forall x, F.of_Z m x = F.of_Z m (x mod m).
    Proof. unwrap_F; trivial. Qed.

    Lemma mod_to_Z : forall (x:F m),  F.to_Z x mod m = F.to_Z x.
    Proof. unwrap_F. congruence. Qed.

    Lemma to_Z_0 : F.to_Z (0:F m) = 0%Z.
    Proof. unwrap_F. apply Zmod_0_l. Qed.

    Lemma of_Z_small_nonzero z : (0 < z < m)%Z -> F.of_Z m z <> 0.
    Proof. intros Hrange Hnz. inversion Hnz. rewrite Zmod_small, Zmod_0_l in *; omega. Qed.

    Lemma to_Z_nonzero (x:F m) : x <> 0 -> F.to_Z x <> 0%Z.
    Proof. intros Hnz Hz. rewrite <- Hz, of_Z_to_Z in Hnz; auto. Qed.

    Lemma to_Z_range (x : F m) : 0 < m -> 0 <= F.to_Z x < m.
    Proof. intros. rewrite <- mod_to_Z. apply Z.mod_pos_bound. trivial. Qed.

    Lemma to_Z_nonzero_range (x : F m) : (x <> 0) -> 0 < m -> (1 <= F.to_Z x < m)%Z.
    Proof.
      unfold not; intros Hnz Hlt.
      rewrite eq_to_Z_iff, to_Z_0 in Hnz; pose proof (to_Z_range x Hlt).
      omega.
    Qed.

    Lemma of_Z_add : forall (x y : Z),
        F.of_Z m (x + y) = F.of_Z m x + F.of_Z m y.
    Proof. unwrap_F; trivial. Qed.

    Lemma to_Z_add : forall x y : F m,
        F.to_Z (x + y) = ((F.to_Z x + F.to_Z y) mod m)%Z.
    Proof. unwrap_F; trivial. Qed.

    Lemma of_Z_mul x y : F.of_Z m (x * y) = F.of_Z _ x * F.of_Z _ y :> F m.
    Proof. unwrap_F. trivial. Qed.

    Lemma to_Z_mul : forall x y : F m,
        F.to_Z (x * y) = ((F.to_Z x * F.to_Z y) mod m)%Z.
    Proof. unwrap_F; trivial. Qed.
    
    Lemma of_Z_sub x y : F.of_Z _ (x - y) = F.of_Z _ x - F.of_Z _ y :> F m.
    Proof. unwrap_F. trivial. Qed.

    Lemma to_Z_opp : forall x : F m, F.to_Z (F.opp x) = (- F.to_Z x) mod m.
    Proof. unwrap_F; trivial. Qed.

    Lemma of_Z_pow x n : F.of_Z _ x ^ n = F.of_Z _ (x ^ (Z.of_N n) mod m) :> F m.
    Proof.
      intros.
      induction n using N.peano_ind;
        destruct (pow_spec (F.of_Z m x)) as [pow_0 pow_succ] . {
        rewrite pow_0.
        unwrap_F; trivial.
      } {
        rewrite N2Z.inj_succ.
        rewrite Z.pow_succ_r by apply N2Z.is_nonneg.
        rewrite <- N.add_1_l.
        rewrite pow_succ.
        rewrite IHn.
        unwrap_F; trivial.
      }
    Qed.

    Lemma to_Z_pow : forall (x : F m) n,
        F.to_Z (x ^ n)%F = (F.to_Z x ^ Z.of_N n mod m)%Z.
    Proof.
      intros.
      symmetry.
      induction n using N.peano_ind;
        destruct (pow_spec x) as [pow_0 pow_succ] . {
        rewrite pow_0, Z.pow_0_r; auto.
      } {
        rewrite N2Z.inj_succ.
        rewrite Z.pow_succ_r by apply N2Z.is_nonneg.
        rewrite <- N.add_1_l.
        rewrite pow_succ.
        rewrite <- Zmult_mod_idemp_r.
        rewrite IHn.
        apply to_Z_mul.
      }
    Qed.

    Lemma square_iff (x:F m) :
      (exists y : F m, y * y = x) <-> (exists y : Z, y * y mod m = F.to_Z x)%Z.
    Proof.
      setoid_rewrite eq_to_Z_iff; setoid_rewrite to_Z_mul; split; intro H; destruct H as [x' H].
      - eauto.
      - exists (F.of_Z _ x'); rewrite !to_Z_of_Z; pull_Zmod; auto.
    Qed.
  End FandZ.

  Section FandNat.
    Import NPeano Nat.
    Local Infix "mod" := modulo : nat_scope.
    Local Open Scope nat_scope.

    Context {m} (m_pos: (0 < m)%Z).
    Let to_nat_m_nonzero : Z.to_nat m <> 0.
      rewrite Z2Nat.inj_lt in m_pos; omega.
    Qed.

    Lemma to_nat_of_nat (n:nat) : F.to_nat (F.of_nat m n) = (n mod (Z.to_nat m))%nat.
    Proof.
      unfold F.to_nat, F.of_nat.
      rewrite F.to_Z_of_Z.
      pose proof (mod_Zmod n (Z.to_nat m) to_nat_m_nonzero) as Hmod.
      rewrite Z2Nat.id in Hmod by omega.
      rewrite <- Hmod.
      rewrite <-Nat2Z.id by omega.
      reflexivity.
    Qed.

    Lemma of_nat_to_nat x : F.of_nat m (F.to_nat x) = x.
      unfold F.to_nat, F.of_nat.
      rewrite Z2Nat.id; [ eapply F.of_Z_to_Z | eapply F.to_Z_range; trivial].
    Qed.

    Lemma of_nat_mod (n:nat) : F.of_nat m (n mod (Z.to_nat m)) = F.of_nat m n.
    Proof.
      unfold F.of_nat.
      replace (Z.of_nat (n mod Z.to_nat m)) with(Z.of_nat n mod Z.of_nat (Z.to_nat m))%Z
        by (symmetry; eapply (mod_Zmod n (Z.to_nat m) to_nat_m_nonzero)).
      rewrite Z2Nat.id by omega.
      rewrite <-F.of_Z_mod; reflexivity.
    Qed.

    Lemma to_nat_mod (x:F m) (Hm:(0 < m)%Z) : F.to_nat x mod (Z.to_nat m) = F.to_nat x.
      unfold F.to_nat.
      rewrite <-F.mod_to_Z at 2.
      apply Z.mod_to_nat; [assumption|].
      apply F.to_Z_range; assumption.
    Qed.

    Lemma of_nat_add x y :
      F.of_nat m (x + y) = (F.of_nat m x + F.of_nat m y)%F.
    Proof. unfold F.of_nat; rewrite Nat2Z.inj_add, F.of_Z_add; reflexivity. Qed.

    Lemma of_nat_mul x y :
      F.of_nat m (x * y) = (F.of_nat m x * F.of_nat m y)%F.
    Proof. unfold F.of_nat; rewrite Nat2Z.inj_mul, F.of_Z_mul; reflexivity. Qed.
  End FandNat.

  Section RingTacticGadgets.
    Context (m:Z).

    Definition ring_theory : ring_theory 0%F 1%F (@F.add m) (@F.mul m) (@F.sub m) (@F.opp m) eq
      := Algebra.Ring.ring_theory_for_stdlib_tactic.

    Lemma pow_pow_N (x : F m) : forall (n : N), (x ^ id n)%F = pow_N 1%F F.mul x n.
    Proof.
      destruct (pow_spec x) as [HO HS]; intros.
      destruct n; auto; unfold id.
      rewrite Pre.N_pos_1plus at 1.
      rewrite HS.
      simpl.
      induction p using Pos.peano_ind.
      - simpl. rewrite HO. apply Algebra.right_identity.
      - rewrite (@pow_pos_succ (F m) (@F.mul m) eq _ _ associative x).
        rewrite <-IHp, Pos.pred_N_succ, Pre.N_pos_1plus, HS.
        trivial.
    Qed.

    Lemma power_theory : power_theory 1%F (@F.mul m) eq id (@F.pow m).
    Proof. split; apply pow_pow_N. Qed.

    (***** Division Theory *****)
    Definition quotrem(a b: F m): F m * F m :=
      let '(q, r) := (Z.quotrem (F.to_Z a) (F.to_Z b)) in (F.of_Z _ q , F.of_Z _ r).
    Lemma div_theory : div_theory eq (@F.add m) (@F.mul m) (@id _) quotrem.
    Proof.
      constructor; intros; unfold quotrem, id.

      replace (Z.quotrem (F.to_Z a) (F.to_Z b)) with (Z.quot (F.to_Z a) (F.to_Z b), Z.rem (F.to_Z a) (F.to_Z b)) by
          try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).

      unwrap_F; rewrite <-Z.quot_rem'; trivial.
    Qed.

    (* Define a "ring morphism" between GF and Z, i.e. an equivalence
     * between 'inject (ZFunction (X))' and 'GFFunction (inject (X))'.
     *
     * Doing this allows the [ring] tactic to do coefficient
     * manipulations in Z rather than F, because we know it's equivalent
     * to inject the result afterward. *)
    Lemma ring_morph: ring_morph 0%F 1%F F.add F.mul F.sub F.opp   eq
                                 0%Z 1%Z Z.add Z.mul Z.sub Z.opp Z.eqb  (F.of_Z m).
    Proof. split; intros; unwrap_F; solve [ auto | rewrite (proj1 (Z.eqb_eq x y)); trivial]. Qed.

    (* Redefine our division theory under the ring morphism *)
    Lemma morph_div_theory:
      Ring_theory.div_theory eq Zplus Zmult (F.of_Z m) Z.quotrem.
    Proof.
      split; intros.
      replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b);
        try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).
      unwrap_F; rewrite <- (Z.quot_rem' a b); trivial.
    Qed.

  End RingTacticGadgets.

  Ltac is_constant t := match t with F.of_Z _ ?x => x | _ => NotConstant end.
  Ltac is_pow_constant t := Ncst t.

  Module Type Modulus. Parameter modulus : Z. End Modulus.

  (* Example of how to instantiate the ring tactic *)
  Module RingModulo (Export M : Modulus).
    Add Ring _theory : (ring_theory modulus)
                         (morphism (ring_morph modulus),
                          constants [is_constant],
                          div (morph_div_theory modulus),
                          power_tac (power_theory modulus) [is_pow_constant]).

    Example ring_modulo_example : forall x y z, x*z + z*y = z*(x+y).
    Proof. intros. ring. Qed.
  End RingModulo.

  Section VariousModulo.
    Context {m:Z}.
    Local Open Scope F_scope.

    Add Ring _theory : (ring_theory m)
                         (morphism (ring_morph m),
                          constants [is_constant],
                          div (morph_div_theory m),
                          power_tac (power_theory m) [is_pow_constant]).

    Lemma mul_nonzero_l : forall a b : F m, a*b <> 0 -> a <> 0.
    Proof. intros a b Hnz Hz. rewrite Hz in Hnz; apply Hnz; ring. Qed.

    Lemma mul_nonzero_r : forall a b : F m, a*b <> 0 -> b <> 0.
    Proof. intros a b Hnz Hz. rewrite Hz in Hnz; apply Hnz; ring. Qed.
  End VariousModulo.

  Section Pow.
    Context {m:Z}.
    Add Ring _theory' : (ring_theory m)
                          (morphism (ring_morph m),
                           constants [is_constant],
                           div (morph_div_theory m),
                           power_tac (power_theory m) [is_pow_constant]).
    Local Open Scope F_scope.

    Import Algebra.ScalarMult.
    Global Instance pow_is_scalarmult
      : is_scalarmult (G:=F m) (eq:=eq) (add:=F.mul) (zero:=1%F) (mul := fun n x => x ^ (N.of_nat n)).
    Proof.
      split; intros; rewrite ?Nat2N.inj_succ, <-?N.add_1_l;
        match goal with
        | [x:F m |- _ ] => solve [destruct (@pow_spec m P); auto]
        | |- Proper _ _ => solve_proper
        end.
    Qed.

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

    Ltac pow_to_scalarmult_ref :=
      repeat (autorewrite with nat2N;
              match goal with
              | |- context [ (_^?n)%F ] =>
                rewrite <-(N2Nat.id n); generalize (N.to_nat n); clear n;
                let m := fresh n in intro m
              | |- context [ (_^N.of_nat ?n)%F ] =>
                let rw := constr:(scalarmult_ext(zero:=F.of_Z m 1) n) in
                setoid_rewrite rw (* rewriting moduloa reduction *)
              end).

    Lemma pow_0_r (x:F m) : x^0 = 1.
    Proof. pow_to_scalarmult_ref. apply scalarmult_0_l. Qed.

    Lemma pow_add_r (x:F m) (a b:N) : x^(a+b) = x^a * x^b.
    Proof. pow_to_scalarmult_ref; apply scalarmult_add_l. Qed.

    Lemma pow_0_l (n:N) : n <> 0%N -> 0^n = 0 :> F m.
    Proof. pow_to_scalarmult_ref; destruct n; simpl; intros; [congruence|ring]. Qed.

    Lemma pow_pow_l (x:F m) (a b:N) : (x^a)^b = x^(a*b).
    Proof. pow_to_scalarmult_ref. apply scalarmult_assoc. Qed.

    Lemma pow_1_r (x:F m) : x^1 = x.
    Proof. pow_to_scalarmult_ref; simpl; ring. Qed.

    Lemma pow_2_r (x:F m) : x^2 = x*x.
    Proof. pow_to_scalarmult_ref; simpl; ring. Qed.

    Lemma pow_3_r (x:F m) : x^3 = x*x*x.
    Proof. pow_to_scalarmult_ref; simpl; ring. Qed.
  End Pow.
End F.

Require Import Coq.omega.Omega.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.Pre.

Require Import Coq.ZArith.BinInt Coq.ZArith.Zdiv Coq.ZArith.Znumtheory Coq.NArith.NArith. (* import Zdiv before Znumtheory *)
Require Import Coq.Classes.Morphisms Coq.Setoids.Setoid.
Require Export Coq.setoid_ring.Ring_theory Coq.setoid_ring.Ring_tac.

Require Import Crypto.Algebra Crypto.Util.Decidable.
Require Export Crypto.Util.FixCoqMistakes.

(* Fails iff the input term does some arithmetic with mod'd values. *)
Ltac notFancy E :=
  match E with
  | - (_ mod _) => idtac
  | context[_ mod _] => fail 1
  | _ => idtac
  end.

(* Remove redundant [mod] operations from the conclusion. *)
Ltac demod :=
  repeat match goal with
         | [ |- context[(?x mod _ + _) mod _] ] =>
           notFancy x; rewrite (Zplus_mod_idemp_l x)
         | [ |- context[(_ + ?y mod _) mod _] ] =>
           notFancy y; rewrite (Zplus_mod_idemp_r y)
         | [ |- context[(?x mod _ - _) mod _] ] =>
           notFancy x; rewrite (Zminus_mod_idemp_l x)
         | [ |- context[(_ - ?y mod _) mod _] ] =>
           notFancy y; rewrite (Zminus_mod_idemp_r _ y)
         | [ |- context[(?x mod _ * _) mod _] ] =>
           notFancy x; rewrite (Zmult_mod_idemp_l x)
         | [ |- context[(_ * (?y mod _)) mod _] ] =>
           notFancy y; rewrite (Zmult_mod_idemp_r y)
         | [ |- context[(?x mod _) mod _] ] =>
           notFancy x; rewrite (Zmod_mod x)
         end.

Ltac unwrap_F :=
  intros;
  repeat match goal with [ x : F _ |- _ ] => destruct x end;
  lazy iota beta delta [add sub mul opp FieldToZ ZToField proj1_sig] in *;
  try apply eqsig_eq;
  demod.

(* FIXME: remove the pose proof once [monoid] no longer contains decidable equality *)
Global Instance eq_dec {m} : DecidableRel (@eq (F m)). pose proof dec_eq_Z. exact _. Defined.

Global Instance commutative_ring_modulo m
  : @Algebra.commutative_ring (F m) Logic.eq 0%F 1%F opp add sub mul.
Proof.
  repeat (split || intro); unwrap_F;
    autorewrite with zsimplify; solve [ exact _ | auto with zarith | congruence].
Qed.


Module Zmod.
  Lemma pow_spec {m} a : pow a 0%N = 1%F :> F m /\ forall x, pow a (1 + x)%N = mul a (pow a x).
  Proof. change (@pow m) with (proj1_sig (@pow_with_spec m)); destruct (@pow_with_spec m); eauto. Qed.

  Section FandZ.
    Context {m:Z}.
    Local Open Scope F_scope.

    Theorem eq_FieldToZ_iff (x y : F m) : x = y <-> FieldToZ x = FieldToZ y.
    Proof. destruct x, y; intuition; simpl in *; try apply (eqsig_eq _ _); congruence. Qed.

    Lemma eq_ZToField_iff : forall x y : Z, x mod m = y mod m <-> ZToField m x = ZToField m y.
    Proof. split; unwrap_F; congruence. Qed.

    
    Lemma FieldToZ_ZToField : forall z, FieldToZ (@ZToField m z) = z mod m.
    Proof. unwrap_F; trivial. Qed.

    Lemma ZToField_FieldToZ x : ZToField m (FieldToZ x) = x :> F m.
    Proof. unwrap_F; congruence. Qed.

    
    Lemma ZToField_mod : forall x, ZToField m x = ZToField m (x mod m).
    Proof. unwrap_F; trivial. Qed.

    Lemma mod_FieldToZ : forall (x:F m),  FieldToZ x mod m = FieldToZ x.
    Proof. unwrap_F. congruence. Qed.

    Lemma FieldToZ_0 : FieldToZ (0:F m) = 0%Z.
    Proof. unwrap_F. apply Zmod_0_l. Qed.

    Lemma ZToField_small_nonzero z : (0 < z < m)%Z -> ZToField m z <> 0.
    Proof. intros Hrange Hnz. inversion Hnz. rewrite Zmod_small, Zmod_0_l in *; omega. Qed.

    Lemma FieldToZ_nonzero (x:F m) : x <> 0 -> FieldToZ x <> 0%Z.
    Proof. intros Hnz Hz. rewrite <- Hz, ZToField_FieldToZ in Hnz; auto. Qed.

    Lemma FieldToZ_range (x : F m) : 0 < m -> 0 <= x < m.
    Proof. intros. rewrite <- mod_FieldToZ. apply Z.mod_pos_bound. trivial. Qed.

    Lemma FieldToZ_nonzero_range (x : F m) : (x <> 0) -> 0 < m -> (1 <= x < m)%Z.
    Proof.
      unfold not; intros Hnz Hlt.
      rewrite eq_FieldToZ_iff, FieldToZ_0 in Hnz; pose proof (FieldToZ_range x Hlt).
      omega.
    Qed.

    Lemma ZToField_add : forall (x y : Z),
        ZToField m (x + y) = ZToField m x + ZToField m y.
    Proof. unwrap_F; trivial. Qed.

    Lemma FieldToZ_add : forall x y : F m,
        FieldToZ (x + y) = ((FieldToZ x + FieldToZ y) mod m)%Z.
    Proof. unwrap_F; trivial. Qed.

    Lemma ZToField_mul x y : ZToField m (x * y) = ZToField _ x * ZToField _ y :> F m.
    Proof. unwrap_F. trivial. Qed.

    Lemma FieldToZ_mul : forall x y : F m,
        FieldToZ (x * y) = ((FieldToZ x * FieldToZ y) mod m)%Z.
    Proof. unwrap_F; trivial. Qed.
    
    Lemma ZToField_sub x y : ZToField _ (x - y) = ZToField _ x - ZToField _ y :> F m.
    Proof. unwrap_F. trivial. Qed.

    Lemma FieldToZ_opp : forall x, FieldToZ (@opp m x) = -x mod m.
    Proof. unwrap_F; trivial. Qed.

    Lemma ZToField_pow x n : ZToField _ x ^ n = ZToField _ (x ^ (Z.of_N n) mod m) :> F m.
    Proof.
      intros.
      induction n using N.peano_ind;
        destruct (pow_spec (@ZToField m x)) as [pow_0 pow_succ] . {
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

    Lemma FieldToZ_pow : forall (x : F m) n,
        FieldToZ (x ^ n)%F = (FieldToZ x ^ Z.of_N n mod m)%Z.
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
        apply FieldToZ_mul.
      }
    Qed.

    Lemma square_iff (x:F m) :
      (exists y : F m, y * y = x) <-> (exists y : Z, y * y mod m = x)%Z.
    Proof.
      setoid_rewrite eq_FieldToZ_iff; setoid_rewrite FieldToZ_mul; split; intro H; destruct H as [x' H].
      - eauto.
      - exists (ZToField _ x'); rewrite !FieldToZ_ZToField; demod; auto.
    Qed.

    (* TODO: move to ZUtil *)
    Lemma sub_intersperse_modulus : forall x y, ((x - y) mod m = (x + (m - y)) mod m)%Z.
    Proof.
      intros.
      replace (x + (m - y))%Z with (m+(x-y))%Z by omega.
      rewrite Zplus_mod.
      rewrite Z_mod_same_full; simpl Z.add.
      rewrite Zmod_mod.
      reflexivity.
    Qed.
  End FandZ.

  Section RingTacticGadgets.
    Context (m:Z).

    Definition ring_theory : ring_theory 0%F 1%F (@add m) (@mul m) (@sub m) (@opp m) eq
      := Algebra.Ring.ring_theory_for_stdlib_tactic.

    Lemma pow_pow_N (x : F m) : forall (n : N), (x ^ id n)%F = pow_N 1%F mul x n.
    Proof.
      destruct (pow_spec x) as [HO HS]; intros.
      destruct n; auto; unfold id.
      rewrite Pre.N_pos_1plus at 1.
      rewrite HS.
      simpl.
      induction p using Pos.peano_ind.
      - simpl. rewrite HO. apply Algebra.right_identity.
      - rewrite (@pow_pos_succ (F m) (@mul m) eq _ _ associative x).
        rewrite <-IHp, Pos.pred_N_succ, Pre.N_pos_1plus, HS.
        trivial.
    Qed.

    Lemma power_theory : power_theory 1%F (@mul m) eq id (@pow m).
    Proof. split; apply pow_pow_N. Qed.

    (***** Division Theory *****)
    Definition quotrem(a b: F m): F m * F m :=
      let '(q, r) := (Z.quotrem a b) in (ZToField _ q , ZToField _ r).
    Lemma Fdiv_theory : div_theory eq (@add m) (@mul m) (@id _) quotrem.
    Proof.
      constructor; intros; unfold quotrem, id.

      replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b) by
          try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).

      unwrap_F; rewrite <-Z.quot_rem'; trivial.
    Qed.

    Lemma Z_mod_opp_equiv : forall x y m,  x  mod m = (-y) mod m ->
                                           (-x) mod m =   y  mod m.
    Proof.
      intros.
      rewrite <-Z.sub_0_l.
      rewrite Zminus_mod. rewrite H.
      rewrite ?Zminus_mod_idemp_l, ?Zminus_mod_idemp_r; f_equal.
      destruct y; auto.
    Qed.

    Lemma Z_opp_opp : forall x : Z, (-(-x)) = x.
      destruct x; auto.
    Qed.

    Lemma Z_mod_opp : forall x m, (- x) mod m = (- (x mod m)) mod m.
      intros.
      apply Z_mod_opp_equiv.
      rewrite Z_opp_opp.
      demod; auto.
    Qed.

    (* Define a "ring morphism" between GF and Z, i.e. an equivalence
     * between 'inject (ZFunction (X))' and 'GFFunction (inject (X))'.
     *
     * Doing this allows the [ring] tactic to do coefficient
     * manipulations in Z rather than F, because we know it's equivalent
     * to inject the result afterward. *)
    Lemma ring_morph: ring_morph 0%F 1%F (@add m) (@mul m) (@sub m) (@opp m) eq
                                 0%Z 1%Z Z.add    Z.mul    Z.sub    Z.opp  Z.eqb  (@ZToField m).
    Proof. split; intros; unwrap_F; solve [ auto | rewrite (proj1 (Z.eqb_eq x y)); trivial]. Qed.

    (* Redefine our division theory under the ring morphism *)
    Lemma morph_div_theory:
      div_theory eq Zplus Zmult (@ZToField m) Z.quotrem.
    Proof.
      split; intros.
      replace (Z.quotrem a b) with (Z.quot a b, Z.rem a b);
        try (unfold Z.quot, Z.rem; rewrite <- surjective_pairing; trivial).
      unwrap_F; rewrite <- (Z.quot_rem' a b); trivial.
    Qed.

  End RingTacticGadgets.

  Ltac is_constant t := match t with @ZToField _ ?x => x | _ => NotConstant end.
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
      : is_scalarmult (G:=F m) (eq:=eq) (add:=mul) (zero:=1%F) (mul := fun n x => x ^ (N.of_nat n)).
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
                let rw := constr:(scalarmult_ext(zero:=ZToField m 1) n) in
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
End Zmod.

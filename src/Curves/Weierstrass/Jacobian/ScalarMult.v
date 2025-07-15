From Coq Require Import Morphisms.
Require Import Crypto.Spec.WeierstrassCurve Crypto.Algebra.ScalarMult.
Require Import Crypto.Curves.Weierstrass.Jacobian.Jacobian.
Require Import Crypto.Curves.Weierstrass.Affine Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.Jacobian.CoZ.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Notations Crypto.Util.LetIn.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.Sigma.
Require Import Crypto.Util.FsatzAutoLemmas.
Require Import Crypto.Util.Loops.
Require Import Crypto.Util.ZUtil.Notations.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Shift.
Require Import Crypto.Util.ZUtil.Peano.
Require Import Crypto.Util.Tuple.
From Coq Require Import ZArith.
From Coq Require Import Lia.

Module Z.
(* Note: ideally we would contribute this to Coq *)
Lemma mod_pow2_succ_r a n (Hi : Z.le 0 n) : (a mod 2 ^ Z.succ n = a mod 2 ^ n + Z.b2z (Z.testbit a n) * 2 ^ n)%Z.
Proof.
  clear -Hi.
  rewrite Z_div_mod_eq_full with (a:=(a mod _)%Z) (b:=(2^n)%Z).
  rewrite <-(Z.mod_small ((a mod 2 ^ Z.succ n / 2 ^ n)) 2); cycle 1.
  { rewrite Z.pow_succ_r by lia; Z.div_mod_to_equations; nia. }
  rewrite <-Z.mod_pow2_bits_low with (n:=Z.succ n) by lia.
  rewrite <-Znumtheory.Zmod_div_mod; cycle 1.
  { lia. } { lia. } { exists 2%Z. rewrite <-Z.pow_succ_r; f_equal; lia. }
  rewrite Z.testbit_spec'; lia.
Qed.
End Z.

Module ScalarMult.
  Section JoyeDoubleAddDecomposition.
    (* Joye's double-add ladder for computing [n]P basically tracks the
       values of two sequences [SS i]P and [TT i]P.
       This section proves some properties on the sequences SS and TT.
     *)
    Variables n : Z.
    Local Coercion Z.of_nat : nat >-> Z.

    Definition SS (i : nat) : Z := n mod 2 ^ i.
    Definition TT (i : nat) : Z := 2^i - SS i.

    Lemma SS_plus_TT k : (SS k + TT k = 2^(Z.of_nat k))%Z.
    Proof. cbv [SS TT]; lia. Qed.

    Lemma SS_succ i : SS (S i) = if (Z.testbit n (Z.of_nat i)) then (2 * SS i + TT i)%Z else SS i.
    Proof.
      cbv [TT SS].
      pose proof Z.mod_pow2_succ_r n i; case Z.testbit in *; cbv [Z.b2z] in *; lia.
    Qed.

    Lemma TT_succ i : TT (S i) = if (Z.testbit n (Z.of_nat i)) then TT i else (2 * TT i + SS i)%Z.
    Proof.
      cbv [TT SS].
      rewrite Nat2Z.inj_succ by lia.
      pose proof Z.mod_pow2_succ_r n i; case Z.testbit in *; cbv [Z.b2z] in *; rewrite ?Z.pow_succ_r in *; lia.
    Qed.

    Lemma SS_monotone1 (k : nat) : (SS 1 <= SS (S k))%Z.
    Proof.
      cbv [SS].
      rewrite Z.pow_1_r, Nat2Z.inj_succ, Z.pow_succ_r, Znumtheory.Zmod_div_mod with (n:=2) (m:=(2*2^k)%Z)
        by (try exists (2^k)%Z; lia).
      apply Z.mod_bound_pos_le; Z.div_mod_to_equations; lia.
    Qed.

    Lemma TT_monotone1 (k : nat) : (TT 1 <= TT (S k))%Z.
    Proof.
      cbv [TT SS]; repeat rewrite Nat2Z.inj_succ. set (z := Z.succ k).
      enough (n mod 2 ^ z < 2 ^ z + (n mod 2 ^ Z.succ 0 - 1))%Z by lia; rewrite Z.pow_1_r.
      enough (n mod 2 = 0 -> n mod 2 ^ z <> Z.pred (2^z))%Z by try (Z.div_mod_to_equations; nia); intros ? X.
      apply (f_equal (fun x => Z.testbit x 0)) in X.
      rewrite <-Z.ones_equiv, Z.ones_spec_low, Z.mod_pow2_bits_low, Z.bit0_eqb in X; lia.
    Qed.

    Lemma SSn scalarbitsz (Hn : (0 <= n < 2^scalarbitsz)%Z) (Hscalarbitsz : (0 < scalarbitsz)%Z) :
      SS (Z.to_nat scalarbitsz) = n :> Z.
    Proof.
      cbv [SS]. rewrite Z2Nat.id by lia.
      apply Z.mod_small; trivial.
    Qed.
  End JoyeDoubleAddDecomposition.

  Section JoyeLadder.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero. Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x^2*x).
    Local Notation "2" := (1+1). Local Notation "4" := (2+1+1).
    Local Notation "8" := (4+4). Local Notation "27" := (4*4 + 4+4 +1+1+1).
    Local Notation "'∞'" := (@W.zero F Feq Fadd Fmul a b).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).
    Context {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12%positive}
            {discriminant_nonzero:id(4*a*a*a + 27*b*b <> 0)}.
    Local Notation Wopp := (@W.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 a b).
    Local Notation Wzero := (@W.zero F Feq Fadd Fmul a b).
    Local Notation Weq := (@W.eq F Feq Fadd Fmul a b).
    Local Notation Wgroup := (@W.commutative_group F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec char_ge_3 char_ge_12 discriminant_nonzero).
    Local Notation point := (@Jacobian.point F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation eq := (@Jacobian.eq F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation x_of := (@Jacobian.x_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation y_of := (@Jacobian.y_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation z_of := (@Jacobian.z_of F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation add := (@Jacobian.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec).
    Local Notation opp := (@Jacobian.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation co_z := (@Jacobian.co_z F Feq Fzero Fadd Fmul a b Feq_dec).
    Local Notation make_co_z := (@Jacobian.make_co_z F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation of_affine := (@Jacobian.of_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation to_affine := (@Jacobian.to_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zero := (of_affine Wzero).
    Local Notation dblu := (@Jacobian.dblu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation tplu := (@Jacobian.tplu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zaddu := (@Jacobian.zaddu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zdau := (@Jacobian.zdau F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation is_point := (@Jacobian.is_point F Feq Fzero Fadd Fmul a b Feq_dec).

    Ltac prept_step_opt :=
      match goal with
      | [ H : ?T |- ?T ] => exact H
      | [ |- ?x = ?x ] => reflexivity
      | [ H : ?T, H' : ~?T |- _ ] => solve [ exfalso; apply H', H ]
      end.

    Ltac prept_step :=
      match goal with
      | _ => progress prept_step_opt
      | _ => progress intros
      (*| _ => progress specialize_by_assumption*)
      (*| _ => progress specialize_by trivial*)
      | _ => progress cbv [proj1_sig fst snd] in *
      | _ => progress autounfold with points_as_coordinates in *
      | _ => progress destruct_head'_True
      | _ => progress destruct_head'_unit
      | _ => progress destruct_head'_prod
      | _ => progress destruct_head'_sig
      | _ => progress destruct_head'_and
      | _ => progress destruct_head'_sum
      | _ => progress destruct_head'_bool
      | _ => progress destruct_head'_or
      | H: context[@dec ?P ?pf] |- _ => destruct (@dec P pf)
      | |- context[@dec ?P ?pf]      => destruct (@dec P pf)
      | |- ?P => lazymatch type of P with Prop => split end
      end.
    Ltac prept := repeat prept_step.
    Ltac t := prept; trivial; try contradiction; fsatz.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold Proper respectful Reflexive Symmetric Transitive : points_as_coordinates.
    Hint Unfold Jacobian.point Jacobian.eq W.eq W.point W.coordinates proj1_sig fst snd : points_as_coordinates.

    Hint Unfold Jacobian.x_of Jacobian.y_of Jacobian.z_of Jacobian.opp Jacobian.co_z : points_as_coordinates.

    Lemma co_z_comm (A B : point) (H : co_z A B) :
      co_z B A.
    Proof. t. Qed.

    Definition co_z_points : Type := { '(A, B) | co_z A B }.

    Program Definition make_co_z_points (P Q : point) (HQaff : z_of Q = 1) : co_z_points :=
      make_co_z P Q HQaff.
    Next Obligation. Proof. t. Qed.

    Program Definition cswap_co_z_points (b : bool) (AB : co_z_points) : co_z_points :=
      exist _
        (let '(A, B) := proj1_sig AB
        in if b then (B, A) else (A, B))
        _.
    Next Obligation. Proof. generalize (proj2_sig AB); rewrite (surjective_pairing (proj1_sig _)); destruct b0; [apply co_z_comm|auto]. Qed.

    Program Definition zdau_co_z_points (AB : co_z_points) : co_z_points :=
      exist _ (let '(A, B) := proj1_sig AB in zdau A B _) _.
    Next Obligation. Proof. generalize (proj2_sig AB). rewrite <- Heq_anonymous. auto. Qed.
    Next Obligation. Proof. destruct AB as ((A & B) & HAB). simpl. t. Qed.

    Program Definition zaddu_co_z_points (AB : co_z_points) : co_z_points :=
      exist _ (let '(A, B) := proj1_sig AB in zaddu A B _) _.
    Next Obligation. Proof. generalize (proj2_sig AB); rewrite <- Heq_anonymous. auto. Qed.
    Next Obligation. Proof. destruct AB as ((A & B) & HAB). simpl. t. Qed.

    Program Definition tplu_co_z_points (P : point) (HPaff : z_of P = 1) : co_z_points :=
      tplu P _.
    Next Obligation. Proof. t. Qed.

    Lemma opp_of_affine (P : Wpoint) (HPnz : P <> ∞ :> Wpoint) :
      z_of (opp (of_affine P)) = 1.
    Proof. t. Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 14 Joye’s double-add algorithm with Co-Z addition formulæ *)
    (* This is an adapted version that consumes and returns points in jacobian
       coordinates, correctness assumes the scalar is odd (i.e., testbit 0 = true). *)
    Definition joye_ladder_inner (scalarbitsz : Z) (testbit : Z -> bool) (P : point)
      (HPaff : z_of P = 1) : point :=
      (* Initialization *)
      let swap := testbit 1%Z in
      let R1R0 := tplu_co_z_points P HPaff in
      (* loop *)
      let '(R1R0, swap, _) :=
        (@while (co_z_points*bool*Z) (fun '(_, _, i) => (Z.ltb i scalarbitsz))
           (fun '(R1R0, swap, i) =>
              let b := testbit i in
              let swap := xorb swap b in
              let R1R0 := cswap_co_z_points swap R1R0 in
              let R1R0 := zdau_co_z_points R1R0 in
              let swap := b in
              let i := Z.succ i in
              (R1R0, swap, i))
           (Z.to_nat scalarbitsz - 2) (* bound on loop iterations *)
           (R1R0, swap, 2%Z)) in
      let R1R0 := cswap_co_z_points swap R1R0 in
      snd (proj1_sig R1R0).

    (* Wrapper around joye_ladder_inner for points in affine coordinates,
       it also readjusts the result if the scalar input is even. *)
    Program Definition joye_ladder (scalarbitsz : Z) (testbit : Z -> bool) (P : Wpoint)
      (HPnz : P <> ∞ :> Wpoint) : Wpoint :=
      to_affine (
      let P := of_affine P in
      let R0 := joye_ladder_inner scalarbitsz testbit P _ in
      let b := testbit 0%Z in
      let mP := opp P in
      (* Make sure R0 and -P are co-z *)
      let R0R1 := make_co_z_points R0 mP (opp_of_affine _ HPnz) in
      (* if b = 0 then R0 <- R0 - P and R1 <- R0 *)
      (* if b = 1 then R0 <- R0 and R1 <- R0 - P *)
      let R0 := fst (proj1_sig (cswap_co_z_points b (zaddu_co_z_points R0R1))) in
      R0).
    Next Obligation. Proof. t. Qed.

    Section Proofs.

      Local Notation scalarmult := (@scalarmult_ref Wpoint Wadd Wzero Wopp).
      Local Notation scalarmult':= (@scalarmult_ref point add zero opp).

      Local Instance Equivalence_Weq : Equivalence Weq.
      Proof. apply Wgroup.(Hierarchy.commutative_group_group).(Hierarchy.group_monoid).(Hierarchy.monoid_Equivalence). Qed.

      Lemma Pgroup :
        @Hierarchy.group point eq add zero opp.
      Proof.
        destruct (@Group.group_by_isomorphism _ _ _ _ _ point eq add zero opp of_affine to_affine Wgroup.(Hierarchy.commutative_group_group) ltac:(apply Jacobian.to_affine_of_affine)); auto.
        - intros; split; intros.
          + rewrite <- (Jacobian.of_affine_to_affine a0), <- (Jacobian.of_affine_to_affine b0).
            rewrite H. reflexivity.
          + apply Jacobian.Proper_to_affine; auto.
        - apply Jacobian.to_affine_add.
        - intros. destruct a0 as (((X & Y) & Z) & HP).
          unfold to_affine, Wopp, opp, Weq. simpl.
          t.
        - rewrite Jacobian.to_affine_of_affine. reflexivity.
      Qed.

      Lemma scalarmult_scalarmult' (n : Z) (P : Wpoint) :
        eq (of_affine (scalarmult n P)) (scalarmult' n (of_affine P)).
      Proof.
        eapply (@homomorphism_scalarmult Wpoint Weq Wadd Wzero Wopp Wgroup.(Hierarchy.commutative_group_group) point eq add zero opp Pgroup scalarmult (@scalarmult_ref_is_scalarmult Wpoint Weq Wadd Wzero Wopp Wgroup.(Hierarchy.commutative_group_group)) scalarmult' (@scalarmult_ref_is_scalarmult point eq add zero opp Pgroup) of_affine ltac:(econstructor; [eapply Jacobian.of_affine_add|eapply Jacobian.Proper_of_affine])).
      Qed.

      Context {scalarbitsz : Z}
              {Hscalarbitsz : (2 <= scalarbitsz)%Z}
              {ordP : Z} {HordPpos : (2 < ordP)%Z}
              {HordPodd : Z.odd ordP = true :> bool}.

      Section Inner.
        (* Proofs about joye_ladder_inner *)

        (* Bit 0 of the scalar input is irrelevant *)
        Lemma joye_ladder_inner_bit0_irr (bitsz : Z) (testbit0 testbit1 : Z -> bool)
          (P : point) (HPaff : z_of P = 1)
          (bit0_irr : forall i, (i >= 1)%Z -> testbit0 i = testbit1 i :> bool) :
          eq (joye_ladder_inner bitsz testbit0 P HPaff)
             (joye_ladder_inner bitsz testbit1 P HPaff).
        Proof.
          unfold joye_ladder_inner.
          rewrite (surjective_pairing (while _ _ _ (_, testbit0 _, _))).
          rewrite (surjective_pairing (while _ _ _ (_, testbit1 _, _))).
          rewrite (surjective_pairing (fst (while _ _ _ (_, testbit0 _, _)))).
          rewrite (surjective_pairing (fst (while _ _ _ (_, testbit1 _, _)))).
          rewrite bit0_irr by lia.
          match goal with
          | |- eq (snd (proj1_sig (cswap_co_z_points (snd (fst (while ?T0 ?B0 ?F0 ?I0))) _)))
                 (snd (proj1_sig (cswap_co_z_points (snd (fst (while ?T1 ?B1 ?F1 ?I1))) _))) =>
              set (test0 := T0);
              set (body0 := B0);
              set (fuel := F0);
              set (init0 := I0);
              set (body1 := B1)
          end.
          eelim (while.preservation test0 body0 test0 body1 (fun s1 s2 => (s1 = s2 :> (co_z_points * bool * Z)) /\ (2 <= snd s1)%Z)).
          { intros A B. rewrite A. reflexivity. }
          - intros s1 s2 (<- & _). reflexivity.
          - unfold test0. intros ((PQ1 & b1) & i1) ((PQ2 & b2) & i2) _.
            cbn [fst snd]. intros (Heq & Hi). inversion Heq; clear Heq.
            subst PQ1; subst b1; subst i1.
            unfold body0, body1. rewrite bit0_irr by lia.
            split; [reflexivity|simpl; lia].
          - repeat (split; try reflexivity).
        Qed.

        Context {n : Z} {Hnodd : n = Z.setbit n 0 :> Z}
          {Hn : (2 <= n < 2^scalarbitsz)%Z}
          {P : point} {HPaff : z_of P = 1}
          {HordP : forall l, (eq (scalarmult' l P) zero) <-> exists k, (l = k * ordP :> Z)%Z}.
        Local Notation testbitn := (Z.testbit n).
        Context {HSS : forall i, (2 <= i <= scalarbitsz)%Z -> not (eq (scalarmult' (SS n (Z.to_nat i)) P) zero)}
                {HTT : forall i, (2 <= i <= scalarbitsz)%Z -> not (eq (scalarmult' (TT n (Z.to_nat i)) P) zero)}.

        Lemma mult_two_power (k : Z) :
          (0 <= k)%Z ->
          not (eq (scalarmult' (2^k)%Z P) zero).
        Proof.
          eapply (Zlt_0_ind (fun x => ~ eq (scalarmult' (2 ^ x) P) zero)).
          intros x Hind Hxpos Heqz.
          destruct (proj1 (HordP (2^x)%Z) Heqz) as [l Hl].
          destruct (Z.eq_dec x 0); [subst x|].
          - simpl in Hl. clear -Hl HordPpos.
            generalize (Z.divide_1_r_nonneg ordP ltac:(lia) ltac:(exists l; lia)).
            lia.
          - assert (x = Z.succ (Z.pred x) :> Z) by lia.
            rewrite H in Hl. rewrite Z.pow_succ_r in Hl; [|lia].
            generalize (Znumtheory.prime_mult 2%Z Znumtheory.prime_2 l ordP ltac:(exists (2 ^ Z.pred x)%Z; lia)).
            intros [A|A]; destruct A as [m Hm]; [|replace ordP with (0 + 2 * m)%Z in HordPodd by lia; rewrite Z.odd_add_mul_2 in HordPodd; simpl in HordPodd; congruence].
            rewrite Hm in Hl.
            assert ((2 ^ Z.pred x)%Z = (m * ordP)%Z :> Z) by lia.
            apply (Hind (Z.pred x) ltac:(lia)).
            eapply HordP. exists m; assumption.
        Qed.

        Lemma mult_two (k : Z) :
          eq (scalarmult' (2 * k)%Z P) zero ->
          eq (scalarmult' k P) zero.
        Proof.
          intros Heqz. destruct (proj1 (HordP (2 * k)%Z) Heqz) as [l Hl].
          generalize (Znumtheory.prime_mult 2%Z Znumtheory.prime_2 l ordP ltac:(exists k; lia)).
          intros [A|A]; destruct A as [m Hm]; [|replace ordP with (0 + 2 * m)%Z in HordPodd by lia; rewrite Z.odd_add_mul_2 in HordPodd; simpl in HordPodd; congruence].
          rewrite Hm in Hl. assert (k = m * ordP :> Z)%Z as -> by lia.
          apply HordP; eauto.
        Qed.

        Lemma HSS_plus_TT (m : Z) (k : nat) :
          not (eq (scalarmult' (SS m k + TT m k)%Z P) zero).
        Proof. rewrite SS_plus_TT. apply mult_two_power. lia. Qed.

        Lemma SS1 : SS n 1 = 1%Z :> Z.
        Proof. cbv [SS]. rewrite Z.pow_1_r, <-Z.bit0_mod, Hnodd, Z.setbit_eqb; trivial; lia. Qed.

        Lemma TT1 : TT n 1 = 1%Z :> Z.
        Proof. cbv [TT]. rewrite SS1; trivial. Qed.

        Lemma SS2 : SS n 2 = (if Z.testbit n 1 then 3%Z else 1%Z) :> Z.
        Proof.
          cbv [SS]; rewrite Hnodd, <-Z.land_ones, Z.land_comm by lia.
          destruct n; cbn; trivial; repeat (destruct p; cbn; trivial).
        Qed.

        Lemma TT2 : TT n 2 = (if Z.testbit n 1 then 1%Z else 3%Z) :> Z.
        Proof. cbv [TT]. rewrite SS2. case Z.testbit; lia. Qed.

        Lemma SS_TT2 : (if testbitn 1 then SS n 2 else TT n 2) = 3%Z :> Z.
        Proof. rewrite SS2, TT2; try lia; case testbitn; trivial. Qed.

        Lemma HordP3 :
          not (eq (scalarmult' 3%Z P) zero).
        Proof.
          rewrite <- SS_TT2, <- (Nat2Z.id 2).
          case testbitn; [eapply HSS|eapply HTT]; lia.
        Qed.

        Hint Unfold fst snd proj1_sig : points_as_coordinates.
        Hint Unfold fieldwise fieldwise' : points_as_coordinates.

        Lemma eq_fieldwise (P1 P2 : point) :
          fieldwise (n:=3) Feq
            (proj1_sig P1) (proj1_sig P2) ->
          eq P1 P2.
        Proof. clear -field; intros; t. Qed.

        Lemma Pynz :
          y_of P <> 0.
        Proof.
          intro Hy. assert (HA : eq P (opp P)).
          - apply eq_fieldwise. destruct P as (((X & Y) & Z) & HP).
            simpl; cbv in HPaff, Hy; repeat split; fsatz.
          - apply (mult_two_power 1%Z ltac:(lia)).
            replace (2 ^ 1)%Z with (1 - -1)%Z by lia.
            rewrite (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            rewrite <- (scalarmult_1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in HA.
            rewrite HA.
            rewrite <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            rewrite <- (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            replace (- (1) - -1)%Z with 0%Z by lia. reflexivity.
        Qed.

        Lemma add_opp_zero (A : point) :
          eq (add A (opp A)) zero.
        Proof.
          generalize (Jacobian.add_opp_same_r(discriminant_nonzero:=discriminant_nonzero) A).
          destruct (add A (opp A)) as (((X & Y) & Z) & H).
          cbn. intros HP; destruct (dec (Z = 0)); t.
        Qed.

        Lemma scalarmult_difference (A : point) (n1 n2 : Z):
          eq (scalarmult' n1 A) (scalarmult' n2 A) ->
          eq (scalarmult' (n1 - n2)%Z A) zero.
        Proof.
          intros. rewrite (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))), H, <- (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))), Z.sub_diag.
          apply (scalarmult_0_l (is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
        Qed.

        Lemma dblu_scalarmult' (Q : point) (Hz1 : z_of Q = 1) (Hynz : y_of Q <> 0) :
          let '(M, N) := dblu Q Hz1 in
          eq M (scalarmult' 2 Q)
          /\ eq N (scalarmult' 1 Q).
        Proof.
          generalize (@Jacobian.dblu_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec char_ge_12 Q Hz1 Hynz).
          rewrite (surjective_pairing (dblu _ _)) at 1.
          intros (A & B & C). split.
          - rewrite <- A. replace 2%Z with (1 + 1)%Z by lia.
            rewrite (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            rewrite (scalarmult_1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            rewrite <- Jacobian.add_double; reflexivity.
          - rewrite (scalarmult_1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            symmetry. assumption.
        Qed.

        Lemma co_xz_implies (P1 P2 : point) (Hxeq : x_of P1 = x_of P2)
          (Hzeq : z_of P1 = z_of P2) :
          eq P1 P2 \/ eq P1 (opp P2).
        Proof.
          clear -Hxeq Hzeq. prept; [tauto|fsatz|fsatz|].
          assert (f4 = f1 \/ f4 = Fopp f1) by (destruct (dec (f4 = f1)); [left; assumption|right; fsatz]).
          destruct H; [left; repeat split; fsatz|right; repeat split; fsatz].
        Qed.

        Lemma tplu_scalarmult' {p q} (H : tplu P HPaff = (p, q) :> _) :
          eq p (scalarmult' 3 P) /\ eq q (scalarmult' 1 P) /\ co_z p q.
        Proof.
          intros; unfold tplu. generalize (dblu_scalarmult' P HPaff Pynz).
          inversion_prod; subst p q.
          rewrite (surjective_pairing (dblu _ _)) at 1.
          set (P1 := (snd (dblu P HPaff))).
          set (P2 := (fst (dblu P HPaff))). intros [A1 A2].
          destruct (dec (x_of P1 = x_of P2)) as [Hxe|Hxne].
          { destruct (co_xz_implies P1 P2 Hxe (CoZ.Jacobian.tplu_obligation_1 P HPaff)) as [A|A].
            - rewrite A1, A2 in A. elim (mult_two_power 1%Z ltac:(lia)).
              rewrite <- A. replace 1%Z with (2 - 1)%Z by lia.
              apply scalarmult_difference; symmetry; assumption.
            - rewrite A1, A2, <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in A.
              apply scalarmult_difference in A.
              elim HordP3. exact A. }
          generalize (Jacobian.zaddu_correct _ _ (CoZ.Jacobian.tplu_obligation_1 P HPaff) Hxne).
          rewrite (surjective_pairing (zaddu _ _ _)) at 1.
          intros (A & B & C); subst P1 P2.
          repeat try split; trivial.
          { rewrite <-A, A1, A2, (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 1 2); reflexivity. }
          { rewrite <-B. rewrite A2. reflexivity. }
        Qed.

        (* Since co-Z formulas are incomplete, we need to show that we won't hit the neutral point for ZDAU in the loop *)
        Lemma zaddu_SS_TT (i : Z) (B1 B2 Y1 Y2 R0 R1 : point) (HB12 : co_z B1 B2)
          (Hi : (2 <= i < scalarbitsz)%Z)
          (HBx : x_of B1 <> x_of B2)
          (HY : zaddu B1 B2 HB12 = (Y1, Y2) :> point * point)
          (HR0 : eq R0 (scalarmult' (SS n (Z.to_nat i)) P))
          (HR1 : eq R1 (scalarmult' (TT n (Z.to_nat i)) P))
          (HB1 : B1 = (if testbitn i then R0 else R1) :> point)
          (HB2 : B2 = (if testbitn i then R1 else R0) :> point) :
          x_of Y1 <> x_of Y2.
        Proof.
          intro XX. generalize (Jacobian.zaddu_correct B1 B2 HB12 HBx).
          rewrite HY. intros (W1 & W2 & W3).
          destruct (co_xz_implies _ _ XX W3) as [W|W]; rewrite W, <- W2, HB1, HB2 in W1.
          - destruct (testbitn i);
            rewrite HR1, HR0, <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in W1;
            apply scalarmult_difference in W1;
            rewrite Z.add_simpl_l in W1;
            [apply (HTT i ltac:(lia))|apply (HSS i ltac:(lia))]; auto.
          - destruct (testbitn i) eqn:Hti;
            rewrite HR1, HR0, <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))), <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in W1;
            apply scalarmult_difference in W1.
            all: match goal with
                 | H : eq (scalarmult' ?X _) zero |- _ =>
                     match X with
                     | (SS _ _ + _ - _)%Z =>
                         replace X with (SS n (S (Z.to_nat i))) in H by (rewrite SS_succ, Z2Nat.id, Hti; lia)
                     | (TT _ _ + _ - _)%Z =>
                         replace X with (TT n (S (Z.to_nat i))) in H by (rewrite TT_succ, Z2Nat.id, Hti; lia)
                     end
                 end.
            all: rewrite <- Z2Nat.inj_succ in W1; try lia.
            all: match goal with
                 | H : eq (scalarmult' (SS _ _) _) zero |- _ =>
                     apply (HSS (Z.succ i) ltac:(lia))
                 | _ =>
                     apply (HTT (Z.succ i) ltac:(lia))
                 end; auto.
        Qed.

        Hint Unfold Jacobian.of_affine_impl : points_as_coordinates.

        Lemma SS_TT_xne (i : Z) (R0 R1 : point) (HCOZ : co_z R0 R1)
          (Hi : (2 <= i < scalarbitsz)%Z)
          (HR0 : eq R0 (scalarmult' (SS n (Z.to_nat i)) P))
          (HR1 : eq R1 (scalarmult' (TT n (Z.to_nat i)) P)) :
          x_of R0 <> x_of R1.
        Proof.
          assert (HH : forall A, eq (opp A) zero -> eq A zero) by (clear -field; unfold zero, Wzero; intros; t).
          intros Hxe. generalize (co_xz_implies _ _ Hxe HCOZ).
          destruct (Z.eq_dec 2 i).
          { subst i. replace (Z.to_nat 2) with 2%nat in HR1 by lia.
            replace (Z.to_nat 2) with 2%nat in HR0 by lia.
            rewrite TT2 in HR1. rewrite SS2 in HR0.
            rewrite HR0, HR1, <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            destruct (testbitn 1) eqn:Htj; intros [Q|Q]; apply scalarmult_difference in Q.
            all: match goal with
                 | H : eq (scalarmult' ?X _) zero |- _ =>
                     try replace X with 2%Z in H by lia;
                     try replace X with 4%Z in H by lia;
                     try replace X with (- (2))%Z in H by lia
                 end.
            all: match goal with
                 | H : eq (scalarmult' ?X _) zero |- _ =>
                     match X with
                     | 2%Z => apply (mult_two_power 1%Z ltac:(lia) H)
                     | 4%Z => apply (mult_two_power 2%Z ltac:(lia) H)
                     | (- (2))%Z =>
                         rewrite (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in Q;
                         apply HH in H;
                         apply (mult_two_power 1%Z ltac:(lia) H)
                     end
                 end. }
          { set (j := Z.pred i). assert (His : i = Z.succ j :> Z) by lia.
            assert (Hj : (2 <= j)%Z) by lia.
            rewrite His, Z2Nat.inj_succ in HR0, HR1 by lia.
            rewrite HR0, HR1, <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
            rewrite TT_succ, SS_succ, Z2Nat.id by lia.
            destruct (testbitn j) eqn:Htj; intros [Q|Q]; apply scalarmult_difference in Q.
            all: try match goal with
                   | H : eq (scalarmult' ?X _) zero |- _ =>
                       match X with
                       | Z.sub _ ?Y =>
                           match Y with
                           | (- _)%Z =>
                               replace X with (2 * (SS n (Z.to_nat j) + TT n (Z.to_nat j)))%Z in H by lia;
                               apply mult_two in H;
                               apply (HSS_plus_TT n (Z.to_nat j) H)
                           | (TT _ _) =>
                               replace X with (2 * SS n (Z.to_nat j))%Z in H by lia;
                               apply mult_two in H;
                               apply (HSS j ltac:(lia) H)
                           | (SS _ _) =>
                               replace X with (2 * TT n (Z.to_nat j))%Z in H by lia;
                               apply mult_two in H;
                               apply (HTT j ltac:(lia) H)
                           | (Z.add _ _) =>
                               replace X with (2 * - TT n (Z.to_nat j))%Z in H by lia;
                               apply mult_two in H;
                               rewrite (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in H;
                               apply HH in H;
                               apply (HTT j ltac:(lia) H)
                           end
                       end
                   end. }
        Qed.

        (* When n is odd, joye_ladder_inner computes [n]P *)
        Lemma joye_ladder_inner_correct :
          eq (joye_ladder_inner scalarbitsz testbitn P HPaff)
             (scalarmult' n P).
        Proof.
          unfold joye_ladder_inner. set (WW := while _ _ _ _).
          destruct (tplu_co_z_points P HPaff) as ((A1 & A2) & HA12) eqn:Htplu.
          rewrite (sig_eta (tplu_co_z_points _ _)) in Htplu.
          apply proj1_sig_eq in Htplu; simpl in Htplu.
          (* Initialize the ladder state with ([3]P, [1]P) or its symmetric *)
          destruct (tplu_scalarmult' Htplu) as (HeqA1 & HeqA2 & _).
          set (inv :=
                 fun '(R1R0, swap, i) =>
                   let '(R1, R0) := proj1_sig (R1R0:co_z_points) in
                   (2 <= i <= scalarbitsz)%Z /\
                     (eq (if (swap: bool) then R0 else R1) (scalarmult' (TT n (Z.to_nat i)) P)
                      /\ eq (if swap then R1 else R0) (scalarmult' (SS n (Z.to_nat i)) P))
                   /\ ((i < scalarbitsz)%Z -> x_of R1 <> x_of R0)
                   /\ (swap = testbitn (i - 1) :> bool)).
          assert (HH : forall (A B : Prop), A -> (A -> B) -> A /\ B) by tauto.
          assert (WWinv : inv WW /\ (snd WW = scalarbitsz :> Z) /\ (snd (fst WW) = testbitn (scalarbitsz - 1) :> bool)).
          { set (measure := fun (state : (co_z_points*bool*Z)) => ((Z.to_nat scalarbitsz) - (Z.to_nat (snd state)))%nat).
            unfold WW. replace (Z.to_nat scalarbitsz - 2)%nat with (measure (exist _ (A1, A2) HA12, testbitn 1, 2%Z)) by (unfold measure; simpl; lia).
            eapply (while.by_invariant inv measure (fun s => inv s /\ (snd s = scalarbitsz :> Z) /\ (snd (fst s) = testbitn (scalarbitsz - 1) :> bool))).
            - (* Invariant holds at beginning *)
              unfold inv. cbn [proj1_sig].
              split; [lia|]. apply HH.
              + change (Z.to_nat 2) with 2%nat.
                rewrite SS2, TT2.
                case Z.testbit; auto.
              + intros [He1 He2]. split.
                * intros Hxe.
                  generalize (SS_TT_xne 2%Z (if testbitn 1 then A1 else A2) (if testbitn 1 then A2 else A1) ltac:(destruct (testbitn 1); [|apply co_z_comm]; exact HA12) ltac:(lia) He2 He1).
                  case Z.testbit; [|symmetry]; auto.
                * reflexivity.
            - (* Invariant is preserved by the loop,
               measure decreases,
               and post-condition i = scalarbitsz. *)
              intros s Hs. destruct s as ((R1R0 & swap) & i).
              destruct R1R0 as ((R1 & R0) & HCOZ).
              destruct Hs as (Hi & (HR1 & HR0) & Hx & Hswape).
              destruct (Z.ltb i scalarbitsz) eqn:Hltb.
              + apply Z.ltb_lt in Hltb.
                split.
                * (* Invariant preservation.
                   The loop body is basically :
                   (R1, R0) <- cswap (testbitn i) (R1, R0);
                   (R1, R0) <- ZDAU (R1, R0);
                   (R1, R0) <- cswap (testbitn i) (R1, R0);
                   *)
                  (* Start by giving names to all intermediate values *)
                  unfold inv. destruct (cswap_co_z_points (xorb swap (testbitn i)) (exist _ _ _)) as ((B1 & B2) & HB12) eqn:Hswap1.
                  rewrite (sig_eta (cswap_co_z_points _ _)) in Hswap1.
                  apply proj1_sig_eq in Hswap1. simpl in Hswap1.
                  assert (HB1: B1 = (if xorb swap (testbitn i) then R0 else R1) :> point) by (destruct (xorb swap (testbitn i)); congruence).
                  assert (HB2: B2 = (if xorb swap (testbitn i) then R1 else R0) :> point) by (destruct (xorb swap (testbitn i)); congruence).
                  clear Hswap1.
                  destruct (zdau_co_z_points _) as ((C1 & C2) & HC12) eqn:HZDAU.
                  rewrite (sig_eta (zdau_co_z_points _)) in HZDAU.
                  apply proj1_sig_eq in HZDAU. simpl in HZDAU.
                  assert (HBx : x_of B1 <> x_of B2) by (rewrite HB1, HB2; destruct (xorb swap (testbitn i)); [symmetry|]; auto).
                  destruct (zaddu B1 B2 (zdau_co_z_points_obligation_1 (exist (fun '(A, B) => co_z A B) (B1, B2) HB12) B1 B2 eq_refl)) as (Y1 & Y2) eqn:HY.
                  assert (HYx : x_of Y1 <> x_of Y2) by (eapply zaddu_SS_TT; eauto; try lia; destruct swap; destruct (testbitn i); auto).
                  generalize (@Jacobian.zdau_correct_alt F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec char_ge_12 ltac:(unfold id in *; fsatz) B1 B2 (zdau_co_z_points_obligation_1 (exist (fun '(A, B) => co_z A B) (B1, B2) HB12) B1 B2 eq_refl) HBx ltac:(rewrite HY; simpl; apply HYx)).
                  rewrite HZDAU. intros (HC1 & HC2 & _).
                  (* clear HD. *) simpl.
                  (* invariant preservation *)
                  (* counter still within bounds *)
                  split; [lia|]. (* rewrite HD1, HD2. *) apply HH.
                  { (* New values are indeed [SS (i+1)]P and [TT (i+1)]P *)
                    destruct (testbitn i) eqn:Hti;
                    destruct swap eqn:Hswap;
                    rewrite <- HC1, <- HC2, HB1, HB2;
                    replace (Z.to_nat (Z.succ i)) with (S (Z.to_nat i)) by lia;
                    rewrite SS_succ, TT_succ, Z2Nat.id by lia;
                    rewrite Hti; split; try assumption;
                    rewrite <- Jacobian.add_double; try reflexivity;
                    cbv [xorb]; rewrite HR0, HR1;
                    repeat rewrite <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup)));
                    rewrite <- Z.add_diag; reflexivity. }
                  { (* Make sure we don't hit bad values *)
                    intros [He1 He2].
                    split; [|f_equal; lia].
                    intros Hxe He. eapply (SS_TT_xne (Z.succ i) (if testbitn i then C1 else C2) (if testbitn i then C2 else C1)); eauto.
                    - destruct (testbitn i); [|apply co_z_comm]; auto.
                    - lia.
                    - destruct (testbitn i); [|symmetry]; auto.
                   }
                * (* measure decreases *)
                  apply Z.ltb_lt in Hltb.
                  unfold measure; simpl; lia.
              + (* Post-condition *)
                simpl; split; auto.
                rewrite Z.ltb_nlt in Hltb. split; [|rewrite Hswape; f_equal]; try lia. }
          destruct WWinv as (Hinv & Hj & Hswap).
          destruct WW as ((R1R0 & swap) & i). destruct R1R0 as ((R1 & R0) & HCOZ).
          simpl in Hj; subst i. simpl in Hswap; subst swap.
          destruct Hinv as (_ & (_ & HR0) & _).
          rewrite (SSn n scalarbitsz ltac:(lia) ltac:(lia)) in HR0.
          simpl. destruct (testbitn (scalarbitsz - 1)); simpl; exact HR0.
        Qed.
      End Inner.

      (* We compute [n]P where P ≠ ∞ and n < ord(P) *)
      Context {n : Z} {Hn : (2 <= n < 2^scalarbitsz)%Z}
              {P : Wpoint} {HPnz : P <> ∞ :> Wpoint}
              {HordP : forall l, (Weq (scalarmult l P) ∞) <-> exists k, (l = k * ordP :> Z)%Z}
              {HordPn : (n + 2 < ordP)%Z}.

      Local Notation testbitn := (Z.testbit n).
      (* Local Notation n' := (if testbitn 0 then n else (n + 1)%Z). *)
      Local Notation n' := (Z.setbit n 0) (only parsing).
      Local Notation testbitn' := (Z.testbit n') (only parsing).

      (* Technically, if q is the order of the curve, and scalarbitsz = [log2 q],
         and ordP is close to q, then only the last two values of SS and TT are
         dangerous.
         See §3.1 of "Faster Montgomery and double-add ladders for short
         Weierstrass curves" (Mike Hamburg, CHES'20) for instance.
       *)
      Context {HSS : forall i, (2 <= i <= scalarbitsz)%Z -> not (Weq (scalarmult (SS n' (Z.to_nat i)) P) ∞) }
              {HTT : forall i, (2 <= i <= scalarbitsz)%Z -> not (Weq (scalarmult (TT n' (Z.to_nat i)) P) ∞) }.

      Lemma Hn' : (2 <= n' < 2^scalarbitsz)%Z.
      Proof.
        rewrite Z.setbit_spec'; simpl; split.
        - etransitivity; [|apply LandLorShiftBounds.Z.lor_lower]; lia.
        - apply (LandLorShiftBounds.Z.lor_range n 1 scalarbitsz); lia.
      Qed.

      Lemma scalarmult_eq_weq_conversion (k1 k2 : Z) :
        Weq (scalarmult k1 P) (scalarmult k2 P) <-> eq (scalarmult' k1 (of_affine P)) (scalarmult' k2 (of_affine P)).
      Proof.
        split; intros.
        - repeat rewrite <- scalarmult_scalarmult'.
          eapply Jacobian.Proper_of_affine. apply H.
        - rewrite <- Jacobian.to_affine_of_affine at 1.
          symmetry. rewrite <- Jacobian.to_affine_of_affine at 1.
          apply Jacobian.Proper_to_affine.
          symmetry; repeat rewrite scalarmult_scalarmult'; auto.
      Qed.

      Lemma HordP_alt (k : Z) :
        (0 < k < ordP)%Z ->
        not (Weq (scalarmult k P) ∞).
      Proof.
        intros Hbds Heq. destruct (proj1 (HordP k) Heq) as [l Hl].
        clear -Hbds Hl. generalize (Zmult_gt_0_lt_0_reg_r ordP l ltac:(lia) ltac:(lia)).
        intros. generalize (proj1 (Z.mul_le_mono_pos_r 1%Z l ordP ltac:(lia)) ltac:(lia)). lia.
      Qed.

      Lemma n'_alt :
        n' = (if testbitn 0 then n else (n + 1)%Z) :> Z.
      Proof.
        apply Z.bits_inj'; intros.
        destruct (Z.eq_dec n0 0) as [->|?]; [rewrite Z.setbit_eq|rewrite Z.setbit_neq]; try lia.
        - destruct (testbitn 0) eqn:Hbit0; auto.
          rewrite Z.bit0_odd, <- Z.even_pred.
          replace (Z.pred (n + 1))%Z with n by lia.
          rewrite <- Z.negb_odd, <- Z.bit0_odd, Hbit0; reflexivity.
        - destruct (testbitn 0) eqn:Hbit0; auto.
          replace n0 with (Z.succ (n0 - 1))%Z by lia.
          rewrite Z.bit0_odd in Hbit0.
          rewrite (Zeven_div2 n); [|apply Zeven_bool_iff; rewrite <- Z.negb_odd, Hbit0; reflexivity].
          rewrite Z.testbit_even_succ, Z.testbit_odd_succ; auto; lia.
      Qed.

      Lemma joye_ladder_correct :
        Weq (joye_ladder scalarbitsz testbitn P HPnz) (scalarmult n P).
      Proof.
        (* Unfold the ladder *)
        rewrite <- (Jacobian.to_affine_of_affine (scalarmult n P)).
        apply Jacobian.Proper_to_affine. rewrite scalarmult_scalarmult'.
        set (P' := of_affine P). set (HPaff := joye_ladder_obligation_1 P HPnz).
        assert (Hnodd : n' = Z.setbit n' 0 :> Z) by (repeat rewrite Z.setbit_spec'; rewrite <- Z.lor_assoc, Z.lor_diag; reflexivity).
        assert (HordP' : forall l, (eq (scalarmult' l P') zero) <-> exists k, (l = k * ordP :> Z)%Z).
        { intros l; split; replace zero with (scalarmult' 0%Z P') by reflexivity.
          - intros H; apply scalarmult_eq_weq_conversion in H; apply HordP; auto.
          - intros H; apply scalarmult_eq_weq_conversion; apply HordP; auto. }
        assert (HSS' : forall i, (2 <= i <= scalarbitsz)%Z -> not (eq (scalarmult' (SS n' (Z.to_nat i)) P') zero)).
        { replace zero with (scalarmult' 0%Z P') by reflexivity.
          intros i Hi He; apply scalarmult_eq_weq_conversion in He; apply (HSS i Hi); auto. }
        assert (HTT' : forall i, (2 <= i <= scalarbitsz)%Z -> not (eq (scalarmult' (TT n' (Z.to_nat i)) P') zero)).
        { replace zero with (scalarmult' 0%Z P') by reflexivity.
          intros i Hi He; apply scalarmult_eq_weq_conversion in He; apply (HTT i Hi); auto. }
        generalize (joye_ladder_inner_correct (n:=n') (P:=of_affine P) (HPaff:=HPaff) (Hnodd:=Hnodd) (Hn:=Hn') (HordP:=HordP')(HSS:=HSS') (HTT:=HTT')).
        intros Hinner. rewrite (joye_ladder_inner_bit0_irr scalarbitsz testbitn' testbitn (of_affine P) HPaff ltac:(intros; rewrite Z.setbit_neq; trivial; lia)) in Hinner.
        set (R0 := joye_ladder_inner scalarbitsz testbitn P' HPaff).
        cbv zeta. fold R0. fold P' in Hinner. fold R0 in Hinner.
        (* We now have R0 = [n']P *)
        destruct (make_co_z_points R0 _ _) as ((B1 & B2) & HB12) eqn:HMCZ.
        rewrite (sig_eta (make_co_z_points _ _ _)) in HMCZ.
        apply proj1_sig_eq in HMCZ; simpl in HMCZ.
        (* Prove [n']P ≠ ∞ *)
        assert (HR0znz : z_of R0 <> 0).
        { intro. apply (HSS scalarbitsz ltac:(lia)).
          replace Wzero with (scalarmult 0%Z P) by reflexivity.
          apply scalarmult_eq_weq_conversion.
          rewrite SSn by (generalize Hn'; lia).
          fold P'. rewrite <- Hinner. destruct R0 as (((? & ?) & ?) & ?).
          cbn in H; cbn. clear -field H.
          destruct (dec (f1 = 0)); fsatz. }
        (* Have co-Z representations of [n']P and [-1]P *)
        generalize (Jacobian.make_co_z_correct R0 (opp P') (opp_of_affine P HPnz) HR0znz).
        rewrite HMCZ. intros (HB1 & HB2 & _).
        destruct (zaddu_co_z_points _) as ((C1 & C2) & HC12) eqn:HZADDU.
        rewrite (sig_eta (zaddu_co_z_points _)) in HZADDU.
        apply proj1_sig_eq in HZADDU. simpl in HZADDU.
        (* Ensure ZADDU doesn't hit the neutral point *)
        assert (Hxne: x_of B1 <> x_of B2).
        { intro Hxe. destruct (co_xz_implies _ _ Hxe HB12) as [HEq|HNeq]; [rewrite <- HB1, Hinner, <- HB2 in HEq|rewrite <- HB1, Hinner, <- HB2 in HNeq].
          - rewrite <- (scalarmult_opp1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in HEq.
            apply scalarmult_difference in HEq.
            apply (HordP_alt (n' - -1)%Z).
            + rewrite n'_alt; destruct (testbitn 0); lia.
            + replace Wzero with (scalarmult 0 P) by reflexivity.
              apply scalarmult_eq_weq_conversion. auto.
          - rewrite (Group.inv_inv (H:=Pgroup)) in HNeq.
            rewrite <- (scalarmult_1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup)) P') in HNeq at 2.
            apply scalarmult_difference in HNeq.
            apply (HordP_alt (n' - 1)%Z).
            + rewrite n'_alt; destruct (testbitn 0); lia.
            + replace Wzero with (scalarmult 0 P) by reflexivity.
              apply scalarmult_eq_weq_conversion. auto. }
        generalize (Jacobian.zaddu_correct B1 B2 (zaddu_co_z_points_obligation_1 (exist (fun '(A, B) => co_z A B) (B1, B2) HB12) B1 B2 eq_refl) Hxne).
        rewrite HZADDU. intros (HC1 & HC2 & _).
        rewrite <- HB1, <- HB2, Hinner in HC1. rewrite <- HB1, Hinner in HC2.
        destruct (cswap_co_z_points (testbitn 0) _) as ((D1 & D2) & HD12) eqn:Hswap.
        rewrite (sig_eta (cswap_co_z_points _ _)) in Hswap.
        apply proj1_sig_eq in Hswap. cbn [proj1_sig cswap_co_z_points] in Hswap.
        simpl. assert (D1 = (if testbitn 0 then C2 else C1) :> point) as -> by (destruct (testbitn 0); congruence).
        rewrite n'_alt in HC1, HC2.
        destruct (testbitn 0); [rewrite <- HC2; reflexivity|rewrite <- HC1].
        rewrite <- (scalarmult_opp1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))), <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
        replace (n + 1 + -1)%Z with n by lia. reflexivity.
      Qed.
    End Proofs.
  End JoyeLadder.
End ScalarMult.

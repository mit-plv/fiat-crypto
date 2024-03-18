Require Import Coq.Classes.Morphisms.
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
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

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

    Definition SS (i : nat) : Z := n mod 2 ^ Z.succ i.
    Definition TT (i: nat) : Z := 2^Z.succ i - SS i.

    Lemma SS_plus_TT k : (SS k + TT k = 2^(Z.of_nat (S k)))%Z.
    Proof. cbv [SS TT]; lia. Qed.

    Lemma SS_succ i : SS (S i) = if (Z.testbit n (Z.of_nat (S i))) then (2 * SS i + TT i)%Z else SS i.
    Proof.
      cbv [TT SS].
      pose proof Z.mod_pow2_succ_r n (S i); case Z.testbit in *; cbv [Z.b2z] in *; lia.
    Qed.

    Lemma TT_succ i : TT (S i) = if (Z.testbit n (Z.of_nat (S i))) then TT i else (2 * TT i + SS i)%Z.
    Proof.
      cbv [TT SS].
      rewrite Nat2Z.inj_succ by lia.
      pose proof Z.mod_pow2_succ_r n (Z.succ i); case Z.testbit in *; cbv [Z.b2z] in *; rewrite ?Z.pow_succ_r in *; lia.
    Qed.

    Lemma SS_monotone0 (k : nat) : (SS 0 <= SS k)%Z.
    Proof.
      cbv [SS].
      rewrite Z.pow_1_r, Z.pow_succ_r, Znumtheory.Zmod_div_mod with (n:=2) (m:=(2*2^k)%Z)
        by (try exists (2^k)%Z; lia).
      apply Z.mod_bound_pos_le; Z.div_mod_to_equations; lia.
    Qed.

    Lemma TT_monotone0 (k : nat) : (TT 0 <= TT k)%Z.
    Proof.
      cbv [TT SS]; set (z := Z.succ k).
      enough (n mod 2 ^ z < 2 ^ z + (n mod 2 ^ Z.succ 0 - 1))%Z by lia; rewrite Z.pow_1_r.
      enough (n mod 2 = 0 -> n mod 2 ^ z <> Z.pred (2^z))%Z by try (Z.div_mod_to_equations; nia); intros ? X.
      apply (f_equal (fun x => Z.testbit x 0)) in X.
      rewrite <-Z.ones_equiv, Z.ones_spec_low, Z.mod_pow2_bits_low, Z.bit0_eqb in X; lia.
    Qed.

    Lemma SSn scalarbitsz (Hn : (0 <= n < 2^scalarbitsz)%Z) (Hscalarbitsz : (0 < scalarbitsz)%Z) :
      SS (Z.to_nat (scalarbitsz - 1)%Z) = n :> Z.
    Proof.
      cbv [SS].
      assert (Z.succ (Z.to_nat (scalarbitsz - 1)) = scalarbitsz) as -> by lia.
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

    Program Definition tplu_co_z_points (P : Wpoint) (HPnz : P <> ∞ :> W.point) : co_z_points :=
      tplu (of_affine P) _.
    Next Obligation. Proof. t. Qed.
    Next Obligation. Proof. t. Qed.

    Lemma opp_of_affine (P : Wpoint) (HPnz : P <> ∞ :> Wpoint) :
      z_of (opp (of_affine P)) = 1.
    Proof. t. Qed.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 14 Joye’s double-add algorithm with Co-Z addition formulæ *)
    (* Adapted *)
    Definition joye_ladder (scalarbitsz : Z) (testbit : Z -> bool) (P : Wpoint)
      (HPnz : P <> ∞ :> Wpoint) : Wpoint :=
      to_affine (
      (* Initialization *)
      let b := testbit 1%Z in
      let R1R0 := cswap_co_z_points b (tplu_co_z_points P HPnz) in
      (* loop *)
      let '(R1R0, _) :=
        (@while (co_z_points*Z) (fun '(_, i) => (Z.ltb i scalarbitsz))
           (fun '(R1R0, i) =>
              let b := testbit i in
              let R1R0 := cswap_co_z_points b R1R0 in
              let R1R0 := cswap_co_z_points b (zdau_co_z_points R1R0) in
              let i := Z.succ i in
              (R1R0, i))
           (Z.to_nat scalarbitsz) (* bound on loop iterations *)
           (R1R0, 2%Z)) in
      (* R0 is now (k | 1) P *)
      (* Substract P from R0 if lsb was actually 0 *)
      let R0 := snd (proj1_sig R1R0) in
      let b := testbit 0%Z in
      let mP := opp (of_affine P) in
      (* Make sure R0 and -P are co-z *)
      let R0R1 := make_co_z_points R0 mP (opp_of_affine P HPnz) in
      (* if b = 0 then R0 <- R0 - P and R1 <- R0 *)
      (* if b = 1 then R0 <- R0 and R1 <- R0 - P *)
      let R0 := fst (proj1_sig (cswap_co_z_points b (zaddu_co_z_points R0R1))) in
      R0).

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

      (* We compute [n]P where P ≠ ∞ and n < ord(P) *)
      Context {n scalarbitsz : Z}
              {Hn : (2 <= n < 2^scalarbitsz)%Z}
              {Hscalarbitsz : (2 <= scalarbitsz)%Z}
              {P : Wpoint} {HPnz : P <> ∞ :> Wpoint}
              {ordP : Z} {HordPpos : (2 < ordP)%Z}
              {HordPodd : Z.odd ordP = true :> bool}
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
      Context {HSS : forall i, (1 <= i < scalarbitsz)%Z -> not (Weq (scalarmult (SS n' (Z.to_nat i)) P) ∞) }
              {HTT : forall i, (1 <= i < scalarbitsz)%Z -> not (Weq (scalarmult (TT n' (Z.to_nat i)) P) ∞) }.

      Lemma Hn' : (2 <= n' < 2^scalarbitsz)%Z.
      Proof.
        rewrite Z.setbit_spec'; simpl; split.
        - etransitivity; [|apply LandLorShiftBounds.Z.lor_lower]; lia.
        - apply (LandLorShiftBounds.Z.lor_range n 1 scalarbitsz); lia.
      Qed.

      Lemma Htestbitn'0 : testbitn' 0 = true :> bool.
      Proof. rewrite Z.setbit_eqb; lia. Qed.

      Lemma Htestbitn' j (Hj : (1 <= j)%Z) : testbitn j = testbitn' j :> bool.
      Proof. rewrite Z.setbit_neq; trivial; lia. Qed.

      Lemma SS0 : (SS n' 0 = 1%Z :> Z).
      Proof. cbv [SS]. rewrite Z.pow_1_r, <-Z.bit0_mod, Z.setbit_eq; trivial; lia.  Qed.

      Lemma TT0 : (TT n' 0 = 1%Z :> Z).
      Proof. cbv [TT]. rewrite SS0; trivial. Qed.

      Lemma SS_1 : SS n' 1 = (if Z.testbit n' 1 then 3%Z else 1%Z) :> Z.
      Proof.
        cbv [SS n']; rewrite <-Z.land_ones, Z.land_comm by lia.
        destruct n; cbn; trivial; repeat (destruct p; cbn; trivial).
      Qed.

      Lemma TT_1 : TT n' 1 = (if Z.testbit n' 1 then 1%Z else 3%Z) :> Z.
      Proof. cbv [TT]. rewrite SS_1. case Z.testbit; lia. Qed.

      Lemma SS_TT1 : ((if testbitn 1 then SS n' 1 else TT n' 1) = 3 :> Z)%Z.
      Proof. rewrite SS_1, TT_1, Z.setbit_neq; try lia; case testbitn; trivial. Qed.
      Lemma HordP3 :
        (3 < ordP)%Z.
      Proof.
        destruct (Z.eq_dec 3 ordP); [|lia].
        generalize SS_TT1; intros HSSTT.
        destruct (testbitn 1); [elim (HSS 1 ltac:(lia))|elim (HTT 1 ltac:(lia))]; replace (Z.to_nat 1) with 1%nat by lia; rewrite HSSTT; eapply HordP; try lia.
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

      Lemma HordPn' :
        (0 < n' < ordP)%Z.
      Proof. rewrite n'_alt; destruct (testbitn 0); lia. Qed.

      Lemma mult_two_power (k : Z) :
        (0 <= k)%Z ->
        not (Weq (scalarmult (2^k)%Z P) ∞).
      Proof.
        eapply (Zlt_0_ind (fun x => ~ Weq (scalarmult (2 ^ x) P) Wzero)).
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

      Hint Unfold fst snd proj1_sig : points_as_coordinates.
      Hint Unfold fieldwise fieldwise' : points_as_coordinates.

      Lemma eq_fieldwise (P1 P2 : point) :
        fieldwise (n:=3) Feq
          (proj1_sig P1) (proj1_sig P2) ->
        eq P1 P2.
      Proof. clear -field; intros. t. Qed.

      Lemma Pynz :
        y_of (of_affine P) <> 0.
      Proof.
        intro Hy. assert (HA : eq (of_affine P) (opp (of_affine P))).
        - apply eq_fieldwise. destruct P as [ [ [X Y] | u] HP]; simpl; cbv in Hy; repeat split; fsatz.
        - apply (mult_two_power 1%Z ltac:(lia)).
          replace Wzero with (scalarmult 0%Z P) by reflexivity.
          eapply scalarmult_eq_weq_conversion.
          replace (2 ^ 1)%Z with (1 - -1)%Z by lia.
          rewrite (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
          rewrite <- (scalarmult_1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in HA.
          rewrite HA.
          rewrite <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
          rewrite <- (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
          replace (- (1) - -1)%Z with 0%Z by lia. reflexivity.
      Qed.

      Lemma HordP_alt (k : Z) :
        (0 < k < ordP)%Z ->
        not (Weq (scalarmult k P) ∞).
      Proof.
        intros Hbds Heq.
        destruct (proj1 (HordP k) Heq) as [l Hl].
        clear -Hbds Hl. generalize (Zmult_gt_0_lt_0_reg_r ordP l ltac:(lia) ltac:(lia)).
        intros. generalize (proj1 (Z.mul_le_mono_pos_r 1%Z l ordP ltac:(lia)) ltac:(lia)). lia.
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

      Lemma tplu_scalarmult' (Hz1 : z_of (of_affine P) = 1) {p q} (H : tplu (of_affine P) Hz1 = (p, q) :> _) :
        eq p (scalarmult' 3 (of_affine P)) /\ eq q (scalarmult' 1 (of_affine P)) /\ co_z p q.
      Proof.
        intros; unfold tplu. generalize (dblu_scalarmult' (of_affine P) Hz1 Pynz).
        inversion_prod; subst p q.
        rewrite (surjective_pairing (dblu _ _)) at 1.
        set (P1 := (snd (dblu (of_affine P) Hz1))).
        set (P2 := (fst (dblu (of_affine P) Hz1))). intros [A1 A2].
        destruct (dec (x_of P1 = x_of P2)) as [Hxe|Hxne].
        { destruct (co_xz_implies P1 P2 Hxe (CoZ.Jacobian.tplu_obligation_1 (of_affine P) Hz1)) as [A|A].
          - rewrite A1, A2 in A. elim (HordP_alt 1%Z ltac:(lia)).
            replace Wzero with (scalarmult 0%Z P) by reflexivity.
            apply scalarmult_eq_weq_conversion.
            replace 1%Z with (2 - 1)%Z by lia.
            rewrite (@scalarmult_sub_l _ _ _ _ _ Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 2 1).
            rewrite A.
            rewrite <- (@scalarmult_sub_l _ _ _ _ _ Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            replace (2 - 2)%Z with 0%Z by lia. reflexivity.
          - rewrite A1, A2 in A.
            elim (HordP_alt 3%Z ltac:(generalize HordP3; lia)).
            replace Wzero with (scalarmult 0%Z P) by reflexivity.
            apply scalarmult_eq_weq_conversion.
            replace 3%Z with (1 - -2)%Z by lia.
            rewrite (@scalarmult_sub_l _ _ _ _ _ Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            rewrite A.
            rewrite <- (@scalarmult_opp_l _ _ _ _ _ Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            rewrite <- (@scalarmult_sub_l _ _ _ _ _ Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            replace (- (2) - -2)%Z with 0%Z by lia. reflexivity. }
        generalize (@Jacobian.zaddu_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (CoZ.Jacobian.tplu_obligation_1 (of_affine P) Hz1) Hxne).
        rewrite (surjective_pairing (zaddu _ _ _)) at 1.
        intros (A & B & C); subst P1 P2.
        repeat try split; trivial.
        { rewrite <-A, A1, A2, (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 1 2); reflexivity. }
        { rewrite <-B. rewrite A2. reflexivity. }
      Qed.

      Lemma add_opp_zero (A : point) :
        eq (add A (opp A)) zero.
      Proof.
        generalize (Jacobian.add_opp A).
        destruct (add A (opp A)) as (((X & Y) & Z) & H).
        cbn. intros HP; destruct (dec (Z = 0)); fsatz.
      Qed.

      Lemma scalarmult_difference (A : point) (n1 n2 : Z):
        eq (scalarmult' n1 A) (scalarmult' n2 A) ->
        eq (scalarmult' (n1 - n2)%Z A) zero.
      Proof.
        intros. rewrite (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))), H, <- (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))), Z.sub_diag.
        apply (scalarmult_0_l (is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
      Qed.

      Lemma joye_ladder_correct :
        Weq (joye_ladder scalarbitsz testbitn P HPnz) (scalarmult n P).
      Proof.
        (* Unfold the ladder *)
        rewrite <- (Jacobian.to_affine_of_affine (scalarmult n P)).
        apply Jacobian.Proper_to_affine. rewrite scalarmult_scalarmult'.
        destruct (tplu_co_z_points P HPnz) as ((A1 & A2) & HA12) eqn:Htplu.
        rewrite (sig_eta (tplu_co_z_points _ _)) in Htplu.
        apply proj1_sig_eq in Htplu; simpl in Htplu.
        (* Initialize the ladder state with ([3]P, [1]P) or its symmetric *)
        cbv zeta. destruct (cswap_co_z_points (testbitn 1) _) as ((A3 & A4) & HA34) eqn:HA1.
        rewrite (sig_eta (cswap_co_z_points _ _)) in HA1.
        apply proj1_sig_eq in HA1. cbn [proj1_sig cswap_co_z_points] in HA1.
        assert (A3 = (if testbitn 1 then A2 else A1) :> point) as HA3 by (destruct (testbitn 1); inversion HA1; auto).
        assert (A4 = (if testbitn 1 then A1 else A2) :> point) as HA4 by (destruct (testbitn 1); inversion HA1; auto).
        clear HA1.  destruct (tplu_scalarmult' (tplu_co_z_points_obligation_1 P HPnz) Htplu) as (HeqA1 & HeqA2 & _).
        (* While loop *)
        set (WW := while _ _ _ _).
        (* Invariant is:
           - loop counter i is such that 2 ≤ i ≤ scalarbitsz
           - R1 = [TT (i - 1)]P
           - R0 = [SS (i - 1)]P
           - additional condition to ensure that the ladder state does not encounter the neutral point
        *)
        set (inv :=
               fun '(R1R0, i) =>
                 let '(R1, R0) := proj1_sig (R1R0:co_z_points) in
                 (2 <= i <= scalarbitsz)%Z  /\
                     (eq R1 (scalarmult' (TT n' (Z.to_nat (i - 1)%Z)) (of_affine P))
                     /\ eq R0 (scalarmult' (SS n' (Z.to_nat (i - 1)%Z)) (of_affine P)))
                     /\ ((i < scalarbitsz)%Z -> x_of R1 <> x_of R0)).
        assert (WWinv : inv WW /\ (snd WW = scalarbitsz :> Z)).
        { set (measure := fun (state : (co_z_points*Z)) => ((Z.to_nat scalarbitsz) + 2 - (Z.to_nat (snd state)))%nat).
          unfold WW. replace (Z.to_nat scalarbitsz) with (measure (exist _ (A3, A4) HA34, 2%Z)) by (unfold measure; simpl; lia).
          eapply (while.by_invariant inv measure (fun s => inv s /\ (snd s = scalarbitsz :> Z))).
          - (* Invariant holds at beginning *)
            unfold inv. cbn [proj1_sig].
            split; [lia|].
            split.
            + change (Z.to_nat (2 - 1)) with 1%nat.
              rewrite SS_1, TT_1, <-Htestbitn', HA3, HA4 by lia.
              case Z.testbit; auto.
            + intros AB Hxe. destruct (co_xz_implies A3 A4 Hxe HA34) as [Heq|Hopp]; [rewrite HA3, HA4 in Heq|rewrite HA3, HA4 in Hopp].
              * eapply (HordP_alt 2 ltac:(lia)).
                replace Wzero with (scalarmult 0 P) by reflexivity.
                apply scalarmult_eq_weq_conversion.
                replace 2%Z with (3 - 1)%Z by lia.
                rewrite (scalarmult_sub_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
                rewrite <- HeqA1, <- HeqA2.
                destruct (testbitn 1); rewrite Heq; simpl; apply add_opp_zero.
              * eapply (mult_two_power 2%Z ltac:(lia)).
                replace (Z.pow 2 2) with 4%Z by lia.
                replace Wzero with (scalarmult 0%Z P) by reflexivity.
                replace 4%Z with (3 + 1)%Z by lia.
                apply scalarmult_eq_weq_conversion.
                rewrite (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))).
                rewrite <- HeqA1, <- HeqA2.
                destruct (testbitn 1); rewrite Hopp; [|rewrite Jacobian.add_comm]; apply add_opp_zero.
          - (* Invariant is preserved by the loop,
               measure decreases,
               and post-condition i = scalarbitsz.
            *)
            intros s Hs. destruct s as (R1R0 & i).
            destruct R1R0 as ((R1 & R0) & HCOZ).
            destruct Hs as (Hi & (HR1 & HR0) & Hx).
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
                unfold inv. destruct (cswap_co_z_points (testbitn i) (exist _ _ _)) as ((B1 & B2) & HB12) eqn:Hswap1.
                rewrite (sig_eta (cswap_co_z_points _ _)) in Hswap1.
                apply proj1_sig_eq in Hswap1. simpl in Hswap1.
                assert (HB1: B1 = (if testbitn i then R0 else R1) :> point) by (destruct (testbitn i); congruence).
                assert (HB2: B2 = (if testbitn i then R1 else R0) :> point) by (destruct (testbitn i); congruence).
                clear Hswap1.
                destruct (zdau_co_z_points _) as ((C1 & C2) & HC12) eqn:HZDAU.
                rewrite (sig_eta (zdau_co_z_points _)) in HZDAU.
                apply proj1_sig_eq in HZDAU. simpl in HZDAU.
                assert (HBx : x_of B1 <> x_of B2) by (rewrite HB1, HB2; destruct (testbitn i); [symmetry|]; auto).
                destruct (zaddu B1 B2 (zdau_co_z_points_obligation_1 (exist (fun '(A, B) => co_z A B) (B1, B2) HB12) B1 B2 eq_refl)) as (Y1 & Y2) eqn:HY.
                (* Since co-Z formulas are incomplete, we need to show that we won't hit the neutral point for ZDAU *)
                assert (HYx : x_of Y1 <> x_of Y2).
                { (* We need to prove that [SS (i - 1) + TT (i - 1)]P and
                     [SS (i - 1)]P or [TT (i - 1)]P
                     (depending on testbitn i) have different X coordinates, i.e.,
                     [SS (i - 1) + TT (i - 1) ± SS (i - 1)]P ≠ ∞
                     or [SS (i - 1) + TT (i - 1) ± TT (i - 1)]P ≠ ∞
                  *)
                  intro XX. generalize (Jacobian.zaddu_correct B1 B2 (zdau_co_z_points_obligation_1 (exist (fun '(A, B) => co_z A B) (B1, B2) HB12) B1 B2 eq_refl) HBx).
                  rewrite HY. intros (W1 & W2 & W3).
                  destruct (co_xz_implies _ _ XX W3) as [W|W]; rewrite W, <- W2, HB1, HB2 in W1.
                  - destruct (testbitn i);
                    rewrite HR1, HR0, <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in W1;
                    apply scalarmult_difference in W1;
                    rewrite Z.add_simpl_l in W1;
                    [apply (HTT (i - 1)%Z ltac:(lia))|apply (HSS (i - 1)%Z ltac:(lia))];
                    replace Wzero with (scalarmult 0 P) by reflexivity;
                    apply scalarmult_eq_weq_conversion;
                    rewrite W1; reflexivity.
                  - destruct (testbitn i) eqn:Hti;
                    rewrite (Htestbitn' i ltac:(lia)) in Hti;
                    rewrite HR1, HR0, <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))), <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in W1;
                    apply scalarmult_difference in W1.
                    all: match goal with
                         | H : eq (scalarmult' ?X _) zero |- _ =>
                             match X with
                             | (SS _ _ + _ - _)%Z =>
                                 replace X with (SS n' (S (Z.to_nat (i - 1)%Z))) in H by (rewrite SS_succ, Nat2Z.inj_succ, Z2Nat.id, Z.sub_1_r, Z.succ_pred, Hti; lia)
                             | (TT _ _ + _ - _)%Z =>
                                 replace X with (TT n' (S (Z.to_nat (i - 1)%Z))) in H by (rewrite TT_succ, Nat2Z.inj_succ, Z2Nat.id, Z.sub_1_r, Z.succ_pred, Hti; lia)
                             end
                         end.
                    all: rewrite <- Z2Nat.inj_succ, Z.sub_1_r, Z.succ_pred in W1; try lia.
                    all: match goal with
                         | H : eq (scalarmult' (SS _ _) _) zero |- _ =>
                             apply (HSS i ltac:(lia))
                         | _ =>
                             apply (HTT i ltac:(lia))
                         end.
                    all: replace Wzero with (scalarmult 0 P) by reflexivity.
                    all: apply scalarmult_eq_weq_conversion.
                    all: rewrite W1; reflexivity. }
                generalize (@Jacobian.zdau_correct_alt F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec char_ge_12 ltac:(unfold id in *; fsatz) B1 B2 (zdau_co_z_points_obligation_1 (exist (fun '(A, B) => co_z A B) (B1, B2) HB12) B1 B2 eq_refl) HBx ltac:(rewrite HY; simpl; apply HYx)).
                rewrite HZDAU. intros (HC1 & HC2 & _).
                destruct (cswap_co_z_points (testbitn i) _) as ((D1 & D2) & HD12) eqn:HD.
                rewrite (sig_eta (cswap_co_z_points _ _)) in HD.
                apply proj1_sig_eq in HD. cbn [proj1_sig cswap_co_z_points] in HD.
                assert (HD1 : D1 = (if testbitn i then C2 else C1) :> point) by (destruct (testbitn i); congruence).
                assert (HD2 : D2 = (if testbitn i then C1 else C2) :> point) by (destruct (testbitn i); congruence).
                clear HD. simpl.
                (* invariant preservation *)
                (* counter still within bounds *)
                split; [lia|]. rewrite HD1, HD2. split.
                { (* New values are indeed [SS i]P and [TT i]P *)
                  destruct (testbitn i) eqn:Hti;
                  rewrite (Htestbitn' i ltac:(lia)) in Hti;
                  rewrite <- HC1, <- HC2, HB1, HB2;
                  replace (Z.to_nat (Z.succ i - 1)) with (S (Z.to_nat (i - 1)%Z)) by lia;
                  rewrite SS_succ, TT_succ;
                  replace (Z.of_nat (S (Z.to_nat (i - 1)))) with i by lia;
                  rewrite Hti; split; try assumption;
                  rewrite <- Jacobian.add_double; try reflexivity;
                  rewrite HR0, HR1;
                  repeat rewrite <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup)));
                  rewrite <- Z.add_diag; reflexivity. }
                { (* Make sure we don't hit bad values *)
                  intros Hsi Hxe'.
                  assert (Hxe : x_of C1 = x_of C2) by (destruct (testbitn i); fsatz); clear Hxe'.
                  generalize (co_xz_implies _ _ Hxe HC12).
                  rewrite <- HC1, <- HC2, <- Jacobian.add_double; [|reflexivity].
                  rewrite HB1, HB2. destruct (testbitn i) eqn:Hti;
                  rewrite (Htestbitn' i ltac:(lia)) in Hti;
                  rewrite HR0, HR1;
                  repeat rewrite <- (scalarmult_add_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup)));
                  rewrite Z.add_diag, <- (scalarmult_opp_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup)));
                  intros [Q|Q]; apply scalarmult_difference in Q;
                  (* 3 cases *)
                  match goal with
                  | H : eq (scalarmult' ?X _) zero |- _ =>
                      match X with
                      | Z.sub _ ?Y =>
                          match Y with
                          | (- _)%Z => (* Case [2^(i+1)]P ≠ ∞ *)
                              replace X with (2 * (SS n' (Z.to_nat (i - 1)) + TT n' (Z.to_nat (i - 1))))%Z in H by lia
                          | (TT _ _) => (* Case [2 * (SS (i - 1))]P ≠ ∞ *)
                              replace X with (2 * SS n' (Z.to_nat (i - 1)))%Z in H by lia;
                              shelve
                          | (SS _ _) => (* Case [2 * (TT (i - 1))]P ≠ ∞ *)
                              replace X with (2 * TT n' (Z.to_nat (i - 1)))%Z in H by lia;
                              shelve
                          end
                      end
                  end.
                  (* Solve case [2^(i+1)]P ≠ ∞ first *)
                  all: rewrite SS_plus_TT, <- Z2Nat.inj_succ, Z.sub_1_r, Z.succ_pred, Z2Nat.id, <- Z.pow_succ_r in Q; try lia; eauto.
                  all: eapply (mult_two_power (Z.succ i) ltac:(lia)).
                  all: replace Wzero with (scalarmult 0 P) by reflexivity.
                  all: apply scalarmult_eq_weq_conversion.
                  all: rewrite Q; reflexivity.
                  Unshelve. (* Solve the other cases *)
                  all: replace zero with (scalarmult' 0 (of_affine P)) in Q by reflexivity.
                  all: apply scalarmult_eq_weq_conversion in Q.
                  all: generalize (SS_monotone0 n' (Z.to_nat (i - 1)%Z)); rewrite SS0; intro QS.
                  all: generalize (TT_monotone0 n' (Z.to_nat (i - 1)%Z)); rewrite TT0; intro QT.
                  all: match goal with
                       | H : Weq (scalarmult (Z.mul 2%Z ?X) P) (_ 0%Z _) |- _ =>
                           destruct (proj1 (HordP (Z.mul 2%Z X)) Q) as [l Hl];
                           generalize (Znumtheory.prime_mult 2%Z Znumtheory.prime_2 l ordP ltac:(exists X; lia))
                       end.
                  all: intros [A|A]; destruct A as [m Hm];
                       [|replace ordP with (0 + 2 * m)%Z in HordPodd by lia; rewrite Z.odd_add_mul_2 in HordPodd; simpl in HordPodd; congruence].
                  all: subst l; rewrite <- Z.mul_assoc, <- Z.mul_shuffle3 in Hl.
                  all: apply (Z.mul_reg_l _ _ 2%Z ltac:(lia)) in Hl.
                  all: match goal with
                       | H : SS _ (Z.to_nat ?X) = (_ * ordP)%Z :> Z |- _ =>
                           apply (HSS X ltac:(lia));
                           apply (proj2 (HordP (SS n' (Z.to_nat X))))
                       | H : TT _ (Z.to_nat ?X) = (_ * ordP)%Z :> Z |- _ =>
                           apply (HTT X ltac:(lia));
                           apply (proj2 (HordP (TT n' (Z.to_nat X))))
                       end; eauto. }
              * (* measure decreases *)
                apply Z.ltb_lt in Hltb.
                unfold measure; simpl; lia.
            + (* Post-condition *)
              simpl; split; auto.
              rewrite Z.ltb_nlt in Hltb. lia. }
        (* Finalization, compute [n' - 1]P and [n']P *)
        destruct WWinv as (Hinv & Hj).
        destruct WW as (R1R0 & i). destruct R1R0 as ((R1 & R0) & HCOZ).
        simpl in Hj; subst i. destruct Hinv as (_ & (_ & HR0) & _).
        rewrite SSn in HR0; [|generalize Hn'; lia|lia]. cbn [snd proj1_sig].
        destruct (make_co_z_points R0 _ _) as ((B1 & B2) & HB12) eqn:HMCZ.
        rewrite (sig_eta (make_co_z_points _ _ _)) in HMCZ.
        apply proj1_sig_eq in HMCZ; simpl in HMCZ.
        (* Prove [n']P ≠ ∞ *)
        assert (HR0znz : z_of R0 <> 0).
        { intro. apply (HordP_alt n').
          - apply HordPn'.
          - replace Wzero with (scalarmult 0 P) by reflexivity.
            apply scalarmult_eq_weq_conversion.
            rewrite <- HR0. destruct R0 as (((? & ?) & ?) & ?).
            cbn in H; cbn. clear -field H.
            destruct (dec (f1 = 0)); fsatz. }
        (* Have co-Z representations of [n']P and [-1]P *)
        generalize (Jacobian.make_co_z_correct R0 (opp (of_affine P)) (opp_of_affine P HPnz) HR0znz).
        rewrite HMCZ. intros (HB1 & HB2 & _).
        destruct (zaddu_co_z_points _) as ((C1 & C2) & HC12) eqn:HZADDU.
        rewrite (sig_eta (zaddu_co_z_points _)) in HZADDU.
        apply proj1_sig_eq in HZADDU. simpl in HZADDU.
        (* Ensure ZADDU doesn't hit the neutral point *)
        assert (Hxne: x_of B1 <> x_of B2).
        { intro Hxe. destruct (co_xz_implies _ _ Hxe HB12) as [HEq|HNeq]; [rewrite <- HB1, HR0, <- HB2 in HEq|rewrite <- HB1, HR0, <- HB2 in HNeq].
          - rewrite <- (scalarmult_opp1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup))) in HEq.
            apply scalarmult_difference in HEq.
            apply (HordP_alt (n' - -1)%Z).
            + rewrite n'_alt; destruct (testbitn 0); lia.
            + replace Wzero with (scalarmult 0 P) by reflexivity.
              apply scalarmult_eq_weq_conversion. auto.
          - rewrite (Group.inv_inv (H:=Pgroup)) in HNeq.
            rewrite <- (scalarmult_1_l (groupG:=Pgroup) (mul_is_scalarmult:=scalarmult_ref_is_scalarmult (groupG:=Pgroup)) (of_affine P)) in HNeq at 2.
            apply scalarmult_difference in HNeq.
            apply (HordP_alt (n' - 1)%Z).
            + rewrite n'_alt; destruct (testbitn 0); lia.
            + replace Wzero with (scalarmult 0 P) by reflexivity.
              apply scalarmult_eq_weq_conversion. auto. }
        generalize (Jacobian.zaddu_correct B1 B2 (zaddu_co_z_points_obligation_1 (exist (fun '(A, B) => co_z A B) (B1, B2) HB12) B1 B2 eq_refl) Hxne).
        rewrite HZADDU. intros (HC1 & HC2 & _).
        rewrite <- HB1, <- HB2, HR0 in HC1. rewrite <- HB1, HR0 in HC2.
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

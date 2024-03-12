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

Module ScalarMult.
  Section JoyeDoubleAddDecomposition.
    (* Joye's double-add ladder for computing [n]P basically tracks the
       values of two sequences [SS i]P and [TT i]P.
       This section proves some properties on the sequences SS and TT.
     *)
    Variables n scalarbitsz : Z.
    Hypotheses (Hn : (0 <= n < 2^scalarbitsz)%Z)
      (Hscalarbitsz : (0 < scalarbitsz)%Z).
    Local Notation testbitn := (Z.testbit n).

    (* Highly regular right-to-left algorithms for scalar multiplication *)
    (* Marc Joye *)
    (* §2.1 Double-add algorithm *)
    Fixpoint SS (i : nat) :=
      match i with
      | O => Z.b2z (testbitn 0)
      | S j => if (testbitn (Z.of_nat i)) then (2 * SS j + TT j)%Z else SS j
      end
    with TT (i : nat ) :=
           match i with
           | O => 2 - Z.b2z (testbitn 0)
           | S j => if (testbitn (Z.of_nat i)) then TT j else (2 * TT j + SS j)%Z
           end.

    Definition SS' (i : nat) :=
      (n mod (2 ^ (Z.of_nat (S i))))%Z.

    Definition TT' (i: nat) := (2^(Z.of_nat (S i)) - SS' i)%Z.

    Lemma SS_succ' (i : nat) :
      SS' (S i) = ((Z.b2z (testbitn (Z.of_nat (S i))) * 2^(Z.of_nat (S i))) + SS' i)%Z.
    Proof.
      unfold SS'. repeat rewrite <- Pow2Mod.Z.pow2_mod_spec; try lia.
      replace (Z.of_nat (S (S i))) with (Z.of_nat (S i) + 1)%Z by lia.
      rewrite Pow2Mod.Z.pow2_mod_split; try lia.
      repeat rewrite Pow2Mod.Z.pow2_mod_spec; try lia.
      rewrite Z.add_comm, <- Z.add_lor_land.
      replace (Z.land _ _) with 0%Z.
      2: { apply Z.bits_inj'; intros; rewrite Z.bits_0, Z.land_spec.
           rewrite Z.testbit_mod_pow2; [|lia].
           destruct (dec (Z.lt n0 (Z.of_nat (S i)))).
           - rewrite Z.mul_pow2_bits_low, Bool.andb_false_r; auto.
           - rewrite (proj2 (Z.ltb_nlt n0 _)), Bool.andb_false_l; auto. }
      rewrite Z.add_0_r. f_equal.
      rewrite Z.shiftl_mul_pow2; [|lia]. f_equal.
      rewrite <- Z.bit0_mod, Z.shiftr_spec, Z.add_0_l; lia.
    Qed.

    Lemma SS_is_SS' (i : nat) :
      SS i = SS' i :> Z
    with TT_is_TT' (i : nat) :
      TT i = TT' i :> Z.
    Proof.
      { destruct i.
        - unfold SS, SS'. apply Z.bit0_mod.
        - rewrite SS_succ'. cbn [SS].
          destruct (testbitn (Z.of_nat (S i))).
          + rewrite TT_is_TT'. unfold TT'.
            rewrite <- SS_is_SS'. cbv [Z.b2z]. lia.
          + cbv [Z.b2z]. rewrite <- SS_is_SS'. lia. }
      { destruct i.
        - unfold TT, TT', SS'.
          f_equal. apply Z.bit0_mod.
        - cbn [TT]. unfold TT'; fold TT'.
          rewrite SS_succ'. destruct (testbitn (Z.of_nat (S i))).
          + cbv [Z.b2z]. rewrite TT_is_TT'. unfold TT'; fold TT'.
            replace (2 ^ Z.of_nat (S (S i)))%Z with (2 * 2 ^ Z.of_nat (S i))%Z.
            2:{ repeat rewrite <- two_power_nat_equiv.
                rewrite (two_power_nat_S (S i)). reflexivity. }
            lia.
          + cbv [Z.b2z]. rewrite TT_is_TT'.
            unfold TT'; fold TT'. rewrite SS_is_SS'.
            replace (2 ^ Z.of_nat (S (S i)))%Z with (2 * 2 ^ Z.of_nat (S i))%Z.
            2:{ repeat rewrite <- two_power_nat_equiv.
                rewrite (two_power_nat_S (S i)). reflexivity. }
            lia. }
    Qed.

    Lemma SSn :
      SS (Z.to_nat scalarbitsz - 1) = n :> Z.
    Proof.
      rewrite SS_is_SS'. unfold SS'.
      rewrite <- Pow2Mod.Z.pow2_mod_spec; [|lia].
      apply Pow2Mod.Z.pow2_mod_id_iff; try lia.
      replace (Z.of_nat (S (Z.to_nat scalarbitsz - 1)))%Z with scalarbitsz; lia.
    Qed.

    Lemma SS_plus_TT (k: nat) :
      (SS k + TT k)%Z = (2^(Z.of_nat (S k)))%Z :> Z.
    Proof.
      rewrite SS_is_SS', TT_is_TT'.
      unfold TT'. lia.
    Qed.

    Lemma SS_sub_TT0 :
      (TT 0 - SS 0)%Z = (2 * (1 - Z.b2z (testbitn 0)))%Z :> Z.
    Proof. unfold TT, SS. lia. Qed.

    Lemma SS_sub_TT_S (k : nat) :
      if testbitn (Z.of_nat (S k)) then
        (SS (S k) - TT (S k))%Z = (2 * SS k)%Z :> Z
      else
        (TT (S k) - SS (S k))%Z = (2 * TT k)%Z :> Z.
    Proof. cbn [SS TT]. destruct (testbitn (Z.of_nat (S k))); lia. Qed.

    Lemma SS_pos (k : nat) :
      (0 <= SS k)%Z.
    Proof. rewrite SS_is_SS'. apply Z_mod_nonneg_nonneg; lia. Qed.

    Lemma TT_pos (k : nat) :
      (0 <= TT k)%Z.
    Proof.
      induction k.
      - cbn [TT]. destruct (testbitn 0); simpl; lia.
      - cbn [TT]. destruct (testbitn _); auto.
        generalize (SS_pos k); lia.
    Qed.

    Lemma SS_monotone (k : nat) :
      (SS k <= SS (S k))%Z.
    Proof.
      replace (SS (S k)) with (if (testbitn (Z.of_nat (S k))) then (2 * SS k + TT k)%Z else SS k) by reflexivity.
      generalize (SS_pos k). generalize (TT_pos k).
      destruct (testbitn _); lia.
    Qed.

    Lemma TT_monotone (k : nat) :
      (TT k <= TT (S k))%Z.
    Proof.
      replace (TT (S k)) with (if (testbitn (Z.of_nat (S k))) then TT k else (2 * TT k + SS k)%Z) by reflexivity.
      generalize (SS_pos k). generalize (TT_pos k).
      destruct (testbitn _); lia.
    Qed.

    Lemma SS_monotone0 (k : nat) :
      (SS 0 <= SS k)%Z.
    Proof. induction k; [lia|transitivity (SS k); auto; apply SS_monotone]. Qed.

    Lemma TT_monotone0 (k : nat) :
      (TT 0 <= TT k)%Z.
    Proof. induction k; [lia|transitivity (TT k); auto; apply TT_monotone]. Qed.

    Lemma SS_upper_bound (k : nat) :
      (SS k <= n)%Z.
    Proof. rewrite SS_is_SS'; apply Z.mod_le; lia. Qed.

    Lemma SS_upper_bound1 (k : nat) :
      (SS k < 2^(Z.of_nat (S k)))%Z.
    Proof. rewrite SS_is_SS'. apply Z.mod_pos_bound. lia. Qed.

    Lemma TT_upper_bound (k : nat) :
      (TT k <= 2^(Z.of_nat (S k)))%Z.
    Proof.
      rewrite TT_is_TT'; unfold TT'. rewrite <- SS_is_SS'.
      generalize (SS_upper_bound1 k). generalize (SS_pos k). lia.
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
    Local Notation make_co_z_inner := (@Jacobian.make_co_z_inner F Fmul).
    Local Notation make_co_z := (@Jacobian.make_co_z F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation of_affine := (@Jacobian.of_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation to_affine := (@Jacobian.to_affine F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zero := (of_affine Wzero).
    Local Notation dblu := (@Jacobian.dblu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation tplu_inner := (@Jacobian.tplu_inner F Fone Fadd Fsub Fmul a).
    Local Notation tplu := (@Jacobian.tplu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zaddu_inner := (@Jacobian.zaddu_inner F Fsub Fmul).
    Local Notation zaddu := (@Jacobian.zaddu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec).
    Local Notation zdau_inner := (@Jacobian.zdau_inner F Fadd Fsub Fmul).
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

    Lemma tplu_inner_is_point (P : F*F*F) (HPaff : let '(X, Y, Z) := P in Z = 1)
      (HP : is_point P) :
      is_point (fst (tplu_inner P)) /\ is_point (snd (tplu_inner P)) /\ (snd (fst (tplu_inner P)) = snd (snd (tplu_inner P))).
    Proof.
      destruct (@Jacobian.tplu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (ltac:(t))) as (Q & S) eqn:HQS.
      unfold Jacobian.tplu in HQS. inversion HQS; clear HQS.
      destruct Q as [Q HQ]. inversion H0; clear H0.
      destruct S as [S HS]. inversion H1; clear H1.
      rewrite H2, H0. repeat split; auto.
      rewrite <- H2, <- H0. unfold tplu_inner; simpl; t.
    Qed.

    Lemma zdau_inner_is_point (P Q : F*F*F) (HP : is_point P) (HQ : is_point Q)
      (H : snd P = snd Q) :
      is_point (fst (zdau_inner P Q)) /\ is_point (snd (zdau_inner P Q)) /\ (snd (fst (zdau_inner P Q)) = snd (snd (zdau_inner P Q))).
    Proof.
      destruct (@Jacobian.zdau F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (exist _ Q HQ) ltac:(t)) as (R0 & R1) eqn:HRR.
      unfold Jacobian.zdau in HRR. inversion HRR; clear HRR.
      destruct R0 as [R0 HR0]. inversion H1; clear H1.
      destruct R1 as [R1 HR1]. inversion H2; clear H2.
      rewrite H1, H3. repeat split; auto.
      rewrite <- H1, <- H3. unfold zdau_inner; simpl. t.
    Qed.

    Lemma make_co_z_inner_is_co_z (P Q : F*F*F) (HP: is_point P) (HQ : is_point Q)
      (H : snd Q = 1) :
      is_point (fst (make_co_z_inner P Q)) /\ is_point (snd (make_co_z_inner P Q)) /\ snd (fst (make_co_z_inner P Q)) = snd (snd (make_co_z_inner P Q)).
    Proof.
      destruct (@Jacobian.make_co_z F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (exist _ Q HQ) ltac:(t)) as (R0 & R1) eqn:Heq.
      unfold make_co_z in Heq. inversion Heq; clear Heq.
      destruct R0 as [R0 HR0]. inversion H1; clear H1.
      destruct R1 as [R1 HR1]. inversion H2; clear H2.
      rewrite H1, H3. repeat split; auto.
      destruct R0 as ((? & ?) & ?); destruct R1 as ((? & ?) & ?); auto.
      destruct P as ((? & ?) & ?); destruct Q as ((? & ?) & ?); auto.
      simpl in H1, H3; simpl; inversion H1; inversion H3.
      rewrite <- H8. rewrite H5. reflexivity.
    Qed.

    Lemma zaddu_inner_is_point (P Q : F*F*F) (HP : is_point P) (HQ : is_point Q)
      (H : snd P = snd Q) :
      is_point (fst (zaddu_inner P Q)) /\ is_point (snd (zaddu_inner P Q)) /\ snd (fst (zaddu_inner P Q)) = snd (snd (zaddu_inner P Q)).
    Proof.
      destruct (@Jacobian.zaddu F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist _ P HP) (exist _ Q HQ) ltac:(t)) as (R0 & R1) eqn:HRR.
      unfold Jacobian.zaddu in HRR. inversion HRR; clear HRR.
      destruct R0 as [R0 HR0]. inversion H1; clear H1.
      destruct R1 as [R1 HR1]. inversion H2; clear H2.
      rewrite H1, H3. repeat split; auto.
      rewrite <- H1, <- H3. unfold zaddu_inner; simpl. t.
    Qed.

    Local Notation cswap := (fun (b : bool) '(P, Q) => if b then (Q, P) else (P, Q)).

    Definition opp_inner (P : F*F*F) : F*F*F :=
      match P with
      | (X, Y, Z) => (X, Fopp Y, Z)
      end.

    (* Scalar Multiplication on Weierstraß Elliptic Curves from Co-Z Arithmetic *)
    (* Goundar, Joye, Miyaji, Rivain, Vanelli *)
    (* Algorithm 14 Joye’s double-add algorithm with Co-Z addition formulæ *)
    (* Adapted *)
    Definition joye_ladder_inner (scalarbitsz : Z) (testbit : Z -> bool) (P : F*F*F) : F*F*F :=
      (* Assume lsb (aka testbit 0) is 1 *)
      let b := testbit 1%Z in
      (* if b = 0 then (R1, R0) = (3P, P) = (11b * P, 01b * P) *)
      (* if b = 1 then (R1, R0) = (P, 3P) = (01b * P, 11b * P) *)
      let '(R1, R0) := cswap b (tplu_inner P) in
      let '((R1, R0), _) :=
        (@while (((F*F*F)*(F*F*F))*Z) (fun '(_, i) => (Z.ltb i scalarbitsz))
                (fun '((R1, R0), i) =>
                   let b := testbit i in
                   let '(R1, R0) := cswap b (R1, R0) in
                   let '(R1, R0) := cswap b (zdau_inner R1 R0) in
                   let i := Z.succ i in
                   ((R1, R0), i))
                (Z.to_nat scalarbitsz)
                ((R1, R0), 2%Z)) in
      (* R0 is now (k | 1) P *)
      (* Substract P from R0 if lsb was actually 0 *)
      let b := testbit 0%Z in
      let mP := opp_inner P in
      (* Make sure R0 and -P are co-z *)
      let '(R0, R1) := make_co_z_inner R0 mP in
      (* if b = 0 then R0 = R0 - P and R1 = R0 *)
      (* if b = 1 then R0 = R0 and R1 = R0 - P *)
      let '(R0, R1) := cswap b (zaddu_inner R0 R1) in
      R0.

    Lemma joye_ladder_inner_is_point (scalarbitsz : Z) (testbit : Z -> bool) (P : F*F*F)
      (HP : is_point P) (HPaff : let '(X, Y, Z) := P in Z = 1) :
      is_point (joye_ladder_inner scalarbitsz testbit P).
    Proof.
      destruct P as ((X & Y) & Z).
      unfold joye_ladder_inner.
      destruct (tplu_inner_is_point (X, Y, Z) ltac:(auto) HP) as (A & B & C).
      rewrite (surjective_pairing (tplu_inner _)).
      replace (if testbit 1%Z then (snd (tplu_inner (X, Y, Z)), fst (tplu_inner (X, Y, Z))) else (fst (tplu_inner (X, Y, Z)), snd (tplu_inner (X, Y, Z)))) with ((if testbit 1%Z then snd (tplu_inner (X, Y, Z)) else fst (tplu_inner (X, Y, Z)), if testbit 1%Z then fst (tplu_inner (X, Y, Z)) else snd (tplu_inner (X, Y, Z)))) by (destruct (testbit 1%Z); reflexivity).
      pose (CD := (while (fun '(_, i) => (i <? scalarbitsz)%Z)
        (fun '(R1, R0, i) =>
         let
         '(R2, R3) := if testbit i then (R0, R1) else (R1, R0) in
          let
          '(R4, R5) :=
           let '(P, Q) := zdau_inner R2 R3 in if testbit i then (Q, P) else (P, Q) in
           (R4, R5, Z.succ i)) (Z.to_nat scalarbitsz)
        (if testbit 1%Z then snd (tplu_inner (X, Y, Z)) else fst (tplu_inner (X, Y, Z)),
          if testbit 1%Z then fst (tplu_inner (X, Y, Z)) else snd (tplu_inner (X, Y, Z)), 2%Z))).
      pose (inv := fun '(R1, R0, i) => is_point R1 /\ is_point R0 /\ (i >= 0)%Z /\ snd R1 = snd R0).
      assert (HCD: inv CD).
      { unfold CD. set (measure := fun (state : ((F*F*F)*(F*F*F)*BinNums.Z)) => ((Z.to_nat scalarbitsz) + 2 - (Z.to_nat (snd state)))%nat).
        replace (Z.to_nat scalarbitsz) with (measure ((if testbit 1%Z then snd (tplu_inner (X, Y, Z)) else fst (tplu_inner (X, Y, Z)), if testbit 1%Z then fst (tplu_inner (X, Y, Z)) else snd (tplu_inner (X, Y, Z)), 2%Z))) by (unfold measure; simpl; lia).
        eapply (while.by_invariant inv measure inv).
        - destruct (testbit 1%Z); unfold inv; repeat split; auto; lia.
        - intros. destruct s as ((R1 & R0) & i).
          destruct (Z.ltb i scalarbitsz) eqn:Hi; [|assumption].
          destruct H as (A1 & B1 & D1 & C1).
          split; replace (if testbit i then (R0, R1) else (R1, R0)) with (if testbit i then R0 else R1, if testbit i then R1 else R0) by (destruct (testbit i); reflexivity); rewrite (surjective_pairing (zdau_inner _ _)); [|destruct (testbit i); unfold measure; simpl; lia].
          destruct (zdau_inner_is_point R0 R1 B1 A1 ltac:(symmetry; apply C1)) as (A2 & B2 & C2).
          destruct (zdau_inner_is_point R1 R0 A1 B1 ltac:(apply C1)) as (A3 & B3 & C3).
          destruct (testbit i); unfold inv; simpl; repeat split; auto; try lia.
          symmetry; exact C2. }
      fold CD. destruct CD as ((R1 & R0) & i).
      assert (HmP : is_point (opp_inner (X, Y, Z))) by (unfold is_point, opp_inner in *; t).
      rewrite (surjective_pairing (make_co_z_inner _ _)).
      rewrite (surjective_pairing (zaddu_inner _ _)).
      destruct HCD as (HR1 & HR0 & _ & HRZ).
      destruct (make_co_z_inner_is_co_z R0 (X, Fopp Y, Z) HR0 HmP HPaff) as (X1 & X2 & Xeq).
      destruct (zaddu_inner_is_point _ _ X1 X2 Xeq) as (Y1 & Y2 & Yeq).
      destruct (testbit 0%Z); assumption.
    Qed.

    Program Definition joye_ladder (scalarbitsz : Z) (testbit : Z -> bool) (P : Wpoint)
      (HPnz : P <> ∞ :> Wpoint) : Wpoint :=
      to_affine (joye_ladder_inner scalarbitsz testbit (proj1_sig (of_affine P))).
    Next Obligation. Proof.
      destruct P as [P HP]. destruct P as [ [X Y] | ?]; [|t].
      simpl. eapply joye_ladder_inner_is_point; unfold is_point; [|fsatz].
      destruct (dec (1 = 0)); [exfalso; fsatz|rewrite HP; fsatz].
    Qed.

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
              {HordP : forall l, (l <> 0 :> Z)%Z -> ((Weq (scalarmult l P) ∞) <-> exists k, (l = k * ordP :> Z)%Z)}
              {HordPn : (n + 2 < ordP)%Z}.

      Local Notation testbitn := (Z.testbit n).
      (* Local Notation n' := (if testbitn 0 then n else (n + 1)%Z). *)
      Local Notation n' := (Z.setbit n 0).
      Local Notation testbitn' := (Z.testbit n').

      (* Technically, if q is the order of the curve, and scalarbitsz = [log2 q],
         and ordP is close to q, then only the last two values of SS and TT are
         dangerous.
         See §3.1 of "Faster Montgomery and double-add ladders for short
         Weierstrass curves" (Mike Hamburg, CHES'20) for instance.
       *)
      Context {HSS : forall i, (1 <= i < scalarbitsz)%Z -> not (Weq (scalarmult (SS n' (Z.to_nat i)) P) ∞) }
              {HTT : forall i, (1 <= i < scalarbitsz)%Z -> not (Weq (scalarmult (TT n' (Z.to_nat i)) P) ∞) }.

      Lemma Hn' :
        (2 <= n' < 2^scalarbitsz)%Z.
      Proof.
        rewrite Z.setbit_spec'; simpl; split.
        - etransitivity; [|apply LandLorShiftBounds.Z.lor_lower]; lia.
        - apply (LandLorShiftBounds.Z.lor_range n 1 scalarbitsz); lia.
      Qed.

      Lemma Htestbitn'0 :
        testbitn' 0 = true :> bool.
      Proof. rewrite Z.setbit_eqb; lia. Qed.

      Lemma Htestbitn' :
         forall j, (1 <= j)%Z ->
              testbitn j = testbitn' j :> bool.
      Proof. intros; rewrite Z.setbit_neq; auto; lia. Qed.

      Lemma SS_TT1 :
        ((if testbitn 1 then SS n' 1 else TT n' 1) = 3 :> Z)%Z.
      Proof.
        rewrite SS_is_SS', TT_is_TT'; eauto.
        unfold TT'. replace (2 ^ Z.of_nat 2)%Z with 4%Z by lia.
        rewrite SS_succ'; eauto. unfold SS'. rewrite <- Z.bit0_mod.
        rewrite Htestbitn'0, Htestbitn'; [|lia].
        replace (Z.of_nat 1) with 1%Z by lia.
        destruct (testbitn' 1); simpl; lia.
      Qed.

      Lemma SS0 : (SS n' 0 = 1%Z :> Z).
      Proof. cbn [SS]; rewrite Htestbitn'0; reflexivity. Qed.

      Lemma TT0 : (TT n' 0 = 1%Z :> Z).
      Proof. cbn [TT]; rewrite Htestbitn'0; reflexivity. Qed.

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
        destruct (proj1 (HordP (2^x)%Z ltac:(lia)) Heqz) as [l Hl].
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
          eapply HordP; [lia|exists m; assumption].
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

      Lemma eq_proof_irr (P1 P2 : point) :
        fieldwise (n:=3) Feq
          (proj1_sig P1) (proj1_sig P2) ->
        eq P1 P2.
      Proof. clear -field; intros. t. Qed.

      Lemma eq_refl_proof_irr (P1 P2 : point) :
        (proj1_sig P1 = proj1_sig P2 :> F*F*F) ->
        eq P1 P2.
      Proof. clear -field; intros. unfold eq; rewrite H. t. Qed.

      Lemma Pynz :
        y_of (of_affine P) <> 0.
      Proof.
        intro Hy. assert (HA : eq (of_affine P) (opp (of_affine P))).
        - apply eq_proof_irr. destruct P as [ [ [X Y] | u] HP]; simpl; cbv in Hy; repeat split; fsatz.
        - apply (mult_two_power 1%Z ltac:(lia)).
          replace Wzero with (scalarmult 0%Z P) by reflexivity.
          eapply scalarmult_eq_weq_conversion.
          replace (2 ^ 1)%Z with (1 - -1)%Z by lia.
          rewrite (@scalarmult_sub_l point eq add zero opp Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
          rewrite <- (@scalarmult_1_l point eq add zero opp Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)) in HA.
          rewrite HA.
          rewrite <- (@scalarmult_opp_l point eq add zero opp Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
          rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup _ (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
          replace (- (1) - -1)%Z with 0%Z by lia. reflexivity.
      Qed.

      Lemma HordP_alt (k : Z) :
        (0 < k < ordP)%Z ->
        not (Weq (scalarmult k P) ∞).
      Proof.
        intros Hbds Heq.
        destruct (proj1 (HordP k ltac:(lia)) Heq) as [l Hl].
        clear -Hbds Hl. generalize (Zmult_gt_0_lt_0_reg_r ordP l ltac:(lia) ltac:(lia)).
        intros. generalize (proj1 (Z.mul_le_mono_pos_r 1%Z l ordP ltac:(lia)) ltac:(lia)). lia.
      Qed.

      Lemma dblu_scalarmult' (Hz1 : z_of (of_affine P) = 1) :
        eq (fst (dblu (of_affine P) Hz1)) (scalarmult' 2 (of_affine P))
        /\ eq (snd (dblu (of_affine P) Hz1)) (scalarmult' 1 (of_affine P)).
      Proof.
        generalize (@Jacobian.dblu_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec char_ge_12 (of_affine P) Hz1 Pynz).
        rewrite (surjective_pairing (dblu _ _)) at 1.
        intros (A & B & C). split.
        - rewrite <- A. replace 2%Z with (1 + 1)%Z by lia.
          rewrite (@scalarmult_add_l point eq add zero opp Pgroup); [|apply (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)].
          rewrite (@scalarmult_1_l point eq add zero opp Pgroup); [|apply (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)].
          rewrite <- Jacobian.add_double; reflexivity.
        - rewrite (@scalarmult_1_l point eq add zero opp Pgroup); [|apply (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)].
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

      Lemma tplu_scalarmult' (Hz1 : z_of (of_affine P) = 1) :
        eq (fst (tplu (of_affine P) Hz1)) (scalarmult' 3 (of_affine P))
        /\ eq (snd (tplu (of_affine P) Hz1)) (scalarmult' 1 (of_affine P))
        /\ co_z (fst (tplu (of_affine P) Hz1)) (snd (tplu (of_affine P) Hz1)).
      Proof.
        rewrite (proj1 (Jacobian.tplu_tplu2 _ _)) at 1.
        rewrite (proj2 (Jacobian.tplu_tplu2 _ _)) at 1.
        unfold Jacobian.tplu2. generalize (dblu_scalarmult' Hz1).
        set (P1 := (snd (dblu (of_affine P) Hz1))).
        set (P2 := (fst (dblu (of_affine P) Hz1))). intros [A1 A2].
        destruct (dec (x_of P1 = x_of P2)) as [Hxe|Hxne].
        { destruct (co_xz_implies P1 P2 Hxe (CoZ.Jacobian.tplu2_obligation_1 (of_affine P) Hz1)) as [A|A].
          - rewrite A1, A2 in A. elim (HordP_alt 1%Z ltac:(lia)).
            replace Wzero with (scalarmult 0%Z P) by reflexivity.
            apply scalarmult_eq_weq_conversion.
            replace 1%Z with (2 - 1)%Z by lia.
            rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 2 1).
            rewrite A.
            rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            replace (2 - 2)%Z with 0%Z by lia. reflexivity.
          - rewrite A1, A2 in A.
            elim (HordP_alt 3%Z ltac:(generalize HordP3; lia)).
            replace Wzero with (scalarmult 0%Z P) by reflexivity.
            apply scalarmult_eq_weq_conversion.
            replace 3%Z with (1 - -2)%Z by lia.
            rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            rewrite A.
            rewrite <- (@scalarmult_opp_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
            replace (- (2) - -2)%Z with 0%Z by lia. reflexivity. }
        generalize (@Jacobian.zaddu_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec P1 P2 (CoZ.Jacobian.tplu2_obligation_1 (of_affine P) Hz1) Hxne).
        rewrite (surjective_pairing (zaddu _ _ _)) at 1.
        intros (A & B & C). rewrite <- B. split; auto.
        rewrite <- A. rewrite A1, A2.
        rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 1 2).
        replace (1 + 2)%Z with 3%Z by lia. reflexivity.
      Qed.

      Lemma joye_inner_correct (Hjoye : is_point (joye_ladder_inner scalarbitsz testbitn (proj1_sig (of_affine P)))) :
        eq
          (exist _
             (joye_ladder_inner scalarbitsz testbitn (proj1_sig (of_affine P)))
             Hjoye)
          (scalarmult' n (of_affine P)).
      Proof.
        assert (HPaff: z_of (of_affine P) = 1) by (destruct P as [ [ [X Y] | ?] HP] eqn:HPeq; [reflexivity|elim HPnz; clear; t]).
        unfold joye_ladder_inner, eq.
        set (TPLU := (tplu (of_affine P) HPaff)).
        red. replace (tplu_inner (proj1_sig (of_affine P))) with (proj1_sig (fst TPLU), proj1_sig (snd TPLU)); [|symmetry; unfold TPLU, tplu; apply surjective_pairing].
        set (R1 := if testbitn 1 then proj1_sig (snd TPLU) else proj1_sig (fst TPLU)).
        set (R0 := if testbitn 1 then proj1_sig (fst TPLU) else proj1_sig (snd TPLU)).
        replace (if testbitn 1 then (proj1_sig (snd TPLU), proj1_sig (fst TPLU)) else (proj1_sig (fst TPLU), proj1_sig (snd TPLU))) with (R1, R0) by (destruct (testbitn 1); reflexivity).
        set (WW := while (fun '(_, i) => (i <? scalarbitsz)%Z)
        (fun '(R2, R3, i) =>
         let
         '(R4, R5) := if testbitn i then (R3, R2) else (R2, R3) in
          let
          '(R6, R7) :=
           let '(P0, Q) := zdau_inner R4 R5 in if testbitn i then (Q, P0) else (P0, Q)
          in (R6, R7, Z.succ i)) (Z.to_nat scalarbitsz) (R1, R0, 2%Z)).
        set (inv :=
               fun '(R1, R0, i) =>
                 is_point R1 /\ is_point R0 /\ snd R1 = snd R0 /\
                   (2 <= i <= scalarbitsz)%Z  /\
                   forall (pR1 : is_point R1) (pR0 : is_point R0),
                     (eq (exist _ R1 pR1) (scalarmult' (TT n' ((Z.to_nat i) - 1)%nat) (of_affine P))
                     /\ eq (exist _ R0 pR0) (scalarmult' (SS n' ((Z.to_nat i) - 1)%nat) (of_affine P)))
                     /\ ((i < scalarbitsz)%Z -> x_of (exist _ R1 pR1) <> x_of (exist _ R0 pR0))).
        assert (WWinv : inv WW /\ (snd WW = scalarbitsz :> Z)).
        { set (measure := fun (state : ((F*F*F)*(F*F*F)*BinNums.Z)) => ((Z.to_nat scalarbitsz) + 2 - (Z.to_nat (snd state)))%nat).
          unfold WW. replace (Z.to_nat scalarbitsz) with (measure (R1, R0, 2%Z)) by (unfold measure; simpl; lia).
          eapply (while.by_invariant inv measure (fun s => inv s /\ (snd s = scalarbitsz :> Z))).
          - unfold inv. do 3 (try split).
            + unfold R1. destruct (testbitn 1);
              match goal with |- is_point (proj1_sig ?X) => destruct X as (? & ?Y); exact Y end.
            + unfold R0. destruct (testbitn 1);
              match goal with |- is_point (proj1_sig ?X) => destruct X as (? & ?Y); exact Y end.
            + destruct (tplu_scalarmult' HPaff) as [Heq1 [Heq2 Heqz] ].
              fold TPLU in Heq1, Heq2, Heqz. intros.
              unfold R1, R0; unfold co_z, z_of in Heqz; destruct (proj1_sig (snd TPLU)) as ((? & ?) & ?); destruct (proj1_sig (fst TPLU)) as ((? & ?) & ?); destruct (testbitn 1); simpl; fsatz.
            + replace (Z.to_nat 2 - 1)%nat with 1%nat by lia.
              cbn [TT SS]. rewrite Htestbitn'0.
              replace (Z.of_nat 1%nat) with 1%Z by lia.
              rewrite <- (Htestbitn' 1%Z ltac:(lia)).
              cbn [Z.b2z]. replace (2 - 1)%Z with 1%Z by lia.
              replace (2 * 1 + 1)%Z with 3%Z by lia.
              destruct (tplu_scalarmult' HPaff) as [Heq1 [Heq2 Heqz] ].
              fold TPLU in Heq1, Heq2, Heqz. split; [lia|].
              intros. split.
              * intros. unfold R1, R0; destruct (testbitn 1); rewrite <- Heq1, <- Heq2; split; eapply eq_proof_irr; reflexivity.
              * intros AB Hxe. destruct (co_xz_implies (fst TPLU) (snd TPLU)).
                { unfold x_of. unfold R1, R0 in Hxe.
                  destruct (proj1_sig (snd TPLU)) as ((? & ?) & ?); destruct (proj1_sig (fst TPLU)) as ((? & ?) & ?); destruct (testbitn 1); simpl; fsatz. }
                { exact Heqz. }
                { rewrite Heq1, Heq2 in H.
                  eapply (HordP_alt 2 ltac:(lia)).
                  replace Wzero with (scalarmult 0 P) by reflexivity.
                  apply scalarmult_eq_weq_conversion.
                  replace 2%Z with (3 + (- 1))%Z by lia.
                  rewrite (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 3 (-1)).
                  rewrite H.
                  rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) 1 (-1)).
                  replace (1 + -1)%Z with 0%Z by lia. reflexivity. }
                { rewrite Heq1, Heq2 in H.
                  eapply (mult_two_power 2%Z ltac:(lia)).
                  replace (Z.pow 2 2) with 4%Z by lia.
                  replace Wzero with (scalarmult 0%Z P) by reflexivity.
                  replace 4%Z with (3 - -1)%Z by lia.
                  apply scalarmult_eq_weq_conversion.
                  rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
                  rewrite H.
                  rewrite <- (@scalarmult_opp_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
                  rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
                  replace (- (1) - (-1))%Z with 0%Z by lia. reflexivity. }
          - intros s Hinv. destruct s as ((X1 & X0) & i).
            destruct Hinv as (HX1 & HX0 & HXze & Hi & Heqs).
            destruct (Z.ltb i scalarbitsz) eqn:Hltb.
            + split.
              * (* invariant preservation *)
                apply Z.ltb_lt in Hltb.
                specialize (Heqs HX1 HX0). destruct Heqs as [ [Heq1 Heq0] Hxne].
                specialize (Hxne Hltb).
                unfold inv. replace (if testbitn i then (X0, X1) else (X1, X0)) with (if testbitn i then X0 else X1, if testbitn i then X1 else X0) by (destruct (testbitn i); reflexivity).
                set (Y0 := if testbitn i then exist _ X0 HX0 else exist _ X1 HX1).
                set (Y1 := if testbitn i then exist _ X1 HX1 else exist _ X0 HX0).
                replace (if testbitn i then X0 else X1) with (proj1_sig Y0) by (destruct (testbitn i); reflexivity).
                replace (if testbitn i then X1 else X0) with (proj1_sig Y1) by (destruct (testbitn i); reflexivity).
                set (ZD := zdau_inner _ _). rewrite (surjective_pairing ZD).
                replace (if testbitn i then (snd ZD, fst ZD) else (fst ZD, snd ZD)) with (if testbitn i then snd ZD else fst ZD, if testbitn i then fst ZD else snd ZD) by (destruct (testbitn i); reflexivity).
                assert (HYCOZ : co_z Y0 Y1).
                { unfold co_z, Y0, Y1, z_of; simpl.
                  destruct X0 as ((? & ?) & ?); destruct X1 as ((? & ?) & ?); destruct (testbitn i); simpl in HXze; fsatz. }
                assert (HYxne : x_of Y0 <> x_of Y1).
                { unfold Y0, Y1, x_of in *; destruct X0 as ((? & ?) & ?); destruct X1 as ((? & ?) & ?); destruct (testbitn i); simpl; simpl in Hxne; fsatz. }
                generalize (@Jacobian.zdau_correct_alt F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec char_ge_12 ltac:(unfold id in *; fsatz) Y0 Y1 HYCOZ HYxne).
                rewrite (surjective_pairing (zdau _ _ _)).
                intros PP. assert (HPP: x_of (fst (zaddu Y0 Y1 HYCOZ)) <> x_of (snd (zaddu Y0 Y1 HYCOZ))).
                { intro XX. generalize (Jacobian.zaddu_correct Y0 Y1 HYCOZ HYxne).
                  rewrite (surjective_pairing (zaddu _ _ _)). intros [W1 [W2 W3] ].
                  destruct (co_xz_implies _ _ XX W3) as [W|W].
                  - rewrite W, <- W2 in W1.
                    unfold Y0, Y1 in W1.
                    assert (VV: eq (add (exist is_point X0 HX0) (exist is_point X1 HX1)) (if testbitn i then exist is_point X0 HX0 else exist is_point X1 HX1)).
                    { rewrite <- W1. destruct (testbitn i); [reflexivity|apply Jacobian.add_comm]. }
                    assert (QQ : Weq (scalarmult (if testbitn i then TT n' (Z.to_nat i - 1) else SS n' (Z.to_nat i - 1)) P) Wzero).
                    { replace Wzero with (scalarmult 0 P) by reflexivity.
                      apply scalarmult_eq_weq_conversion.
                      replace (TT n' (Z.to_nat i - 1)) with (((SS n' (Z.to_nat i - 1)) + (TT n' (Z.to_nat i - 1))) - (SS n' (Z.to_nat i - 1)))%Z by lia.
                      replace (SS n' (Z.to_nat i - 1)) with (((SS n' (Z.to_nat i - 1)) + (TT n' (Z.to_nat i - 1))) - (TT n' (Z.to_nat i - 1)))%Z at 3 by lia.
                      destruct (testbitn i);
                        rewrite Heq1, Heq0 in VV;
                        rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P));
                        rewrite (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P));
                        rewrite VV;
                        rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P));
                        replace (_ - _)%Z with 0%Z by lia; reflexivity. }
                    replace (Z.to_nat i - 1)%nat with (Z.to_nat (i - 1)%Z) in QQ by lia.
                    destruct (testbitn i); [eapply HTT|eapply HSS]; eauto; lia.
                  - rewrite W, <- W2 in W1.
                    unfold Y0, Y1 in W1.
                    assert (VV: eq (add (exist is_point X0 HX0) (exist is_point X1 HX1)) (opp (if testbitn i then exist is_point X0 HX0 else exist is_point X1 HX1))).
                    { rewrite <- W1. destruct (testbitn i); [reflexivity|apply Jacobian.add_comm]. }
                    assert (QQ : Weq (scalarmult (if testbitn i then SS n' (Z.to_nat i) else TT n' (Z.to_nat i)) P) Wzero).
                    { replace Wzero with (scalarmult 0 P) by reflexivity.
                      apply scalarmult_eq_weq_conversion.
                      replace (TT n' (Z.to_nat i)) with (if testbitn i then TT n' (Z.to_nat i - 1) else ((SS n' (Z.to_nat i - 1) + TT n' (Z.to_nat i - 1)) + TT n' (Z.to_nat i - 1))%Z).
                      2: { replace (Z.to_nat i) with (S (Z.to_nat i - 1)) at 5 by lia.
                           replace (TT n' (S (Z.to_nat i - 1))) with (if testbitn' (Z.of_nat (S (Z.to_nat i - 1))) then TT n' (Z.to_nat i - 1) else (2 * TT n' (Z.to_nat i - 1) + SS n' (Z.to_nat i - 1)%nat)%Z) by reflexivity.
                           replace ((Z.of_nat (S (Z.to_nat i - 1)))) with i by lia.
                           rewrite Htestbitn'; [|lia].
                           destruct (testbitn' i); lia. }
                      replace (SS n' (Z.to_nat i)) with (if testbitn i then ((SS n' (Z.to_nat i - 1) + TT n' (Z.to_nat i - 1)) + SS n' (Z.to_nat i - 1))%Z else SS n' (Z.to_nat i - 1)).
                      2: { replace (Z.to_nat i) with (S (Z.to_nat i - 1)) at 5 by lia.
                           replace (SS n' (S (Z.to_nat i - 1))) with (if testbitn' (Z.of_nat (S (Z.to_nat i - 1))) then (2 * SS n' (Z.to_nat i - 1) + TT n' (Z.to_nat i - 1)%nat)%Z else SS n' (Z.to_nat i - 1)) by reflexivity.
                           replace ((Z.of_nat (S (Z.to_nat i - 1)))) with i by lia.
                           rewrite Htestbitn'; [|lia].
                           destruct (testbitn' i); lia. }
                      destruct (testbitn i);
                        rewrite Heq0, Heq1 in VV;
                        repeat rewrite (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P));
                        rewrite VV, Jacobian.add_comm;
                        rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P));
                        replace (_ - _)%Z with 0%Z by lia; reflexivity. }
                    destruct (testbitn i); [eapply HSS|eapply HTT]; eauto; lia. }
                specialize (PP HPP). destruct PP as [A1 [A2 A3] ].
                do 4 (try split).
                { unfold ZD. destruct (testbitn i); [apply (CoZ.Jacobian.zdau_obligation_2 Y0 Y1 HYCOZ)|apply (CoZ.Jacobian.zdau_obligation_1 Y0 Y1 HYCOZ)]. }
                { unfold ZD. destruct (testbitn i); [apply (CoZ.Jacobian.zdau_obligation_1 Y0 Y1 HYCOZ)|apply (CoZ.Jacobian.zdau_obligation_2 Y0 Y1 HYCOZ)]. }
                { unfold ZD. unfold zdau, co_z, z_of in A3. simpl in A3.
                  rewrite (surjective_pairing (fst _)) in A3.
                  rewrite (surjective_pairing (snd _)) in A3.
                  rewrite (surjective_pairing (fst _)) in A3.
                  rewrite (surjective_pairing (fst (snd _))) in A3.
                  destruct (testbitn i); fsatz. }
                { lia. }
                { intros. assert (eq (exist is_point (if testbitn i then snd ZD else fst ZD) pR1) (scalarmult' (TT n' (Z.to_nat (Z.succ i) - 1)) (of_affine P)) /\ eq (exist is_point (if testbitn i then fst ZD else snd ZD) pR0) (scalarmult' (SS n' (Z.to_nat (Z.succ i) - 1)) (of_affine P))) as [YY1 YY2].
                  { unfold ZD. assert (eq (exist is_point (if testbitn i then snd (zdau_inner (proj1_sig Y0) (proj1_sig Y1)) else fst (zdau_inner (proj1_sig Y0) (proj1_sig Y1))) pR1) (if testbitn i then snd (zdau Y0 Y1 HYCOZ) else fst (zdau Y0 Y1 HYCOZ))) as -> by (apply eq_refl_proof_irr; destruct (testbitn i); unfold zdau; simpl; reflexivity).
                    assert (eq (exist is_point (if testbitn i then fst (zdau_inner (proj1_sig Y0) (proj1_sig Y1)) else snd (zdau_inner (proj1_sig Y0) (proj1_sig Y1))) pR0) (if testbitn i then fst (zdau Y0 Y1 HYCOZ) else snd (zdau Y0 Y1 HYCOZ))) as -> by (apply eq_refl_proof_irr; destruct (testbitn i); unfold zdau; simpl; reflexivity).
                    replace (Z.to_nat (Z.succ i) - 1)%nat with (S (Z.to_nat i - 1)) by lia.
                    assert ((TT n' (S _)) = (if testbitn' i then TT n' (Z.to_nat i - 1) else (2 * (TT n' (Z.to_nat i - 1)) + SS n' (Z.to_nat i - 1))%Z) :> Z) as -> by (cbn [TT]; replace (Z.of_nat (S (Z.to_nat i - 1))) with i by lia; reflexivity).
                    assert ((SS n' (S _)) = (if testbitn' i then (2 * (SS n' (Z.to_nat i - 1)) + TT n' (Z.to_nat i - 1))%Z else SS n' (Z.to_nat i - 1)) :> Z) as -> by (cbn [SS]; replace (Z.of_nat (S (Z.to_nat i - 1))) with i by lia; reflexivity).
                    rewrite <- Htestbitn'; [|lia].
                    rewrite <- Jacobian.add_double in A1; [|reflexivity].
                    destruct (testbitn i); rewrite <- A1, <- A2; unfold Y0, Y1; rewrite Heq0, Heq1; repeat rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)); rewrite Z.add_diag; split; reflexivity. }
                  split; auto. intros Hlti Hxeqs.
                  destruct (co_xz_implies _ _ Hxeqs ltac:(unfold co_z, zdau in A3; unfold ZD; unfold z_of in *; simpl in *; destruct (testbitn i); rewrite A3; reflexivity)) as [U|U]; rewrite YY1, YY2 in U.
                  - replace (Z.to_nat (Z.succ i) - 1)%nat with (S (Z.to_nat i - 1)) in U by lia.
                    generalize (SS_sub_TT_S n' scalarbitsz (Z.to_nat i - 1)).
                    rewrite <- Htestbitn'; [|lia]. replace (Z.of_nat (S (Z.to_nat i - 1))) with i by lia.
                    intro V. assert (QQ : Weq (scalarmult (if testbitn i then (2 * SS n' (Z.to_nat i - 1))%Z else (2 * TT n' (Z.to_nat i - 1))%Z) P) Wzero).
                    { replace Wzero with (scalarmult 0 P) by reflexivity.
                      apply scalarmult_eq_weq_conversion.
                      destruct (testbitn i); rewrite <- V;
                      rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P));
                      [rewrite <- U|rewrite U];
                      rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P));
                      replace (_ - _)%Z with 0%Z by lia;
                      apply (@scalarmult_0_l point eq add zero opp scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)). }
                    generalize (SS_monotone0 n' scalarbitsz ltac:(generalize Hn'; lia) ltac:(lia) (Z.to_nat i - 1)); rewrite SS0; intro QS.
                    generalize (TT_monotone0 n' scalarbitsz ltac:(generalize Hn'; lia) ltac:(lia) (Z.to_nat i - 1)); rewrite TT0; intro QT.
                    destruct (proj1 (HordP (if testbitn i then (2 * SS n' (Z.to_nat i - 1))%Z else (2 * TT n' (Z.to_nat i - 1))%Z) ltac:(destruct (testbitn i); lia)) QQ) as [l Hl].
                    generalize (Znumtheory.prime_mult 2%Z Znumtheory.prime_2 l ordP ltac:(destruct (testbitn i); [exists (SS n' (Z.to_nat i - 1))|exists (TT n' (Z.to_nat i - 1))]; lia)).
                    intros [A|A]; destruct A as [m Hm]; [|replace ordP with (0 + 2 * m)%Z in HordPodd by lia; rewrite Z.odd_add_mul_2 in HordPodd; simpl in HordPodd; congruence].
                    subst l. assert (Hm : (if testbitn i then SS n' (Z.to_nat i - 1) else TT n' (Z.to_nat i - 1))%Z = (m * ordP)%Z :> Z) by (destruct (testbitn i); lia).
                    generalize (proj2 (HordP (if testbitn i then (SS n' (Z.to_nat i - 1))%Z else (TT n' (Z.to_nat i - 1))%Z) ltac:(destruct (testbitn i); lia)) ltac:(exists m; auto)).
                    replace (Z.to_nat i - 1)%nat with (Z.to_nat (i - 1)%Z) by lia.
                    destruct (testbitn i); [eapply HSS|eapply HTT]; lia.
                  - replace (Z.to_nat (Z.succ i) - 1)%nat with (Z.to_nat i) in U by lia.
                    generalize (SS_plus_TT n' scalarbitsz (Z.to_nat i)).
                    replace (Z.of_nat (S (Z.to_nat i))) with (Z.succ i) by lia.
                    intro V.
                    apply (mult_two_power (Z.succ i) ltac:(lia)).
                    replace Wzero with (scalarmult 0 P) by reflexivity.
                    apply scalarmult_eq_weq_conversion.
                    rewrite <- V, (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P)), U.
                    rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) _ _ (of_affine P)).
                    replace (_ - _)%Z with 0%Z by lia. reflexivity. }
              * (* measure decreases *)
                replace (if testbitn i then (X0, X1) else (X1, X0)) with (if testbitn i then X0 else X1, if testbitn i then X1 else X0) by (destruct (testbitn i); reflexivity).
                destruct (zdau_inner (if testbitn i then X0 else X1) (if testbitn i then X1 else X0)); destruct (testbitn i); unfold measure; simpl; lia.
            + (* post condition *)
              split; [split; auto|].
              simpl. rewrite Z.ltb_ge in Hltb. lia. }
        destruct WW as ((R1' & R0') & I).
        simpl in WWinv. destruct WWinv as [ [HpR1 [HpR0 [Hz [_ WWinv] ] ] ] ->].
        specialize (WWinv HpR1 HpR0). destruct WWinv as [ [HR1eq HR0eq] _].
        rewrite SSn in HR0eq; [|generalize Hn'; fold n'; lia|lia].
        replace (opp_inner (proj1_sig (of_affine P))) with (proj1_sig (opp (of_affine P))) by reflexivity.
        assert (HPaff' : z_of (opp (of_affine P)) = 1) by (destruct P as [ [ [X Y] | ?] HP] eqn:HPeq; [reflexivity|elim HPnz; clear; t]).
        pose (COZ := make_co_z (exist _ R0' HpR0) (opp (of_affine P)) HPaff').
        replace (make_co_z_inner R0' (proj1_sig (opp (of_affine P)))) with (proj1_sig (fst COZ), proj1_sig (snd COZ)) by (symmetry; unfold COZ, make_co_z; simpl; apply surjective_pairing).
        assert (HR0znz : z_of (exist is_point R0' HpR0) <> 0).
        { intro. apply (HordP_alt n').
          - apply HordPn'.
          - replace Wzero with (scalarmult 0 P) by reflexivity.
            apply scalarmult_eq_weq_conversion.
            rewrite <- HR0eq. unfold z_of in H. simpl. unfold eq, zero. simpl.
            simpl in H. destruct (dec (0 = 0)) as [?|Hnn]; [|elim Hnn; reflexivity].
            destruct R0' as ((? & ?) & ?); auto.
            destruct (dec (f2 = 0)) as [?|Hnn]; [|elim Hnn; exact H]. reflexivity. }
        destruct (@Jacobian.make_co_z_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field Feq_dec (exist is_point R0' HpR0) (opp (of_affine P)) HPaff' HR0znz) as (Heq0 & Heq1 & HCOZ).
        rewrite Heq0 in HR0eq.
        rewrite <- (@scalarmult_opp1_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup) (of_affine P)) in Heq1 at 1.
        set (ZADDU := zaddu (fst COZ) (snd COZ) HCOZ).
        replace (zaddu_inner (proj1_sig (fst COZ)) (proj1_sig (snd COZ))) with (proj1_sig (fst ZADDU), proj1_sig (snd ZADDU)) by (symmetry; unfold ZADDU, zaddu; simpl; apply surjective_pairing).
        assert (Hxne: x_of (fst COZ) <> x_of (snd COZ)).
        { intro Hxe. destruct (co_xz_implies _ _ Hxe HCOZ) as [HEq|HNeq].
          - unfold COZ in HEq.
            rewrite HR0eq in HEq.
            rewrite <- Heq1 in HEq.
            apply (HordP_alt (n' - -1)%Z).
            + rewrite n'_alt; destruct (testbitn 0); lia.
            + replace Wzero with (scalarmult 0 P) by reflexivity.
              apply scalarmult_eq_weq_conversion.
              rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              rewrite HEq.
              rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              replace (-1 - -1)%Z with 0%Z by lia. reflexivity.
          - unfold COZ in HNeq.
            rewrite HR0eq in HNeq.
            rewrite <- Heq1 in HNeq.
            apply (HordP_alt (n' - 1)%Z).
            + rewrite n'_alt; destruct (testbitn 0); lia.
            + replace Wzero with (scalarmult 0 P) by reflexivity.
              apply scalarmult_eq_weq_conversion.
              rewrite (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              rewrite HNeq.
              rewrite <- (@scalarmult_opp_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)) at 1.
              rewrite <- (@scalarmult_sub_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
              replace (- -1 - 1)%Z with 0%Z by lia. reflexivity. }
        generalize (@Jacobian.zaddu_correct F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a b field char_ge_3 Feq_dec (fst COZ) (snd COZ) HCOZ Hxne).
        fold ZADDU. rewrite (surjective_pairing ZADDU) at 1.
        intros [Heq2 [Heq3 HCOZ1] ]. rewrite Z.bit0_odd.
        replace (if Z.odd n then (proj1_sig (snd ZADDU), proj1_sig (fst ZADDU)) else (proj1_sig (fst ZADDU), proj1_sig (snd ZADDU))) with (proj1_sig (if Z.odd n then snd ZADDU else fst ZADDU), proj1_sig (if Z.odd n then fst ZADDU else snd ZADDU)) by (destruct (Z.odd n); reflexivity).
        assert (eq (if Z.odd n then snd ZADDU else fst ZADDU) (scalarmult' n (of_affine P))); auto.
        rewrite n'_alt, Z.bit0_odd in HR0eq.
        destruct (Z.odd n); fold COZ in Heq0, Heq1, HR0eq.
        - rewrite <- Heq3, HR0eq. reflexivity.
        - rewrite <- Heq2, HR0eq, <- Heq1.
          rewrite <- (@scalarmult_add_l point eq add zero opp Pgroup scalarmult' (@scalarmult_ref_is_scalarmult _ _ _ _ _ Pgroup)).
          replace (n + 1 + -1)%Z with n by lia. reflexivity.
      Qed.

      Lemma joye_ladder_correct :
        Weq (joye_ladder scalarbitsz testbitn P HPnz) (scalarmult n P).
      Proof.
        rewrite <- (Jacobian.to_affine_of_affine (scalarmult n P)).
        apply Jacobian.Proper_to_affine. rewrite scalarmult_scalarmult'.
        eapply joye_inner_correct.
      Qed.
    End Proofs.
  End JoyeLadder.
End ScalarMult.

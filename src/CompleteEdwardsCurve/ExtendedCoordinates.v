Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.FField.
Require Import Crypto.Tactics.VerdiTactics.
Local Open Scope F_scope.

Section ExtendedCoordinates.
  Context {prm:TwistedEdwardsParams}.
  Local Opaque q a d prime_q two_lt_q nonzero_a square_a nonsquare_d. (* [F_field] calls [compute] *)
  Existing Instance prime_q.

  Add Field Ffield_p' : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

  Add Field Ffield_notConstant : (OpaqueFieldTheory q)
    (constants [notConstant]). 

  (** [extended] represents a point on an elliptic curve using extended projective
  * Edwards coordinates with twist a=-1 (see <https://eprint.iacr.org/2008/522.pdf>). *)
  Record extended := mkExtended {extendedX : F q;
                                 extendedY : F q;
                                 extendedZ : F q;
                                 extendedT : F q}.
  Local Notation "'(' X ',' Y ',' Z ',' T ')'" := (mkExtended X Y Z T).

  Definition twistedToExtended (P : (F q*F q)) : extended :=
    let '(x, y) := P in (x, y, 1, x*y).
  Definition extendedToTwisted (P : extended) : F q * F q :=
    let '(X, Y, Z, T) := P in ((X/Z), (Y/Z)).
  Definition rep (P:extended) (rP:(F q*F q)) : Prop :=
    let '(X, Y, Z, T) := P in
    extendedToTwisted P = rP /\
    Z <> 0 /\
    T = X*Y/Z.
  Local Hint Unfold twistedToExtended extendedToTwisted rep.
  Local Notation "P '~=' rP" := (rep P rP) (at level 70).

  Ltac unfoldExtended := 
    repeat progress (autounfold; unfold onCurve, unifiedAdd, unifiedAdd', rep in *; intros); 
    repeat match goal with
      | [ p : (F q*F q)%type |- _ ] =>
          let x := fresh "x" p in
          let y := fresh "y" p in
          destruct p as [x y]
      | [ p : extended |- _ ] =>
          let X := fresh "X" p in
          let Y := fresh "Y" p in
          let Z := fresh "Z" p in
          let T := fresh "T" p in
          destruct p as [X Y Z T]
      | [ H: _ /\ _ |- _ ] => destruct H
      | [ H: @eq (F q * F q)%type _ _ |- _ ] => invcs H
      | [ H: @eq F q ?x _ |- _ ] => isVar x; rewrite H; clear H
  end.
  
  Ltac solveExtended := unfoldExtended;
    repeat match goal with
      | [ |- _ /\ _ ] => split
      | [ |- @eq (F q * F q)%type _ _] => apply f_equal2
      | _ => progress rewrite ?@F_add_0_r, ?@F_add_0_l, ?@F_sub_0_l, ?@F_sub_0_r,
           ?@F_mul_0_r, ?@F_mul_0_l, ?@F_mul_1_l, ?@F_mul_1_r, ?@F_div_1_r
      | _ => solve [eapply @Fq_1_neq_0; eauto with typeclass_instances]
      | _ => solve [eauto with typeclass_instances]
      | [ H: a = _ |- _ ] => rewrite H
  end.

  Lemma twistedToExtended_rep : forall P, twistedToExtended P ~= P.
  Proof.
    solveExtended.
  Qed.

  Lemma extendedToTwisted_rep : forall P rP, P ~= rP -> extendedToTwisted P = rP.
  Proof.
    solveExtended.
  Qed.

  Section TwistMinus1.
    Context (a_eq_minus1 : a = opp 1).
    (** Second equation from <http://eprint.iacr.org/2008/522.pdf> section 3.1, also <https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#addition-add-2008-hwcd-3> and <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
    Definition unifiedAddM1 (P1 P2 : extended) : extended :=
      let '(X1, Y1, Z1, T1) := P1 in
      let '(X2, Y2, Z2, T2) := P2 in
      let  A := (Y1-X1)*(Y2-X2) in
      let  B := (Y1+X1)*(Y2+X2) in
      let  C := T1*ZToField 2*d*T2 in
      let  D := Z1*ZToField 2  *Z2 in
      let  E := B-A in
      let  F := D-C in
      let  G := D+C in
      let  H := B+A in
      let X3 := E*F in
      let Y3 := G*H in
      let T3 := E*H in
      let Z3 := F*G in
      (X3, Y3, Z3, T3).
    Local Hint Unfold unifiedAdd.

    Lemma unifiedAdd_repM1: forall P Q rP rQ, onCurve rP -> onCurve rQ ->
      P ~= rP -> Q ~= rQ -> (unifiedAddM1 P Q) ~= (unifiedAdd' rP rQ).
    Proof.
      intros P Q rP rQ HoP HoQ HrP HrQ.
      pose proof (@edwardsAddCompletePlus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d).
      pose proof (@edwardsAddCompleteMinus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d).
      unfoldExtended; rewrite a_eq_minus1 in *; simpl in *.
        repeat split; repeat apply (f_equal2 pair); try F_field; repeat split; auto;
        repeat rewrite ?F_add_0_r, ?F_add_0_l, ?F_sub_0_l, ?F_sub_0_r,
           ?F_mul_0_r, ?F_mul_0_l, ?F_mul_1_l, ?F_mul_1_r, ?F_div_1_r.

    Ltac tnz := repeat apply Fq_mul_nonzero_nonzero; auto using (@char_gt_2 q two_lt_q).
    (* If we we had reasoning modulo associativity and commutativity,
    *  the following tactic would probably solve all remaining goals here:
    repeat match goal with [H1: @eq (F p) _ _, H2: @eq (F p) _ _ |- _ ] =>
      let H := fresh "H" in ( 
        pose proof (edwardsAddCompletePlus _ _ _ _ H1 H2) as H;
        match type of H with ?xs <> 0 => ac_rewrite (eq_refl xs) end
      ) || (
        pose proof (edwardsAddCompleteMinus _ _ _ _ H1 H2) as H;
        match type of H with ?xs <> 0 => ac_rewrite (eq_refl xs) end
      ); tnz
    end. *)

      - replace (ZP * ZQ * ZP * ZQ + d * XP * XQ * YP * YQ) with (ZQ*ZQ*ZP*ZP* (1 + d * (XQ / ZQ) * (XP / ZP) * (YQ / ZQ) * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZToField 2 * ZQ * (ZP * ZQ)  + XP * YP * ZToField 2 * d * (XQ * YQ)) with (ZToField 2*ZQ*ZQ*ZP*ZP* (1 + d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZToField 2 * ZQ * (ZP * ZQ)  - XP * YP * ZToField 2 * d * (XQ * YQ)) with (ZToField 2*ZQ*ZQ*ZP*ZP* (1 - d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZQ * ZP * ZQ - d * XP * XQ * YP * YQ) with (ZQ*ZQ*ZP*ZP* (1 - d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZToField 2 * ZQ * (ZP * ZQ)  + XP * YP * ZToField 2 * d * (XQ * YQ)) with (ZToField 2*ZQ*ZQ*ZP*ZP* (1 + d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZToField 2 * ZQ * (ZP * ZQ)  - XP * YP * ZToField 2 * d * (XQ * YQ)) with (ZToField 2*ZQ*ZQ*ZP*ZP* (1 - d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZToField 2 * ZQ - XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ) ) with (ZToField 2*ZQ*ZP* (1 - d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
        replace (ZP * ZToField 2 * ZQ + XP * YP / ZP * ZToField 2 * d * (XQ * YQ / ZQ) ) with (ZToField 2*ZQ*ZP* (1 + d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZToField 2 * ZQ * (ZP * ZQ)  + XP * YP * ZToField 2 * d * (XQ * YQ)) with (ZToField 2*ZQ*ZQ*ZP*ZP* (1 + d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
      - replace (ZP * ZToField 2 * ZQ * (ZP * ZQ)  - XP * YP * ZToField 2 * d * (XQ * YQ)) with (ZToField 2*ZQ*ZQ*ZP*ZP* (1 - d * (XQ / ZQ)  * (XP / ZP) * (YQ / ZQ)  * (YP / ZP))) by (field; tnz); tnz.
    Qed.
  End TwistMinus1.
End ExtendedCoordinates.
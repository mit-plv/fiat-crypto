Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Tactics.VerdiTactics.

Section ExtendedCoordinates.
  Local Open Scope F_scope.
  Context {prm:TwistedEdwardsParams}.
  Existing Instance prime_q.

  Add Field GFfield_Z : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 


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

  Ltac extended_tac :=
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
      | [ |- _ /\ _ ] => split
      | [ H: @eq (F q * F q)%type _ _ |- _ ] => invcs H
      | [ H: @eq F q ?x _ |- _ ] => isVar x; rewrite H; clear H
      | [ |- @eq (F q * F q)%type _ _] => apply f_equal2
      | _ => progress rewrite ?F_add_0_r, ?F_add_0_l, ?F_sub_0_l, ?F_sub_0_r,
           ?F_mul_0_r, ?F_mul_0_l, ?F_mul_1_l, ?F_mul_1_r, ?F_div_1_r
      | _ => progress eauto using Fq_1_neq_0
      | [ H: a = _ |- _ ] => rewrite H
      | [ |- @eq (F q) _ _] => fail; field (*FIXME*)
  end.

  Lemma twistedToExtended_rep : forall P, twistedToExtended P ~= P.
  Proof.
    extended_tac.
  Qed.

  Lemma extendedToTwisted_rep : forall P rP, P ~= rP -> extendedToTwisted P = rP.
  Proof.
    extended_tac.
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
      pose proof (@edwardsAddCompletePlus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d) as HoR; simpl in HoR.
      extended_tac.
      field.

      (* If we we had reasoning modulo associativity and commutativity,
      *  the following tactic would probably solve all 10 goals here:
      repeat match goal with [H1: @eq GF _ _, H2: @eq GF _ _ |- _ ] =>
        let H := fresh "H" in ( 
          pose proof (edwardsAddCompletePlus _ _ _ _ H1 H2) as H;
          match type of H with ?xs <> 0 => ac_rewrite (eq_refl xs) end
        ) || (
          pose proof (edwardsAddCompleteMinus _ _ _ _ H1 H2) as H;
          match type of H with ?xs <> 0 => ac_rewrite (eq_refl xs) end
        ); repeat apply mul_nonzero_nonzero; auto 10
      end.
      *)

      - replace (Z0 * Z * Z0 * Z + d * X0 * X * Y0 * Y) with (Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * inject 2 * Z * (Z0 * Z) + X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * inject 2 * Z * (Z0 * Z) - X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * Z * Z0 * Z - d * X0 * X * Y0 * Y) with (Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * inject 2 * Z * (Z0 * Z) + X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * inject 2 * Z * (Z0 * Z) - X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * Z * Z0 * Z - d * X0 * X * Y0 * Y) with (Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto).
      repeat apply mul_nonzero_nonzero.
        + replace (Z0 * 2 * Z - X0 * Y0 / Z0 * 2 * d * (X * Y / Z)) with (2*Z*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
        + replace (Z0 * 2 * Z + X0 * Y0 / Z0 * 2 * d * (X * Y / Z)) with (2*Z*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * inject 2 * Z * (Z0 * Z) + X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      - replace (Z0 * inject 2 * Z * (Z0 * Z) - X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    Qed.
End ExtendedCoordinates.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.FField.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Util.IterAssocOp BinNat NArith.
Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms Coq.Classes.Equivalence.
Local Open Scope equiv_scope.
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
    repeat progress (autounfold; unfold E.onCurve, E.add, E.add', rep in *; intros);
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

  Definition extendedPoint := { P:extended | rep P (extendedToTwisted P) /\ E.onCurve (extendedToTwisted P) }.

  Program Definition mkExtendedPoint : E.point -> extendedPoint := twistedToExtended.
  Next Obligation.
    destruct x; erewrite extendedToTwisted_rep; eauto using twistedToExtended_rep.
  Qed.

  Program Definition unExtendedPoint : extendedPoint -> E.point := extendedToTwisted.
  Next Obligation.
    destruct x; simpl; intuition.
  Qed.

  Definition extendedPoint_eq P Q := unExtendedPoint P = unExtendedPoint Q.
  Global Instance Equivalence_extendedPoint_eq : Equivalence extendedPoint_eq.
  Proof.
    repeat (econstructor || intro); unfold extendedPoint_eq in *; congruence.
  Qed.

  Lemma unExtendedPoint_mkExtendedPoint : forall P, unExtendedPoint (mkExtendedPoint P) = P.
  Proof.
    destruct P; eapply E.point_eq; simpl; erewrite extendedToTwisted_rep; eauto using twistedToExtended_rep.
  Qed.

  Global Instance Proper_mkExtendedPoint : Proper (eq==>equiv) mkExtendedPoint.
  Proof.
    repeat (econstructor || intro); unfold extendedPoint_eq in *; congruence.
  Qed.

  Global Instance Proper_unExtendedPoint : Proper (equiv==>eq) unExtendedPoint.
  Proof.
    repeat (econstructor || intro); unfold extendedPoint_eq in *; congruence.
  Qed.

  Section TwistMinus1.
    Context (a_eq_minus1 : a = opp 1).
    (** Second equation from <http://eprint.iacr.org/2008/522.pdf> section 3.1, also <https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#addition-add-2008-hwcd-3> and <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
    Definition unifiedAddM1' (P1 P2 : extended) : extended :=
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
    Local Hint Unfold E.add.

    Local Ltac tnz := repeat apply Fq_mul_nonzero_nonzero; auto using (@char_gt_2 q two_lt_q).

    Lemma unifiedAddM1'_rep: forall P Q rP rQ, E.onCurve rP -> E.onCurve rQ ->
      P ~= rP -> Q ~= rQ -> (unifiedAddM1' P Q) ~= (E.add' rP rQ).
    Proof.
      intros P Q rP rQ HoP HoQ HrP HrQ.
      pose proof (@edwardsAddCompletePlus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d).
      pose proof (@edwardsAddCompleteMinus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d).
      unfoldExtended; rewrite a_eq_minus1 in *; simpl in *.
        repeat split; repeat apply (f_equal2 pair); try F_field; repeat split; auto;
        repeat rewrite ?F_add_0_r, ?F_add_0_l, ?F_sub_0_l, ?F_sub_0_r,
           ?F_mul_0_r, ?F_mul_0_l, ?F_mul_1_l, ?F_mul_1_r, ?F_div_1_r;
        field_nonzero tnz.
    Qed.

    Lemma unifiedAdd'_onCurve : forall P Q, E.onCurve P -> E.onCurve Q -> E.onCurve (E.add' P Q).
    Proof.
      intros; pose proof (proj2_sig (E.add (exist _ _ H) (exist _ _ H0))); eauto.
    Qed.

    Program Definition unifiedAddM1 : extendedPoint -> extendedPoint -> extendedPoint := unifiedAddM1'.
    Next Obligation.
      destruct x, x0; simpl; intuition.
      - erewrite extendedToTwisted_rep; eauto using unifiedAddM1'_rep.
      - erewrite extendedToTwisted_rep.
        (* It would be nice if I could use eauto here, but it gets evars wrong :( *)
        2: eapply unifiedAddM1'_rep. 5:apply H1. 4:apply H. 3:auto. 2:auto.
        eauto using unifiedAdd'_onCurve.
    Qed.

    Lemma unifiedAddM1_rep : forall P Q, E.add (unExtendedPoint P) (unExtendedPoint Q) = unExtendedPoint (unifiedAddM1 P Q).
    Proof.
      destruct P, Q; unfold unExtendedPoint, E.add, unifiedAddM1; eapply E.point_eq; simpl in *; intuition.
      pose proof (unifiedAddM1'_rep x x0 (extendedToTwisted x) (extendedToTwisted x0));
        destruct (unifiedAddM1' x x0);
        unfold rep in *; intuition.
    Qed.

    Global Instance Proper_unifiedAddM1 : Proper (equiv==>equiv==>equiv) unifiedAddM1.
    Proof.
      repeat (econstructor || intro).
      repeat match goal with [H: _ === _ |- _ ] => inversion H; clear H end; unfold equiv, extendedPoint_eq.
      rewrite <-!unifiedAddM1_rep.
      destruct x, y, x0, y0; simpl in *; eapply E.point_eq; congruence.
    Qed.

    Lemma unifiedAddM1_0_r : forall P, unifiedAddM1 P (mkExtendedPoint E.zero) === P.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, unExtendedPoint_mkExtendedPoint, E.add_0_r; auto.
    Qed.

    Lemma unifiedAddM1_0_l : forall P, unifiedAddM1 (mkExtendedPoint E.zero) P === P.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, E.add_comm, unExtendedPoint_mkExtendedPoint, E.add_0_r; auto.
    Qed.

    Lemma unifiedAddM1_assoc : forall a b c, unifiedAddM1 a (unifiedAddM1 b c) === unifiedAddM1 (unifiedAddM1 a b) c.
    Proof.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, E.add_assoc; auto.
    Qed.

    Lemma testbit_conversion_identity : forall x i, N.testbit_nat x i = N.testbit_nat ((fun a => a) x) i.
    Proof.
      trivial.
    Qed.

    Definition scalarMultM1 := iter_op unifiedAddM1 (mkExtendedPoint E.zero) N.testbit_nat.
    Definition scalarMultM1_spec :=
      iter_op_spec unifiedAddM1 unifiedAddM1_assoc (mkExtendedPoint E.zero) unifiedAddM1_0_l
        N.testbit_nat (fun x => x) testbit_conversion_identity.
    Lemma scalarMultM1_rep : forall n P, unExtendedPoint (scalarMultM1 (N.of_nat n) P (N.size_nat (N.of_nat n))) = E.mul n (unExtendedPoint P).
      intros; rewrite scalarMultM1_spec, Nat2N.id; auto.
      induction n; [simpl; rewrite !unExtendedPoint_mkExtendedPoint; reflexivity|].
      unfold E.mul; fold E.mul.
      rewrite <-IHn, unifiedAddM1_rep; auto.
    Qed.

  End TwistMinus1.

End ExtendedCoordinates.

Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.AffineProofs.

Require Import Crypto.Util.Notations Crypto.Util.GlobalSettings.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.

Section ExtendedCoordinates.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two)}
          {Feq_dec:DecidableRel Feq}.
  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "*" := Fmul.
  Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x).

  Context {a d: F}
          {nonzero_a : a <> 0}
          {square_a : exists sqrt_a, sqrt_a^2 = a}
          {nonsquare_d : forall x, x^2 <> d}.
  Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul a d).
  Local Notation Eadd := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).

  Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).
  (** [Extended.point] represents a point on an elliptic curve using extended projective
   * Edwards coordinates 1 (see <https://eprint.iacr.org/2008/522.pdf>). *)
  Definition point := { P | let '(X,Y,Z,Ta,Tb) := P in
                            a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2
                            /\ X * Y = Z * Ta * Tb
                            /\ Z <> 0 }.
  Definition coordinates (P:point) : F*F*F*F*F := proj1_sig P.
  Definition eq (P1 P2:point) :=
    let '(X1, Y1, Z1, _, _) := coordinates P1 in
    let '(X2, Y2, Z2, _, _) := coordinates P2 in
    Z2*X1 = Z1*X2 /\ Z2*Y1 = Z1*Y2.

  Ltac t_step :=
    match goal with
    | |- Proper _ _ => intro
    | _ => progress intros
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' @E.point
    | _ => progress destruct_head' point
    | _ => progress destruct_head' and
    | _ => progress cbv [eq CompleteEdwardsCurve.E.eq E.eq E.zero E.add E.opp fst snd coordinates E.coordinates proj1_sig] in *
    | |- _ /\ _ => split | |- _ <-> _ => split
    end.
  Ltac t := repeat t_step; try Field.fsatz.

  Global Instance Equivalence_eq : Equivalence eq.
  Proof using Feq_dec field nonzero_a. split; repeat intro; t. Qed.
  Global Instance DecidableRel_eq : Decidable.DecidableRel eq.
  Proof. intros P Q; destruct P as [ [ [ [ ] ? ] ? ] ?], Q as [ [ [ [ ] ? ] ? ] ? ]; exact _. Defined.

  Program Definition from_twisted (P:Epoint) : point :=
    let xy := E.coordinates P in (fst xy, snd xy, 1, fst xy, snd xy).
  Next Obligation. t. Qed.
  Global Instance Proper_from_twisted : Proper (E.eq==>eq) from_twisted.
  Proof using Type. cbv [from_twisted]; t. Qed.

  Program Definition to_twisted (P:point) : Epoint :=
    let XYZTT := coordinates P in let Ta := snd XYZTT in
                                  let XYZT  := fst XYZTT in
                                  let Tb := snd XYZT in
                                  let XYZ := fst XYZT in      let Z := snd XYZ in
                                                              let XY   := fst XYZ in       let Y := snd XY in
                                                                                           let X    := fst XY in
                                                                                           let iZ := Finv Z in ((X*iZ), (Y*iZ)).
  Next Obligation. t. Qed.
  Global Instance Proper_to_twisted : Proper (eq==>E.eq) to_twisted.
  Proof using Type. cbv [to_twisted]; t. Qed.

  Lemma to_twisted_from_twisted P : E.eq (to_twisted (from_twisted P)) P.
  Proof using Type. cbv [to_twisted from_twisted]; t. Qed.
  Lemma from_twisted_to_twisted P : eq (from_twisted (to_twisted P)) P.
  Proof using Type. cbv [to_twisted from_twisted]; t. Qed.

  Program Definition zero : point := (0, 1, 1, 0, 1).
  Next Obligation. t. Qed.

  Program Definition opp P : point :=
    match coordinates P return F*F*F*F*F with (X,Y,Z,Ta,Tb) => (Fopp X, Y, Z, Fopp Ta, Tb) end.
  Next Obligation. t. Qed.

  Section TwistMinusOne.
    Context {a_eq_minus1:a = Fopp 1} {twice_d} {k_eq_2d:twice_d = d+d}.
    Program Definition m1add
            (P1 P2:point) : point :=
      match coordinates P1, coordinates P2 return F*F*F*F*F with
        (X1, Y1, Z1, Ta1, Tb1), (X2, Y2, Z2, Ta2, Tb2) =>
        let A := (Y1-X1)*(Y2-X2) in
        let B := (Y1+X1)*(Y2+X2) in
        let C := (Ta1*Tb1)*twice_d*(Ta2*Tb2) in
        let D := Z1*(Z2+Z2) in
        let E := B-A in
        let F := D-C in
        let G := D+C in
        let H := B+A in
        let X3 := E*F in
        let Y3 := G*H in
        let Z3 := F*G in
        (X3, Y3, Z3, E, H)
      end.
    Next Obligation.
      match goal with
      | [ |- match (let (_, _) := coordinates ?P1 in let (_, _) := _ in let (_, _) := _ in let (_, _) := _ in let (_, _) := coordinates ?P2 in _) with _ => _ end ]
        => pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _ (proj2_sig (to_twisted P1))  _ _  (proj2_sig (to_twisted P2)))
      end; t.
    Qed.

    Global Instance isomorphic_commutative_group_m1 :
      @Group.isomorphic_commutative_groups
        Epoint E.eq
        Eadd
        (E.zero(nonzero_a:=nonzero_a))
        (E.opp(nonzero_a:=nonzero_a))
        point eq m1add zero opp
        from_twisted to_twisted.
    Proof.
      eapply Group.commutative_group_by_isomorphism; try exact _.
      par: abstract
             (cbv [to_twisted from_twisted zero opp m1add]; intros;
              repeat match goal with
                     | |- context[E.add ?P ?Q] =>
                       unique pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q)) end;
              t).
    Qed.

    Lemma to_twisted_m1add P Q : E.eq (to_twisted (m1add P Q)) (Eadd (to_twisted P) (to_twisted Q)).
    Proof. pose proof isomorphic_commutative_group_m1 as H; destruct H as [ [] [] [] [] ]; trivial. Qed.

    Program Definition m1double (P : point) : point :=
      match coordinates P return F*F*F*F*F with
        (X, Y, Z, _, _) =>
        let trX := X^2 in
        let trZ := Y^2 in
        let trT := (let t0 := Z^2 in t0+t0) in
        let rY := X+Y in
        let t0 := rY^2 in
        let cY := trZ+trX in
        let cZ := trZ-trX in
        let cX := t0-cY in
        let cT := trT-cZ in
        let X3 := cX*cT in
        let Y3 := cY*cZ in
        let Z3 := cZ*cT in
        (X3, Y3, Z3, cX, cY)
      end.
    Next Obligation.
      match goal with
      | [ |- context [let (_, _) := coordinates ?P in _] ]
        => pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _ (proj2_sig (to_twisted P))  _ _  (proj2_sig (to_twisted P)))
      end; t.
    Qed.

    Lemma m1double_correct P : eq (m1double P) (m1add P P).
    Proof. intros; progress destruct_head' @point; cbv [m1add m1double]; t. Qed.

    Lemma to_twisted_m1double P : E.eq (to_twisted (m1double P)) (Eadd (to_twisted P) (to_twisted P)).
    Proof. setoid_rewrite m1double_correct; trivial. eapply to_twisted_m1add. Qed.
  End TwistMinusOne.

  (* https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#doubling-double-2008-hwcd *)
  Program Definition double (P : point) : point :=
    match coordinates P return F*F*F*F*F with
      (X1, Y1, Z1, _, _) =>
      let A := X1^2 in
      let B := Y1^2 in
      let t0 := Z1^2 in
      let C := t0+t0 in
      let D := a*A in
      let t1 := X1+Y1 in
      let t2 := t1^2 in
      let t3 := t2-A in
      let E := t3-B in
      let G := D+B in
      let F := G-C in
      let H := D-B in
      let X3 := E*F in
      let Y3 := G*H in
      let Z3 := F*G in
      (X3, Y3, Z3, E, H)
    end.
  Next Obligation.
    match goal with
    | [ |- context [let (_, _) := coordinates ?P in _] ]
      => pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _ (proj2_sig (to_twisted P))  _ _  (proj2_sig (to_twisted P)))
    end; t.
  Qed.

  Lemma to_twisted_double P : E.eq (to_twisted (double P)) (Eadd (to_twisted P) (to_twisted P)).
  Proof.
    cbv beta delta [double].
    match goal with
    | [ |- context [let (_, _) := coordinates ?P in _] ]
      => pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _ (proj2_sig (to_twisted P))  _ _  (proj2_sig (to_twisted P)))
    end; progress destruct_head' @point; cbv [E.add double to_twisted]; t. Qed.
End ExtendedCoordinates.

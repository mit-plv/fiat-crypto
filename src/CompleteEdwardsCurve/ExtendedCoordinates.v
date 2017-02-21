Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.

Require Import Crypto.Algebra Crypto.Algebra.
Require Import Crypto.Util.Notations Crypto.Util.GlobalSettings.
Require Export Crypto.Util.FixCoqMistakes Crypto.Util.Tactics.

Module Extended.
  Section ExtendedCoordinates.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_gt_2 : @Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.one)}
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

    Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).
    (** [Extended.point] represents a point on an elliptic curve using extended projective
     * Edwards coordinates 1 (see <https://eprint.iacr.org/2008/522.pdf>). *)
    Definition point := { P | let '(X,Y,Z,T) := P in
                              a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2
                              /\ X * Y = Z * T
                              /\ Z <> 0 }.
    Definition coordinates (P:point) : F*F*F*F := proj1_sig P.
    Definition eq (P1 P2:point) :=
        let '(X1, Y1, Z1, _) := coordinates P1 in
        let '(X2, Y2, Z2, _) := coordinates P2 in
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
    Ltac t := repeat t_step; Field.fsatz.

    Global Instance Equivalence_eq : Equivalence eq.
    Proof. split; repeat intro; t. Qed.
    Global Instance DecidableRel_eq : Decidable.DecidableRel eq.
    Proof. intros P Q; destruct P as [ [ [ [ ] ? ] ? ] ?], Q as [ [ [ [ ] ? ] ? ] ? ]; exact _. Defined.

    Program Definition from_twisted (P:Epoint) : point :=
      let xy := E.coordinates P in (fst xy, snd xy, 1, fst xy * snd xy).
    Next Obligation. t. Qed.
    Global Instance Proper_from_twisted : Proper (E.eq==>eq) from_twisted.
    Proof. cbv [from_twisted]; t. Qed.

    Program Definition to_twisted (P:point) : Epoint := 
      let XYZT := coordinates P in let T := snd XYZT in
      let XYZ  := fst XYZT in      let Z := snd XYZ in
      let XY   := fst XYZ in       let Y := snd XY in
      let X    := fst XY in
      let iZ := Finv Z in ((X*iZ), (Y*iZ)).
    Next Obligation. t. Qed.
    Global Instance Proper_to_twisted : Proper (eq==>E.eq) to_twisted.
    Proof. cbv [to_twisted]; t. Qed.

    Lemma to_twisted_from_twisted P : E.eq (to_twisted (from_twisted P)) P.
    Proof. cbv [to_twisted from_twisted]; t. Qed.
    Lemma from_twisted_to_twisted P : eq (from_twisted (to_twisted P)) P.
    Proof. cbv [to_twisted from_twisted]; t. Qed.

    Program Definition zero : point := (0, 1, 1, 0).
    Next Obligation. t. Qed.

    Program Definition opp P : point :=
      match coordinates P return F*F*F*F with (X,Y,Z,T) => (Fopp X, Y, Z, Fopp T) end.
    Next Obligation. t. Qed.

    Section TwistMinusOne.
      Context {a_eq_minus1:a = Fopp 1} {twice_d} {k_eq_2d:twice_d = d+d}.
      Program Definition m1add
              (P1 P2:point) : point :=
        match coordinates P1, coordinates P2 return F*F*F*F with
          (X1, Y1, Z1, T1), (X2, Y2, Z2, T2) =>
          let A := (Y1-X1)*(Y2-X2) in
          let B := (Y1+X1)*(Y2+X2) in
          let C := T1*twice_d*T2 in
          let D := Z1*(Z2+Z2) in
          let E := B-A in
          let F := D-C in
          let G := D+C in
          let H := B+A in
          let X3 := E*F in
          let Y3 := G*H in
          let T3 := E*H in
          let Z3 := F*G in
          (X3, Y3, Z3, T3)
        end.
      Next Obligation. pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _ (proj2_sig (to_twisted P1))  _ _  (proj2_sig (to_twisted P2))); t. Qed.

      Program Definition _group_proof nonzero_a' square_a' nonsquare_d' : group /\ _ /\ _ :=
                 @Group.group_from_redundant_representation
                   _ _ _ _ _
                   ((E.edwards_curve_abelian_group(a:=a)(d:=d)(nonzero_a:=nonzero_a')(square_a:=square_a')
                                                  (nonsquare_d:=nonsquare_d')).(abelian_group_group))
                   _
                   eq
                   m1add
                   zero
                   opp
                   from_twisted
                   to_twisted
                   to_twisted_from_twisted
                   _ _ _ _.
      Next Obligation. cbv [to_twisted]. t. Qed.
      Next Obligation.
        match goal with
        | |- context[E.add ?P ?Q] =>
          unique pose proof (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q))
        end. cbv [to_twisted m1add]. t. Qed.
      Next Obligation. cbv [to_twisted opp]. t. Qed.
      Next Obligation. cbv [to_twisted zero]. t. Qed.
      Global Instance group x y z
        : group := proj1 (_group_proof x y z).
      Global Instance homomorphism_from_twisted x y z :
        Monoid.is_homomorphism := proj1 (proj2 (_group_proof x y z)).
      Global Instance homomorphism_to_twisted x y z :
        Monoid.is_homomorphism := proj2 (proj2 (_group_proof x y z)).
    End TwistMinusOne.
  End ExtendedCoordinates.
End Extended.

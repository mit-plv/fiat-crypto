Require Import Crypto.Util.Decidable Crypto.Util.Notations Crypto.Algebra.Hierarchy.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.XYZT.Basic.
Require Import Coq.Classes.Morphisms.

Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Prod.
Require Import Crypto.Algebra.Field.

Section ExtendedCoordinates.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two)}
          {Feq_dec:DecidableRel Feq}.

  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero.  Local Notation "1" := Fone. Local Notation "2" := (Fadd 1 1).
  Local Infix "+" := Fadd. Local Infix "*" := Fmul.
  Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x).

  Context {a d: F}
          {nonzero_a : a <> 0}
          {square_a : exists sqrt_a, sqrt_a^2 = a}
          {nonsquare_d : forall x, x^2 <> d}.
  Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul a d).

  Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).
  Definition precomputed_point : Type := F*F*F. (* (y+x)/2, (y-x)/2, dxy *)

  Definition of_twisted (P:Epoint) :=
    let '(x, y) := E.coordinates P in
    ((y+x)/2, (y-x)/2, x*y*d).

  Section TwistMinusOne.
    Context {a_eq_minus1:a = Fopp 1}.
    (* https://hyperelliptic.org/EFD/g1p/data/twisted/extended-1/addition/madd-2008-hwcd-3,
       but with halved precomputed coordinates (making D unnecessary) *)
    Definition m1add_precomputed_coordinates (P:F*F*F*F*F) (Q:precomputed_point) : F*F*F*F*F :=
    let '(X1, Y1, Z1, Ta, Tb) := P in
    let '(half_ypx, half_ymx, xyd) := Q in
    let YpX1 := Y1+X1 in
    let YmX1 := Y1-X1 in
    let A := YmX1*half_ymx in
    let B := YpX1*half_ypx in
    let T1 := Ta*Tb in
    let C := xyd*T1 in (* = T1*2d*T2, since Z2=1 so T2=X2*Y2 *)
    let E := B-A in
    let F := Z1-C in
    let G := Z1+C in
    let H := B+A in
    (* X/Z, Y/Z = x, y *)
    let X3 := E*F in
    let Y3 := G*H in
    let Z3 := F*G in
    (* Leave T split in two parts *)
    (X3, Y3, Z3, E, H).

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold XYZT.Basic.point XYZT.Basic.coordinates XYZT.Basic.from_twisted XYZT.Basic.m1add
         E.point E.coordinates m1add_precomputed_coordinates of_twisted precomputed_point : points_as_coordinates.
    Local Notation m1add := (Basic.m1add(nonzero_a:=nonzero_a)(square_a:=square_a)(a_eq_minus1:=a_eq_minus1)(nonsquare_d:=nonsquare_d)(k_eq_2d:=reflexivity _)).
    Local Notation XYZT_of_twisted := (Basic.from_twisted(nonzero_a:=nonzero_a)(d:=d)).
    Lemma m1add_precomputed_coordinates_correct P Q :
      let '(X1, Y1, Z1, Ta1, Tb1) := m1add_precomputed_coordinates (XYZT.Basic.coordinates P) (of_twisted Q) in
      let '(X2, Y2, Z2, _, _) := coordinates (m1add P (XYZT_of_twisted Q)) in
            Z2*X1 = Z1*X2 /\ Z2*Y1 = Z1*Y2 /\ X1*Y1 = Z1*Ta1*Tb1.
    Proof.
      repeat match goal with
             | _ => progress autounfold with points_as_coordinates in *
             | _ => progress destruct_head' @prod
             | _ => progress destruct_head' @sig
             | _ => progress destruct_head' @and
             | _ => progress cbv [proj1_sig fst snd]
             | |- _ /\ _ => split
             end; fsatz.
    Qed.

  End TwistMinusOne.
End ExtendedCoordinates.

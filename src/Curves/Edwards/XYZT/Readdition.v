Require Import Coq.Classes.Morphisms.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.AffineProofs.
Require Import Crypto.Curves.Edwards.XYZT.Basic.

Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Notations Crypto.Util.GlobalSettings.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.

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
  Local Notation Eadd := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).

  Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2) (only parsing).

  (* Match this context to the Basic.ExtendedCoordinates context *)
  Local Notation point := (point(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(d:=d)).
  Local Notation coordinates := (coordinates(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(d:=d)).
  Context {a_eq_minus1:a = Fopp 1} {twice_d} {k_eq_2d:twice_d = d+d}.
  Local Notation m1add := (m1add(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fone:=Fone)(Fopp:=Fopp)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)(Finv:=Finv)(Fdiv:=Fdiv)(field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=Feq_dec)(a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)(a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)).

  (* Stolen from Basic; should be a way to reuse instead? *)
  Ltac t_step :=
    match goal with
    | |- Proper _ _ => intro
    | _ => progress intros
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' @E.point
    | _ => progress destruct_head' @Basic.point
    | _ => progress destruct_head' and
    | _ => progress cbv [eq CompleteEdwardsCurve.E.eq E.eq E.zero E.add E.opp fst snd coordinates E.coordinates proj1_sig] in *
    | |- _ /\ _ => split | |- _ <-> _ => split
    end.
  Ltac t := repeat t_step; try Field.fsatz.

  (* Define a new cached point type *)
  Definition cached :=
    { C | let '(half_YmX,half_YpX,Z,Td) := C in
          let X := half_YpX - half_YmX in
          let Y := half_YpX + half_YmX in
          let T := Td * (Finv d) in
            a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2
            /\ X * Y = Z * T
            /\ Z <> 0 }.
  Definition cached_coordinates (C:cached) : F*F*F*F := proj1_sig C.

  Program Definition m1_prep (P : F*F*F*F*F) : F*F*F*F :=
      match P with
        (X, Y, Z, Ta, Tb) =>
        let half_YmX := (Y-X)/2 in
        let half_YpX := (Y+X)/2 in
        let Td := Ta*Tb*d in
        (half_YmX, half_YpX, Z, Td)
      end.

  Program Definition m1_readd
      (P1 : F*F*F*F*F) (C : F*F*F*F) : F*F*F*F*F :=
    match P1, C with
      (X1, Y1, Z1, Ta1, Tb1), (half_YmX, half_YpX, Z2, Td) =>
      let A := (Y1-X1)*half_YmX in
      let B := (Y1+X1)*half_YpX in
      let C := (Ta1*Tb1)*Td in
      let D := Z1*Z2 in
      let E := B-A in
      let F := D-C in
      let G := D+C in
      let H := B+A in
      let X3 := E*F in
      let Y3 := G*H in
      let Z3 := F*G in
      (X3, Y3, Z3, E, H)
    end.


  Create HintDb points_as_coordinates discriminated.
  Hint Unfold XYZT.Basic.point XYZT.Basic.coordinates XYZT.Basic.m1add
       E.point E.coordinates m1_readd m1_prep : points_as_coordinates.
  Lemma readd_correct P Q :
    let '(X1, Y1, Z1, Ta1, Tb1) := m1_readd (coordinates P) (m1_prep (coordinates Q)) in
    let '(X2, Y2, Z2, _, _) := coordinates (m1add P Q) in
      Z2*X1 = Z1*X2 /\ Z2*Y1 = Z1*Y2 /\ X1*Y1 = Z1*Ta1*Tb1.
  Proof.
    repeat match goal with
           | _ => progress autounfold with points_as_coordinates in *
           | _ => progress destruct_head' @prod
           | _ => progress destruct_head' @sig
           | _ => progress cbv [proj1_sig fst snd]
           | |- _ /\ _ => split
           end; fsatz.
  Qed.

End ExtendedCoordinates.

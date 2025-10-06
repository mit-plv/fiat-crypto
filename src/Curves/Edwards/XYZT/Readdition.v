From Coq Require Import Morphisms.

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
  Local Notation point := (Extended.point(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(d:=d)).
  Context {a_eq_minus1:a = Fopp 1} {twice_d} {k_eq_2d:twice_d = d+d} {nonzero_d: d<>0}.
  Local Notation m1add := (Extended.m1add(F:=F)(Feq:=Feq)(Fzero:=Fzero)(Fone:=Fone)(Fopp:=Fopp)(Fadd:=Fadd)(Fsub:=Fsub)(Fmul:=Fmul)(Finv:=Finv)(Fdiv:=Fdiv)(field:=field)(char_ge_3:=char_ge_3)(Feq_dec:=Feq_dec)(a:=a)(d:=d)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)(a_eq_minus1:=a_eq_minus1)(twice_d:=twice_d)(k_eq_2d:=k_eq_2d)).

  (* Define a new cached point type *)
  Definition cached :=
    { C | let '(half_YmX,half_YpX,Z,Td) := C in
          let X := half_YpX - half_YmX in
          let Y := half_YpX + half_YmX in
          let T := Td / d in
            a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2
            /\ X * Y = Z * T
            /\ Z <> 0 }.
  Definition cached_coordinates (C:cached) : F*F*F*F := proj1_sig C.
  Definition cached_eq (C1 C2:cached) :=
    let '(hYmX1, hYpX1, Z1, _) := cached_coordinates C1 in
    let '(hYmX2, hYpX2, Z2, _) := cached_coordinates C2 in
    Z2*(hYpX1-hYmX1) = Z1*(hYpX2-hYmX2) /\ Z2*(hYpX1+hYmX1) = Z1*(hYpX2+hYmX2).

  Local Ltac t_step :=
    match goal with
    | |- Proper _ _ => intro
    | _ => progress intros
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' @E.point
    | _ => progress destruct_head' @Extended.point
    | _ => progress destruct_head' @cached
    | _ => progress destruct_head' and
    | _ => progress cbv [Extended.eq CompleteEdwardsCurve.E.eq E.eq E.zero E.add E.opp fst snd cached_coordinates E.coordinates proj1_sig] in *
    | |- _ /\ _ => split | |- _ <-> _ => split
    end.
  Local Ltac t := repeat t_step; try Field.fsatz.

  Program Definition cached_to_twisted (C:cached) : Epoint :=
    let MPZT := cached_coordinates C in
      let Td  := snd MPZT in
      let MPZ := fst MPZT in
        let Z  := snd MPZ in
        let MP := fst MPZ in
          let hYpX := snd MP in
          let hYmX := fst MP in
            let iZ := Finv Z in (((hYpX-hYmX)*iZ), ((hYpX+hYmX)*iZ)).
  Next Obligation. t. Qed.

  Program Definition m1_prep (P : point) : cached :=
      match proj1_sig P return F*F*F*F with
        (X, Y, Z, Ta, Tb) =>
        let half_YmX := (Y-X)/2 in
        let half_YpX := (Y+X)/2 in
        let Td := Ta*Tb*d in
        (half_YmX, half_YpX, Z, Td)
      end.
  Next Obligation. t. Qed.

    Lemma to_affine_denom_nonzero (P1 : point) (P2: cached) : 
      let '(X1, Y1, Z1, _, _) := proj1_sig P1 in
      let '(half_YmX, half_YpX, Z2, _) := proj1_sig P2 in
      (d * (X1 * Finv Z1) * ((half_YpX-half_YmX)*(Finv Z2)) * (Y1 * Finv Z1) * ((half_YpX+half_YmX)*(Finv Z2)))^2 <> 1.
    Proof.
      destruct P1 as (((((?X & ?Y) & ?Z) & ?Ta) & ?Tb) & ?HP).
      destruct P2 as ((((?half_YmX & ?half_YpX) & ?Z) & ?T) & ?HP).
      unshelve epose proof
        (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d
          (X * Finv Z) (Y * Finv Z) _ ((half_YpX-half_YmX)*(Finv Z0)) ((half_YpX+half_YmX)*(Finv Z0)) _); t.
    Qed.

  Program Definition m1_readd
      (P1 : point) (C : cached) : point :=
    match proj1_sig P1, C return F*F*F*F*F with
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
  Next Obligation.
    pose proof (to_affine_denom_nonzero P1 C).
    t. Qed.

  Create HintDb points_as_coordinates discriminated.
  Hint Unfold Extended.point proj1_sig Extended.m1add
       E.point E.coordinates m1_readd m1_prep : points_as_coordinates.
  Lemma readd_correct P Q :
    Extended.eq (m1_readd P (m1_prep Q)) (m1add P Q).
  Proof. cbv [m1add m1_readd m1_prep]; t. Qed.

End ExtendedCoordinates.

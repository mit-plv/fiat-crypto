Require Import Crypto.Util.Decidable Crypto.Util.Notations Crypto.Algebra.Hierarchy.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.XYZT.Basic.
From Coq Require Import Morphisms.

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
  Local Notation point := (point (Feq:=Feq)(Fzero:=Fzero)(Fadd:=Fadd)(Fmul:=Fmul)(a:=a)(d:=d)).

  Definition precomputed_point := { P | let '(half_ypx, half_ymx, xyd) := P in
                            let x := half_ypx - half_ymx in
                            let y := half_ypx + half_ymx in
                            onCurve x y /\ xyd = x * y * d}.
  Definition precomputed_coordinates (P:precomputed_point) : F*F*F := proj1_sig P.
  Definition eq (P1 P2:precomputed_point) :=
    let '(half_ypx1, half_ymx1, _) := precomputed_coordinates P1 in
    let '(half_ypx2, half_ymx2, _) := precomputed_coordinates P2 in
    half_ypx1 = half_ypx2 /\ half_ymx1 = half_ymx2.

  Local Ltac t_step :=
    match goal with
    | |- Proper _ _ => intro
    | _ => progress intros
    | _ => progress (Prod.inversion_prod; subst)
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' @E.point
    | _ => progress destruct_head' Basic.point
    | _ => progress destruct_head' @precomputed_point
    | _ => progress destruct_head' and
    | _ => progress cbv beta match zeta delta [eq CompleteEdwardsCurve.E.eq Basic.eq E.eq E.zero E.add fst snd precomputed_coordinates coordinates E.coordinates proj1_sig point] in *
    | |- _ /\ _ => split | |- _ <-> _ => split
    end.
  Local Ltac t := repeat t_step; try Field.fsatz.

  Definition of_twisted (P:Epoint) : precomputed_point.
    refine ( exist _ (
      let '(x, y) := E.coordinates P in
        ((y+x)/2, (y-x)/2, x*y*d)) _). abstract t. Defined.
  Global Instance Proper_from_twisted : Proper (E.eq==>eq) of_twisted.
  Proof using Type. cbv [of_twisted]; t. Qed.
  
  Definition to_twisted (P: precomputed_point) : Epoint.
    refine ( exist _ (  
      let '(half_ypx, half_ymx, _) := precomputed_coordinates P in
        (half_ypx - half_ymx, half_ypx + half_ymx)) _). abstract t. Defined.
  Global Instance Proper_to_twisted : Proper (eq==>E.eq) to_twisted.
  Proof using Type. cbv [to_twisted]; t. Qed.

  Definition to_projective (P: precomputed_point) : point.
    refine ( exist _ (
      let '(half_ypx, half_ymx, _) := precomputed_coordinates P in
        (half_ypx - half_ymx, half_ypx + half_ymx, 1,
         half_ypx - half_ymx, half_ypx + half_ymx)) _ ). abstract t. Defined.
  Global Instance Proper_to_projective : Proper (eq==>(Basic.eq (Feq:=Feq))) to_projective.
  Proof using Type. cbv [to_projective]; t. Qed.

  Definition from_projective (P:point) : precomputed_point.
    refine ( exist _ (
      let '(X, Y, Z, _, _) := proj1_sig P in
      let iZ := Finv Z in 
      let x := X * iZ in 
      let y := Y * iZ in 
        ((y+x)/2, (y-x)/2, x*y*d)) _ ). abstract t. Defined.
  Global Instance Proper_from_projective: Proper (Basic.eq (Feq:=Feq)==>eq) from_projective.
  Proof using Type. cbv [from_projective]; t. Qed.

  Global Instance Equivalence_eq : Equivalence eq.
  Proof using Feq_dec field nonzero_a. split; repeat intro; t. Qed.
  Global Instance DecidableRel_eq : Decidable.DecidableRel eq.
  Proof. intros P Q. destruct P as [ [ [ ] ? ] ? ], Q as [ [ [ ] ? ] ? ]; exact _. Defined.

  Section TwistMinusOne.
    Context {a_eq_minus1:a = Fopp 1}.

    (* https://hyperelliptic.org/EFD/g1p/data/twisted/extended-1/addition/madd-2008-hwcd-3,
       but with halved precomputed coordinates (making D unnecessary) *)
    Definition m1add_precomputed_coordinates (P: point) (Q:precomputed_point) : point.
      refine ( exist _ (  
        let '(X1, Y1, Z1, Ta, Tb) := proj1_sig P in
        let '(half_ypx, half_ymx, xyd) := proj1_sig Q in
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
        (X3, Y3, Z3, E, H)) _ ). abstract (t; (* The last goal boils down to completeness of addition on edwards curves. *)
      pose proof Pre.denominator_nonzero a nonzero_a square_a d nonsquare_d _ _ H as H_nz; intro;
      eapply (H_nz (f2 * Finv f1)(f3 * Finv f1)); t). Defined.
    
    Create HintDb points_as_coordinates discriminated.
    Hint Unfold XYZT.Basic.point XYZT.Basic.coordinates XYZT.Basic.from_twisted XYZT.Basic.m1add
         E.point E.coordinates m1add_precomputed_coordinates of_twisted precomputed_point : points_as_coordinates.
    Local Notation m1add := (Basic.m1add(nonzero_a:=nonzero_a)(square_a:=square_a)(a_eq_minus1:=a_eq_minus1)(nonsquare_d:=nonsquare_d)(k_eq_2d:=reflexivity _)).
    Local Notation XYZT_of_twisted := (Basic.from_twisted(nonzero_a:=nonzero_a)(d:=d)).
    Lemma m1add_precomputed_coordinates_correct P Q :
      let '(X1, Y1, Z1, Ta1, Tb1) := proj1_sig (m1add_precomputed_coordinates (P) (of_twisted Q)) in
      let '(X2, Y2, Z2, _, _) := coordinates (m1add P (XYZT_of_twisted Q)) in
            Z2*X1 = Z1*X2 /\ Z2*Y1 = Z1*Y2 /\ X1*Y1 = Z1*Ta1*Tb1.
    Proof. cbv [proj1_sig m1add_precomputed_coordinates of_twisted m1add XYZT_of_twisted]; t.
    Qed.

  End TwistMinusOne.
End ExtendedCoordinates.

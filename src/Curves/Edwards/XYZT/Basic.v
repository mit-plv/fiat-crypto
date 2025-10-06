From Coq Require Import Morphisms.

Require Import Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.AffineProofs.

Require Import Crypto.Util.Notations Crypto.Util.GlobalSettings.
Require Export Crypto.Util.FixCoqMistakes.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.UniquePose.

Module Extended.
  Section ExtendedProjective.
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
    Local Notation affine_point := (@E.point F Feq Fone Fadd Fmul a d).
    Local Notation affine_add := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).

    (** [Extended.point] represents a point on an elliptic curve using extended projective Edwards coordinates. 
    *  See <https://eprint.iacr.org/2008/522.pdf> and <https://www.shiftleft.org/papers/fff/fff.pdf>.
    *)
    Definition point := { P | let '(X,Y,Z,Ta,Tb) := P in
                              a * X^2*Z^2 + Y^2*Z^2 = (Z^2)^2 + d * X^2 * Y^2
                              /\ X * Y = Z * Ta * Tb
                              /\ Z <> 0 }.
    Definition eq (P1 P2:point) :=
      let '(X1, Y1, Z1, _, _) := proj1_sig P1 in
      let '(X2, Y2, Z2, _, _) := proj1_sig P2 in
      Z2*X1 = Z1*X2 /\ Z2*Y1 = Z1*Y2.

    Ltac t_step :=
      match goal with
      | |- Proper _ _ => intro
      | _ => progress intros
      | _ => progress destruct_head' prod
      | _ => progress destruct_head' @E.point
      | _ => progress destruct_head' point
      | _ => progress destruct_head' and
      | _ => progress (Prod.inversion_prod; subst)
      | _ => progress cbv [eq CompleteEdwardsCurve.E.eq E.eq E.zero E.add E.opp fst snd E.coordinates proj1_sig proj2_sig] in *
      | |- _ /\ _ => split | |- _ <-> _ => split
      end.
    Ltac t := repeat t_step; try Field.fsatz.

    Global Instance Equivalence_eq : Equivalence eq.
    Proof using Feq_dec field nonzero_a. split; repeat intro; t. Qed.
    Global Instance DecidableRel_eq : Decidable.DecidableRel eq.
    Proof. intros P Q; destruct P as [ [ [ [ ] ? ] ? ] ?], Q as [ [ [ [ ] ? ] ? ] ? ]; exact _. Defined.

    Definition from_affine (P : affine_point) : point.
      refine ( exist _ (let '(x, y) := proj1_sig P in (x, y, 1, x, y)) _).
      abstract t. Defined.
      
    Global Instance Proper_from_affine : Proper (E.eq==>eq) from_affine.
    Proof using Type. cbv [from_affine]; t. Qed.

    Definition to_affine (P : point) : affine_point.
      refine ( exist _ (let '(X,Y,Z,Ta,Tb) := proj1_sig P in
                        let iZ := Finv Z in (X*iZ, Y*iZ))_ ). abstract t. Defined.
    Global Instance Proper_to_affine : Proper (eq==>E.eq) to_affine.
    Proof using Type. cbv [to_affine];  t. Qed.

    Local Ltac destruct_point P :=
      destruct P as (((((?X & ?Y) & ?Z) & ?Ta) & ?Tb) & ?HP).
    Lemma to_affine_denom_nonzero (P1 P2 : point) : 
      let '(X1, Y1, Z1, _, _) := proj1_sig P1 in
      let '(X2, Y2, Z2, _, _) := proj1_sig P2 in
      (d * (X1 * Finv Z1) * (X2 * Finv Z2) * (Y1 * Finv Z1) * (Y2 * Finv Z2))^2 <> 1.
    Proof.
      destruct_point P1. destruct_point P2.
      unshelve epose proof
        (E.denominator_nonzero _ nonzero_a square_a _ nonsquare_d
          (X * Finv Z) (Y * Finv Z) _ (X0 * Finv Z0) (Y0 * Finv Z0) _); t.
    Qed.
      
    Lemma to_affine_from_affine P : E.eq (to_affine (from_affine P)) P.
    Proof using Type. cbv [to_affine from_affine]; t. Qed.
    Lemma from_affine_to_affine P : eq (from_affine (to_affine P)) P.
    Proof using Type. cbv [to_affine from_affine]; t. Qed.

    Definition zero : point. refine (exist _ (0, 1, 1, 0, 1) _). abstract t. Defined.

    Definition opp (P : point) : point. refine (exist _ (
      let '(X, Y, Z, Ta, Tb) := proj1_sig P in (Fopp X, Y, Z, Fopp Ta, Tb)) _).
      abstract t. Defined.

    Section AMinusOne.
      Context {a_eq_minus1:a = Fopp 1} {twice_d} {k_eq_2d:twice_d = d+d}.
      Definition m1add (P1 P2:point) : point.
      refine (exist _ (
        let '(X1, Y1, Z1, Ta1, Tb1) := proj1_sig P1 in
        let '(X2, Y2, Z2, Ta2, Tb2) := proj1_sig P2 in
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
          (X3, Y3, Z3, E, H)) _).
      abstract (pose proof (to_affine_denom_nonzero P1 P2); t).
      Defined.

      Lemma to_affine_m1add P Q : E.eq (to_affine (m1add P Q)) (affine_add (to_affine P) (to_affine Q)).
      Proof.
        pose proof (to_affine_denom_nonzero P Q). cbv [proj1_sig to_affine m1add] in *.
        t.
      Qed.

      Global Instance isomorphic_commutative_group_m1 :
        @Group.isomorphic_commutative_groups
          affine_point E.eq
          affine_add
          (E.zero(nonzero_a:=nonzero_a))
          (E.opp(nonzero_a:=nonzero_a))
          point eq m1add zero opp
          from_affine to_affine.
      Proof.
        eapply Group.commutative_group_by_isomorphism;
        [ (exact _) | (apply to_affine_from_affine) | |(apply to_affine_m1add) | | ];
        solve [cbv [to_affine zero opp m1add]; t].
      Qed.

      Definition m1double (P : point) : point.
        refine (exist _ (
        let '(X, Y, Z, _, _) := proj1_sig P in
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
          (X3, Y3, Z3, cX, cY)) _).
      Proof. abstract (pose proof (to_affine_denom_nonzero P P); t). Defined.

      Lemma m1double_correct P : eq (m1double P) (m1add P P).
      Proof. intros; progress destruct_head' @point; cbv [m1add m1double]; t. Qed.

      Lemma to_affine_m1double P : E.eq (to_affine (m1double P)) (affine_add (to_affine P) (to_affine P)).
      Proof. setoid_rewrite m1double_correct; trivial. eapply to_affine_m1add. Qed.
    End AMinusOne.

    (* https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#doubling-double-2008-hwcd *)
    Definition double (P : point) : point.
      refine (exist _ (
        let '(X, Y, Z, Ta, Tb) := proj1_sig P in
        let A := X^2 in
        let B := Y^2 in
        let t0 := Z^2 in
        let C := t0+t0 in
        let D := a*A in
        let t1 := X+Y in
        let t2 := t1^2 in
        let t3 := t2-A in
        let E := t3-B in
        let G := D+B in
        let F := G-C in
        let H := D-B in
        let X3 := E*F in
        let Y3 := G*H in
        let Z3 := F*G in
        (X3, Y3, Z3, E, H)) _ ).
      Proof. abstract (pose proof (to_affine_denom_nonzero P P); t). Defined.

    Lemma to_affine_double P : E.eq (to_affine (double P)) (affine_add (to_affine P) (to_affine P)).
    Proof.
      cbv beta delta [double].
      pose proof (to_affine_denom_nonzero P P); cbv [E.add double to_affine]; t.
    Qed.
  End ExtendedProjective.
End Extended.

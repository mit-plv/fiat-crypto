Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SetoidSubst.
Require Import Crypto.Util.Notations Crypto.Util.LetIn.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.Sigma.

Module Jacobian.
  Section Jacobian.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x^2*x).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul a b).

    (* TODO: move non-precomputation-related defintions to a different file *)
    Definition point : Type := { P : F*F*F | let '(X,Y,Z) := P in
                                             if dec (Z=0) then True else Y^2 = X^3 + a*X*(Z^2)^2 + b*(Z^3)^2 }.

    Ltac prept :=
      repeat match goal with
             | _ => progress intros
             | _ => progress specialize_by trivial
             | _ => progress cbv [proj1_sig fst snd]
             | _ => progress autounfold with points_as_coordinates in *
             | _ => progress destruct_head' @unit
             | _ => progress destruct_head' @prod
             | _ => progress destruct_head' @sig
             | _ => progress destruct_head' @sum
             | _ => progress destruct_head' @and
             | _ => progress destruct_head' @or
             | H: context[dec ?P] |- _ => destruct (dec P)
             | |- context[dec ?P]      => destruct (dec P)
             | |- _ /\ _ => split
             end.
    Ltac t := prept; trivial; try fsatz.

    Create HintDb points_as_coordinates discriminated.
    Hint Unfold point W.point W.coordinates proj1_sig fst snd : points_as_coordinates.

    Program Definition of_affine (P:Wpoint) : point :=
      match W.coordinates P return F*F*F with
      | inl (x, y) => (x, y, 1)
      | inr _ => (0, 0, 0)
      end.
    Next Obligation. Proof. t. Qed.

    Program Definition to_affine (P:point) : Wpoint :=
      match proj1_sig P return F*F+_ with
      | (X, Y, Z) =>
        if dec (Z = 0) then inr tt
        else inl (X/Z^2, Y/Z^3)
      end.
    Next Obligation. Proof. t. Qed.

    Program Definition opp (P:point) : point :=
      match proj1_sig P return F*F*F with
      | (X, Y, Z) => (X, Fopp Y, Z)
      end.
    Next Obligation. Proof. t. Qed.

    Context (nonzero_b : b <> 0).
    (* jacobian zero: (?,?,0); affine zero: (0,0) *)
    Definition add_affine_coordinates (P:F*F*F) (Q:F*F) : F*F*F :=
      let '(X1, Y1, Z1) := P in
      let '(X2, Y2) := Q in
      dlet ZZ : F := Z1^2 in
      dlet P1z := if dec (Z1 = 0) then true else false in
      dlet U2 : F := ZZ * X2 in
      dlet X2z := if dec (X2 = 0) then true else false in
      dlet ZZZ: F := ZZ * Z1 in
      dlet H : F := U2 - X1 in
      dlet Z3 : F := Z1 * H in
      dlet P2z := if dec (Y2 = 0) then X2z else false in
      dlet S2 : F := ZZZ * Y2 in
      dlet R : F := S2 - Y1 in
      dlet HH : F := H^2 in
      dlet RR : F := R^2 in
      dlet HHH: F := HH*H in
      dlet Z3 := if P1z then 1 else Z3 in
      dlet Z3 := if P2z then Z1 else Z3 in
      dlet HHX : F := HH * X1 in
      dlet T10 : F := HHX + HHX in
      dlet E4 : F := RR - T10 in
      dlet X3 : F := E4 - HHH in
      dlet X3 := if P1z then X2 else X3 in
      dlet X3 := if P2z then X1 else X3 in
      dlet T13 : F := HHH * Y1 in
      dlet T11 : F := HHX - X3 in
      dlet T12 : F := T11 * R in
      dlet Y3 : F := T12 - T13 in
      dlet Y3 := if P1z then Y2 else Y3 in
      dlet Y3 := if P2z then Y1 else Y3 in
      (X3, Y3, Z3).

    Definition affine_of_table (P:F*F) :=
      let '(x, y) := P in if dec (x = 0 /\ y = 0) then inr tt else inl (x,y).

    Hint Unfold W.zero W.add W.coordinates W.eq to_affine of_affine add_affine_coordinates affine_of_table Let_In : points_as_coordinates. 

    Existing Class Decidable.decidable.
    Local Instance decidable_Decidable {P} (_:Decidable P) : Decidable.decidable P.
    Proof. destruct (dec P); [left|right]; assumption. Qed.
    Ltac not_and_t :=
      repeat match goal with
             | _ => solve [ contradiction | intuition trivial ]
             | H:~(_ /\ _)|-_ => destruct (Decidable.not_and _ _ _ H); clear H
             end.

    Lemma add_affine_coordinates_valid
          (P:point) (q:F*F) pf (Q:=exist _ (affine_of_table q) pf)
          (HPQ:~ W.eq (to_affine P) Q)
      : let '(X, Y, Z) := add_affine_coordinates (proj1_sig P) q in
        if dec (Z = 0) then True else Y^2 = X^3 + a * X * (Z^2)^2 + b * (Z^3)^2.
    Proof. prept; not_and_t. all: try abstract fsatz. Qed.
      
    Lemma add_affine_coordinates_correct
          (P:point) (q:F*F) pf (Q:=exist _ (affine_of_table q) pf)
          (HPQ:~ W.eq (to_affine P) Q)
          pf2
      : W.eq (W.add (to_affine P) Q) (to_affine (exist _ (add_affine_coordinates (proj1_sig P) q) pf2)).
    Proof. subst Q. prept; clear pf2; not_and_t. par: abstract fsatz. Qed.

    Definition add_affine_coordinates_correct_and_valid := fun P q pf neq => add_affine_coordinates_correct P q pf neq (add_affine_coordinates_valid P q pf neq).
  End Jacobian.
End Jacobian.

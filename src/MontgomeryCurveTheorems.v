Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Sum Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Spec.WeierstrassCurve.
Require Import Crypto.WeierstrassCurve.WeierstrassCurveTheorems.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F} {b_nonzero:b <> 0}.

    Program Definition opp (P:@M.point F Feq Fadd Fmul a b) : @M.point F Feq Fadd Fmul a b :=
      match P return F*F+∞ with
      | (x, y) => (x, -y)
      | ∞ => ∞
      end.
    Next Obligation. Proof. destruct P; cbv; break_match; trivial; fsatz. Qed.

    Ltac t :=
      repeat
        match goal with
        | _ => solve [ trivial ]
        | _ => progress intros
        | _ => progress subst
        | _ => progress Tactics.DestructHead.destruct_head' @M.point
        | _ => progress Tactics.DestructHead.destruct_head' @prod
        | _ => progress Tactics.DestructHead.destruct_head' @sum
        | _ => progress Tactics.DestructHead.destruct_head' @and
        | _ => progress Sum.inversion_sum
        | _ => progress Prod.inversion_prod
        | _ => progress Tactics.BreakMatch.break_match_hyps
        | _ => progress Tactics.BreakMatch.break_match
        | _ => progress cbv [M.coordinates M.add M.zero M.eq opp proj1_sig] in *
        | _ => progress cbv [W.coordinates W.add W.zero W.eq W.inv proj1_sig] in *
        | |- _ /\ _ => split | |- _ <-> _ => split
        end.

    Local Notation add := (M.add(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).

    Section MontgomeryWeierstrass.
      Local Notation "4" := (1+3).
      Local Notation "16" := (4*4).
      Local Notation "9" := (3*3).
      Local Notation "27" := (3*9).
      Context {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}.


      Local Notation WeierstrassA := ((3-a^2)/(3*b^2)).
      Local Notation WeierstrassB := ((2*a^3-9*a)/(27*b^3)).
      Local Notation Wpoint := (@W.point F Feq Fadd Fmul WeierstrassA WeierstrassB).
      Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 WeierstrassA WeierstrassB).
      Program Definition to_Weierstrass (P:@point) : Wpoint :=
        match M.coordinates P return F*F+∞ with
        | (x, y) => ((x + a/3)/b, y/b)
        | _ => ∞
        end.
      Next Obligation. Proof. t; fsatz. Qed.

      Program Definition of_Weierstrass (P:Wpoint) : point :=
        match W.coordinates P return F*F+∞ with
        | (x,y) => (b*x-a/3, b*y)
        | _ => ∞
        end.
      Next Obligation. Proof. t. fsatz. Qed.

      (*TODO: rename inv to opp, make it not require [discr_nonzero] *)
      Context {discr_nonzero : (2 + 1 + 1) * WeierstrassA * WeierstrassA * WeierstrassA +
                               ((2 + 1 + 1) ^ 2 + (2 + 1 + 1) + (2 + 1 + 1) + 1 + 1 + 1) *
                               WeierstrassB * WeierstrassB <> 0}.
      (* TODO: weakening lemma for characteristic *)
      Context {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12}.
      Local Notation Wopp := (@W.inv F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv WeierstrassA WeierstrassB field Feq_dec discr_nonzero).

      Program Definition _MW : _ /\ _ /\ _ :=
        @Group.group_from_redundant_representation
          Wpoint W.eq Wadd W.zero Wopp
          (abelian_group_group (W.commutative_group(discriminant_nonzero:=discr_nonzero)))
          point M.eq (M.add(b_nonzero:=b_nonzero)) M.zero opp
          of_Weierstrass
          to_Weierstrass
          _ _ _ _ _
      .
      Next Obligation. Proof. cbv [of_Weierstrass to_Weierstrass]; t; clear discr_nonzero; fsatz. Qed.
      Next Obligation. Proof. cbv [of_Weierstrass to_Weierstrass]; t; clear discr_nonzero; fsatz. Qed.
      Next Obligation. Proof. cbv [of_Weierstrass to_Weierstrass]; t; clear discr_nonzero; fsatz. Qed.
      Next Obligation. Proof. cbv [of_Weierstrass to_Weierstrass]; t; clear discr_nonzero; fsatz. Qed.
      Next Obligation. Proof. cbv [of_Weierstrass to_Weierstrass]; t; clear discr_nonzero; fsatz. Qed.

      Global Instance group : Algebra.group := proj1 _MW.
      Global Instance homomorphism_of_Weierstrass : Monoid.is_homomorphism(phi:=of_Weierstrass) := proj1 (proj2 _MW).
      Global Instance homomorphism_to_Weierstrass : Monoid.is_homomorphism(phi:=to_Weierstrass) := proj2 (proj2 _MW).
    End MontgomeryWeierstrass.
  End MontgomeryCurve.
End M.

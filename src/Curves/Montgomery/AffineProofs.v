Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Sum Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Spec.WeierstrassCurve Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}.
    Let char_ge_12 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12.
    Proof. eapply Algebra.Hierarchy.char_ge_weaken; eauto. vm_decide. Qed.
    Let char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3.
    Proof. eapply Algebra.Hierarchy.char_ge_weaken; eauto; vm_decide. Qed.
      
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2).
    Local Notation "9" := (3*3). Local Notation "27" := (3*9).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F} {b_nonzero:b <> 0}.

    Local Notation WeierstrassA := ((3-a^2)/(3*b^2)).
    Local Notation WeierstrassB := ((2*a^3-9*a)/(27*b^3)).
    Local Notation Wpoint := (@W.point F Feq Fadd Fmul WeierstrassA WeierstrassB).
    Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 WeierstrassA WeierstrassB).
    Local Notation Wopp := (@W.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv WeierstrassA WeierstrassB field Feq_dec).

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
        | _ => progress cbv [M.coordinates M.add M.zero M.eq M.opp proj1_sig
                             W.coordinates W.add W.zero W.eq W.opp
                             M.of_Weierstrass M.to_Weierstrass] in *
        | |- _ /\ _ => split | |- _ <-> _ => split
        end.

    Program Definition _MW (discr_nonzero:id _) : _ /\ _ /\ _ :=
      @Group.group_from_redundant_representation
        Wpoint W.eq Wadd W.zero Wopp
        (Algebra.Hierarchy.abelian_group_group (W.commutative_group(char_ge_12:=char_ge_12)(discriminant_nonzero:=discr_nonzero)))
        (@M.point F Feq Fadd Fmul a b) M.eq (M.add(char_ge_3:=char_ge_3)(b_nonzero:=b_nonzero)) M.zero (M.opp(b_nonzero:=b_nonzero))
        (M.of_Weierstrass(b_nonzero:=b_nonzero))
        (M.to_Weierstrass(b_nonzero:=b_nonzero))
        _ _ _ _ _
    .
    Next Obligation. Proof. t; fsatz. Qed.
    Next Obligation. Proof. t; fsatz. Qed.
    Next Obligation. Proof. t; fsatz. Qed.
    Next Obligation. Proof. t; fsatz. Qed.
    Next Obligation. Proof. t; fsatz. Qed.

    Global Instance group discr_nonzero : Algebra.Hierarchy.group := proj1 (_MW discr_nonzero).
    Global Instance homomorphism_of_Weierstrass discr_nonzero : Monoid.is_homomorphism(phi:=M.of_Weierstrass) := proj1 (proj2 (_MW discr_nonzero)).
    Global Instance homomorphism_to_Weierstrass discr_nonzero : Monoid.is_homomorphism(phi:=M.to_Weierstrass) := proj2 (proj2 (_MW discr_nonzero)).
  End MontgomeryCurve.
End M.

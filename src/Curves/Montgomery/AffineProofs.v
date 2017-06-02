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
            {Feq_dec:Decidable.DecidableRel Feq}.

    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "0" := Fzero.
    Local Notation "1" := Fone.
    Local Notation "2" := (1+1).
    Local Notation "3" := (1+2).
    Local Notation "4" := (1+1+1+1).
    Local Notation "9" := (3*3).
    Local Notation "27" := (4*4 + 4+4 +1+1+1).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F}
            {aw bw}
            {Haw : aw = (3-a^2)/(3*b^2)}
            {Hbw : bw = (2*a^3-9*a)/(27*b^3)}.

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

    Global Instance MontgomeryWeierstrassIsomorphism {_1 _2 _3 _4 _5 _6 _7}
           {discriminant_nonzero:id(4*aw*aw*aw + 27*bw*bw <> 0)}
           {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12}
           {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28} (* XXX: this is a workaround for nsatz assuming arbitrary characteristic *)
      :
      @Group.isomorphic_commutative_groups
        (@W.point F Feq Fadd Fmul aw bw)
        W.eq
        (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field _1 _2 aw bw)
        W.zero
        (@W.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv aw bw field _1)

        (@M.point F Feq Fadd Fmul a b)
        M.eq
        (M.add(char_ge_3:=_3)(b_nonzero:=_4))
        M.zero
        (M.opp(b_nonzero:=_7))

        (M.of_Weierstrass(Haw:=Haw)(Hbw:=Hbw)(b_nonzero:=_5))
        (M.to_Weierstrass(Haw:=Haw)(Hbw:=Hbw)(b_nonzero:=_6)).
    Proof.
      eapply Group.commutative_group_by_isomorphism.
      { eapply W.commutative_group; trivial. }
      Time all:t.
      Time par: abstract fsatz.
    Qed.

  End MontgomeryCurve.
End M.

Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Sum Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Spec.WeierstrassCurve.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
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
    Next Obligation. Proof. destruct_head @M.point; cbv; break_match; trivial; fsatz. Qed.

    Local Notation add := (M.add(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).

    Section MontgomeryWeierstrass.
      Local Notation "2" := (1+1).
      Local Notation "3" := (1+2).
      Local Notation "4" := (1+1+1+1).
      Local Notation "9" := (3*3).
      Local Notation "27" := (4*4 + 4+4 +1+1+1).

      Context {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}.

      Context {aw bw} {Haw:aw=(3-a^2)/(3*b^2)} {Hbw:bw=(2*a^3-9*a)/(27*b^3)}.
      Local Notation Wpoint := (@W.point F Feq Fadd Fmul aw bw).
      Local Notation Wadd := (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 aw bw).
      Program Definition to_Weierstrass (P:@point) : Wpoint :=
        match M.coordinates P return F*F+∞ with
        | (x, y) => ((x + a/3)/b, y/b)
        | _ => ∞
        end.
      Next Obligation. Proof. destruct_head' @point; cbv; break_match; trivial; fsatz. Qed.

      Program Definition of_Weierstrass (P:Wpoint) : point :=
        match W.coordinates P return F*F+∞ with
        | (x,y) => (b*x-a/3, b*y)
        | _ => ∞
        end.
      Next Obligation. Proof. destruct_head' @Wpoint; cbv; break_match; trivial; fsatz. Qed.
    End MontgomeryWeierstrass.
  End MontgomeryCurve.
End M.

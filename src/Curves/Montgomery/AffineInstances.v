Require Import Crypto.Algebra.Field.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Spec.WeierstrassCurve Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Montgomery.AffineProofs.
Require Import Coq.Classes.RelationClasses.

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
    Local Notation "0" := Fzero.
    Local Notation "1" := Fone.
    Local Notation "4" := (1+1+1+1).

    Global Instance MontgomeryWeierstrassIsomorphism
           {a b: F}
           (b_nonzero : b <> 0)
           (discriminant_nonzero: a^2 - 4 <> 0)
           {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3}
           {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12}
           {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28} (* XXX: this is a workaround for nsatz assuming arbitrary characteristic *)
      :
      @Group.isomorphic_commutative_groups
        (@W.point F Feq Fadd Fmul _ _)
        W.eq
        (@W.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field _ char_ge_3 _ _)
        W.zero
        (@W.opp F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv _ _ field _)

        (@M.point F Feq Fadd Fmul a b)
        M.eq
        (M.add(char_ge_3:=char_ge_3)(b_nonzero:=b_nonzero))
        M.zero
        (M.opp(b_nonzero:=b_nonzero))

        (M.of_Weierstrass(Haw:=reflexivity _)(Hbw:=reflexivity _)(b_nonzero:=b_nonzero))
        (M.to_Weierstrass(Haw:=reflexivity _)(Hbw:=reflexivity _)(b_nonzero:=b_nonzero)).
    Proof.
      eapply @AffineProofs.M.MontgomeryWeierstrassIsomorphism; try assumption; cbv [id]; fsatz.
    Qed.
  End MontgomeryCurve.
End M.

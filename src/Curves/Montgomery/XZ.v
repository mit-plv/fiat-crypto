Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.GlobalSettings Crypto.Util.Notations.
Require Import Crypto.Util.Sum Crypto.Util.Prod Crypto.Util.LetIn.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.

Module M.
  Section MontgomeryCurve.
    Import BinNat.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:Decidable.DecidableRel Feq}
            {char_ge_5:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 5}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).

    Context {a b: F} {b_nonzero:b <> 0}.
    Local Notation add := (M.add(b_nonzero:=b_nonzero)).
    Local Notation opp := (M.opp(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).

    Program Definition to_xz (P:point) : F*F :=
      match M.coordinates P with
      | (x, y) => pair x 1
      | ∞ => pair 1 0
      end.

    Let char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two)).
    Proof. eapply Algebra.Hierarchy.char_ge_weaken; eauto; vm_decide. Qed.

    (* From Curve25519 paper by djb, appendix B. Credited to Montgomery *)
    Context {a24:F} {a24_correct:(1+1+1+1)*a24 = a-(1+1)}.
    Definition xzladderstep (x1:F) (Q Q':F*F) : ((F*F)*(F*F)) :=
      match Q, Q' with
        pair x z, pair x' z' =>
        dlet A := x+z in
        dlet B := x-z in
        dlet AA := A^2 in
        dlet BB := B^2 in
        dlet x2 := AA*BB in
        dlet E := AA-BB in
        dlet z2 := E*(AA + a24*E) in
        dlet C := x'+z' in
        dlet D := x'-z' in
        dlet CB := C*B in
        dlet DA := D*A in
        dlet x3 := (DA+CB)^2 in
        dlet z3 := x1*(DA-CB)^2 in
        (pair (pair x2 z2) (pair x3 z3))
      end.
  End MontgomeryCurve.
End M.

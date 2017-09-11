Require Import Crypto.Util.Decidable Crypto.Util.Notations.
Require Import Crypto.Algebra.Ring Crypto.Algebra.Field.

Module _fsatz_test.
  Section _test.
    Context {F eq zero one opp add sub mul inv div}
            {fld:@Hierarchy.field F eq zero one opp add sub mul inv div}
            {eq_dec:DecidableRel eq}.
    Local Infix "=" := eq. Local Notation "a <> b" := (not (a = b)).
    Local Infix "=" := eq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := zero.  Local Notation "1" := one.
    Local Infix "+" := add. Local Infix "*" := mul.
    Local Infix "-" := sub. Local Infix "/" := div.

    Lemma inv_hyp a b c d (H:a*inv b=inv d*c) (bnz:b<>0) (dnz:d<>0) : a*d = b*c.
    Proof using Type*. fsatz. Qed.

    Lemma inv_goal a b c d (H:a=b+c) (anz:a<>0) : inv a*d + 1 = (d+b+c)*inv(b+c).
    Proof using Type*. fsatz. Qed.

    Lemma div_hyp a b c d (H:a/b=c/d) (bnz:b<>0) (dnz:d<>0) : a*d = b*c.
    Proof using Type*. fsatz. Qed.

    Lemma div_goal a b c d (H:a=b+c) (anz:a<>0) : d/a + 1 = (d+b+c)/(b+c).
    Proof using Type*. fsatz. Qed.

    Lemma inv_inv x (H:x <> 0) : 1/(1/x) = x.
    Proof using Type*. fsatz. Qed.

    Lemma zero_neq_one : 0 <> 1.
    Proof using Type*. fsatz. Qed.

    Lemma only_two_square_roots x y : x * x = y * y -> x <> opp y -> x = y.
    Proof using Type*. intros; fsatz. Qed.

    Lemma transitivity_contradiction a b c (ab:a=b) (bc:b=c) (X:a<>c) : False.
    Proof using Type*. fsatz. Qed.

    Lemma algebraic_contradiction a b c (A:a+b=c) (B:a-b=c) (X:a*a - b*b <> c*c) : False.
    Proof using Type*. fsatz. Qed.

    Lemma division_by_zero_in_hyps (bad:1/0 + 1 = (1+1)/0): 1 = 1.
    Proof using Type*. fsatz. Qed.
    Lemma division_by_zero_in_hyps_eq_neq (bad:1/0 + 1 = (1+1)/0): 1 <> 0.
    Proof using Type*.
 fsatz. Qed.
    Lemma division_by_zero_in_hyps_neq_neq (bad:1/0 <> (1+1)/0): 1 <> 0.
    Proof using Type*.
 fsatz. Qed.
    Import BinNums.

    Context {char_ge_16:@Ring.char_ge F eq zero one opp add sub mul 16}.

    Local Notation two := (one+one) (only parsing).
    Local Notation three := (one+one+one) (only parsing).
    Local Notation seven := (three+three+one) (only parsing).
    Local Notation nine := (three+three+three) (only parsing).

    Lemma fractional_equation_solution x (A:x<>1) (B:x<>opp two) (C:x*x+x <> two) (X:nine/(x*x + x - two) = three/(x+two) + seven*inv(x-1)) : x = opp one / (three+two).
    Proof using Type*. fsatz. Qed.

    Lemma fractional_equation_no_solution x (A:x<>1) (B:x<>opp two) (C:x*x+x <> two) (X:nine/(x*x + x - two) = opp three/(x+two) + seven*inv(x-1)) : False.
    Proof using Type*. fsatz. Qed.

    Local Notation "x ^ 2" := (x*x).
    Lemma recursive_nonzero_solving
          (a sqrt_a d x y : F)
          (Hpoly : a * x^2 + y^2 = one + d * x^2 * y^2)
          (Hsqrt : sqrt_a^2 = a)
          (Hfrac : (sqrt_a / y)^2 <> d)
      : x^2 = (y^2 - one) / (d * y^2 - a).
    Proof using eq_dec fld. fsatz. Qed.

    Local Notation "x ^ 3" := (x^2*x).
    Lemma weierstrass_associativity_main a b x1 y1 x2 y2 x4 y4
          (A: y1^2=x1^3+a*x1+b)
          (B: y2^2=x2^3+a*x2+b)
          (C: y4^2=x4^3+a*x4+b)
          (Hi3: x2 <> x1)
          λ3 (Hλ3: λ3 = (y2-y1)/(x2-x1))
          x3 (Hx3: x3 = λ3^2-x1-x2)
          y3 (Hy3: y3 = λ3*(x1-x3)-y1)
          (Hi7: x4 <> x3)
          λ7 (Hλ7: λ7 = (y4-y3)/(x4-x3))
          x7 (Hx7: x7 = λ7^2-x3-x4)
          y7 (Hy7: y7 = λ7*(x3-x7)-y3)
          (Hi6: x4 <> x2)
          λ6 (Hλ6: λ6 = (y4-y2)/(x4-x2))
          x6 (Hx6: x6 = λ6^2-x2-x4)
          y6 (Hy6: y6 = λ6*(x2-x6)-y2)
          (Hi9: x6 <> x1)
          λ9 (Hλ9: λ9 = (y6-y1)/(x6-x1))
          x9 (Hx9: x9 = λ9^2-x1-x6)
          y9 (Hy9: y9 = λ9*(x1-x9)-y1)
      : x7 = x9 /\ y7 = y9.
    Proof using Type*. fsatz_prepare_hyps; split; fsatz. Qed.
  End _test.
End _fsatz_test.

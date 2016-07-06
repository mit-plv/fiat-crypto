Require Crypto.WeierstrassCurve.Pre.

Module E.
  Section WeierstrassCurves.
    (* Short Weierstrass curves with addition laws. References:
     * <https://hyperelliptic.org/EFD/g1p/auto-shortw.html>
     * <https://cr.yp.to/talks/2007.06.07/slides.pdf>
     * See also:
     * <http://cs.ucsb.edu/~koc/ccs130h/2013/EllipticHyperelliptic-CohenFrey.pdf> (page 79)
     *)

    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} `{Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "=?" := Algebra.eq_dec (at level 70, no associativity) : type_scope.
    Local Notation "x =? y" := (Sumbool.bool_of_sumbool (Algebra.eq_dec x y)) : bool_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30). Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2). Local Notation "4" := (1+3).
    Local Notation "8" := (1+(1+(1+(1+4)))). Local Notation "12" := (1+(1+(1+(1+8)))).
    Local Notation "16" := (1+(1+(1+(1+12)))). Local Notation "20" := (1+(1+(1+(1+16)))).
    Local Notation "24" := (1+(1+(1+(1+20)))). Local Notation "27" := (1+(1+(1+24))).

    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F}.

    (** N.B. We may require more conditions to prove that points form
        a group under addition (associativity, in particular.  If
        that's the case, more fields will be added to this class. *)
    Class weierstrass_params :=
      {
        char_gt_2 : 2 <> 0;
        char_ne_3 : 3 <> 0;
        nonzero_discriminant : -(16) * (4 * a^3 + 27 * b^2) <> 0
      }.
    Context `{weierstrass_params}.

    Definition point := { P | match P with
                              | (x, y) => y^2 = x^3 + a*x + b
                              | ∞ => True
                              end }.
    Definition coordinates (P:point) : (F*F + ∞) := proj1_sig P.

    (** The following points are indeed on the curve -- see [WeierstrassCurve.Pre] for proof *)
    Local Obligation Tactic :=
      try solve [ Program.Tactics.program_simpl
                | intros; apply (Pre.unifiedAdd'_onCurve _ _ (proj2_sig _) (proj2_sig _)) ].

    Program Definition zero : point := ∞.

    Program Definition add (P1 P2:point) : point
      := exist
           _
           (match coordinates P1, coordinates P2 return _ with
            | (x1, y1), (x2, y2) =>
              if x1 =? x2 then
                if y2 =? -y1 then          ∞
                else                       ((3*x1^2+a)^2 / (2*y1)^2 - x1 - x1,
                                             (2*x1+x1)*(3*x1^2+a) / (2*y1) - (3*x1^2+a)^3/(2*y1)^3-y1)
              else                         ((y2-y1)^2 / (x2-x1)^2 - x1 - x2,
                                             (2*x1+x2)*(y2-y1) / (x2-x1) - (y2-y1)^3 / (x2-x1)^3 - y1)
            | ∞, ∞ =>                      ∞
            | ∞, _ =>                      coordinates P2
            | _, ∞ =>                      coordinates P1
            end)
           _.

    Fixpoint mul (n:nat) (P : point) : point :=
      match n with
      | O => zero
      | S n' => add P (mul n' P)
      end.
  End WeierstrassCurves.
End E.

Delimit Scope E_scope with E.
Infix "+" := E.add : E_scope.
Infix "*" := E.mul : E_scope.

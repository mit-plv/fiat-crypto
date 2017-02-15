Require Crypto.WeierstrassCurve.Pre.

Module W.
  Section WeierstrassCurves.
    (* Short Weierstrass curves with addition laws. References:
     * <https://hyperelliptic.org/EFD/g1p/auto-shortw.html>
     * <https://cr.yp.to/talks/2007.06.07/slides.pdf>
     * See also:
     * <http://cs.ucsb.edu/~koc/ccs130h/2013/EllipticHyperelliptic-CohenFrey.pdf> (page 79)
     *)

    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq} {char_gt_2:@Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "x =? y" := (Decidable.dec (Feq x y)) (at level 70, no associativity) : type_scope.
    Local Notation "x =? y" := (Sumbool.bool_of_sumbool (Decidable.dec (Feq x y))) : bool_scope.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "- x" := (Fopp x).
    Local Notation "x ^ 2" := (x*x) (at level 30). Local Notation "x ^ 3" := (x*x^2) (at level 30).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.

    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F}.

    Definition point := { P | match P with
                              | (x, y) => y^2 = x^3 + a*x + b
                              | ∞ => True
                              end }.
    Definition coordinates (P:point) : (F*F + ∞) := proj1_sig P.

    Definition eq (P1 P2:point) :=
      match coordinates P1, coordinates P2 with
      | (x1, y1), (x2, y2) => x1 = x2 /\ y1 = y2
      | ∞, ∞ => True
      | _, _ => False
      end.

    Program Definition zero : point := ∞.

    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Notation "2" := (1+1). Local Notation "3" := (1+2). 

    Program Definition add (P1 P2:point) : point  := exist _
      (match coordinates P1, coordinates P2 return _ with
       | (x1, y1), (x2, y2) =>
         if x1 =? x2
         then
           if y2 =? -y1
           then ∞
           else let k := (3*x1^2+a)/(2*y1) in
                let x3 := k^2-x1-x1 in
                let y3 := k*(x1-x3)-y1 in
                (x3, y3)
         else let k := (y2-y1)/(x2-x1) in
              let x3 := k^2-x1-x2 in
              let y3 := k*(x1-x3)-y1 in
              (x3, y3)
       | ∞, ∞ => ∞
       | ∞, _ => coordinates P2
       | _, ∞ => coordinates P1
       end) _.
    Next Obligation. exact (Pre.add_onCurve _ _ (proj2_sig _) (proj2_sig _)). Qed.

    Fixpoint mul (n:nat) (P : point) : point :=
      match n with
      | O => zero
      | S n' => add P (mul n' P)
      end.
  End WeierstrassCurves.
End W.

Delimit Scope W_scope with W.
Infix "+" := W.add : W_scope.
Infix "*" := W.mul : W_scope.

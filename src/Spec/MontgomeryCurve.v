Require Crypto.Algebra.Field.
Require Crypto.Util.GlobalSettings.
Require Crypto.Util.Tactics.DestructHead Crypto.Util.Sum Crypto.Util.Prod.

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
    Local Notation "2" := (1+1). Local Notation "3" := (1+2).
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    Local Notation "( x , y )" := (inl (pair x y)).
    Local Open Scope core_scope.

    Context {a b: F} {b_nonzero:b <> 0}.

    Definition point := { P : F*F+∞ | match P with
                                      | (x, y) => b*y^2 = x^3 + a*x^2 + x
                                      | ∞ => True
                                      end }.
    Definition coordinates (P:point) : (F*F + ∞) := let (xyi, _) := P in xyi.

    Program Definition zero : point := ∞.

    Definition eq (P1 P2:point) :=
      match coordinates P1, coordinates P2 with
      | (x1, y1), (x2, y2) => x1 = x2 /\ y1 = y2
      | ∞, ∞ => True
      | _, _ => False
      end.

    Program Definition add (P1 P2:point) : point :=
            match coordinates P1, coordinates P2 return F*F+∞ with
              (x1, y1), (x2, y2) =>
              if Decidable.dec (x1 = x2)
              then if Decidable.dec (y1 = - y2)
                   then ∞
                   else let k := (3*x1^2 + 2*a*x1 + 1)/(2*b*y1) in
                        let x := b*k^2 - a - x1 - x2 in
                        let y := (2*x1 + x2 + a)*k - b*k^3 - y1 in
                        (x, y)
              else let k := (y2 - y1)/(x2-x1) in
                   let x := b*k^2 - a - x1 - x2 in
                   let y := (2*x1 + x2 + a)*k - b*k^3 - y1 in
                   (x, y)
            | ∞, ∞ => ∞
            | ∞, _ => coordinates P2
            | _, ∞ => coordinates P1
            end.
    Next Obligation.
    Proof.
      cbv [coordinates]; BreakMatch.break_match; trivial; Field.fsatz.
    Qed.
  End MontgomeryCurve.
End M.

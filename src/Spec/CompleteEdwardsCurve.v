Require Crypto.CompleteEdwardsCurve.Pre.
Require Crypto.Util.Decidable.

Module E.
  Section TwistedEdwardsCurves.
    (* Twisted Edwards curves with complete addition laws. References:
    * <https://eprint.iacr.org/2008/013.pdf>
    * <http://ed25519.cr.yp.to/ed25519-20110926.pdf>
    * <https://eprint.iacr.org/2015/677.pdf>
    *)

    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_gt_2 : @Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.one)}
            {Feq_dec:Decidable.DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x) (at level 30).

    Context {a d: F}
            {nonzero_a : a <> 0}
            {square_a : exists sqrt_a, sqrt_a^2 = a}
            {nonsquare_d : forall x, x^2 <> d}.

    Definition point := { xy | let '(x, y) := xy in a*x^2 + y^2 = 1 + d*x^2*y^2 }.
    Definition coordinates (P:point) : (F*F) := let (xy, xy_onCurve_proof) := P in xy.
    Definition eq (P Q:point) :=
      match coordinates P, coordinates Q with
        (x1,y1), (x2,y2) => x1 = x2 /\ y1 = y2
      end.

    Program Definition zero : point := (0, 1).
    Next Obligation. eauto using Pre.onCurve_zero. Qed.

    Program Definition add (P1 P2:point) : point :=
      match coordinates P1, coordinates P2 return (F*F) with
        (x1, y1), (x2, y2) =>
        (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) , ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2)))
      end.
    Next Obligation. destruct P1 as [[??]?], P2 as [[??]?]; eapply Pre.onCurve_add; eauto. Qed.

    Fixpoint mul (n:nat) (P : point) : point :=
      match n with
      | O => zero
      | S n' => add P (mul n' P)
      end.
  End TwistedEdwardsCurves.
End E.

Delimit Scope E_scope with E.
Infix "=" := E.eq : E_scope.
Infix "+" := E.add : E_scope.
Infix "*" := E.mul : E_scope.
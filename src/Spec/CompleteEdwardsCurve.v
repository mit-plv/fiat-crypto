Require Crypto.CompleteEdwardsCurve.Pre.
Require Crypto.Util.Decidable.

Module E.
  Section TwistedEdwardsCurves.
    (* Twisted Edwards curves with complete addition laws. References:
    * <https://eprint.iacr.org/2008/013.pdf>
    * <http://ed25519.cr.yp.to/ed25519-20110926.pdf>
    * <https://eprint.iacr.org/2015/677.pdf>
    *)

    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} `{field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {Feq_dec:Decidable.DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub.
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation "n / d" := (fst (Fdiv n d, (_:(d <> 0)))). (* force nonzero d *)

    Context {a d: F}.
    Class twisted_edwards_params :=
      {
        char_gt_2 : forall p : BinNums.positive, BinPos.Pos.le p 2 -> Pre.ZtoR (BinNums.Zpos p) <> 0;
        nonzero_a : a <> 0;
        square_a : exists sqrt_a, sqrt_a^2 = a;
        nonsquare_d : forall x, x^2 <> d
      }.
    Context `{twisted_edwards_params}. (* TODO: name me *)

    Definition point := { P | let '(x,y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2 }.
    Definition coordinates (P:point) : (F*F) := proj1_sig P.
    Definition eq (P Q:point) :=
      fst (coordinates P) = fst (coordinates Q) /\
      snd (coordinates P) = snd (coordinates Q).

    Program Definition zero : point := (0, 1).
    Next Obligation. eauto using Pre.onCurve_zero. Qed.

    Program Definition add (P1 P2:point) : point :=
      let x1y1 := coordinates P1 in let x1 := fst x1y1 in let y1 := snd x1y1 in
      let x2y2 := coordinates P2 in let x2 := fst x2y2 in let y2 := snd x2y2 in
        (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) , ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2))).
    Next Obligation. destruct P1 as [[??]?], P2 as [[??]?], H. eauto using Pre.denominator_nonzero_x. Qed.
    Next Obligation. destruct P1 as [[??]?], P2 as [[??]?], H; eauto using Pre.denominator_nonzero_y. Qed.
    Next Obligation. destruct P1 as [[??]?], P2 as [[??]?], H; eauto using Pre.onCurve_add. Qed.

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
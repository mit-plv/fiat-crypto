Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.DestructHead Crypto.Util.Tactics.BreakMatch.

Module W.
  Section W.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:DecidableRel Feq}.

    Program Definition opp (P:@W.point F Feq Fadd Fmul a b) : @W.point F Feq Fadd Fmul a b
      := match W.coordinates P return F*F+_ with
         | inl (x1, y1) => inl (x1, Fopp y1)
         | _ => P
         end.
    Next Obligation. destruct P as [[[??]|[]]?]; cbv; trivial; fsatz. Qed.
  End W.
End W.
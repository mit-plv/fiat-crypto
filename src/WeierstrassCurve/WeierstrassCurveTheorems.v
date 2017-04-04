Require Import Coq.Numbers.BinNums.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.DestructHead Crypto.Util.Tactics.BreakMatch.
Require Import Coq.PArith.BinPos.

Module W.
  Section W.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
            {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12%positive} (* FIXME: shouldn't need we need 4, not 12? *)
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub. Local Infix "*" := Fmul.
    Local Notation "4" := (1+1+1+1). Local Notation "27" := (4*4 + 4+4 +1+1+1).
    Context {discriminant_nonzero:4*a*a*a + 27*b*b <> 0}.

    Program Definition inv (P:@W.point F Feq Fadd Fmul a b) : @W.point F Feq Fadd Fmul a b
      := match W.coordinates P return F*F+_ with
         | inl (x1, y1) => inl (x1, Fopp y1)
         | _ => P
         end.
    Next Obligation. destruct P as [[[??]|[]]?]; cbv; trivial; fsatz. Qed.

    Local Set Suggest Proof Using. (** Get travis to tell us what we should actually put here *)
    Global Instance commutative_group : abelian_group(eq:=W.eq)(op:=W.add)(id:=W.zero)(inv:=inv).
    Proof using All.
      repeat match goal with
             | _ => solve [ contradiction | trivial | exact _ ]
             | _ => intro
             | |- Equivalence _ => split
             | |- abelian_group => split | |- group => split | |- monoid => split
             | |- is_associative => split | |- is_commutative => split
             | |- is_left_inverse => split | |- is_right_inverse => split
             | |- is_left_identity => split | |- is_right_identity => split
             | _ => progress destruct_head' @W.point
             | _ => progress destruct_head' sum
             | _ => progress destruct_head' prod
             | _ => progress destruct_head' unit
             | _ => progress destruct_head' and
             | _ => progress cbv [inv W.eq W.zero W.add W.coordinates proj1_sig]in*
             | _ => progress break_match
             end.
      all: try abstract(fsatz_prepare_hyps; repeat split; fsatz_solve).
    Qed.
  End W.
End W.

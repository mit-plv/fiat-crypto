Require Import Coq.Numbers.BinNums.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Spec.WeierstrassCurve Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Algebra.Field Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.DestructHead Crypto.Util.Tactics.BreakMatch.
Require Import Coq.PArith.BinPos.

Module W.
  Section W.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub. Local Infix "*" := Fmul.
    Local Notation "4" := (1+1+1+1). Local Notation "27" := (4*4 + 4+4 +1+1+1).

    Local Ltac Algebra_split :=
      repeat match goal with
             | |- Proper _ _ => cbv [Proper respectful]; intros
             | |- Equivalence _ => split; [intros ? | intros ??? | intros ????? ]
             | |- monoid => split
             | |- group => split
             | |- commutative_group => split
             | |- is_associative => split; intros ???
             | |- is_commutative => split; intros ??
             | |- is_left_inverse => split; intros ?
             | |- is_right_inverse => split; intros ?
             | |- is_left_identity => split; intros ?
             | |- is_right_identity => split; intros ?
             end.

    Global Instance commutative_group
           char_ge_3
           {char_ge_12:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12%positive} (* FIXME: shouldn't need we need 4, not 12? *)
           {discriminant_nonzero:id(4*a*a*a + 27*b*b <> 0)}
      : commutative_group(eq:=W.eq(a:=a)(b:=b))(op:=W.add(char_ge_3:=char_ge_3))(id:=W.zero)(inv:=W.opp).
    Proof using Type.
      Time
        cbv [W.opp W.eq W.zero W.add W.coordinates proj1_sig];
          repeat match goal with
                 | _ => progress Algebra_split
                 | H: _ /\ _ |- _ => destruct H
                 | |- _ /\ _ => split
                 | _ => progress break_match
                 | _ => progress break_match_hyps
                 end; try contradiction; trivial.
      Time par: abstract (fsatz || (cbv [id] in *; fsatz)).
    Time Qed.
  End W.
End W.

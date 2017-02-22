Require Import Coq.Classes.Morphisms. Require Coq.Setoids.Setoid.
Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Decidable.
Import BinNums.

Local Open Scope core_scope.

Section Pre.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {char_ge_3:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos (BinNat.N.two))}
          {eq_dec: DecidableRel Feq}.
  Local Infix "=" := Feq. Local Notation "a <> b" := (not (a = b)).
  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "*" := Fmul.
  Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
  Local Notation "- x" := (Fopp x).
  Local Notation "x ^ 2" := (x*x). Local Notation "x ^ 3" := (x*x^2).
  Local Notation "'∞'" := unit : type_scope.
  Local Notation "'∞'" := (inr tt) : core_scope.
  Local Notation "2" := (1+1). Local Notation "3" := (1+2).
  Local Notation "( x , y )" := (inl (pair x y)).

  Context {a:F}.
  Context {b:F}.

  (* the canonical definitions are in Spec *)
  Let onCurve (P:F*F + ∞) := match P with
                             | (x, y) => y^2 = x^3 + a*x + b
                             | ∞ => True
                             end.
  Let add (P1' P2':F*F + ∞) : F*F + ∞ :=
    match P1', P2' return _ with
    | (x1, y1), (x2, y2) =>
      if dec (x1 = x2)
      then
        if dec (y2 = -y1)
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
    | ∞, _ => P2'
    | _, ∞ => P1'
    end.

  Lemma add_onCurve P1 P2 (_:onCurve P1) (_:onCurve P2) :
    onCurve (add P1 P2).
  Proof.
    destruct_head' sum; destruct_head' prod;
      cbv [onCurve add] in *; break_match; trivial; [|]; fsatz.
  Qed.
End Pre.

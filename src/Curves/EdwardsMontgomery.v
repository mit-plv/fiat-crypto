Require Import Coq.PArith.BinPosDef.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.GlobalSettings.
Require Import Crypto.Util.Sum Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Spec.MontgomeryCurve Crypto.Curves.Montgomery.Affine.
Require Import Crypto.Spec.CompleteEdwardsCurve  Crypto.Curves.Edwards.AffineProofs.
Require Import Coq.setoid_ring.Field_theory.

Module M.
  Section EdwardsMontgomery.
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
    Local Notation "'∞'" := unit : type_scope.
    Local Notation "'∞'" := (inr tt) : core_scope.
    (* Local Notation "( x , y )" := (inl (pair x y)). *)
    Local Open Scope core_scope.

    Context {a b: F} {b_nonzero:b <> 0}.

    Program Definition opp (P:@M.point F Feq Fadd Fmul a b) : @M.point F Feq Fadd Fmul a b :=
      match P return F*F+∞ with
      | inl (x, y) => inl (x, -y)
      | ∞ => ∞
      end.
    Next Obligation. Proof. destruct_head @M.point; cbv; break_match; trivial; fsatz. Qed.

    Local Notation add := (M.add(b_nonzero:=b_nonzero)).
    Local Notation point := (@M.point F Feq Fadd Fmul a b).

    Local Notation "2" := (1+1).
    Local Notation "4" := (1+1+1+1).
    (* Local Notation "3" := (1+2).
    Local Notation "9" := (3*3).
    Local Notation "27" := (4*4 + 4+4 +1+1+1).

    Context {char_ge_28:@Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}. *)

    Context {ae de: F} {Hae: ae=(a+2)/b} {Hde: de=(a-2)/b}
            {nonzero_ae : ae <> 0}
            {square_ae : exists sqrt_ae, sqrt_ae^2 = ae}
            {nonsquare_de : forall x, x^2 <> de}.


    Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul ae de).
    Local Notation Eadd := (@E.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 ae de).
    Program Definition to_Edwards (P:@point) : Epoint :=
      match M.coordinates P return F*F with
      | inl (u, v) => if dec (u + 1 <> 0 /\ v <> 0) 
                      then (u/v , (u-1)/(u+1)) 
                      else (0, 0 - 1)
      | ∞ => (0, 1)
      end.
    Next Obligation.
    (* Note: perhaps we can deal with u = -1 or v = 0 case in a better way*)
    Proof. destruct_head' @point; cbv; break_match; trivial; try fsatz.
    destruct H.
    assert (f + 1 <> 0) by auto.
    assert (f0 <> 0) by auto.
    fsatz.
    Qed.

    Program Definition of_Edwards (P:Epoint) : point :=
      match E.coordinates P return F*F+∞ with
      | (x, y) => if dec (x = 0 /\ y = 0 - 1) 
                  then inl (0, 0) 
                  else if dec (x = 0 /\ y = 1)
                       then inr tt
                       else inl ((1+y)/(1-y), (1+y)/(x*(1-y)))
      end.
    Next Obligation.
    Proof. destruct_head' @Epoint; cbv; break_match; trivial; try fsatz. 
    assert (f <> 0). {
      unfold not. intros Hf. rewrite -> Hf in y.
      destruct (dec (f0 = 1)).
      - auto.
      - assert (f0 = 0 - 1). fsatz. auto.
    }
    assert (f0 <> 1) by fsatz.
    fsatz.
    Qed.

  End EdwardsMontgomery.
End M.


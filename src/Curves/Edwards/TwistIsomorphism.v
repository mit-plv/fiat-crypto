From Coq Require Import Morphisms.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.Curves.Edwards.AffineProofs.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Prod.

Module E. Section __.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.two)}
          {Feq_dec:DecidableRel Feq}.
  Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd. Local Infix "*" := Fmul.
  Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
  Local Notation "x ^ 2" := (x*x) (at level 30, right associativity).
  Context {a1 d1 a2 d2 : F} {Heq : a1*d2 = a2*d1}.
  Context {nonzero_a1 : a1 <> 0} {square_a1 : exists sqrt_a, sqrt_a^2 = a1} {nonsquare_d1 : forall x, x^2 <> d1}.
  Context {nonzero_a2 : a2 <> 0} {square_a2 : exists sqrt_a, sqrt_a^2 = a2} {nonsquare_d2 : forall x, x^2 <> d2}.
  Context {r : F} {Hr : a1 = r^2*a2}.

  Local Notation point1 := (@E.point F Feq Fone Fadd Fmul a1 d1).
  Local Notation point2 := (@E.point F Feq Fone Fadd Fmul a2 d2).

  Definition point2_of_point1 (P : point1) : point2. refine (
    exist _ (let '(x, y) := E.coordinates P in (x*r, y)) _).
    abstract (case P as ((x&y)&?); cbn [E.coordinates]; fsatz).
  Defined.

  Definition point1_of_point2 (P : point2) : point1. refine (
    exist _ (let '(x, y) := E.coordinates P in (x/r, y)) _).
    abstract (case P as ((x&y)&?); cbn [E.coordinates]; fsatz).
  Defined.

  Global Instance Proper_point1_of_point2 : Proper (E.eq ==> E.eq) point1_of_point2.
  Proof. cbv [point1_of_point2 E.eq E.coordinates]; repeat intro; break_match; intuition fsatz. Qed.
  Global Instance Proper_point2_of_point1 : Proper (E.eq ==> E.eq) point2_of_point1.
  Proof. cbv [point2_of_point1 E.eq E.coordinates]; repeat intro; break_match; intuition fsatz. Qed.

  Add Field Private_field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).
  Import Field_tac.

  Lemma twist_isomorphism : @Group.isomorphic_commutative_groups
    _ E.eq
      (E.add(nonzero_a:=nonzero_a1)(square_a:=square_a1)(nonsquare_d:=nonsquare_d1))
      (E.zero(nonzero_a:=nonzero_a1))
      (E.opp(nonzero_a:=nonzero_a1))
    _ E.eq
      (E.add(nonzero_a:=nonzero_a2)(square_a:=square_a2)(nonsquare_d:=nonsquare_d2))
      (E.zero(nonzero_a:=nonzero_a2))
      (E.opp(nonzero_a:=nonzero_a2))
    point2_of_point1 point1_of_point2.
  Proof.
    unshelve epose proof E.edwards_curve_commutative_group(a:=a1)(d:=d1) as G1; trivial.
    unshelve epose proof E.edwards_curve_commutative_group(a:=a2)(d:=d2) as G2; trivial.
    esplit; trivial; [|]; split; try exact _;
      intros ((x&y)&?) ((x'&y')&?); case square_a1 as (r1&?), square_a2 as (r2&?);
      cbv [point2_of_point1 point1_of_point2 E.add E.eq E.coordinates]; intros; split; field_simplify_eq;
      repeat split; eauto using E.denominator_nonzero_x; eauto using E.denominator_nonzero_y; try fsatz.
    - unshelve epose proof E.denominator_nonzero_x a2 _ _ d2 _ (x*r) y _ (x'*r) y' _; trivial; fsatz.
    - unshelve epose proof E.denominator_nonzero_y a2 _ _ d2 _ (x*r) y _ (x'*r) y' _; trivial; fsatz.
    - unshelve epose proof E.denominator_nonzero_x a1 _ _ d1 _ (x/r) y _ (x'/r) y' _; trivial; fsatz.
    - unshelve epose proof E.denominator_nonzero_y a1 _ _ d1 _ (x/r) y _ (x'/r) y' _; trivial; fsatz.
  Qed.
End __. End E.

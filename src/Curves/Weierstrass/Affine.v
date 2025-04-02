Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.DestructHead Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SetoidSubst.
Import RelationClasses Morphisms.

Module W.
  Section W.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv} {a b:F}
            {field:@Algebra.Hierarchy.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "+" := Fadd. Local Infix "-" := Fsub.
    Local Infix "*" := Fmul. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x) (at level 30).
    Local Notation point := (@W.point F Feq Fadd Fmul a b).

    Definition opp (P : point) : point. refine (exist _ (
      match W.coordinates P with
      | inl (x1, y1) => inl (x1, Fopp y1)
      | inr tt => inr tt
      end) _).
    Proof. abstract (cbv [W.coordinates]; break_match; trivial; fsatz). Defined.

    Global Instance Equivalence_eq : Equivalence (@W.eq _ Feq Fadd Fmul a b).
    Proof.
      cbv [W.eq W.coordinates]; split; repeat intros [ [ []|[] ] ?]; intuition try solve
        [contradiction | apply reflexivity | apply symmetry; trivial | eapply transitivity; eauto 1].
    Qed.

    Global Instance Proper_opp : Proper (W.eq ==> W.eq) opp.
    Proof.
      repeat (intros [ [[]|[] ]?] || intro); cbv [W.coordinates opp W.eq] in *;
      repeat (try destruct_head' @and; try case dec as []; try contradiction; try split); trivial.
      setoid_subst_rel Feq; reflexivity.
    Qed.

    (*  Weierstraß Elliptic Curves and Side-Channel Attacks
        by Eric Brier and Marc Joye, 2002 *)
    Definition add' (P1 P2 : point) : point. refine (exist _
      match W.coordinates P1, W.coordinates P2 with
      | inl (x1, y1), inl (x2, y2) =>
        if dec (Feq y1 (Fopp y2)) then
          if dec (Feq x1 x2) then inr tt
          else let k := (y2-y1)/(x2-x1) in
               let x3 := k^2-x1-x2 in
               let y3 := k*(x1-x3)-y1 in
               inl (x3, y3)
        else let k := ((x1^2 + x1*x2 + x2^2 + a)/(y1+y2)) in
             let x3 := k^2-x1-x2 in
             let y3 := k*(x1-x3)-y1 in
             inl (x3, y3)
      | inr tt, inr tt => inr tt
      | inr tt, _ => W.coordinates P2
      | _, inr tt => W.coordinates P1
      end _).
    Proof. abstract (cbv [W.coordinates]; break_match; trivial; fsatz). Defined.

    Lemma add'_correct char_ge_3 : forall P Q : point, W.eq (W.add' P Q) (W.add(char_ge_3:=char_ge_3) P Q).
    Proof. intros [ [[]|]?] [ [[]|]?]; cbv [W.coordinates W.add W.add' W.eq]; break_match; try split; try fsatz. Qed.

    Global Instance Proper_add' : Proper (W.eq ==> W.eq ==> W.eq) add'.
    Proof.
      repeat (intros [ [[]|[] ]?] || intro); cbv [W.coordinates W.add' W.eq] in *;
      repeat (try destruct_head' @and; try case dec as []; try contradiction; try split); trivial.
      Time par : fsatz. (* setoid_subst_rel is slower *)
    Qed.

    Global Instance Proper_add {char_ge_3} :
      Proper (W.eq ==> W.eq ==> W.eq) (@W.add _ Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv _ _ char_ge_3 a b).
    Proof. repeat intro. rewrite <-2add'_correct. apply Proper_add'; trivial. Qed.
  End W.
End W.

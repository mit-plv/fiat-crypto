Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.

Section CompleteEdwardsCurveTheorems.
  Context {prm:TwistedEdwardsParams}.
  Existing Instance prime_q.
  Add Field Ffield_Z : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [idtac],
     postprocess [try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]). 

  Lemma point_eq : forall p1 p2, p1 = p2 -> forall pf1 pf2,
    mkPoint p1 pf1 = mkPoint p2 pf2.
  Proof.
    destruct p1, p2; intros; find_injection; intros; subst; apply f_equal.
    apply UIP_dec, F_eq_dec. (* this is a hack. We actually don't care about the equality of the proofs. However, we *can* prove it, and knowing it lets us use the universal equality instead of a type-specific equivalence, which makes many things nicer. *) 
  Qed.
  Hint Resolve point_eq.

  Ltac Edefn := unfold unifiedAdd, zero; intros;
                  repeat match goal with
                         | [ p : point |- _ ] =>
                           let x := fresh "x" p in
                           let y := fresh "y" p in
                           let pf := fresh "pf" p in
                           destruct p as [[x y] pf]; unfold onCurve in pf
                  | _ => eapply point_eq, f_equal2
                  | _ => eapply point_eq
  end.
  Lemma twistedAddComm : forall A B, (A+B = B+A)%E.
  Proof.
    Edefn; f_equal; field.
  Qed.

  Lemma twistedAddAssoc : forall A B C, A+(B+C) = (A+B)+C.
  Proof.
    (* http://math.rice.edu/~friedl/papers/AAELLIPTIC.PDF *)
  Admitted.

  Lemma zeroIsIdentity : forall P, (P + zero = P)%E.
  Proof.
    Edefn; repeat rewrite ?F_add_0_r, ?F_add_0_l, ?F_sub_0_l, ?F_sub_0_r,
           ?F_mul_0_r, ?F_mul_0_l, ?F_mul_1_l, ?F_mul_1_r, ?F_div_1_r; exact eq_refl.
  Qed.
End CompleteEdwardsCurveTheorems.
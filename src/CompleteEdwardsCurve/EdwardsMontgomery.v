Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.Spec.MontgomeryCurve Crypto.MontgomeryCurveTheorems.
Require Import Crypto.MontgomeryCurve.

Require Import Crypto.Util.Notations Crypto.Util.Decidable.
Require Import (*Crypto.Util.Tactics*) Crypto.Util.Sum Crypto.Util.Prod.
Require Import Crypto.Algebra Crypto.Algebra.Field.
Import BinNums.

Module E.
  Section EdwardsMontgomery.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_ge_28 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 28}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).

    Let char_ge_12 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 12.
    Proof. eapply char_ge_weaken; eauto. vm_decide. Qed.
    Let char_ge_3 : @Ring.char_ge F Feq Fzero Fone Fopp Fadd Fsub Fmul 3.
    Proof. eapply char_ge_weaken; eauto. vm_decide. Qed.

    Context {a d: F}
            {nonzero_a : a <> 0}
            {square_a : exists sqrt_a, sqrt_a^2 = a}
            {nonsquare_d : forall x, x^2 <> d}.
    Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul a d).
    Local Notation Ezero  := (E.zero(nonzero_a:=nonzero_a)(d:=d)).
    Local Notation Eadd   := (E.add(char_ge_3:=char_ge_3)(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).
    Local Notation Eopp   := (E.opp(nonzero_a:=nonzero_a)(d:=d)).

    Let a_neq_d : a <> d.
    Proof. intro X.
           edestruct square_a. eapply nonsquare_d.
           rewrite <-X. eassumption. Qed.

    
    Local Notation "2" := (1+1). Local Notation "4" := (1+1+1+1).
    Local Notation MontgomeryA := (2*(a+d)/(a-d)).
    Local Notation MontgomeryB := (4/(a-d)).

    Let b_nonzero : MontgomeryB <> 0. Proof. fsatz. Qed.

    Local Notation Mpoint := (@M.point F Feq Fadd Fmul MontgomeryA MontgomeryB).
    Local Notation Madd := (@M.add F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv field Feq_dec char_ge_3 MontgomeryA MontgomeryB b_nonzero).
    Local Notation "'∞'" := (inr tt) : core_scope.

    Ltac t_step :=
        match goal with
        | _ => solve [ contradiction | trivial ]
        | _ => progress intros
        | _ => progress subst
        | _ => progress Tactics.DestructHead.destruct_head' @M.point
        | _ => progress Tactics.DestructHead.destruct_head' @prod
        | _ => progress Tactics.DestructHead.destruct_head' @sum
        | _ => progress Tactics.DestructHead.destruct_head' @and
        | _ => progress Sum.inversion_sum
        | _ => progress Prod.inversion_prod
        | _ => progress Tactics.BreakMatch.break_match_hyps
        | _ => progress Tactics.BreakMatch.break_match
        | _ => progress cbv [E.coordinates M.coordinates E.add M.add E.zero M.zero E.eq M.eq E.opp M.opp proj1_sig fst snd] in *
        | |- _ /\ _ => split
        end.
    Ltac t := repeat t_step.

    Program Definition to_Montgomery (P:Epoint) : Mpoint :=
      match E.coordinates P return F*F+_ with
      | (x, y) => 
        if dec (y <> 1 /\ x <> 0)
        then inl ((1+y)/(1-y), (1+y)/(x-x*y))
        else ∞
      end.
    Next Obligation. Proof. t. fsatz. Qed.

    (* The exceptional cases are tricky. *)
    (* See https://eprint.iacr.org/2008/013.pdf page 5 before continuing *)

    Program Definition of_Montgomery (P:Mpoint) : Epoint :=
      match M.coordinates P return F*F with
      | inl (x,y) =>
        if dec (y = 0)
        then (0, Fopp 1)
        else (x/y, (x-1)/(x+1))
      | ∞ => pair 0 1
      end.
    Next Obligation.
    Proof.
      t; try fsatz.
      assert (f1 <> Fopp 1) by admit (* ad, d are nonsero *); fsatz.
    Admitted.

    Program Definition _EM (discr_nonzero:id _) : _ /\ _ /\ _ :=
      @Group.group_from_redundant_representation
        Mpoint M.eq Madd M.zero M.opp
        (M.group discr_nonzero)
        Epoint E.eq Eadd Ezero Eopp
        of_Montgomery
        to_Montgomery
        _ _ _ _ _
    .
    Next Obligation. Proof. Admitted. (* M->E->M *)
    Next Obligation. Proof. Admitted. (* equivalences match *)
    Next Obligation. Proof. Admitted. (* add *)
    Next Obligation. Proof. Admitted. (* opp *)
    Next Obligation. Proof. cbv [of_Montgomery to_Montgomery]; t; fsatz. Qed.

    Global Instance homomorphism_of_Montgomery discr_nonzero : Monoid.is_homomorphism(phi:=of_Montgomery) := proj1 (proj2 (_EM discr_nonzero)).
    Global Instance homomorphism_to_Montgomery discr_nonzero : Monoid.is_homomorphism(phi:=to_Montgomery) := proj2 (proj2 (_EM discr_nonzero)).
  End EdwardsMontgomery.
End E.

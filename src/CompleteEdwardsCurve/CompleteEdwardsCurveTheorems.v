Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.Algebra Crypto.Algebra Crypto.Util.Decidable.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tuple Crypto.Util.Notations Crypto.Util.Tactics.
Require Export Crypto.Util.FixCoqMistakes.

Module E.
  Import Group ScalarMult Ring Field CompleteEdwardsCurve.E.

  Notation onCurve_zero := Pre.onCurve_zero.
  Notation denominator_nonzero := Pre.denominator_nonzero.
  Notation denominator_nonzero_x := Pre.denominator_nonzero_x.
  Notation denominator_nonzero_y := Pre.denominator_nonzero_y.
  Notation onCurve_add := Pre.onCurve_add.

  Section CompleteEdwardsCurveTheorems.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_gt_2 : @Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.one)}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).

    Context {a d: F}
            {nonzero_a : a <> 0}
            {square_a : exists sqrt_a, sqrt_a^2 = a}
            {nonsquare_d : forall x, x^2 <> d}.
    
    Local Notation onCurve x y := (a*x^2 + y^2 = 1 + d*x^2*y^2).
    Local Notation point := (@E.point F Feq Fone Fadd Fmul a d).
    Local Notation eq    := (@E.eq F Feq Fone Fadd Fmul a d).
    Local Notation zero  := (E.zero(nonzero_a:=nonzero_a)(d:=d)).
    Local Notation add   := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).
    Local Notation mul   := (E.mul(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).

    Program Definition opp (P:point) : point := (Fopp (fst P), (snd P)).
    Next Obligation. destruct P as [ [??]?]; cbv; fsatz. Qed.

    Ltac t_step :=
      match goal with
      | _ => solve [trivial | exact _ ]
      | _ => intro
      | |- Equivalence _ => split
      | |- abelian_group => split | |- group => split | |- monoid => split
      | |- is_associative => split | |- is_commutative => split 
      | |- is_left_inverse => split | |- is_right_inverse => split
      | |- is_left_identity => split | |- is_right_identity => split
      | _ => progress destruct_head' @E.point
      | _ => progress destruct_head' prod
      | _ => progress destruct_head' and
      | |- context[E.add ?P ?Q] =>
        unique pose proof (Pre.denominator_nonzero_x _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q));
        unique pose proof (Pre.denominator_nonzero_y _ nonzero_a square_a _ nonsquare_d _ _  (proj2_sig P)  _ _  (proj2_sig Q))
      | _ => progress cbv [opp E.zero E.eq E.add E.coordinates proj1_sig fieldwise fieldwise'] in *
      (* [_gather_nonzeros] must run before [fst_pair] or [simpl] but after splitting E.eq and unfolding [E.add] *)
      | |- _ /\ _ => split | |- _ <-> _ => split
      end.
    Ltac t := repeat t_step; fsatz.

    Global Instance associative_add : is_associative(eq:=E.eq)(op:=add).
    Proof.
      (* [nsatz_compute] for a denominator runs out of 6GB of stack space *)
      (* COQBUG: https://coq.inria.fr/bugs/show_bug.cgi?id=5359 *)
      Add Field _field : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F)).
      Import Field_tac.
      repeat t_step; (field_simplify_eq; [IntegralDomain.nsatz|]); repeat split; trivial.
      { intro. eapply H3. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
      { intro. eapply H. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
      { intro. eapply H4. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
      { intro. eapply H0. field_simplify_eq; repeat split; trivial. IntegralDomain.nsatz. }
    Qed.

    Global Instance edwards_curve_abelian_group : abelian_group (eq:=eq)(op:=add)(id:=zero)(inv:=opp).
    Proof. t. Qed.

    Global Instance Proper_coordinates : Proper (eq==>fieldwise (n:=2) Feq) coordinates. Proof. repeat t_step. Qed.

    Global Instance Proper_mul : Proper (Logic.eq==>eq==>eq) mul.
    Proof.
      intros n n'; repeat intro; subst n'.
      induction n; (reflexivity || eapply (_:Proper (eq==>eq==>eq) add); eauto).
    Qed.

    Global Instance mul_is_scalarmult : @is_scalarmult point eq add zero mul.
    Proof. split; intros; (reflexivity || exact _). Qed.

    Section PointCompression.
      Local Notation "x ^ 2" := (x*x).
      Definition solve_for_x2 (y : F) := ((y^2 - 1) / (d * (y^2) - a)).

      Lemma a_d_y2_nonzero y : d * y^2 - a <> 0.
      Proof.
        destruct square_a as [sqrt_a], (dec (y=0));
          pose proof nonzero_a; pose proof (nonsquare_d (sqrt_a/y)); fsatz.
      Qed.

      Lemma solve_correct : forall x y, onCurve x y <-> (x^2 = solve_for_x2 y).
      Proof. pose proof a_d_y2_nonzero; cbv [solve_for_x2]; t. Qed.
    End PointCompression.
  End CompleteEdwardsCurveTheorems.
  Section Homomorphism.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {char_gt_2_F : @Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.one)}
            {Feq_dec:DecidableRel Feq}.

    Context {Fa Fd: F}
            {nonzero_a : not (Feq Fa Fzero)}
            {square_a : exists sqrt_a, Feq (Fmul sqrt_a sqrt_a) Fa}
            {nonsquare_d : forall x, not (Feq (Fmul x x) Fd)}.
    
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {fieldK: @Algebra.field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {char_gt_2_K : @Ring.char_gt F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinNat.N.succ_pos BinNat.N.one)}
            {Keq_dec:DecidableRel Keq}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {Ka} {Ha:Keq (phi Fa) Ka} {Kd} {Hd:Keq (phi Fd) Kd}.
    Local Notation Fpoint := (@E.point F Feq Fone Fadd Fmul Fa Fd).
    Local Notation Kpoint := (@E.point K Keq Kone Kadd Kmul Ka Kd).
    Local Notation Fzero  := (E.zero(nonzero_a:=nonzero_a)(d:=Fd)).
    Local Notation Fadd   := (E.add(nonzero_a:=nonzero_a)(square_a:=square_a)(nonsquare_d:=nonsquare_d)).

    Create HintDb field_homomorphism discriminated.
    Hint Rewrite <-
         (homomorphism_one(phi:=phi))
         (homomorphism_add(phi:=phi))
         (homomorphism_sub(phi:=phi))
         (homomorphism_mul(phi:=phi))
         (homomorphism_div(phi:=phi))
         Ha
         Hd
      : field_homomorphism.

    Obligation Tactic := idtac.
    Program Definition ref_phi (P:Fpoint) : Kpoint := exist _ (
      let (x, y) := coordinates P in (phi x, phi y)) _.
    Next Obligation.
      destruct P as [ [? ?] ?]; simpl.
      rewrite_strat bottomup hints field_homomorphism.
      eauto using Monoid.is_homomorphism_phi_proper; assumption.
    Qed.

    Context {point_phi:Fpoint->Kpoint}
            {point_phi_Proper:Proper (eq==>eq) point_phi}
            {point_phi_correct: forall (P:point), eq (point_phi P) (ref_phi P)}.

    Lemma lift_homomorphism : @Monoid.is_homomorphism Fpoint eq add
                                                      Kpoint eq add point_phi.
    Proof.
      repeat match goal with
             | |- _ => intro
             | |- Monoid.is_homomorphism => split
             | _ => progress destruct_head' @E.point
             | _ => progress destruct_head' prod
             | _ => progress destruct_head' and
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | _ => progress cbv [ref_phi eq E.eq CompleteEdwardsCurve.E.eq E.add E.coordinates proj1_sig] in *
             (* [_gather_nonzeros] must run before [fst_pair] or [simpl] but after splitting E.eq and unfolding [E.add] *)
             | _ => _gather_nonzeros
             | _ => progress simpl in *
             | |- _ ?x ?x => reflexivity
             | |- _ ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | |- _ /\ _ => split
             | _ => solve [fsatz | repeat (f_equiv; auto) ]
             end.
      Qed.
  End Homomorphism.
End E.
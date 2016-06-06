Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.ModularArithmetic.FField.
Require Import Crypto.ModularArithmetic.FNsatz.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.

Module E.
  Section CompleteEdwardsCurveTheorems.
    Context {prm:TwistedEdwardsParams}.
    Local Opaque q a d prime_q two_lt_q nonzero_a square_a nonsquare_d. (* [F_field] calls [compute] *)
    Existing Instance prime_q.
  
    Add Field Ffield_p' : (@Ffield_theory q _)
      (morphism (@Fring_morph q),
       preprocess [Fpreprocess],
       postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
       constants [Fconstant],
       div (@Fmorph_div_theory q),
       power_tac (@Fpower_theory q) [Fexp_tac]).
  
    Add Field Ffield_notConstant : (OpaqueFieldTheory q)
      (constants [notConstant]).
  
    Ltac clear_prm :=
      generalize dependent a; intro a; intros;
      generalize dependent d; intro d; intros;
      generalize dependent prime_q; intro prime_q; intros;
      generalize dependent q; intro q; intros;
      clear prm.
  
    Lemma point_eq : forall xy1 xy2 pf1 pf2,
      xy1 = xy2 -> exist E.onCurve xy1 pf1 = exist E.onCurve xy2 pf2.
    Proof.
      destruct xy1, xy2; intros; find_injection; intros; subst. apply f_equal.
      apply UIP_dec, F_eq_dec. (* this is a hack. We actually don't care about the equality of the proofs. However, we *can* prove it, and knowing it lets us use the universal equality instead of a type-specific equivalence, which makes many things nicer. *)
    Qed. Hint Resolve point_eq.
  
    Definition point_eqb (p1 p2:E.point) : bool := andb
        (F_eqb (fst (proj1_sig p1)) (fst (proj1_sig p2)))
        (F_eqb (snd (proj1_sig p1)) (snd (proj1_sig p2))).
  
    Local Ltac t :=
      unfold point_eqb;
        repeat match goal with
        | _ => progress intros
        | _ => progress simpl in *
        | _ => progress subst
        | [P:E.point |- _ ] => destruct P
        | [x: (F q * F q)%type |- _ ] => destruct x
        | [H: _ /\ _ |- _ ] => destruct H
        | [H: _ |- _ ] => rewrite Bool.andb_true_iff in H
        | [H: _ |- _ ] => apply F_eqb_eq in H
        | _ => rewrite F_eqb_refl
        end; eauto.
  
    Lemma point_eqb_sound : forall p1 p2, point_eqb p1 p2 = true -> p1 = p2.
    Proof.
      t.
    Qed.
  
    Lemma point_eqb_complete : forall p1 p2, p1 = p2 -> point_eqb p1 p2 = true.
    Proof.
      t.
    Qed.
  
    Lemma point_eqb_neq : forall p1 p2, point_eqb p1 p2 = false -> p1 <> p2.
    Proof.
      intros. destruct (point_eqb p1 p2) eqn:Hneq; intuition.
      apply point_eqb_complete in H0; congruence.
    Qed.
  
    Lemma point_eqb_neq_complete : forall p1 p2, p1 <> p2 -> point_eqb p1 p2 = false.
    Proof.
      intros. destruct (point_eqb p1 p2) eqn:Hneq; intuition.
      apply point_eqb_sound in Hneq. congruence.
    Qed.
  
    Lemma point_eqb_refl : forall p, point_eqb p p = true.
    Proof.
      t.
    Qed.
  
    Definition point_eq_dec (p1 p2:E.point) : {p1 = p2} + {p1 <> p2}.
      destruct (point_eqb p1 p2) eqn:H; match goal with
                                        | [ H: _ |- _ ] => apply point_eqb_sound in H
                                        | [ H: _ |- _ ] => apply point_eqb_neq in H
                                        end; eauto.
    Qed.
  
    Lemma point_eqb_correct : forall p1 p2, point_eqb p1 p2 = if point_eq_dec p1 p2 then true else false.
    Proof.
      intros. destruct (point_eq_dec p1 p2); eauto using point_eqb_complete, point_eqb_neq_complete.
    Qed.
  
    Ltac Edefn := unfold E.add, E.add', E.zero; intros;
                    repeat match goal with
                           | [ p : E.point |- _ ] =>
                             let x := fresh "x" p in
                             let y := fresh "y" p in
                             let pf := fresh "pf" p in
                             destruct p as [[x y] pf]; unfold E.onCurve in pf
                    | _ => eapply point_eq, (f_equal2 pair)
                    | _ => eapply point_eq
    end.
    Lemma add_comm : forall A B, (A+B = B+A)%E.
    Proof.
      Edefn; apply (f_equal2 div); ring.
    Qed.
  
    Ltac unifiedAdd_nonzero := match goal with
    | [ |- (?op 1 (d * _ * _ * _ * _ *
      inv (1 - d * ?xA * ?xB * ?yA * ?yB) * inv (1 + d * ?xA * ?xB * ?yA * ?yB)))%F <> 0%F]
      => let Hadd := fresh "Hadd" in
       pose proof (@unifiedAdd'_onCurve _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d (xA, yA) (xB, yB)) as Hadd;
       simpl in Hadd;
       match goal with
       | [H : (1 - d * ?xC * xB * ?yC * yB)%F <> 0%F |- (?op 1 ?other)%F <> 0%F] =>
         replace other with
          (d * xC * ((xA * yB + yA * xB) / (1 + d * xA * xB * yA * yB)) 
          * yC * ((yA * yB - a * xA * xB) / (1 - d * xA * xB * yA * yB)))%F by (subst; unfold div; ring);
          auto
      end
    end.
  
    Lemma add_assoc : forall A B C, (A+(B+C) = (A+B)+C)%E.
    Proof.
      Edefn; F_field_simplify_eq; try abstract (rewrite ?@F_pow_2_r in *; clear_prm; F_nsatz);
        pose proof (@edwardsAddCompletePlus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d);
        pose proof (@edwardsAddCompleteMinus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d);
        cbv beta iota in *;
        repeat split; field_nonzero idtac; unifiedAdd_nonzero.
    Qed.
  
    Lemma add_0_r : forall P, (P + E.zero = P)%E.
    Proof.
      Edefn; repeat rewrite ?F_add_0_r, ?F_add_0_l, ?F_sub_0_l, ?F_sub_0_r,
             ?F_mul_0_r, ?F_mul_0_l, ?F_mul_1_l, ?F_mul_1_r, ?F_div_1_r; exact eq_refl.
    Qed.

    Lemma add_0_l : forall P, (E.zero + P)%E = P.
    Proof.
      intros; rewrite add_comm. apply add_0_r.
    Qed.

    Lemma mul_0_l : forall P, (0 * P = E.zero)%E.
    Proof.
      auto.
    Qed.

    Lemma mul_S_l : forall n P, (S n * P)%E = (P + n * P)%E.
    Proof.
      auto.
    Qed.

    Lemma mul_add_l : forall a b P, ((a + b)%nat * P)%E = E.add (a * P)%E (b * P)%E.
    Proof.
      induction a; intros; rewrite ?plus_Sn_m, ?plus_O_n, ?mul_S_l, ?mul_0_l, ?add_0_l, ?mul_S_, ?IHa, ?add_assoc; auto.
    Qed.

    Lemma mul_assoc : forall (n m : nat) P, (n * (m * P) = (n * m)%nat * P)%E.
    Proof.
      induction n; intros; auto.
      rewrite ?mul_S_l, ?Mult.mult_succ_l, ?mul_add_l, ?IHn, add_comm. reflexivity.
    Qed.

    Lemma mul_zero_r : forall m, (m * E.zero = E.zero)%E.
    Proof.
      induction m; rewrite ?mul_S_l, ?add_0_l; auto.
    Qed.
  
    (* solve for x ^ 2 *)
    Definition solve_for_x2 (y : F q) := ((y ^ 2 - 1) / (d * (y ^ 2) - a))%F.
  
    Lemma d_y2_a_nonzero : (forall y, 0 <> d * y ^ 2 - a)%F.
      intros ? eq_zero.
      pose proof prime_q.
      destruct square_a as [sqrt_a sqrt_a_id].
      rewrite <- sqrt_a_id in eq_zero.
      destruct (Fq_square_mul_sub _ _ _ eq_zero) as [ [sqrt_d sqrt_d_id] | a_zero].
      + pose proof (nonsquare_d sqrt_d); auto.
      + subst.
        rewrite Fq_pow_zero in sqrt_a_id by congruence.
        auto using nonzero_a.
    Qed.
  
    Lemma a_d_y2_nonzero : (forall y, a - d * y ^ 2 <> 0)%F.
    Proof.
      intros y eq_zero.
      pose proof prime_q.
      eapply F_minus_swap in eq_zero.
      eauto using (d_y2_a_nonzero y).
    Qed.
  
    Lemma solve_correct : forall x y, E.onCurve (x, y) <->
      (x ^ 2 = solve_for_x2 y)%F.
    Proof.
      split.
      + intro onCurve_x_y.
        pose proof prime_q.
        unfold E.onCurve in onCurve_x_y.
        eapply F_div_mul; auto using (d_y2_a_nonzero y).
        replace (x ^ 2 * (d * y ^ 2 - a))%F with ((d * x ^ 2 * y ^ 2) - (a * x ^ 2))%F by ring.
        rewrite F_sub_add_swap.
        replace (y ^ 2 + a * x ^ 2)%F with (a * x ^ 2 + y ^ 2)%F by ring.
        rewrite onCurve_x_y.
        ring.
      + intro x2_eq.
        unfold E.onCurve, solve_for_x2 in *.
        rewrite x2_eq.
        field.
        auto using d_y2_a_nonzero.
    Qed.
  
  
    Program Definition opp (P:E.point) : E.point := let '(x, y) := proj1_sig P in (opp x, y).
    Next Obligation. Proof.
      pose (proj2_sig P) as H; rewrite <-Heq_anonymous in H; simpl in H.
      rewrite F_square_opp; trivial.
    Qed.
    
    Definition sub P Q := (P + opp Q)%E.
    
    Lemma opp_zero : opp E.zero = E.zero.
    Proof.
      pose proof @F_opp_0.
      unfold opp, E.zero; eapply point_eq; congruence.
    Qed.
  
    Lemma add_opp_r : forall P, (P + opp P = E.zero)%E.
    Proof.
      unfold opp; Edefn; rewrite ?@F_pow_2_r in *; (F_field_simplify_eq; [clear_prm; F_nsatz|..]);
        rewrite <-?@F_pow_2_r in *;
        pose proof (@edwardsAddCompletePlus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d _ _ _ _ pfP pfP);
        pose proof (@edwardsAddCompleteMinus _ _ _ _ two_lt_q nonzero_a square_a nonsquare_d _ _ _ _ pfP pfP);
        field_nonzero idtac.
    Qed.
  
    Lemma add_opp_l : forall P, (opp P + P = E.zero)%E.
    Proof.
      intros. rewrite add_comm. eapply add_opp_r.
    Qed.
  
    Lemma add_cancel_r : forall A B C, (B+A = C+A -> B = C)%E.
    Proof.
      intros.
      assert ((B + A) + opp A = (C + A) + opp A)%E as Hc by congruence.
      rewrite <-!add_assoc, !add_opp_r, !add_0_r in Hc; exact Hc.
    Qed.
  
    Lemma add_cancel_l : forall A B C, (A+B = A+C -> B = C)%E.
    Proof.
      intros.
      rewrite (add_comm A C) in H.
      rewrite (add_comm A B) in H.
      eauto using add_cancel_r.
    Qed.
    
    Lemma shuffle_eq_add_opp : forall P Q R, (P + Q = R <-> Q = opp P + R)%E.
    Proof.
      split; intros.
      { assert (opp P + (P + Q) = opp P + R)%E as Hc by congruence.
        rewrite add_assoc, add_opp_l, add_comm, add_0_r in Hc; exact Hc. }
      { subst. rewrite add_assoc, add_opp_r, add_comm, add_0_r; reflexivity. }
    Qed.
        
    Lemma opp_opp : forall P, opp (opp P) = P.
    Proof.
      intros.
      pose proof (add_opp_r P%E) as H.
      rewrite add_comm in H.
      rewrite shuffle_eq_add_opp in H.
      rewrite add_0_r in H.
      congruence.
    Qed.
    
    Lemma opp_add : forall P Q, opp (P + Q)%E = (opp P + opp Q)%E.
    Proof.
      intros.
      pose proof (add_opp_r (P+Q)%E) as H.
      rewrite <-!add_assoc in H.
      rewrite add_comm in H.
      rewrite <-!add_assoc in H.
      rewrite shuffle_eq_add_opp in H.
      rewrite add_comm in H.
      rewrite shuffle_eq_add_opp in H.
      rewrite add_0_r in H.
      assumption.
    Qed.
      
    Lemma opp_mul : forall n P, opp (E.mul n P) = E.mul n (opp P).
    Proof.
      pose proof opp_add; pose proof opp_zero.
      induction n; simpl; intros; congruence.
    Qed.
  End CompleteEdwardsCurveTheorems.
End E.
Infix "-" := E.sub : E_scope.
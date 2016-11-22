Require Export Crypto.Spec.CompleteEdwardsCurve.

Require Import Crypto.Algebra Crypto.Algebra.
Require Import Crypto.CompleteEdwardsCurve.Pre Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Export Crypto.Util.FixCoqMistakes.

Module Extended.
  Section ExtendedCoordinates.
    Import Group Ring Field.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a d}
            {field:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {prm:@E.twisted_edwards_params F Feq Fzero Fone Fadd Fmul a d}
            {Feq_dec:DecidableRel Feq}.
    Local Infix "=" := Feq : type_scope. Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := Fzero.  Local Notation "1" := Fone.
    Local Infix "+" := Fadd. Local Infix "*" := Fmul.
    Local Infix "-" := Fsub. Local Infix "/" := Fdiv.
    Local Notation "x ^ 2" := (x*x).
    Local Notation Epoint := (@E.point F Feq Fone Fadd Fmul a d).
    Local Notation onCurve := (@Pre.onCurve F Feq Fone Fadd Fmul a d).

    Add Field _edwards_curve_extended_field : (field_theory_for_stdlib_tactic (H:=field)).

    (** [Extended.point] represents a point on an elliptic curve using extended projective
     * Edwards coordinates with twist a=-1 (see <https://eprint.iacr.org/2008/522.pdf>). *)
    Definition point := { P | let '(X,Y,Z,T) := P in onCurve((X/Z), (Y/Z)) /\ Z<>0 /\ Z*T=X*Y }.
    Definition coordinates (P:point) : F*F*F*F := proj1_sig P.

    Create HintDb bash discriminated.
    Local Hint Unfold E.eq fst snd fieldwise fieldwise' coordinates E.coordinates proj1_sig Pre.onCurve : bash.
    Ltac safe_bash :=
      repeat match goal with
             | |- Proper _ _ => intro
             | _ => progress intros
             | [ H: _ /\ _ |- _ ] => destruct H
             | [ p:E.point |- _ ] => destruct p as [ [??] ? ]
             | [ p:point |- _ ] => destruct p as [ [ [ [??] ? ] ? ] ? ]
             | _ => progress autounfold with bash in *
             | |- _ /\ _ => split
             | _ => solve [neq01]
             | _ => solve [eauto]
             | _ => solve [intuition eauto]
             | _ => solve [etransitivity; eauto]
             | |- _ => rewrite <-!(field_div_definition(field:=field)) in *
             | |- _*_ <> 0 => apply Ring.zero_product_iff_zero_factor
             | [H: _ |- _ ] => solve [intro; apply H; super_nsatz]
             | |- Feq _ _ => super_nsatz
             end.
    (** Using [pose proof E.char_gt_2] causes [E.char_gt_2] to get
        picked up in the proof term when we don't want it to. *)
    Ltac unsafe_bash := pose proof E.char_gt_2; safe_bash.
    Ltac bash := safe_bash; unsafe_bash.

    Obligation Tactic := bash.

    Program Definition from_twisted (P:Epoint) : point := exist _
      (let (x,y) := E.coordinates P in (x, y, 1, x*y)) _.

    Program Definition to_twisted (P:point) : Epoint := exist _
      (let '(X,Y,Z,T) := coordinates P in let iZ := Finv Z in ((X*iZ), (Y*iZ))) _.

    Definition eq (P Q:point) := E.eq (to_twisted P) (to_twisted Q).

    Definition eq_noinv (P1 P2:point) :=
        let '(X1, Y1, Z1, _) := coordinates P1 in
        let '(X2, Y2, Z2, _) := coordinates P2 in
        Z2*X1 = Z1*X2 /\ Z2*Y1 = Z1*Y2.

    Local Hint Unfold from_twisted to_twisted eq eq_noinv : bash.

    Lemma eq_noinv_eq P Q : eq P Q <-> eq_noinv P Q.
    Proof. safe_bash; repeat split; safe_bash.  Qed.
    Global Instance DecidableRel_eq_noinv : Decidable.DecidableRel eq_noinv.
    Proof.
      intros P Q.
      destruct P as [ [ [ [ ] ? ] ? ] ?], Q as [ [ [ [ ] ? ] ? ] ? ]; simpl; exact _.
    Defined.
    Global Instance DecidableRel_eq : Decidable.DecidableRel eq.
    Proof.
      intros ? ?.
      eapply @Decidable_iff_to_flip_impl; [eapply eq_noinv_eq | exact _].
    Defined.

    Global Instance Equivalence_eq : Equivalence eq. Proof. split; split; safe_bash. Qed.
    Global Instance Proper_from_twisted : Proper (E.eq==>eq) from_twisted. Proof. unsafe_bash. Qed.
    Global Instance Proper_to_twisted : Proper (eq==>E.eq) to_twisted. Proof. safe_bash. Qed.
    Lemma to_twisted_from_twisted P : E.eq (to_twisted (from_twisted P)) P. Proof. unsafe_bash. Qed.

    Section Proper.
      Global Instance point_Proper : Proper (fieldwise (n:=4) Feq ==> iff)
                                            (fun P => let '(X,Y,Z,T) := P in onCurve((X/Z), (Y/Z)) /\ Z<>0 /\ Z*T=X*Y).
      Proof.
        repeat intro.
        repeat match goal with
               | _ => progress simpl in *
               | [ H : prod _ _ |- _ ] => destruct H
               | [ H : and _ _ |- _ ] => destruct H
               | _ => reflexivity
               | [ H : ?x = ?y |- _ ] => is_var x; rewrite H; clear x H
               end.
      Qed.
      Global Instance point_Proper_impl
        : Proper (fieldwise (n:=4) Feq ==> Basics.impl)
                 (fun P => let '(X,Y,Z,T) := P in onCurve((X/Z), (Y/Z)) /\ Z<>0 /\ Z*T=X*Y).
      Proof.
        intros A B H H'.
        apply (@point_Proper A B H); assumption.
      Qed.
      Global Instance point_Proper_flip_impl
        : Proper (fieldwise (n:=4) Feq ==> Basics.flip Basics.impl)
                 (fun P => let '(X,Y,Z,T) := P in onCurve((X/Z), (Y/Z)) /\ Z<>0 /\ Z*T=X*Y).
      Proof.
        intros A B H H'.
        apply (@point_Proper A B H); assumption.
      Qed.
    End Proper.

    Section TwistMinus1.
      Context {a_eq_minus1 : a = Fopp 1}.
      Context {twice_d:F} {Htwice_d:twice_d = d + d}.
      (** Second equation from <http://eprint.iacr.org/2008/522.pdf> section 3.1, also <https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#addition-add-2008-hwcd-3> and <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
      Section generic.
        Context (F4 : Type)
                (pair4 : F -> F -> F -> F -> F4)
                (let_in : F -> (F -> F4) -> F4).
        Local Notation "'slet' x := y 'in' z" := (let_in y (fun x => z)).
        Definition add_coordinates_gen P1 P2 : F4 :=
          let '(X1, Y1, Z1, T1) := P1 in
          let '(X2, Y2, Z2, T2) := P2 in
          slet  A := (Y1-X1)*(Y2-X2) in
          slet  B := (Y1+X1)*(Y2+X2) in
          slet  C := T1*twice_d*T2 in
          slet  D := Z1*(Z2+Z2) in
          slet  E := B-A in
          slet  F := D-C in
          slet  G := D+C in
          slet  H := B+A in
          slet X3 := E*F in
          slet Y3 := G*H in
          slet T3 := E*H in
          slet Z3 := F*G in
          pair4 X3 Y3 Z3 T3.
      End generic.
      Definition add_coordinates P1 P2 : F*F*F*F :=
        Eval cbv beta delta [add_coordinates_gen] in
          @add_coordinates_gen
            (F*F*F*F)
            (fun X3 Y3 Z3 T3 => (X3, Y3, Z3, T3))
            (fun x f => let y := x in f y)
            P1 P2.

      Local Hint Unfold E.add E.coordinates add_coordinates : bash.

      Lemma add_coordinates_correct (P Q:point) :
        let '(X,Y,Z,T) := add_coordinates (coordinates P) (coordinates Q) in
        let (x, y) := E.coordinates (E.add (to_twisted P) (to_twisted Q)) in
        (fieldwise (n:=2) Feq) (x, y) (X/Z, Y/Z).
      Proof.
        destruct P as [ [ [ [ ] ? ] ? ] [ HP [ ] ] ]; destruct Q as [ [ [ [ ] ? ] ? ] [ HQ [ ] ] ].
        pose proof edwardsAddCompletePlus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ.
        pose proof edwardsAddCompleteMinus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ.
        unsafe_bash.
      Qed.

      Context {add_coordinates_opt}
              {add_coordinates_opt_correct
               : forall P1 P2, fieldwise (n:=4) Feq (add_coordinates_opt P1 P2) (add_coordinates P1 P2)}.

      Obligation Tactic := idtac.
      Program Definition add_unopt (P Q:point) : point := add_coordinates (coordinates P) (coordinates Q).
      Next Obligation.
        clear add_coordinates_opt add_coordinates_opt_correct.
        intros P Q.
        pose proof (add_coordinates_correct P Q) as Hrep.
        pose proof Pre.unifiedAdd'_onCurve(a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) (E.coordinates (to_twisted P)) (E.coordinates (to_twisted Q)) as Hon.
        destruct P as [ [ [ [ ] ? ] ? ] [ HP [ ] ] ]; destruct Q as [ [ [ [ ] ? ] ? ] [ HQ [ ] ] ].
        pose proof edwardsAddCompletePlus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ as Hnz1.
        pose proof edwardsAddCompleteMinus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ as Hnz2.
        autounfold with bash in *; simpl in *.
        destruct Hrep as [HA HB]. rewrite <-!HA, <-!HB; clear HA HB.
        safe_bash.
      Qed.
      Local Hint Unfold add_unopt : bash.

      Program Definition add (P Q:point) : point := add_coordinates_opt (coordinates P) (coordinates Q).
      Next Obligation.
        intros; eapply point_Proper_flip_impl;
          [ apply add_coordinates_opt_correct
          | exact (proj2_sig (add_unopt P Q)) ].
      Qed.
      Local Hint Unfold add : bash.

      Lemma to_twisted_add_unopt P Q : E.eq (to_twisted (add_unopt P Q)) (E.add (to_twisted P) (to_twisted Q)).
      Proof.
        clear add_coordinates_opt add_coordinates_opt_correct.
        pose proof (add_coordinates_correct P Q) as Hrep.
        destruct P as [ [ [ [ ] ? ] ? ] [ HP [ ] ] ]; destruct Q as [ [ [ [ ] ? ] ? ] [ HQ [ ] ] ].
        autounfold with bash in *; simpl in *.
        destruct Hrep as [HA HB].
        pose proof (field_div_definition(field:=field)) as Hdiv; symmetry in Hdiv;
          (rewrite_strat bottomup Hdiv);
          (rewrite_strat bottomup Hdiv in HA);
          (rewrite_strat bottomup Hdiv in HB).
        rewrite <-!HA, <-!HB; clear HA HB.
        split; reflexivity.
      Qed.

      Lemma to_twisted_add P Q : E.eq (to_twisted (add P Q)) (E.add (to_twisted P) (to_twisted Q)).
      Proof.
        rewrite <- to_twisted_add_unopt.
        { pose proof (add_coordinates_opt_correct (coordinates P) (coordinates Q)).
          cbv [add add_unopt].
          do 2 match goal with
               | [ |- context[exist _ ?x ?p] ]
                 => first [ is_var p; fail 1
                          | generalize p; cbv zeta; generalize dependent x ]
               end.
          clear add_coordinates_opt add_coordinates_opt_correct.
          cbv [to_twisted coordinates proj1_sig E.eq E.coordinates fst snd] in *.
          repeat match goal with
                 | _ => intro
                 | [ H : prod _ _ |- _ ] => destruct H
                 | [ H : and _ _ |- _ ] => destruct H
                 | _ => progress simpl in *
                 | [ |- and _ _ ] => split
                 | [ H : ?x = ?y |- context[?x] ] => is_var x; rewrite H
                 | _ => reflexivity
                 end. }
      Qed.

      Global Instance Proper_add : Proper (eq==>eq==>eq) add.
      Proof.
        unfold eq. intros x y H x0 y0 H0.
        transitivity (to_twisted x + to_twisted x0)%E; rewrite to_twisted_add, ?H, ?H0; reflexivity.
      Qed.

      Lemma homomorphism_to_twisted : @Monoid.is_homomorphism point eq add Epoint E.eq E.add to_twisted.
      Proof. split; trivial using Proper_to_twisted, to_twisted_add. Qed.

      Lemma add_from_twisted P Q : eq (from_twisted (P + Q)%E) (add (from_twisted P) (from_twisted Q)).
      Proof.
        pose proof (to_twisted_add (from_twisted P) (from_twisted Q)).
        unfold eq; rewrite !to_twisted_from_twisted in *.
        symmetry; assumption.
      Qed.

      Lemma homomorphism_from_twisted : @Monoid.is_homomorphism Epoint E.eq E.add point eq add from_twisted.
      Proof. split; trivial using Proper_from_twisted, add_from_twisted. Qed.

      Definition zero : point := from_twisted E.zero.
      Definition opp P : point := from_twisted (E.opp (to_twisted P)).
      Lemma extended_group : @group point eq add zero opp.
      Proof.
        eapply @isomorphism_to_subgroup_group; eauto with typeclass_instances core.
        - apply DecidableRel_eq.
        - unfold opp. repeat intro. match goal with [H:_|-_] => rewrite H; reflexivity end.
        - intros. apply to_twisted_add.
        - unfold opp; intros; rewrite to_twisted_from_twisted; reflexivity.
        - unfold zero; intros; rewrite to_twisted_from_twisted; reflexivity.
      Qed.

      (* TODO: decide whether we still need those, then port *)
    (*
    Lemma unifiedAddM1_0_r : forall P, unifiedAddM1 P (mkExtendedPoint E.zero) === P.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, unExtendedPoint_mkExtendedPoint, E.add_0_r; auto.
    Qed.

    Lemma unifiedAddM1_0_l : forall P, unifiedAddM1 (mkExtendedPoint E.zero) P === P.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, E.add_comm, unExtendedPoint_mkExtendedPoint, E.add_0_r; auto.
    Qed.

    Lemma unifiedAddM1_assoc : forall a b c, unifiedAddM1 a (unifiedAddM1 b c) === unifiedAddM1 (unifiedAddM1 a b) c.
    Proof.
      unfold equiv, extendedPoint_eq; intros.
      rewrite <-!unifiedAddM1_rep, E.add_assoc; auto.
    Qed.

    Lemma testbit_conversion_identity : forall x i, N.testbit_nat x i = N.testbit_nat ((fun a => a) x) i.
    Proof.
      trivial.
    Qed.

    Lemma scalarMultM1_rep : forall n P, unExtendedPoint (nat_iter_op unifiedAddM1 (mkExtendedPoint E.zero) n P) = E.mul n (unExtendedPoint P).
      induction n; [simpl; rewrite !unExtendedPoint_mkExtendedPoint; reflexivity|]; intros.
      unfold E.mul; fold E.mul.
      rewrite <-IHn, unifiedAddM1_rep; auto.
    Qed.
     *)
    End TwistMinus1.
  End ExtendedCoordinates.

  Lemma add_coordinates_respectful_hetero
        F Fadd Fsub Fmul twice_d P Q
        F' Fadd' Fsub' Fmul' twice_d' P' Q'
        (R : F -> F' -> Prop)
        (Hadd : forall x x' (Hx : R x x') y y' (Hy : R y y'), R (Fadd x y) (Fadd' x' y'))
        (Hsub : forall x x' (Hx : R x x') y y' (Hy : R y y'), R (Fsub x y) (Fsub' x' y'))
        (Hmul : forall x x' (Hx : R x x') y y' (Hy : R y y'), R (Fmul x y) (Fmul' x' y'))
        (Htwice_d : R twice_d twice_d')
        (HP : Tuple.fieldwise (n:=4) R P P')
        (HQ : Tuple.fieldwise (n:=4) R Q Q')
    : Tuple.fieldwise
        (n:=4) R
        (@add_coordinates F Fadd Fsub Fmul twice_d P Q)
        (@add_coordinates F' Fadd' Fsub' Fmul' twice_d' P' Q').
  Proof.
    repeat match goal with
           | [ H : and _ _ |- _ ] => destruct H
           | [ H : prod _ _ |- _ ] => destruct H
           | _ => progress unfold add_coordinates, fieldwise, fieldwise', fst, snd, tuple, tuple' in *
           | [ |- and _ _ ] => split
           | _ => solve [ auto ]
           end.
  Qed.
End Extended.

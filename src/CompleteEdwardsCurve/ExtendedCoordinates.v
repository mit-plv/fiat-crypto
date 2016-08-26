Require Export Crypto.Spec.CompleteEdwardsCurve.
Require Export Crypto.Util.FixCoqMistakes.
Require Export Crypto.Util.GlobalSettings.

Require Import Crypto.Algebra Crypto.Algebra.
Require Import Crypto.CompleteEdwardsCurve.Pre Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Coq.Logic.Eqdep_dec.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Relations.Relation_Definitions.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.

Module Extended.
  Local Ltac uninv := repeat rewrite <-field_div_definition;
                      repeat match goal with [H:_|-_] => rewrite <-field_div_definition in H end.
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
    (* split [bash] to work around obligation shrinking bug https://coq.inria.fr/bugs/show_bug.cgi?id=5044 *)
    Local Ltac bash_workaround :=
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
             | |- _*_ <> 0 => apply Ring.zero_product_iff_zero_factor
             | [H: _ |- _ ] => solve [intro; apply H; super_nsatz]
             | _ => progress uninv
             | |- Feq _ _ => super_nsatz
             end.
    Local Ltac bash := pose proof E.char_gt_2; bash_workaround.

    Local Obligation Tactic := solve [bash_workaround | bash].

    Program Definition from_twisted (P:Epoint) : point := exist _
      (let (x,y) := E.coordinates P in (x, y, 1, x*y)) _.

    Program Definition to_twisted (P:point) : Epoint := exist _
      (let '(X,Y,Z,T) := coordinates P in let iZ := Finv Z in ((X*iZ), (Y*iZ))) _.

    Definition eq (P Q:point) := E.eq (to_twisted P) (to_twisted Q).
    Global Instance DecidableRel_eq : Decidable.DecidableRel eq := _.

    Local Hint Unfold from_twisted to_twisted eq : bash.

    Global Instance Equivalence_eq : Equivalence eq. Proof. split; split; bash. Qed.
    Global Instance Proper_from_twisted : Proper (E.eq==>eq) from_twisted. Proof. bash. Qed.
    Global Instance Proper_to_twisted : Proper (eq==>E.eq) to_twisted. Proof. bash. Qed.
    Lemma to_twisted_from_twisted P : E.eq (to_twisted (from_twisted P)) P. Proof. bash. Qed.

    Section TwistMinus1.
      Context {a_eq_minus1 : a = Fopp 1}.
      Context {twice_d:F} {Htwice_d:twice_d = d + d}.
      (** Second equation from <http://eprint.iacr.org/2008/522.pdf> section 3.1, also <https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#addition-add-2008-hwcd-3> and <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
      Definition add_coordinates P1 P2 : F*F*F*F :=
        let '(X1, Y1, Z1, T1) := P1 in
        let '(X2, Y2, Z2, T2) := P2 in
        let  A := (Y1-X1)*(Y2-X2) in
        let  B := (Y1+X1)*(Y2+X2) in
        let  C := T1*twice_d*T2 in
        let  D := Z1*(Z2+Z2) in
        let  E := B-A in
        let  F := D-C in
        let  G := D+C in
        let  H := B+A in
        let X3 := E*F in
        let Y3 := G*H in
        let T3 := E*H in
        let Z3 := F*G in
        (X3, Y3, Z3, T3).

      Local Hint Unfold E.add E.coordinates add_coordinates : bash.

      Lemma add_coordinates_correct (P Q:point) :
        let '(X,Y,Z,T) := add_coordinates (coordinates P) (coordinates Q) in
        let (x, y) := E.coordinates (E.add (to_twisted P) (to_twisted Q)) in
        (fieldwise (n:=2) Feq) (x, y) (X/Z, Y/Z).
      Proof.
        destruct P as [ [ [ [ ] ? ] ? ] [ HP [ ] ] ]; destruct Q as [ [ [ [ ] ? ] ? ] [ HQ [ ] ] ].
        pose proof edwardsAddCompletePlus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ.
        pose proof edwardsAddCompleteMinus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ.
        bash.
      Qed.

      Obligation Tactic := idtac.
      Program Definition add (P Q:point) : point := add_coordinates (coordinates P) (coordinates Q).
      Next Obligation.
        intros.
        pose proof (add_coordinates_correct P Q) as Hrep.
        pose proof Pre.unifiedAdd'_onCurve(a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) (E.coordinates (to_twisted P)) (E.coordinates (to_twisted Q)) as Hon.
        destruct P as [ [ [ [ ] ? ] ? ] [ HP [ ] ] ]; destruct Q as [ [ [ [ ] ? ] ? ] [ HQ [ ] ] ].
        pose proof edwardsAddCompletePlus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ as Hnz1.
        pose proof edwardsAddCompleteMinus (a_nonzero:=E.nonzero_a)(a_square:=E.square_a)(d_nonsquare:=E.nonsquare_d)(char_gt_2:=E.char_gt_2) _ _ _ _ HP HQ as Hnz2.
        autounfold with bash in *; simpl in *.
        destruct Hrep as [HA HB]. rewrite <-!HA, <-!HB; clear HA HB.
        bash.
      Qed.
      Local Hint Unfold add : bash.

      Lemma to_twisted_add P Q : E.eq (to_twisted (add P Q)) (E.add (to_twisted P) (to_twisted Q)).
      Proof.
        pose proof (add_coordinates_correct P Q) as Hrep.
        destruct P as [ [ [ [ ] ? ] ? ] [ HP [ ] ] ]; destruct Q as [ [ [ [ ] ? ] ? ] [ HQ [ ] ] ].
        autounfold with bash in *; simpl in *.
        repeat rewrite field_div_definition; repeat rewrite field_div_definition in Hrep.
        destruct Hrep as [HA HB]. rewrite <-!HA, <-!HB; clear HA HB.
        split; reflexivity.
      Qed.

      Global Instance Proper_add : Proper (eq==>eq==>eq) add.
      Proof.
        unfold eq. intros x y H x0 y0 H0.
        transitivity (to_twisted x + to_twisted x0)%E; rewrite to_twisted_add, ?H, ?H0; reflexivity.
      Qed.

      Lemma homomorphism_to_twisted : @Group.is_homomorphism point eq add Epoint E.eq E.add to_twisted.
      Proof. split; trivial using Proper_to_twisted, to_twisted_add. Qed.

      Lemma add_from_twisted P Q : eq (from_twisted (P + Q)%E) (add (from_twisted P) (from_twisted Q)).
      Proof.
        pose proof (to_twisted_add (from_twisted P) (from_twisted Q)).
        unfold eq; rewrite !to_twisted_from_twisted in *.
        symmetry; assumption.
      Qed.

      Lemma homomorphism_from_twisted : @Group.is_homomorphism Epoint E.eq E.add point eq add from_twisted.
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
    End TwistMinus1.
  End ExtendedCoordinates.

  Section Homomorphism.
    Import Group Ring Field.
    Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv Fa Fd}
            {fieldF:@field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
            {Fprm:@E.twisted_edwards_params F Feq Fzero Fone Fadd Fmul Fa Fd}
            {Feq_dec:DecidableRel Feq}.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv Ka Kd}
            {fieldK:@field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Kprm:@E.twisted_edwards_params K Keq Kzero Kone Kadd Kmul Ka Kd}
            {Keq_dec:DecidableRel Keq}.
    Context {phi:F->K} {Hphi:@Ring.is_homomorphism F Feq Fone Fadd Fmul
                                                   K Keq Kone Kadd Kmul phi}.
    Context {phi_nonzero : forall x, ~ Feq x Fzero -> ~ Keq (phi x) Kzero}.
    Context {HFa: Feq Fa (Fopp Fone)} {HKa:Keq Ka (Kopp Kone)}.
    Context {Hd:Keq (phi Fd) Kd} {Kdd Fdd} {HKdd:Keq Kdd (Kadd Kd Kd)} {HFdd:Feq Fdd (Fadd Fd Fd)}.
    Local Notation Fpoint := (@point F Feq Fzero Fone Fadd Fmul Fdiv Fa Fd).
    Local Notation Kpoint := (@point K Keq Kzero Kone Kadd Kmul Kdiv Ka Kd).
    Local Notation FonCurve := (@onCurve F Feq Fone Fadd Fmul Fa Fd).
    Local Notation KonCurve := (@onCurve K Keq Kone Kadd Kmul Ka Kd).

    Lemma Ha : Keq (phi Fa) Ka.
    Proof. rewrite HFa, HKa, <-homomorphism_one. eapply homomorphism_opp. Qed.

    Lemma Hdd : Keq (phi Fdd) Kdd.
    Proof. rewrite HFdd, HKdd. rewrite homomorphism_add. repeat f_equiv; auto. Qed.

    Create HintDb field_homomorphism discriminated.
    Hint Rewrite <-
         homomorphism_one
         homomorphism_add
         homomorphism_sub
         homomorphism_mul
         homomorphism_inv
         homomorphism_div
         Ha
         Hd
         Hdd
      : field_homomorphism.

    Program Definition ref_phi (P:Fpoint) : Kpoint := exist _ (
      let '(X, Y, Z, T) := coordinates P in (phi X, phi Y, phi Z, phi T)) _.
    Next Obligation.
      destruct P as [ [ [ [ ] ? ] ? ] [ ? [ ? ? ] ] ]; unfold onCurve in *; simpl.
      (rewrite_strat bottomup hints field_homomorphism); try assumption.
      eauto 10 using is_homomorphism_phi_proper, phi_nonzero.
    Qed.

    Global Instance Proper_ref_phi : Proper (eq==>eq) ref_phi.
    Proof.
      intros [P ?] [Q ?] [H1 H2]; repeat match goal with [x:prod _ _ |- _ ] => destruct x end.
      cbv in H1, H2; cbv; split; uninv;
        (rewrite_strat bottomup hints field_homomorphism); rewrite ?H1, ?H2; try reflexivity.
    Admitted.
      
    Context {point_phi:Fpoint->Kpoint}
            {point_phi_Proper:Proper (eq==>eq) point_phi}
            {point_phi_correct: forall (P:Fpoint), eq (point_phi P) (ref_phi P)}.

    Lemma lift_homomorphism : @Group.is_homomorphism Fpoint eq (add(a_eq_minus1:=HFa)(Htwice_d:=HFdd)) Kpoint eq (add(a_eq_minus1:=HKa)(Htwice_d:=HKdd)) point_phi.
    Proof.
      repeat match goal with
             | |- Group.is_homomorphism => split
             | |- _ => intro
             | |-  _ /\ _ => split
             | [H: _ /\ _ |- _ ] => destruct H
             | [p: point |- _ ] => destruct p as [ [ [ [ ] ? ] ? ] [ ? [ ? ? ] ] ]
             | |- context[point_phi] => setoid_rewrite point_phi_correct
             | |- _ => progress cbv [fst snd coordinates proj1_sig eq to_twisted E.eq E.coordinates fieldwise fieldwise' add add_coordinates ref_phi] in *
             | _ => progress uninv
             | |- Keq ?x ?x => reflexivity
             | |- Keq ?x ?y => rewrite_strat bottomup hints field_homomorphism
             | [ H : Feq _ _ |- Keq (phi _) (phi _)] => solve [f_equiv; intuition]
             end.
      Admitted. (* TODO(jadep or andreser) *)
  End Homomorphism.
End Extended.
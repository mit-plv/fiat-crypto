Require Import Crypto.Galois.Galois Crypto.Galois.GaloisTheory Crypto.Galois.ComputationalGaloisField.
Require Import Tactics.VerdiTactics.
Require Import Logic.Eqdep_dec.
Require Import BinNums NArith.

Module GaloisDefs (M : Modulus).
  Module Export GT := GaloisTheory M.
End GaloisDefs.

Module Type TwistedEdwardsParams (M : Modulus).
  Module Export GFDefs := GaloisDefs M.
  Local Open Scope GF_scope.
  Parameter a : GF.
  Axiom a_nonzero : a <> 0.
  Axiom a_square : exists x, x * x = a.
  Parameter d : GF.
  Axiom d_nonsquare : forall x, x * x <> d.
End TwistedEdwardsParams.

Definition testbit_rev p i b := Pos.testbit_nat p (b - i).

(* TODO: decide if this should go here or somewhere else (util?) *)
(* implements Pos.iter_op only using testbit, not destructing the positive *)
Definition iter_op  {A} (op : A -> A -> A) (zero : A) (bound : nat) :=
  fix iter (p : positive) (i : nat) (a : A) : A :=
    match i with
    | O => zero
    | S i' => if testbit_rev p i bound
              then op a (iter p i' (op a a))
              else iter p i' (op a a)
    end.

Lemma testbit_rev_xI : forall p i b, (i < S b) ->
  testbit_rev p~1 i (S b) = testbit_rev p i b.
Proof.
  unfold testbit_rev; intros.
  replace (S b - i) with (S (b - i)) by omega.
  case_eq (b - S i); intros; simpl; auto.
Qed.

Lemma testbit_rev_xO : forall p i b, (i < S b) ->
  testbit_rev p~0 i (S b) = testbit_rev p i b.
Proof.
  unfold testbit_rev; intros.
  replace (S b - i) with (S (b - i)) by omega.
  case_eq (b - S i); intros; simpl; auto.
Qed.

Lemma testbit_rev_1 : forall i b, (i < S b) ->
  testbit_rev 1%positive i (S b) = false.
Proof.
  unfold testbit_rev; intros.
  replace (S b - i) with (S (b - i)) by omega.
  case_eq (b - S i); intros; simpl; auto.
Qed.

Lemma iter_op_step_xI : forall {A} p i op z b (a : A), (i < S b) ->
  iter_op op z (S b) p~1 i a = iter_op op z b p i a.
Proof.
  induction i; intros; [pose proof (Gt.gt_irrefl 0); intuition | ].
  simpl; rewrite testbit_rev_xI by omega.
  case_eq i; intros; auto.
  rewrite <- H0; simpl.
  rewrite IHi by omega; auto.
Qed.

Lemma iter_op_step_xO : forall {A} p i op z b (a : A), (i < S b) ->
  iter_op op z (S b) p~0 i a = iter_op op z b p i a.
Proof.
  induction i; intros; [pose proof (Gt.gt_irrefl 0); intuition | ].
  simpl; rewrite testbit_rev_xO by omega.
  case_eq i; intros; auto.
  rewrite <- H0; simpl.
  rewrite IHi by omega; auto.
Qed.

Lemma iter_op_step_1 : forall {A} i op z b (a : A), (i < S b) ->
  iter_op op z (S b) 1%positive i a = z.
Proof.
  induction i; intros; [pose proof (Gt.gt_irrefl 0); intuition | ].
  simpl; rewrite testbit_rev_1 by omega.
  case_eq i; intros; auto.
  rewrite <- H0; simpl.
  rewrite IHi by omega; auto.
Qed.

Lemma pos_size_gt0 : forall p, 0 < Pos.size_nat p.
Proof.
  intros; case_eq p; intros; simpl; auto; try apply Lt.lt_0_Sn.
Qed.
Hint Resolve pos_size_gt0.

Ltac iter_op_step := match goal with
| [ |- context[iter_op ?op ?z ?b ?p~1 ?i ?a] ] => rewrite iter_op_step_xI
| [ |- context[iter_op ?op ?z ?b ?p~0 ?i ?a] ] => rewrite iter_op_step_xO
| [ |- context[iter_op ?op ?z ?b 1%positive ?i ?a] ] => rewrite iter_op_step_1
end; auto.

Lemma iter_op_spec : forall b p {A} op z (a : A) (zero_id : forall x : A, op x z = x), (Pos.size_nat p <= b) ->
  iter_op op z b p b a = Pos.iter_op op p a.
Proof.
  induction b; intros; [pose proof (pos_size_gt0 p); omega |].
  simpl; unfold testbit_rev; rewrite Minus.minus_diag.
  case_eq p; intros; simpl; iter_op_step; simpl; 
  rewrite IHb; rewrite H0 in *; simpl in H; apply Le.le_S_n in H; auto.
Qed.

Module CompleteTwistedEdwardsCurve (M : Modulus) (Import P : TwistedEdwardsParams M).
  Local Open Scope GF_scope.
  (** Twisted Ewdwards curves with complete addition laws. References:
  * <https://eprint.iacr.org/2008/013.pdf>
  * <http://ed25519.cr.yp.to/ed25519-20110926.pdf>
  * <https://eprint.iacr.org/2015/677.pdf>
  *)
  Definition onCurve P := let '(x,y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2.
  Definition point := { P | onCurve P}.
  Definition mkPoint := exist onCurve.

  Definition projX (P:point) := fst (proj1_sig P).
  Definition projY (P:point) := snd (proj1_sig P).

  Definition checkOnCurve x y : if Zbool.Zeq_bool (a*x^2 + y^2) (1 + d*x^2*y^2) then point else True.
    break_if. exists (x, y). exact (GFdecidable  _ _ Heqb). trivial.
  Defined.
  Hint Unfold onCurve mkPoint.

  Definition zero : point. exists (0, 1).
    abstract (unfold onCurve; ring).
  Defined.

  Definition unifiedAdd' (P1' P2' : (GF*GF)) :=
    let '(x1, y1) := P1' in
    let '(x2, y2) := P2' in
    (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) , ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2))).

  Definition unifiedAdd (P1 P2 : point) : point. refine (
    let 'exist P1' pf1 := P1 in
    let 'exist P2' pf2 := P2 in
    mkPoint (unifiedAdd' P1' P2') _).
  Proof.
    destruct P1' as [x1 y1], P2' as [x2 y2]; unfold unifiedAdd', onCurve.
    admit. (* field will likely work here, but I have not done this by hand *)
  Defined.
  Local Infix "+" := unifiedAdd.

  Fixpoint scalarMult (n:nat) (P : point) : point :=
    match n with
    | O => zero
    | S n' => P + scalarMult n' P
    end
  .

  Definition doubleAndAdd (b n : nat) (P : point) : point :=
    match N.of_nat n with
    | 0%N => zero
    | N.pos p => iter_op unifiedAdd zero b p b P
    end.

End CompleteTwistedEdwardsCurve.


Module Type CompleteTwistedEdwardsPointFormat (M : Modulus) (Import P : TwistedEdwardsParams M).
  Local Open Scope GF_scope.
  Module Curve := CompleteTwistedEdwardsCurve M P.
  Parameter point : Type.
  Parameter encode : (GF*GF) -> point.
  Parameter decode : point -> (GF*GF).
  Parameter unifiedAdd : point -> point -> point.

  Parameter rep : point -> (GF*GF) -> Prop.
  Local Notation "P '~=' rP" := (rep P rP) (at level 70).

  Axiom encode_rep: forall P, encode P ~= P.
  Axiom decode_rep : forall P rP, P ~= rP -> decode P = rP.
  Axiom unifiedAdd_rep: forall P Q rP rQ, Curve.onCurve rP -> Curve.onCurve rQ ->
    P ~= rP -> Q ~= rQ -> (unifiedAdd P Q) ~= (Curve.unifiedAdd' rP rQ).
End CompleteTwistedEdwardsPointFormat.

Module CompleteTwistedEdwardsFacts (M : Modulus) (Import P : TwistedEdwardsParams M).
  Local Open Scope GF_scope.
  Module Import Curve := CompleteTwistedEdwardsCurve M P.
  Lemma twistedAddCompletePlus : forall (P1 P2:point),
    let '(x1, y1) := proj1_sig P1 in
    let '(x2, y2) := proj1_sig P2 in
    (1 + d*x1*x2*y1*y2) <> 0.
    (* "Twisted Edwards Curves" <http://eprint.iacr.org/2008/013.pdf> section 6 *)
  Admitted.
  Lemma twistedAddCompleteMinus : forall (P1 P2:point),
    let '(x1, y1) := proj1_sig P1 in
    let '(x2, y2) := proj1_sig P2 in
    (1 - d*x1*x2*y1*y2) <> 0.
    (* "Twisted Edwards Curves" <http://eprint.iacr.org/2008/013.pdf> section 6 *)
  Admitted.

  Lemma point_eq : forall x1 x2 y1 y2,
    x1 = x2 -> y1 = y2 ->
    forall p1 p2,
    mkPoint (x1, y1) p1 = mkPoint (x2, y2) p2.
  Proof.
    intros; subst; f_equal.
    apply (UIP_dec). (* this is a hack. We actually don't care about the equality of the proofs. However, we *can* prove it, and knowing it lets us use the universal equality instead of a type-specific equivalence, which makes many things nicer. *)
    admit. (* GF_eq_dec *)
  Qed.
  Hint Resolve point_eq.

  Hint Unfold unifiedAdd onCurve.
  Ltac twisted := autounfold; intros;
                  repeat (match goal with
                             | [ x : point |- _ ] => destruct x; unfold onCurve in *
                             | [ x : (GF*GF)%type |- _ ] => destruct x
                             | [  |- exist _ _ _ = exist _ _ _ ] => eapply point_eq
                         end; simpl; repeat (ring || f_equal)).
  Local Infix "+" := unifiedAdd.
  Lemma twistedAddComm : forall A B, (A+B = B+A).
  Proof.
    twisted.
  Qed.

  Lemma twistedAddAssoc : forall A B C, A+(B+C) = (A+B)+C.
  Proof.
    (* http://math.rice.edu/~friedl/papers/AAELLIPTIC.PDF *)
  Admitted.

  Lemma zeroIsIdentity : forall P, P + zero = P.
  Admitted.
  Hint Resolve zeroIsIdentity.

  Lemma scalarMult_double : forall n P, scalarMult (n + n) P = scalarMult n (P + P).
  Proof.
    intros.
    replace (n + n)%nat with (n * 2)%nat by omega.
    induction n; simpl; auto.
    rewrite twistedAddAssoc.
    f_equal; auto.
  Qed.

  Lemma iter_op_double : forall p P,
    Pos.iter_op unifiedAdd (p + p) P = Pos.iter_op unifiedAdd p (P + P).
  Proof.
    intros.
    rewrite Pos.add_diag.
    unfold Pos.iter_op; simpl.
    auto.
  Qed.

  Lemma xO_neq1 : forall p, (1 < p~0)%positive.
  Proof.
    induction p; simpl; auto.
    replace 2%positive with (Pos.succ 1) by auto.
    apply Pos.lt_succ_diag_r.
  Qed.

  Lemma xI_neq1 : forall p, (1 < p~1)%positive.
  Proof.
    induction p; simpl; auto.
    replace 3%positive with (Pos.succ (Pos.succ 1)) by auto.
    pose proof (Pos.lt_succ_diag_r (Pos.succ 1)).
    pose proof (Pos.lt_succ_diag_r 1).
    apply (Pos.lt_trans _ _ _ H0 H).
  Qed.

  Lemma xI_is_succ : forall n p
    (H : Pos.of_succ_nat n = p~1%positive),
    (Pos.to_nat (2 * p))%nat = n.
  Proof.
    induction n; intros; simpl in *; auto. {
      pose proof (xI_neq1 p).
      rewrite H in H0.
      pose proof (Pos.lt_irrefl p~1).
      intuition.
    } {
      rewrite Pos.xI_succ_xO in H.
      pose proof (Pos.succ_inj _ _ H); clear H.
      rewrite Pos.of_nat_succ in H0.
      rewrite <- Pnat.Pos2Nat.inj_iff in H0.
      rewrite Pnat.Pos2Nat.inj_xO in H0.
      rewrite Pnat.Nat2Pos.id in H0 by apply NPeano.Nat.neq_succ_0.
      rewrite H0.
      apply Pnat.Pos2Nat.inj_xO.
    }
  Qed.

  Lemma xO_is_succ : forall n p
    (H : Pos.of_succ_nat n = p~0%positive),
    Pos.to_nat (Pos.pred_double p) = n.
  Proof.
    induction n; intros; simpl; auto. {
      pose proof (xO_neq1 p).
      simpl in H; rewrite H in H0.
      pose proof (Pos.lt_irrefl p~0).
      intuition.
    } {
      rewrite Pos.pred_double_spec.
      rewrite <- Pnat.Pos2Nat.inj_iff in H.
      rewrite Pnat.Pos2Nat.inj_xO in H.
      rewrite Pnat.SuccNat2Pos.id_succ in H.
      rewrite Pnat.Pos2Nat.inj_pred by apply xO_neq1.
      rewrite <- NPeano.Nat.succ_inj_wd.
      rewrite Pnat.Pos2Nat.inj_xO.
      rewrite <-  H.
      auto.
    }
  Qed.

  Lemma size_of_succ : forall n,
    Pos.size_nat (Pos.of_nat n) <= Pos.size_nat (Pos.of_nat (S n)).
  Proof.
    intros; induction n; [simpl; auto|].
    apply Pos.size_nat_monotone.
    apply Pos.lt_succ_diag_r.
  Qed.

  Lemma doubleAndAdd_spec : forall n b P, (Pos.size_nat (Pos.of_nat n) <= b) ->
    scalarMult n P = doubleAndAdd b n P.
  Proof.
    induction n; auto; intros.
    unfold doubleAndAdd; simpl.
    rewrite Pos.of_nat_succ.
    rewrite iter_op_spec by auto.
    case_eq (Pos.of_nat (S n)); intros. {
      simpl; f_equal.
      rewrite (IHn b) by (pose proof (size_of_succ n); omega).
      unfold doubleAndAdd.
      rewrite H0 in H.
      rewrite <- Pos.of_nat_succ in H0.
      rewrite <- (xI_is_succ n p) by apply H0.
      rewrite Znat.positive_nat_N; simpl.
      rewrite iter_op_spec; auto.
    } {
      simpl; f_equal.
      rewrite (IHn b) by (pose proof (size_of_succ n); omega).
      unfold doubleAndAdd.
      rewrite <- (xO_is_succ n p) by (rewrite Pos.of_nat_succ; auto).
      rewrite Znat.positive_nat_N; simpl.
      rewrite <- Pos.succ_pred_double in H0.
      rewrite H0 in H.
      rewrite iter_op_spec by
        (try (pose proof (Pos.lt_succ_diag_r (Pos.pred_double p));
        apply Pos.size_nat_monotone in H1; omega); auto).
      rewrite <- iter_op_double.
      rewrite Pos.add_diag.
      rewrite <- Pos.succ_pred_double.
      rewrite Pos.iter_op_succ by apply twistedAddAssoc; auto.
    } {
      rewrite <- Pnat.Pos2Nat.inj_iff in H0.
      rewrite Pnat.Nat2Pos.id in H0 by auto.
      rewrite Pnat.Pos2Nat.inj_1 in H0.
      assert (n = 0)%nat by omega; subst.
      auto.
    }
  Qed.

End CompleteTwistedEdwardsFacts.

Module Type Minus1Params (Import M : Modulus) <: TwistedEdwardsParams M.
  Module Export GFDefs := GaloisDefs M.
  Local Open Scope GF_scope.
  Definition a := inject (- 1).
  Axiom a_nonzero : a <> 0.
  Axiom a_square : exists x, x * x = a.
  Parameter d : GF.
  Axiom d_nonsquare : forall x, x * x <> d.
End Minus1Params.

Module Minus1Format (M : Modulus) (Import P : Minus1Params M) <: CompleteTwistedEdwardsPointFormat M P.
  Local Open Scope GF_scope.
  Module Import Facts := CompleteTwistedEdwardsFacts M P.
  Module Import Curve := Facts.Curve.
  (** [projective] represents a point on an elliptic curve using projective
  * Edwards coordinates for twisted edwards curves with a=-1 (see
  * <https://hyperelliptic.org/EFD/g1p/auto-edwards-projective.html>
  * <https://en.wikipedia.org/wiki/Edwards_curve#Projective_homogeneous_coordinates>) *)
  Record projective := mkProjective {projectiveX : GF; projectiveY : GF; projectiveZ : GF}.
  Local Notation "'(' X ',' Y ',' Z ')'" := (mkProjective X Y Z).

  Definition twistedToProjective (P : (GF*GF)) : projective :=
    let '(x, y) := P in (x, y, 1).

  Definition projectiveToTwisted (P : projective) : GF * GF :=
    let 'mkProjective X Y Z := P in
    pair (X/Z) (Y/Z).
  Hint Unfold projectiveToTwisted twistedToProjective.

  Lemma GFdiv_1 : forall x, x/1 = x.
  Admitted.
  Hint Resolve GFdiv_1.

  Lemma twistedProjectiveInv P : projectiveToTwisted (twistedToProjective P) = P.
  Proof.
    twisted; eapply GFdiv_1.
  Qed.

  (** [extended] represents a point on an elliptic curve using extended projective
  * Edwards coordinates with twist a=-1 (see <https://eprint.iacr.org/2008/522.pdf>). *)
  Record extended := mkExtended {extendedToProjective : projective; extendedT : GF}.

  Definition point := extended.
  Local Notation "'(' X ',' Y ',' Z ',' T ')'" := (mkExtended (X, Y, Z) T).
  Definition extendedValid (P : point) : Prop :=
    let pP := extendedToProjective P in
    let X := projectiveX pP in
    let Y := projectiveY pP in
    let Z := projectiveZ pP in
    let T := extendedT P in
    T = X*Y/Z.


  Definition twistedToExtended (P : (GF*GF)) : point :=
    let '(x, y) := P in (x, y, 1, x*y).
  Definition encode P := let '(x, y) := P in twistedToExtended (x, y).

  Definition decode (P : point) :=
    projectiveToTwisted (extendedToProjective P).
  Local Hint Unfold extendedValid twistedToExtended decode projectiveToTwisted Curve.unifiedAdd'.

  Lemma twistedExtendedInv : forall P,
    decode (twistedToExtended P) = P.
  Proof.
    twisted; eapply GFdiv_1.
  Qed.

  Lemma twistedToExtendedValid : forall P, extendedValid (twistedToExtended P).
  Proof.
    autounfold.
    destruct P.
    simpl.
    rewrite GFdiv_1; reflexivity.
  Qed.

  Definition rep (P:point) (rP:(GF*GF)) : Prop :=
    decode P = rP /\ extendedValid P.
  Local Notation "P '~=' rP" := (rep P rP) (at level 70).
  Ltac rep := repeat progress (intros; autounfold; subst; auto; match goal with
                           | [ x : rep ?a ?b |- _ ] => destruct x
                           end).

  Lemma encode_rep : forall P, encode P ~= P.
  Proof.
    split.
    apply twistedExtendedInv.
    apply twistedToExtendedValid.
  Qed.

  Lemma decode_rep : forall P rP, P ~= rP -> decode P = rP.
  Proof.
    rep.
  Qed.


  Local Notation "2" := (1+1).
  (** Second equation from <http://eprint.iacr.org/2008/522.pdf> section 3.1, also <https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#addition-add-2008-hwcd-3> and <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
  Definition unifiedAdd (P1 P2 : point) : point :=
    let k := 2 * d in
    let pP1 := extendedToProjective P1 in
    let X1 := projectiveX pP1 in
    let Y1 := projectiveY pP1 in
    let Z1 := projectiveZ pP1 in
    let T1 := extendedT P1 in
    let pP2 := extendedToProjective P2 in
    let X2 := projectiveX pP2 in
    let Y2 := projectiveY pP2 in
    let Z2 := projectiveZ pP2 in
    let T2 := extendedT P2 in
    let  A := (Y1-X1)*(Y2-X2) in
    let  B := (Y1+X1)*(Y2+X2) in
    let  C := T1*k*T2 in
    let  D := Z1*2*Z2 in
    let  E := B-A in
    let  F := D-C in
    let  G := D+C in
    let  H := B+A in
    let X3 := E*F in
    let Y3 := G*H in
    let T3 := E*H in
    let Z3 := F*G in
    mkExtended (mkProjective X3 Y3 Z3) T3.

  Delimit Scope extendedM1_scope with extendedM1.
  Infix "+" := unifiedAdd : extendedM1_scope.

  Lemma unifiedAddCon : forall (P1 P2:point)
    (hv1:extendedValid P1) (hv2:extendedValid P2),
    extendedValid (P1 + P2)%extendedM1.
  Proof.
    intros.
    remember ((P1+P2)%extendedM1) as P3.
    destruct P1 as [[X1 Y1 Z1] T1].
    destruct P2 as [[X2 Y2 Z2] T2].
    destruct P3 as [[X3 Y3 Z3] T3].
    unfold extendedValid, extendedToProjective, projectiveToTwisted in *.
    invcs HeqP3.
    subst.
    (* field. -- fails. but it works in sage:
sage -c 'var("d X1 X2 Y1 Y2 Z1 Z2");
print(bool((((Y1 + X1) * (Y2 + X2) - (Y1 - X1) * (Y2 - X2)) *
((Y1 + X1) * (Y2 + X2) - (Y1 - X1) * (Y2 - X2)) ==
((Y1 + X1) * (Y2 + X2) - (Y1 - X1) * (Y2 - X2)) *
(2 * Z1 * Z2 - 2 * ((0 - d) / a) * (X1 * Y1 / Z1) * (X2 * Y2 / Z2)) *
((2 * Z1 * Z2 + 2 * ((0 - d) / a) * (X1 * Y1 / Z1) * (X2 * Y2 / Z2)) *
((Y1 + X1) * (Y2 + X2) - (Y1 - X1) * (Y2 - X2))) /
((2 * Z1 * Z2 - 2 * ((0 - d) / a) * (X1 * Y1 / Z1) * (X2 * Y2 / Z2)) *
(2 * Z1 * Z2 + 2 * ((0 - d) / a) * (X1 * Y1 / Z1) * (X2 * Y2 / Z2))))))'
      Outputs:
        True
    *)
  Admitted.

  Ltac extended0 := repeat progress (autounfold; simpl); intros;
                    repeat match goal with
                           | [ x : Curve.point |- _ ] => destruct x
                           | [ x : point |- _ ] => destruct x
                           | [ x : projective |- _ ] => destruct x
                           end; simpl in *; subst.

  Ltac extended := extended0; repeat (ring || f_equal)(*; field*).

  Lemma unifiedAddToTwisted : forall (P1 P2 : point) tP1 tP2
    (P1con : extendedValid P1) (P1on : Curve.onCurve tP1) (P1rep : decode P1 = tP1)
    (P2con : extendedValid P2) (P2on : Curve.onCurve tP2) (P2rep : decode P2 = tP2),
    decode (P1 + P2)%extendedM1 = Curve.unifiedAdd' tP1 tP2.
  Proof.
    extended0.
    apply f_equal2.
    (* case 1 verified by hand: follows from field and completeness of edwards addition *)
  Admitted.

  Lemma unifiedAdd_rep: forall P Q rP rQ, Curve.onCurve rP -> Curve.onCurve rQ ->
    P ~= rP -> Q ~= rQ -> (unifiedAdd P Q) ~= (Curve.unifiedAdd' rP rQ).
  Proof.
    split; rep.
    apply unifiedAddToTwisted; auto.
    apply unifiedAddCon; auto.
  Qed.
End Minus1Format.


(*
(** [precomputed] represents a point on an elliptic curve using "precomputed"
* Edwards coordinates, as used for fixed-base scalar multiplication
* (see <http://ed25519.cr.yp.to/ed25519-20110926.pdf> section 4: addition). *)
Record precomputed := mkPrecomputed {precomputedSum : GF;
                                   precomputedDifference : GF;
                                   precomputed2dxy : GF}.
Definition twistedToPrecomputed (d:GF) (P : twisted) : precomputed :=
let x := twistedX P in
let y := twistedY P in
mkPrecomputed (y+x) (y-x) (2*d*x*y).
*)

Module WeirstrassMontgomery (Import M : Modulus).
  Module Import GT := GaloisTheory M.
  Local Open Scope GF_scope.
  Local Notation "2" := (1+1).
  Local Notation "3" := (1+1+1).
  Local Notation "4" := (1+1+1+1).
  Local Notation "27" := (3*3*3).
  (** [weierstrass] represents a point on an elliptic curve using Weierstrass
  * coordinates (<http://cs.ucsb.edu/~koc/ccs130h/2013/EllipticHyperelliptic-CohenFrey.pdf>) definition 13.1*)
  Record weierstrass := mkWeierstrass {weierstrassX : GF; weierstrassY : GF}.
  Definition weierstrassOnCurve (a1 a2 a3 a4 a5 a6:GF) (P : weierstrass) : Prop :=
  let x := weierstrassX P in
  let y := weierstrassY P in
  y^2 + a1*x*y + a3*y = x^3 + a2*x^2 + a4*x + a6.

  (** [montgomery] represents a point on an elliptic curve using Montgomery
  * coordinates (see <https://en.wikipedia.org/wiki/Montgomery_curve>) *)
  Record montgomery := mkMontgomery {montgomeryX : GF; montgomeryY : GF}.
  Definition montgomeryOnCurve (B A:GF) (P : montgomery) : Prop :=
  let x := montgomeryX P in
  let y := montgomeryY P in
  B*y^2 = x^3 + A*x^2 + x.

  (** see <http://cs.ucsb.edu/~koc/ccs130h/2013/EllipticHyperelliptic-CohenFrey.pdf> section 13.2.3.c and <https://en.wikipedia.org/wiki/Montgomery_curve#Equivalence_with_Weierstrass_curves> *)
  Definition montgomeryToWeierstrass (B A:GF) (P : montgomery) : weierstrass :=
  let x := montgomeryX P in
  let y := montgomeryY P in
  mkWeierstrass (x/B + A/(3*B)) (y/B).

  Lemma montgomeryToWeierstrassOnCurve : forall (B A:GF) (P:montgomery),
  let a4 := 1/B^2 - A^2/(3*B^2) in
  let a6 := 0- A^3/(27*B^3) - a4*A/(3*B) in
  let P' := montgomeryToWeierstrass B A P in
  montgomeryOnCurve B A P -> weierstrassOnCurve 0 0 0 a4 0 a6 P'.
  Proof.
  intros.
  unfold montgomeryToWeierstrass, montgomeryOnCurve, weierstrassOnCurve in *.
  remember (weierstrassY P') as y in *.
  remember (weierstrassX P') as x in *.
  remember (montgomeryX P) as u in *.
  remember (montgomeryY P) as v in *.
  clear Hequ Heqv Heqy Heqx P'.
  (* This is not currently important and makes field run out of memory. Maybe
  * because I transcribed it incorrectly... *)
  Abort.


  (* from <http://www.hyperelliptic.org/EFD/g1p/auto-montgom.html> *)
  Definition montgomeryAddDistinct (B A:GF) (P1 P2:montgomery) : montgomery :=
  let x1 := montgomeryX P1 in
  let y1 := montgomeryY P1 in
  let x2 := montgomeryX P2 in
  let y2 := montgomeryY P2 in
  mkMontgomery
  (B*(y2-y1)^2/(x2-x1)^2-A-x1-x2)
  ((2*x1+x2+A)*(y2-y1)/(x2-x1)-B*(y2-y1)^3/(x2-x1)^3-y1).
  Definition montgomeryDouble (B A:GF) (P1:montgomery) : montgomery :=
  let x1 := montgomeryX P1 in
  let y1 := montgomeryY P1 in
  mkMontgomery
  (B*(3*x1^2+2*A*x1+1)^2/(2*B*y1)^2-A-x1-x1)
  ((2*x1+x1+A)*(3*x1^2+2*A*x1+1)/(2*B*y1)-B*(3*x1^2+2*A*x1+1)^3/(2*B*y1)^3-y1).
  Definition montgomeryNegate P := mkMontgomery (montgomeryX P) (0-montgomeryY P).

  (** [montgomeryXFrac] represents a point on an elliptic curve using Montgomery x
  * coordinate stored as fraction as in
  * <http://cr.yp.to/ecdh/curve25519-20060209.pdf> appendix B. *)
  Record montgomeryXFrac := mkMontgomeryXFrac {montgomeryXFracX : GF; montgomeryXFracZ : GF}.
  Definition montgomeryToMontgomeryXFrac P := mkMontgomeryXFrac (montgomeryX P) 1.
  Definition montgomeryXFracToMontgomeryX P : GF := (montgomeryXFracX P) / (montgomeryXFracZ P).

  (* from <http://www.hyperelliptic.org/EFD/g1p/auto-montgom-xz.html#ladder-mladd-1987-m>,
  * also appears in <https://tools.ietf.org/html/draft-josefsson-tls-curve25519-06#appendix-A.1.3> *)
  Definition montgomeryDifferentialDoubleAndAdd (a : GF)
  (X1 : GF) (P2 P3 : montgomeryXFrac) : (montgomeryXFrac * montgomeryXFrac) :=
    let X2 := montgomeryXFracX P2 in
    let Z2 := montgomeryXFracZ P2 in
    let X3 := montgomeryXFracX P3 in
    let Z3 := montgomeryXFracZ P3 in
    let A  := X2 + Z2 in
    let AA := A^2 in
    let B  := X2 - Z2 in
    let BB := B^2 in
    let E  := AA - BB in
    let C  := X3 + Z3 in
    let D  := X3 - Z3 in
    let DA := D * A in
    let CB := C * B in
    let X5 := (DA + CB)^2 in
    let Z5 := X1 * (DA - CB)^2 in
    let X4 := AA * BB in
    let Z4 := E * (BB + (a-2)/4 * E) in
    (mkMontgomeryXFrac X4 Z4, mkMontgomeryXFrac X5 Z5).

  (*
  (* <https://eprint.iacr.org/2008/013.pdf> Theorem 3.2. *)
  (* TODO: exceptional points *)
  Definition twistedToMontfomery (a d:GF) (P : twisted) : montgomery :=
  let x := twistedX P in
  let y := twistedY P in
  mkMontgomery ((1+y)/(1-y)) ((1+y)/((1-y)*x)).
  Definition montgomeryToTwisted (B A:GF) (P : montgomery) : twisted :=
  let X := montgomeryX P in
  let Y := montgomeryY P in
  mkTwisted (X/Y) ((X-1)/(X+1)).
  *)

End WeirstrassMontgomery.

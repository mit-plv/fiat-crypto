Require Import Crypto.Galois.GaloisTheory Crypto.Galois.GaloisField.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Logic Logic.Eqdep_dec.
Require Import BinNums NArith Nnat ZArith.

Module Type TwistedEdwardsParams (M : Modulus).
  Module Export GFDefs := GaloisField M.
  Local Open Scope GF_scope.
  Axiom char_gt_2 : (1+1) <> 0.
  Parameter a : GF.
  Axiom a_nonzero : a <> 0.
  Parameter sqrt_a : GF.
  Axiom a_square : sqrt_a^2 = a.
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
  (** Twisted Edwards curves with complete addition laws. References:
  * <https://eprint.iacr.org/2008/013.pdf>
  * <http://ed25519.cr.yp.to/ed25519-20110926.pdf>
  * <https://eprint.iacr.org/2015/677.pdf>
  *)
  Definition onCurve P := let '(x,y) := P in a*x^2 + y^2 = 1 + d*x^2*y^2.
  Definition point := { P | onCurve P}.
  Definition mkPoint := exist onCurve.

  Lemma GFdecidable_neq : forall x y : GF, Zbool.Zeq_bool x y = false -> x <> y.
  Proof.
    intros. intro. rewrite GFcomplete in H; intuition.
  Qed.

  Ltac case_eq_GF a b :=
    case_eq (Zbool.Zeq_bool a b); intro Hx;
    match type of Hx with
    | Zbool.Zeq_bool (GFToZ a) (GFToZ b) = true =>
        pose proof (GFdecidable a b Hx)
    | Zbool.Zeq_bool (GFToZ a) (GFToZ b) = false =>
        pose proof (GFdecidable_neq a b Hx)
    end; clear Hx.

  Ltac rewriteAny := match goal with [H: _ = _ |- _ ] => rewrite H end.
  Ltac rewriteLeftAny := match goal with [H: _ = _ |- _ ] => rewrite <- H end.

  (* https://eprint.iacr.org/2007/286.pdf Theorem 3.3 *)
  (* c=1 and an extra a in front of x^2 *) 

  (* NOTE: these should serve as an example for using field *)

  Lemma mul_nonzero_l : forall a b, a*b <> 0 -> a <> 0.
    intros; intuition; subst.
    assert (0 * b = 0) by field; intuition.
  Qed.

  Lemma mul_nonzero_r : forall a b, a*b <> 0 -> b <> 0.
    intros; intuition; subst.
    assert (a0 * 0 = 0) by field; intuition.
  Qed.

  Definition GF_eq_dec : forall x y : GF, {x = y} + {x <> y}.
    intros.
    assert (H := Z.eq_dec (inject x) (inject y)).

    destruct H.
    
    - left; galois; intuition.

    - right; intuition.
      rewrite H in n.
      assert (y = y); intuition.
  Qed.

  Lemma mul_zero_why : forall a b, a*b = 0 -> a = 0 \/ b = 0.
    intros.
    assert (Z := GF_eq_dec a0 0); destruct Z.

    - left; intuition.

    - assert (a0 * b / a0 = 0) by
        ( rewrite H; field; intuition ).

      field_simplify in H0.
      replace (b/1) with b in H0 by (field; intuition).
      right; intuition.
      apply n in H0; intuition.
  Qed.

  Lemma mul_nonzero_nonzero : forall a b, a <> 0 -> b <> 0 -> a*b <> 0.
    intros; intuition; subst.
    apply mul_zero_why in H1.
    destruct H1; subst; intuition.
  Qed.
  Hint Resolve mul_nonzero_nonzero.

  Lemma root_zero : forall (x: GF) (p: N), x^p = 0 -> x = 0.
    intros.

    induction p; inversion H.

    revert H H1; generalize x; induction p; intros.

    - simpl in H; apply mul_zero_why in H; destruct H; intuition.

      + subst; intuition.

      + apply IHp in H.
        rewrite H1.
        simpl in H1.
        apply mul_zero_why in H1; destruct H1; intuition.
        rewrite H0 in H.
        apply mul_zero_why in H; destruct H; intuition.

        simpl; intuition.

    - simpl in H1; apply IHp in H1; simpl; intuition.
      simpl in H; rewrite H in H1; rewrite H.
      apply mul_zero_why in H1; destruct H1; intuition.

    - simpl in H; subst; intuition.

  Qed.

  Lemma root_nonzero : forall x p, x^p <> 0 -> (p <> 0)%N -> x <> 0.
    intros; intuition.

    induction p.

    - apply H; intuition.

    - apply H.
      rewrite H1 in *.
      induction p.

      + simpl.
        field.

      + simpl in *.
        replace (0 * 0) with 0 in * by field.
        apply IHp; intuition.
        induction p; inversion H2.

      + simpl; intuition.

  Qed.

  Ltac whatsNotZero :=
    repeat match goal with
    | [H: ?lhs = ?rhs |- _ ] =>
        match goal with [Ha: lhs <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (lhs <> 0) by (rewrite H; auto)
    | [H: ?lhs = ?rhs |- _ ] =>
        match goal with [Ha: rhs <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (rhs <> 0) by (rewrite H; auto)
    | [H: (?a^?p)%GF <> 0 |- _ ] =>
        match goal with [Ha: a <> 0 |- _ ] => fail 1 | _ => idtac end;
        let Y:=fresh in let Z:=fresh in try (
          assert (p <> 0%N) as Z by (intro Y; inversion Y);
          assert (a <> 0) by (eapply root_nonzero; eauto);
          clear Z)
    | [H: (?a*?b)%GF <> 0 |- _ ] =>
        match goal with [Ha: a <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (a <> 0) by (eapply mul_nonzero_l; eauto)
    | [H: (?a*?b)%GF <> 0 |- _ ] =>
        match goal with [Ha: b <> 0 |- _ ] => fail 1 | _ => idtac end;
        assert (b <> 0) by (eapply mul_nonzero_r; eauto)
    end.

  Lemma edwardsAddComplete' x1 y1 x2 y2 :
    onCurve (x1,y1) ->
    onCurve (x2, y2) ->
    (d*x1*x2*y1*y2)^2 <> 1.
  Proof.
    (* TODO: this proof was made inconsistent by an actually
             correct version of root_nonzero. This adds the necessary
             hypothesis*)
    unfold onCurve; intuition; whatsNotZero.

    pose proof char_gt_2. pose proof a_nonzero as Ha_nonzero. 
    destruct a_square as [sqrt_a a_square].
    rewrite a_square in Ha_nonzero.

    (* Furthermore... *)
    pose proof (eq_refl (d*x1^2*y1^2*(sqrt_a^2*x2^2 + y2^2))) as Heqt.
    rewrite H0 in Heqt at 2.
    replace (d * x1 ^ 2 * y1 ^ 2 * (1 + d * x2 ^ 2 * y2 ^ 2))
       with (d*x1^2*y1^2 + (d*x1*x2*y1*y2)^2) in Heqt by field.
    rewrite H1 in Heqt.
    replace (d * x1 ^ 2 * y1 ^ 2 + 1) with (1 + d * x1 ^ 2 * y1 ^ 2) in Heqt by field.
    rewrite <-H in Heqt.

    (* main equation for both potentially nonzero denominators *)
    case_eq_GF (sqrt_a*x2 + y2) 0; case_eq_GF (sqrt_a*x2 - y2) 0;
      try match goal with [H: ?f (sqrt_a * x2)  y2 <> 0 |- _ ] =>
        assert ((f (sqrt_a*x1) (d * x1 * x2 * y1 * y2*y1))^2 =
                 f ((sqrt_a^2)*x1^2 + (d * x1 * x2 * y1 * y2)^2*y1^2)
                   (d * x1 * x2 * y1 * y2*sqrt_a*(inject 2)*x1*y1)) as Heqw1 by field;
        rewrite H1 in *;
        replace (1 * y1^2) with (y1^2) in * by field;
        rewrite <- Heqt in *;
        assert (d = (f (sqrt_a * x1) (d * x1 * x2 * y1 * y2 * y1))^2 /
                                 (x1 * y1 * (f (sqrt_a * x2)  y2))^2)
                                 by (rewriteAny; field; auto);
        match goal with [H: d = (?n^2)/(?l^2) |- _ ] =>
            destruct (d_nonsquare (n/l)); (remember n; rewriteAny; field; auto)
        end
      end.

    assert (Hc: (sqrt_a * x2 + y2) + (sqrt_a * x2 - y2) = 0) by (repeat rewriteAny; field).

    rewrite a_square in *.
    replace (sqrt_a * x2 + y2 + (sqrt_a * x2 - y2)) with (inject 2 * sqrt_a * x2) in Hc by field.

    (* contradiction: product of nonzero things is zero *)
    destruct (mul_zero_why _ _ Hc) as [Hcc|Hcc]; try solve [subst; intuition].
    destruct (mul_zero_why _ _ Hcc) as [Hccc|Hccc]; subst; intuition; apply Ha_nonzero.

    + replace (inject 2%Z) with (1+1) in Hccc by field; intuition.

    + rewrite <- a_square; simpl; rewrite Hccc; field.
  Qed.
  Lemma edwardsAddCompletePlus x1 y1 x2 y2 :
    onCurve (x1,y1) ->
    onCurve (x2, y2) ->
    (1 + d*x1*x2*y1*y2) <> 0.
  Proof.
    unfold onCurve; intros; case_eq_GF (d*x1*x2*y1*y2) (0-1)%GF.
    - assert ((d*x1*x2*y1*y2)^2 = 1) by (rewriteAny; field). destruct (edwardsAddComplete' x1 y1 x2 y2); auto.
    - replace (d * x1 * x2 * y1 * y2) with (1+d * x1 * x2 * y1 * y2-1) in H1 by field.
      intro; rewrite H2 in H1; intuition.
  Qed.
  
  Lemma edwardsAddCompleteMinus x1 y1 x2 y2 :
    onCurve (x1,y1) ->
    onCurve (x2, y2) ->
    (1 - d*x1*x2*y1*y2) <> 0.
  Proof.
    unfold onCurve; intros; case_eq_GF (d*x1*x2*y1*y2) (1)%GF.
    - assert ((d*x1*x2*y1*y2)^2 = 1) by (rewriteAny; field). destruct (edwardsAddComplete' x1 y1 x2 y2); auto.
    - replace (d * x1 * x2 * y1 * y2) with ((1-(1-d * x1 * x2 * y1 * y2))) in H1 by field.
      intro; rewrite H2 in H1; apply H1; field.
  Qed.
  Hint Resolve edwardsAddCompletePlus edwardsAddCompleteMinus.

  Definition projX (P:point) := fst (proj1_sig P).
  Definition projY (P:point) := snd (proj1_sig P).

  Definition checkOnCurve (x y: GF) : if Zbool.Zeq_bool (a*x^2 + y^2)%GF (1 + d*x^2*y^2)%GF then point else True.
    break_if; trivial. exists (x, y). apply GFdecidable. exact Heqb.
  Defined.
  Local Hint Unfold onCurve mkPoint.

  Definition zero : point. exists (0, 1).
    abstract (unfold onCurve; field).
  Defined.

  Definition unifiedAdd' (P1' P2' : (GF*GF)) :=
    let '(x1, y1) := P1' in
    let '(x2, y2) := P2' in
    (((x1*y2  +  y1*x2)/(1 + d*x1*x2*y1*y2)) , ((y1*y2 - a*x1*x2)/(1 - d*x1*x2*y1*y2))).

  Lemma unifiedAdd'_onCurve x1 y1 x2 y2 x3 y3
    (H: (x3, y3) = unifiedAdd' (x1, y1) (x2, y2)) :
    onCurve (x1,y1) -> onCurve (x2, y2) -> onCurve (x3, y3).
  Proof.
    (* https://eprint.iacr.org/2007/286.pdf Theorem 3.1;
      * c=1 and an extra a in front of x^2 *) 

    unfold unifiedAdd', onCurve in *; injection H; clear H; intros.

    Ltac t x1 y1 x2 y2 :=
      assert ((a*x2^2 + y2^2)*d*x1^2*y1^2
             = (1 + d*x2^2*y2^2) * d*x1^2*y1^2) by (rewriteAny; auto);
      assert (a*x1^2 + y1^2 - (a*x2^2 + y2^2)*d*x1^2*y1^2
             = 1 - d^2*x1^2*x2^2*y1^2*y2^2) by (repeat rewriteAny; field).
    t x1 y1 x2 y2; t x2 y2 x1 y1.

    remember ((a*x1^2 + y1^2 - (a*x2^2+y2^2)*d*x1^2*y1^2)*(a*x2^2 + y2^2 -
      (a*x1^2 + y1^2)*d*x2^2*y2^2)) as T.
    assert (HT1: T = (1 - d^2*x1^2*x2^2*y1^2*y2^2)^2) by (repeat rewriteAny; field).
    assert (HT2: T = (a * ((x1 * y2 + y1 * x2) * (1 - d * x1 * x2 * y1 * y2)) ^ 2 +(
    (y1 * y2 - a * x1 * x2) * (1 + d * x1 * x2 * y1 * y2)) ^ 2 -d * ((x1 *
     y2 + y1 * x2)* (y1 * y2 - a * x1 * x2))^2)) by (subst; field).
    replace 1 with (a*x3^2 + y3^2 -d*x3^2*y3^2); [field|]; subst x3 y3.

    match goal with [ |- ?x = 1 ] => replace x with
    ((a * ((x1 * y2 + y1 * x2) * (1 - d * x1 * x2 * y1 * y2)) ^ 2 +
     ((y1 * y2 - a * x1 * x2) * (1 + d * x1 * x2 * y1 * y2)) ^ 2 -
      d*((x1 * y2 + y1 * x2) * (y1 * y2 - a * x1 * x2)) ^ 2)/
    ((1-d^2*x1^2*x2^2*y1^2*y2^2)^2)) end; try field; auto.
    - rewrite <-HT1, <-HT2; field; rewrite HT1.
      replace ((1 - d ^ 2 * x1 ^ 2 * x2 ^ 2 * y1 ^ 2 * y2 ^ 2))
         with ((1 - d*x1*x2*y1*y2)*(1 + d*x1*x2*y1*y2))
           by field; simpl; auto.
    - replace (1 - (d * x1 * x2 * y1 * y2) ^ 2)
         with ((1 - d*x1*x2*y1*y2)*(1 + d*x1*x2*y1*y2))
           by field; auto.
  Qed.

  Lemma unifiedAdd'_onCurve' : forall P1 P2, onCurve P1 -> onCurve P2 ->
    onCurve (unifiedAdd' P1 P2).
  Proof.
    intros; destruct P1, P2.
    remember (unifiedAdd' (g, g0) (g1, g2)) as p; destruct p.
    eapply unifiedAdd'_onCurve; eauto.
  Qed.

  Definition unifiedAdd (P1 P2 : point) : point :=
    let 'exist P1' pf1 := P1 in
    let 'exist P2' pf2 := P2 in
    mkPoint (unifiedAdd' P1' P2') (unifiedAdd'_onCurve' _ _ pf1 pf2).
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

  Lemma point_eq : forall x1 x2 y1 y2,
    x1 = x2 -> y1 = y2 ->
    forall p1 p2,
    mkPoint (x1, y1) p1 = mkPoint (x2, y2) p2.
  Proof.
    intros; subst; f_equal.
    apply (UIP_dec). (* this is a hack. We actually don't care about the equality of the proofs. However, we *can* prove it, and knowing it lets us use the universal equality instead of a type-specific equivalence, which makes many things nicer. *)
    apply GF_eq_dec.
  Qed.
  Hint Resolve point_eq.

  Local Hint Unfold unifiedAdd onCurve mkPoint.
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

  Lemma zeroIsIdentity' : forall P, unifiedAdd' P (proj1_sig zero) = P.
    unfold unifiedAdd', zero; simpl; intros; break_let; f_equal; field; auto.
  Qed.

  Lemma zeroIsIdentity : forall P, P + zero = P.
    (* Should follow from zeroIsIdentity', but dependent types... *)
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
  Module Export GFDefs := GaloisField M.
  Local Open Scope GF_scope.
  Axiom char_gt_2 : (1+1) <> 0.
  Definition a := inject (- 1).
  Axiom a_nonzero : a <> 0.
  Parameter sqrt_a : GF.
  Axiom a_square : sqrt_a^2 = a.
  Parameter d : GF.
  Axiom d_nonsquare : forall x, x * x <> d.
End Minus1Params.

Module ExtendedM1 (M : Modulus) (Import P : Minus1Params M) <: CompleteTwistedEdwardsPointFormat M P.
  Local Hint Unfold a.
  Local Open Scope GF_scope.
  Module Import Facts := CompleteTwistedEdwardsFacts M P.
  Module Import Curve := Facts.Curve.

  (* TODO: move to wherever GF theorems are *)
  Lemma GFdiv_1 : forall x, x/1 = x.
  Proof.
    intros; field; auto.
  Qed.
  Hint Resolve GFdiv_1.

  (** [extended] represents a point on an elliptic curve using extended projective
  * Edwards coordinates with twist a=-1 (see <https://eprint.iacr.org/2008/522.pdf>). *)
  Record extended := mkExtended {extendedX : GF;
                                 extendedY : GF;
                                 extendedZ : GF;
                                 extendedT : GF}.
  Local Notation "'(' X ',' Y ',' Z ',' T ')'" := (mkExtended X Y Z T).
  Definition point := extended.

  Definition encode (P : (GF*GF)) : point :=
    let '(x, y) := P in (x, y, 1, x*y).
  Definition decode (P : point) : GF * GF :=
    let '(X, Y, Z, T) := P in ((X/Z), (Y/Z)).
  Definition rep (P:point) (rP:(GF*GF)) : Prop :=
    let '(X, Y, Z, T) := P in
    decode P = rP /\
    Z <> 0 /\
    T = X*Y/Z.
  Local Hint Unfold encode decode rep.
  Local Notation "P '~=' rP" := (rep P rP) (at level 70).

  Ltac extended_tac :=
    repeat progress (autounfold; intros);
    repeat match goal with
      | [ p : (GF*GF)%type |- _ ] =>
          let x := fresh "x" in
          let y := fresh "y" in
          destruct p as [x y]
      | [ p : point |- _ ] =>
          let X := fresh "X" in
          let Y := fresh "Y" in
          let Z := fresh "Z" in
          let T := fresh "T" in
          destruct p as [X Y Z T]
      | [ H: _ /\ _ |- _ ] => destruct H
      | [ |- _ /\ _ ] => split
      | [ H: @eq (GF * GF)%type _ _ |- _ ] => invcs H
      | [ H: @eq GF ?x _ |- _ ] => isVar x; rewrite H; clear H
      | [ |- @eq (GF * GF)%type _ _] => apply f_equal2
      | [ |- @eq GF _ _] => field
      | [ |- _ ] => progress eauto
  end.

  Lemma encode_rep : forall P, encode P ~= P.
  Proof.
    extended_tac.
  Qed.

  Lemma decode_rep : forall P rP, P ~= rP -> decode P = rP.
  Proof.
    extended_tac.
  Qed.

  Local Notation "2" := (1+1).
  (** Second equation from <http://eprint.iacr.org/2008/522.pdf> section 3.1, also <https://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html#addition-add-2008-hwcd-3> and <https://tools.ietf.org/html/draft-josefsson-eddsa-ed25519-03> *)
  Definition unifiedAdd (P1 P2 : point) : point :=
    let '(X1, Y1, Z1, T1) := P1 in
    let '(X2, Y2, Z2, T2) := P2 in
    let  A := (Y1-X1)*(Y2-X2) in
    let  B := (Y1+X1)*(Y2+X2) in
    let  C := T1*2*d*T2 in
    let  D := Z1*2  *Z2 in
    let  E := B-A in
    let  F := D-C in
    let  G := D+C in
    let  H := B+A in
    let X3 := E*F in
    let Y3 := G*H in
    let T3 := E*H in
    let Z3 := F*G in
    (X3, Y3, Z3, T3).
  Local Hint Unfold unifiedAdd.

  Delimit Scope extendedM1_scope with extendedM1.
  Infix "+" := unifiedAdd : extendedM1_scope.

  Lemma char_gt_2 : 2 <> 0.
  Admitted.
  Hint Resolve char_gt_2.

  Local Hint Unfold unifiedAdd'.
  Lemma unifiedAdd_rep: forall P Q rP rQ, Curve.onCurve rP -> Curve.onCurve rQ ->
    P ~= rP -> Q ~= rQ -> (unifiedAdd P Q) ~= (Curve.unifiedAdd' rP rQ).
  Proof.
    extended_tac;
      pose proof (edwardsAddCompletePlus _ _ _ _ H0 H) as Hp;
      pose proof (edwardsAddCompleteMinus _ _ _ _ H0 H) as Hm.

    (* If we we had reasoning modulo associativity and commutativity,
    *  the following tactic would probably solve all 10 goals here:
    repeat match goal with [H1: @eq GF _ _, H2: @eq GF _ _ |- _ ] =>
      let H := fresh "H" in ( 
        pose proof (edwardsAddCompletePlus _ _ _ _ H1 H2) as H;
        match type of H with ?xs <> 0 => ac_rewrite (eq_refl xs) end
      ) || (
        pose proof (edwardsAddCompleteMinus _ _ _ _ H1 H2) as Hm;
        match type of H with ?xs <> 0 => ac_rewrite (eq_refl xs) end
      ); repeat apply mul_nonzero_nonzero; auto 10
    end.
    *)

    - replace (Z0 * Z * Z0 * Z + d * X0 * X * Y0 * Y) with (Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * inject 2 * Z * (Z0 * Z) + X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * inject 2 * Z * (Z0 * Z) - X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * Z * Z0 * Z - d * X0 * X * Y0 * Y) with (Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * inject 2 * Z * (Z0 * Z) + X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * inject 2 * Z * (Z0 * Z) - X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * Z * Z0 * Z - d * X0 * X * Y0 * Y) with (Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto).
    repeat apply mul_nonzero_nonzero.
      + replace (Z0 * 2 * Z - X0 * Y0 / Z0 * 2 * d * (X * Y / Z)) with (2*Z*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
      + replace (Z0 * 2 * Z + X0 * Y0 / Z0 * 2 * d * (X * Y / Z)) with (2*Z*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * inject 2 * Z * (Z0 * Z) + X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 + d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
    - replace (Z0 * inject 2 * Z * (Z0 * Z) - X0 * Y0 * inject 2 * d * (X * Y)) with (2*Z*Z*Z0*Z0* (1 - d * (X / Z) * (X0 / Z0) * (Y / Z) * (Y0 / Z0))) by (field; auto); auto 10.
  Qed.
End ExtendedM1.


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

Require Import Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Equality.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Bedrock.Word.
Require Import Crypto.Encoding.ModularWordEncodingTheorems.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Algebra.

Require Import Crypto.Spec.Encoding Crypto.Spec.ModularWordEncoding Crypto.Spec.ModularArithmetic.

Generalizable All Variables.
Section PointEncodingPre.
  Context {F eq zero one opp add sub mul inv div} `{field F eq zero one opp add sub mul inv div}.
  Local Infix "==" := eq (at level 30) : type_scope.
  Local Notation "a !== b" := (not (a == b)) (at level 30): type_scope.
  Local Notation "0" := zero.  Local Notation "1" := one.
  Local Infix "+" := add. Local Infix "*" := mul.
  Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "x '^' 2" := (x*x) (at level 30).

  Add Field EdwardsCurveField : (Field.field_theory_for_stdlib_tactic (T:=F)).
  
  Context {eq_dec:forall x y : F, {x==y}+{x==y->False}}.
  Definition F_eqb x y := if eq_dec x y then true else false.
  Lemma F_eqb_iff : forall x y, F_eqb x y = true <-> x == y.
  Proof.
    unfold F_eqb; intros; destruct (eq_dec x y); split; auto; discriminate.
  Qed.

  Context {a d:F} {prm:@E.twisted_edwards_params F eq zero one add mul a d}.
  Local Notation point := (@E.point F eq one add mul a d).
  Local Notation onCurve := (@onCurve F eq one add mul a d).
  Local Notation solve_for_x2 := (@E.solve_for_x2 F one sub mul div a d).

  Context {sz : nat} (sz_nonzero : (0 < sz)%nat).
  Context {sqrt : F -> F} (sqrt_square : forall x root, x == (root ^2) -> sqrt x == root)
    (sqrt_subst : forall x y, x == y -> sqrt x == sqrt y).
  Context (FEncoding : canonical encoding of F as (word sz)).
  Context {sign_bit : F -> bool} (sign_bit_zero : forall x, x == 0 -> Logic.eq (sign_bit x) false)
    (sign_bit_opp : forall x, x !== 0 -> Logic.eq (negb (sign_bit x)) (sign_bit (opp x)))
    (sign_bit_subst : forall x y, x == y -> sign_bit x = sign_bit y).

  Definition sqrt_ok (a : F) := (sqrt a) ^ 2 == a.

  Lemma square_sqrt : forall y root, y == (root ^2) ->
    sqrt_ok y.
  Proof.
    unfold sqrt_ok; intros ? ? root2_y.
    pose proof root2_y.
    apply sqrt_square in root2_y.
    rewrite root2_y.
    symmetry; assumption.
  Qed.

  Lemma solve_onCurve: forall x y : F, onCurve (x,y) ->
    onCurve (sqrt (solve_for_x2 y), y).
  Proof.
    intros.
    apply E.solve_correct.
    eapply square_sqrt.
    symmetry.
    apply E.solve_correct; eassumption.
  Qed.
 
  (* TODO : move? *)
  Lemma square_opp : forall x : F, (opp x ^2) == (x ^2).
  Proof.
    intros. ring.
  Qed.

  Lemma solve_opp_onCurve: forall x y : F, onCurve (x,y) ->
    onCurve (opp (sqrt (solve_for_x2 y)), y).
  Proof.
    intros.
    apply E.solve_correct.
    etransitivity; [ apply square_opp | ].
    eapply square_sqrt.
    symmetry.
    apply E.solve_correct; eassumption.
  Qed.

  Definition point_enc_coordinates (p : (F * F)) : Word.word (S sz) := let '(x,y) := p in
    Word.WS (sign_bit x) (enc y).

  Let point_enc (p : point) : Word.word (S sz) := point_enc_coordinates (E.coordinates p).

  Definition point_dec_coordinates (w : Word.word (S sz)) : option (F * F) :=
    match dec (Word.wtl w) with
    | None => None
    | Some y => let x2 := solve_for_x2 y in
        let x := sqrt x2 in
        if eq_dec (x ^ 2) x2
        then
          let p := (if Bool.eqb (whd w) (sign_bit x) then x else opp x, y) in
          if (andb (F_eqb x 0) (whd w))
          then None (* special case for 0, since its opposite has the same sign; if the sign bit of 0 is 1, produce None.*)
          else Some p 
        else None
    end.

  (* Definition of product equality parameterized over equality of underlying types *)
  Definition prod_eq {A B} eqA eqB (x y : (A * B)) := let (xA,xB) := x in let (yA,yB) := y in
    (eqA xA yA) /\ (eqB xB yB).

  Lemma prod_eq_dec : forall {A eq} (A_eq_dec : forall a a' : A, {eq a a'} + {not (eq a a')})
   (x y : (A * A)), {prod_eq eq eq x y} + {not (prod_eq eq eq x y)}.
  Proof.
    intros.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    match goal with
    | |- {prod_eq _ _ (?x1, ?x2) (?y1,?y2)} + {not (prod_eq _ _ (?x1, ?x2) (?y1,?y2))} => 
      destruct (A_eq_dec x1 y1); destruct (A_eq_dec x2 y2) end;
      unfold prod_eq; intuition.
  Qed.

  Definition option_eq {A} eq (x y : option A) :=
    match x with
    | None    => y = None
    | Some ax => match y with
                 | None => False
                 | Some ay => eq ax ay
                 end
    end.

  Lemma option_eq_dec : forall {A eq} (A_eq_dec : forall a a' : A, {eq a a'} + {not (eq a a')})
    (x y : option A), {option_eq eq x y} + {not (option_eq eq x y)}.
  Proof.
    unfold option_eq; intros; destruct x as [ax|], y as [ay|]; try tauto; auto.
    right; congruence.
  Qed.
  Definition option_coordinates_eq := option_eq (prod_eq eq eq).

  Lemma option_coordinates_eq_NS : forall x, option_coordinates_eq None (Some x) -> False.
  Proof.
    unfold option_coordinates_eq, option_eq.
    intros; discriminate.
  Qed.

  Lemma inversion_option_coordinates_eq : forall x y,
    option_coordinates_eq (Some x) (Some y) -> prod_eq eq eq x y.
  Proof.
    unfold option_coordinates_eq, option_eq; intros; assumption.
  Qed.

  Lemma prod_eq_onCurve : forall p q : F * F, prod_eq eq eq p q ->
    onCurve p -> onCurve q.
  Proof.
    unfold prod_eq; intros.
    destruct p; destruct q.
    eauto using onCurve_subst.
  Qed.

  Lemma option_coordinates_eq_iff : forall x1 x2 y1 y2,
    option_coordinates_eq (Some (x1,y1)) (Some (x2,y2)) <-> and (eq x1 x2) (eq y1 y2).
  Proof.
    unfold option_coordinates_eq, option_eq, prod_eq; tauto.
  Qed.

  Definition point_eq (p q : point) : Prop := prod_eq eq eq (proj1_sig p) (proj1_sig q).
  Definition option_point_eq := option_eq (point_eq).
  
  Lemma option_point_eq_iff : forall p q,
    option_point_eq (Some p) (Some q) <->
    option_coordinates_eq (Some (proj1_sig p)) (Some (proj1_sig q)).
  Proof.
    unfold option_point_eq, option_coordinates_eq, option_eq, point_eq; intros.
    reflexivity.
  Qed.

  Lemma option_coordinates_eq_dec : forall p q,
     {option_coordinates_eq p q} + {~ option_coordinates_eq p q}.
  Proof.
    intros.
    apply option_eq_dec.
    apply prod_eq_dec.
    apply eq_dec.
  Qed.

  Lemma point_eq_dec : forall p q, {point_eq p q} + {~ point_eq p q}.
  Proof.
    intros.
    apply prod_eq_dec.
    apply eq_dec.
  Qed.

  Lemma option_point_eq_dec : forall p q,
     {option_point_eq p q} + {~ option_point_eq p q}.
  Proof.
    intros.
    apply option_eq_dec.
    apply point_eq_dec.
  Qed.

  Lemma prod_eq_trans : forall p q r, prod_eq eq eq p q -> prod_eq eq eq q r ->
    prod_eq eq eq p r.
  Proof.
    unfold prod_eq; intros.
    repeat break_let.
    intuition; etransitivity; eauto.
  Qed.

  Lemma option_coordinates_eq_trans : forall p q r, option_coordinates_eq p q ->
    option_coordinates_eq q r -> option_coordinates_eq p r.
  Proof.
    unfold option_coordinates_eq, option_eq; intros.
    repeat break_match; subst; congruence || eauto using prod_eq_trans.
  Qed.

  Lemma prod_eq_sym : forall p q, prod_eq eq eq p q -> prod_eq eq eq q p.
  Proof.
    unfold prod_eq; intros.
    repeat break_let.
    intuition; etransitivity; eauto.
  Qed.

  Lemma option_coordinates_eq_sym : forall p q, option_coordinates_eq p q ->
    option_coordinates_eq q p.
  Proof.
    unfold option_coordinates_eq, option_eq; intros.
    repeat break_match; subst; congruence || eauto using prod_eq_sym; intuition.
  Qed.

  Opaque option_coordinates_eq option_point_eq point_eq option_eq prod_eq.

  Ltac inversion_Some_eq := match goal with [H: Some ?x = Some ?y |- _] => inversion H; subst end.

  Ltac congruence_option_coord := exfalso; eauto using option_coordinates_eq_NS.

  Lemma point_dec_coordinates_onCurve : forall w p, option_coordinates_eq  (point_dec_coordinates w) (Some p) -> onCurve p.
  Proof.
    unfold point_dec_coordinates; intros.
    edestruct dec; [ | congruence_option_coord ].
    break_if; [ | congruence_option_coord].
    break_if; [ congruence_option_coord | ].
    apply E.solve_correct in e.
    break_if; eapply prod_eq_onCurve;
      eauto using inversion_option_coordinates_eq, solve_onCurve, solve_opp_onCurve.
  Qed.

  Definition point_dec' w p : option point :=
    match (option_coordinates_eq_dec  (point_dec_coordinates w) (Some p)) with
      | left EQ => Some (exist _ p (point_dec_coordinates_onCurve w p EQ))
      | right _ => None (* this case is never reached *)
    end.

  Definition point_dec (w : word (S sz)) : option point :=
    match point_dec_coordinates w with
    | Some p => point_dec' w p
    | None => None
    end.

  Lemma point_coordinates_encoding_canonical : forall w p,
    point_dec_coordinates w = Some p -> point_enc_coordinates p = w.
  Proof.
    unfold point_dec_coordinates, point_enc_coordinates; intros ? ? coord_dec_Some.
    case_eq (dec (wtl w)); [ intros ? dec_Some | intros dec_None; rewrite dec_None in *; congruence ].
    destruct p.
    rewrite (shatter_word w).
    f_equal; rewrite dec_Some in *;
      do 2 (break_if; try congruence); inversion coord_dec_Some; subst.
    + destruct (eq_dec (sqrt (solve_for_x2 f1)) 0) as [sqrt_0 | ?].
      - break_if; rewrite sign_bit_zero in * by (assumption || (rewrite sqrt_0; ring));
          auto using Bool.eqb_prop.
        apply F_eqb_iff in sqrt_0.
        rewrite sqrt_0 in *.
        destruct (whd w); inversion Heqb0; auto.
      - break_if.
        symmetry; auto using Bool.eqb_prop.
        rewrite <- sign_bit_opp by assumption.
        destruct (whd w); inversion Heqb0; break_if; auto.
    + inversion coord_dec_Some; subst.
      auto using encoding_canonical.
  Qed.

  Lemma inversion_point_dec : forall w x, point_dec w = Some x ->
    point_dec_coordinates w = Some (E.coordinates x).
  Proof.
    unfold point_dec, E.coordinates; intros.
    break_match; [ | congruence].
    unfold point_dec' in *; break_match; [ | congruence].
    match goal with [ H : Some _ = Some _ |- _ ] => inversion H end.
    reflexivity.
  Qed.

  Lemma point_encoding_canonical : forall w x, point_dec w = Some x -> point_enc x = w.
  Proof.
    unfold point_enc; intros.
    apply point_coordinates_encoding_canonical.
    auto using inversion_point_dec.
  Qed.

  Lemma y_decode : forall p, dec (wtl (point_enc_coordinates p)) = Some (snd p).
  Proof.
    intros; destruct p. cbv [point_enc_coordinates wtl snd].
    exact (encoding_valid _).
  Qed.

  Lemma F_eqb_false : forall x y, x !== y -> F_eqb x y = false.
  Proof.
    intros; unfold F_eqb; destruct (eq_dec x y); congruence.
  Qed.

  Lemma eqb_sign_opp_r : forall x y, (y !== 0) ->
    Bool.eqb (sign_bit x) (sign_bit y) = false ->
    Bool.eqb (sign_bit x) (sign_bit (opp y)) = true.
  Proof.
    intros x y y_nonzero ?.
    specialize (sign_bit_opp y y_nonzero).
    destruct (sign_bit x), (sign_bit y); try discriminate;
      rewrite <-sign_bit_opp; auto.
  Qed.

  Lemma sign_match : forall x y sqrt_y, sqrt_y !== 0 -> (x ^2) == y -> sqrt_y ^2 == y ->
    Bool.eqb (sign_bit x) (sign_bit sqrt_y) = true ->
    sqrt_y == x.
  Proof.
    intros.
    pose proof (only_two_square_roots_choice x sqrt_y y) as Hchoice.
    destruct Hchoice; try assumption; symmetry; try assumption.
    rewrite (sign_bit_subst x (opp sqrt_y)) in * by assumption.
    rewrite <-sign_bit_opp in * by assumption.
    rewrite Bool.eqb_negb1 in *; discriminate.
  Qed.

  Lemma point_encoding_coordinates_valid : forall p, onCurve p ->
    option_coordinates_eq (point_dec_coordinates (point_enc_coordinates p)) (Some p).
  Proof.
    intros [x y] onCurve_p.
    unfold point_dec_coordinates.
    rewrite y_decode.
    cbv [whd point_enc_coordinates snd].
    pose proof (square_sqrt (solve_for_x2 y) x) as solve_sqrt_ok.
    forward solve_sqrt_ok. {
      symmetry.
      apply E.solve_correct.
      assumption.
    }
    match goal with [ H1 : ?P, H2 : ?P -> _ |- _ ] => specialize (H2 H1); clear H1 end.
    unfold sqrt_ok in solve_sqrt_ok.
    break_if; [ |  congruence].
    assert (solve_for_x2 y == (x ^2)) as solve_correct by (symmetry; apply E.solve_correct; assumption).
    destruct (eq_dec x 0) as [eq_x_0 | neq_x_0].
    + rewrite !sign_bit_zero by
        (eauto || (rewrite eq_x_0 in *; rewrite sqrt_square; [ | eauto]; reflexivity)).
      rewrite Bool.andb_false_r, Bool.eqb_reflx.
      apply option_coordinates_eq_iff; split; try reflexivity.
      transitivity (sqrt (x ^2)); auto.
      apply (sqrt_square); reflexivity.
    + rewrite F_eqb_false, Bool.andb_false_l by (rewrite sqrt_square; [ | eauto]; assumption).
      break_if; [ | apply eqb_sign_opp_r in Heqb];
        try (apply option_coordinates_eq_iff; split; try reflexivity);
        try eapply sign_match with (y := solve_for_x2 y); eauto;
        try solve [symmetry; auto]; rewrite ?square_opp; auto;
        (rewrite sqrt_square; [ | eauto]); try apply Ring.opp_nonzero_nonzero;
        assumption.
Qed.

Lemma point_dec'_valid : forall p q, option_coordinates_eq (Some q) (Some (proj1_sig p)) ->
  option_point_eq (point_dec' (point_enc_coordinates (proj1_sig p)) q) (Some p).
Proof.
  unfold point_dec'; intros.
  break_match.
  + f_equal.
    apply option_point_eq_iff.
    destruct p as [[? ?] ?]; simpl in *.
    assumption.
  + exfalso; apply  n.
    eapply option_coordinates_eq_trans; [ | eauto using option_coordinates_eq_sym ].
    apply point_encoding_coordinates_valid.
    apply (proj2_sig p).
Qed.

Lemma point_encoding_valid : forall p,
  option_point_eq (point_dec (point_enc p)) (Some p).
Proof.
  intros.
  unfold point_dec.
  replace (point_enc p) with (point_enc_coordinates (proj1_sig p)) by reflexivity.
  break_match.
  + eapply (point_dec'_valid p).
    rewrite <-Heqo.
    apply point_encoding_coordinates_valid.
    apply (proj2_sig p).
  + exfalso.
    eapply option_coordinates_eq_NS.
    pose proof (point_encoding_coordinates_valid _ (proj2_sig p)).
    rewrite Heqo in *.
    eassumption.
Qed.

End PointEncodingPre.

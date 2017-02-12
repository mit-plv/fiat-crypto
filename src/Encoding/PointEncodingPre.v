Require Import Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Equality.
Require Import Crypto.CompleteEdwardsCurve.Pre.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Crypto.Encoding.ModularWordEncodingTheorems.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Algebra Crypto.Algebra.Field.
Require Import Crypto.Util.Option.
Import Morphisms.

Require Import Crypto.Spec.Encoding Crypto.Spec.ModularWordEncoding Crypto.Spec.ModularArithmetic.

Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Tactics.VerdiTactics.
Require Export Crypto.Util.FixCoqMistakes.

Generalizable All Variables.
Section PointEncodingPre.
  Context {F eq zero one opp add sub mul inv div} `{field F eq zero one opp add sub mul inv div} {eq_dec:DecidableRel eq}.
  Local Infix "==" := eq : type_scope.
  Local Notation "a !== b" := (not (a == b)): type_scope.
  Local Notation "0" := zero.  Local Notation "1" := one.
  Local Infix "+" := add. Local Infix "*" := mul.
  Local Infix "-" := sub. Local Infix "/" := div.
  Local Notation "x ^ 2" := (x*x).

  Add Field EdwardsCurveField : (Field.field_theory_for_stdlib_tactic (T:=F)).

  Definition F_eqb x y := if eq_dec x y then true else false.
  Lemma F_eqb_iff : forall x y, F_eqb x y = true <-> x == y.
  Proof.
    unfold F_eqb; intros; destruct (eq_dec x y); split; auto; discriminate.
  Qed.

  Context {a d:F} {prm:@E.twisted_edwards_params F eq zero one opp add sub mul a d}.
  Local Notation point := (@E.point F eq one add mul a d).
  Local Notation onCurve := (@E.onCurve F eq one add mul a d).
  Local Notation solve_for_x2 := (@E.solve_for_x2 F one sub mul div a d).

  Context {sz : nat} (sz_nonzero : (0 < sz)%nat).
  Context {sqrt : F -> F} {Proper_sqrt : Proper (eq ==>eq) sqrt}
          (sqrt_square : forall x root, x == (root ^2) ->
                                        (sqrt x *sqrt x == x))
          (sqrt_subst : forall x y, x == y -> sqrt x == sqrt y).
  Context (FEncoding : canonical encoding of F as (word sz)).
  Context {enc_canonical_equiv : forall x_enc x,
              option_eq eq (dec x_enc) (Some x) -> enc x = x_enc}.
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
    reflexivity.
  Qed.

  Lemma solve_onCurve: forall x y : F, onCurve x y ->
    onCurve (sqrt (E.solve_for_x2(Fone:=one)(Fsub:=sub)(Fmul:=mul)(Fdiv:=div)(a:=a)(d:=d) y)) y.
  Proof.
    intros.
    eapply E.solve_correct.
    eapply square_sqrt.
    symmetry.
    eapply E.solve_correct. eassumption.
  Qed.

  (* TODO : move? *)
  Lemma square_opp : forall x : F, (opp x ^2) == (x ^2).
  Proof.
    intros. ring.
  Qed.

  Lemma solve_opp_onCurve: forall x y : F, onCurve x y ->
    onCurve (opp (sqrt (solve_for_x2 y))) y.
  Proof.
    intros.
    apply E.solve_correct.
    etransitivity; [ apply square_opp | ].
    eapply square_sqrt.
    symmetry.
    apply E.solve_correct; eassumption.
  Qed.

  Definition point_enc_coordinates (p : (F * F)) : Word.word (sz+1) := let '(x,y) := p in
    combine (enc y) (WS (sign_bit x) WO).

  Let point_enc (p : point) : Word.word (sz+1) := point_enc_coordinates (E.coordinates p).

  Definition coord_from_y sign (y : F) : option (F * F) :=
    let x2 := solve_for_x2 y in
    let x := sqrt x2 in
    if eq_dec (mul x x) x2
    then
        let p := (if Bool.eqb sign (sign_bit x) then x else opp x, y) in
        if (F_eqb x zero && sign)%bool
        then None
        else Some p
    else None.

  Definition point_dec_coordinates (w : word (sz+1)) : option (F * F) :=
    option_rect (fun _ => _) (coord_from_y (wlast w)) None (dec (winit w)).

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
    repeat break_match; subst; try destruct p,q; congruence || eauto using prod_eq_trans.
  Qed.

  Lemma prod_eq_sym : forall p q, prod_eq eq eq p q -> prod_eq eq eq q p.
  Proof.
    unfold prod_eq; intros.
    repeat break_let.
    intuition auto with relations; etransitivity; eauto.
  Qed.

  Lemma option_coordinates_eq_sym : forall p q, option_coordinates_eq p q ->
    option_coordinates_eq q p.
  Proof.
    unfold option_coordinates_eq, option_eq; intros.
    repeat break_match; subst; try destruct p; congruence || eauto using prod_eq_sym; intuition.
  Qed.

  Opaque option_coordinates_eq option_point_eq.

  Ltac inversion_Some_eq := match goal with [H: Some ?x = Some ?y |- _] => inversion H; subst end.

  Ltac congruence_option_coord := exfalso; eauto using option_coordinates_eq_NS.

  Lemma onCurve_eq : forall x y,
    eq (add (mul a (mul x x)) (mul y y))
        (add one (mul (mul d (mul x x)) (mul y y))) ->
    @E.onCurve _ eq one add mul a d x y.
  Proof.
      tauto.
  Qed.

  Definition point_from_xy (xy : F * F) : option point :=
    let '(x,y) := xy in
    match Decidable.dec (eq (add (mul a (mul x x)) (mul y y))
                  (add one (mul (mul d (mul x x)) (mul y y)))) with
      | left A => Some (exist _ (x,y) (onCurve_eq x y A))
      | right _ => None
    end.

  Definition point_dec (w : word (sz+1)) : option point :=
    option_rect (fun _ => option point) point_from_xy None (point_dec_coordinates w).

  Lemma bool_neq_negb x y : x <> y <-> x = negb y.
    destruct x, y; split; (discriminate||tauto).
  Qed.

  Lemma point_coordinates_encoding_canonical : forall w p,
    option_eq (Tuple.fieldwise (n := 2) eq) (point_dec_coordinates w) (Some p) ->
    point_enc_coordinates p = w.
  Proof.
    repeat match goal with
           | |- _ => progress cbv [point_dec_coordinates option_rect
                                   point_enc_coordinates coord_from_y] in *
           | |- _ => progress intros
           | |- _ => progress rewrite ?Bool.andb_true_r,
                     ?Bool.andb_false_r, ?Bool.eqb_false_iff in *
           | |- _ => rewrite <-sign_bit_opp
               by ((rewrite <-F_eqb_iff; congruence) ||
                   (intro A; specialize (sign_bit_zero _ A); congruence))
           | p : F * F |- _ => destruct p
           | |- _ => break_match; try discriminate
           | w : word (S sz) |- WS _ _ = ?w => rewrite (shatter_word w);
                                                 f_equal
           | H : option_eq _ (Some _) (Some _) |- _ =>
             cbv [option_eq Tuple.fieldwise Tuple.fieldwise' fst snd] in H;
               destruct H
           | H :  Bool.eqb _ _ = _ |- _  => apply Bool.eqb_prop in H
           | H : ?b = sign_bit ?x |- sign_bit ?y = ?b => erewrite <-sign_bit_subst by eassumption; instantiate; congruence
           | H : ?b <> sign_bit ?x |- sign_bit ?y <> ?b => erewrite <-sign_bit_subst by eassumption; instantiate; congruence
           | |- sign_bit _ = whd ?w => destruct (whd w)
           | |- negb _ = false => apply Bool.negb_false_iff
           | |- _ => solve [auto using Bool.eqb_prop,
                            Bool.eq_true_not_negb,
                            Bool.not_false_is_true, encoding_canonical]
           end;
      rewrite combine_winit_wlast; split;
        try apply (f_equal2 (fun a b => WS a b));
        try solve
            [ trivial
            | apply enc_canonical_equiv; rewrite Heqo; auto];
        erewrite <-sign_bit_subst by eassumption.
    { intuition. }
    { apply bool_neq_negb in Heqb0. rewrite <-sign_bit_opp.
      { congruence. }
      { rewrite Bool.andb_false_iff in *.
        unfold not; intro Hx; destruct Heqb;
          [apply F_eqb_iff in Hx; congruence
          |rewrite (sign_bit_zero _ Hx) in *; simpl negb in *; congruence]. } }
  Qed.

  Lemma inversion_point_dec : forall w x,
    option_eq point_eq (point_dec w) (Some x) ->
    option_eq (Tuple.fieldwise (n := 2) eq) (point_dec_coordinates w) (Some (E.coordinates x)).
  Proof.
    unfold point_dec, E.coordinates, point_from_xy, option_rect; intros.
    break_match; [ | congruence].
    destruct p. break_match; [ | congruence ].
    destruct x as [xy pf]; destruct xy.
    cbv [option_eq point_eq] in *.
    simpl in *.
    intuition.
  Qed.

  Lemma point_encoding_canonical : forall w x,
      option_eq point_eq (point_dec w) (Some x) -> point_enc x = w.
  Proof.
    unfold point_enc; intros.
    apply point_coordinates_encoding_canonical.
    auto using inversion_point_dec.
  Qed.


  Lemma y_decode : forall p, dec (winit (point_enc_coordinates p)) = Some (snd p).
  Proof.
    intros; destruct p. cbv [point_enc_coordinates wtl snd].
    rewrite winit_combine.
    exact (encoding_valid _).
  Qed.

  Lemma F_eqb_false : forall x y, x !== y <-> F_eqb x y = false.
  Proof.
    intros; unfold F_eqb; destruct (eq_dec x y).
    + split; intuition eauto; try discriminate.
    + tauto.
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
    pose proof (Field.only_two_square_roots_choice x sqrt_y y) as Hchoice.
    destruct Hchoice; try assumption; symmetry; try assumption.
    rewrite (sign_bit_subst x (opp sqrt_y)) in * by assumption.
    rewrite <-sign_bit_opp in * by assumption.
    rewrite Bool.eqb_negb1 in *; discriminate.
  Qed.

  Lemma point_encoding_coordinates_valid p (onCurve_p:onCurve (fst p) (snd p))
    : option_coordinates_eq (point_dec_coordinates (point_enc_coordinates p)) (Some p).
  Proof.
    destruct p as [x y].
    unfold point_dec_coordinates, point_from_xy, coord_from_y, option_rect.
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
    + rewrite eq_x_0 in *.
      assert (0^2 == 0) as zero_square by apply Ring.mul_0_l.
      specialize (sqrt_square _ _ solve_correct).
      rewrite solve_correct, zero_square in sqrt_square.
      rewrite Ring.zero_product_iff_zero_factor in sqrt_square.
      rewrite zero_square in *.
      assert (sqrt (solve_for_x2 y) == 0) by (rewrite solve_correct; tauto).
      rewrite !sign_bit_zero by (tauto || eauto).
      rewrite wlast_combine.
      rewrite Bool.andb_false_r, Bool.eqb_reflx.
      apply option_coordinates_eq_iff; split; try reflexivity.
      etransitivity; eauto.
      symmetry; eauto.
    + assert (0^2 == 0) as zero_square by apply Ring.mul_0_l.
      specialize (sqrt_square _ _ solve_correct).
      rewrite !solve_correct in *.
      symmetry in sqrt_square.
      rewrite (proj1 (F_eqb_false _ 0)), Bool.andb_false_l.
      Focus 2. {
        rewrite !solve_correct in *.
        intro.
        apply neq_x_0.
        rewrite H0, zero_square in sqrt_square.
        rewrite Ring.zero_product_iff_zero_factor in sqrt_square.
        tauto. } Unfocus.
      rewrite wlast_combine.
      break_if; [ | apply eqb_sign_opp_r in Heqb];
        try (apply option_coordinates_eq_iff; split; try reflexivity);
        try eapply sign_match with (y := solve_for_x2 y); eauto;
          try solve [symmetry; auto]; rewrite ?square_opp; auto;
            intro; apply neq_x_0; rewrite solve_correct in *;
      try apply Group.inv_zero_zero in H0;
      rewrite H0, zero_square in sqrt_square; 
        rewrite Ring.zero_product_iff_zero_factor in sqrt_square; tauto.
Qed.

Lemma point_encoding_valid : forall p,
  option_point_eq (point_dec (point_enc p)) (Some p).
Proof.
  repeat match goal with
         | |- _ => progress (cbv [point_dec point_enc E.coordinates
                                 option_rect point_from_xy]; intros)
         | |- _ => progress simpl proj1_sig in *
         | p : point |- _ => destruct p
         | p : F * F |- _ => destruct p
         | |- appcontext[proj1_sig (exist ?a ?b ?c)] =>
           progress replace (proj1_sig (exist a b c)) with b by reflexivity
         | |- _ => break_match
         | |- _ => split
         | |- option_point_eq _ _ => apply option_point_eq_iff
         | |- option_coordinates_eq _ _ => apply option_coordinates_eq_iff
         | H : a * ?x^2 + ?y^2 == 1 + d * ?x^2 * ?y^2 |- _ =>
           unique pose proof (point_encoding_coordinates_valid (_,_) H)
         | Hpq : point_dec_coordinates (point_enc_coordinates ?p) = Some ?q,
           Hp : option_coordinates_eq
                  (point_dec_coordinates (point_enc_coordinates ?p)) (Some ?p)
           |- _ => unique assert (option_coordinates_eq (Some q) (Some p))
                                   by (rewrite Hpq in Hp; auto)
         | H : option_coordinates_eq (Some ?p) (Some ?q) |- _ =>
           apply option_coordinates_eq_iff in H; destruct H;
             (assumption || (symmetry; assumption))
         end.
  exfalso.
  apply n.
  apply option_coordinates_eq_iff in H1; destruct H1.
  rewrite H1, H2; assumption.


  rewrite Heqo in H0.
  congruence_option_coord.
Qed.

End PointEncodingPre.

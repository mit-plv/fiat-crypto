Require Import Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.Program.Equality.
Require Import Crypto.Encoding.EncodingTheorems.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Bedrock.Word.
Require Import Crypto.Tactics.VerdiTactics.

Require Import Crypto.Spec.Encoding Crypto.Spec.ModularArithmetic.

Local Open Scope F_scope.

Section PointEncoding.
  Context {prm: TwistedEdwardsParams} {sz : nat} {sz_nonzero : (0 < sz)%nat}
   {FqEncoding : encoding of F q as word sz} {q_5mod8 : (q mod 8 = 5)%Z}
   {sqrt_minus1_valid : (@ZToField q 2 ^ Z.to_N (q / 4)) ^ 2 = opp 1}.
  Existing Instance prime_q.

  Add Field Ffield : (@Ffield_theory q _)
    (morphism (@Fring_morph q),
     preprocess [Fpreprocess],
     postprocess [Fpostprocess; try exact Fq_1_neq_0; try assumption],
     constants [Fconstant],
     div (@Fmorph_div_theory q),
     power_tac (@Fpower_theory q) [Fexp_tac]).

  Definition sqrt_valid (a : F q) := ((sqrt_mod_q a) ^ 2 = a)%F.

  Lemma solve_sqrt_valid : forall p, onCurve p ->
    sqrt_valid (solve_for_x2 (snd p)).
  Proof.
    intros ? onCurve_xy.
    destruct p as [x y]; simpl.
    rewrite (solve_correct x y) in onCurve_xy.
    rewrite <- onCurve_xy.
    unfold sqrt_valid.
    eapply sqrt_mod_q_valid; eauto.
    unfold isSquare; eauto.
    Grab Existential Variables. eauto.
  Qed.

  Lemma solve_onCurve: forall (y : F q), sqrt_valid (solve_for_x2 y) ->
    onCurve (sqrt_mod_q (solve_for_x2 y), y).
  Proof.
    intros.
    unfold sqrt_valid in *.
    apply solve_correct; auto.
  Qed.

  Lemma solve_opp_onCurve: forall (y : F q), sqrt_valid (solve_for_x2 y) ->
    onCurve (opp (sqrt_mod_q (solve_for_x2 y)), y).
  Proof.
    intros y sqrt_valid_x2.
    unfold sqrt_valid in *.
    apply solve_correct.
    rewrite <- sqrt_valid_x2 at 2.
    ring.
  Qed.

  Let sign_bit (x : F CompleteEdwardsCurve.q) :=
    match (enc x) with
      | Word.WO => false
      | Word.WS b _ w' => b
    end.

  Definition point_enc_coordinates (p : (F q * F q)) : Word.word (S sz) := let '(x,y) := p in
    Word.WS (sign_bit x) (enc y).

  Let point_enc (p : CompleteEdwardsCurve.point) : Word.word (S sz) := let '(x,y) := proj1_sig p in
    Word.WS (sign_bit x) (enc y).

  Definition point_dec_coordinates (sign_bit : F q -> bool) (w : Word.word (S sz)) : option (F q * F q) :=
    match dec (Word.wtl w) with
    | None => None
    | Some y => let x2 := solve_for_x2 y in
        let x := sqrt_mod_q x2 in
        if F_eq_dec (x ^ 2) x2
        then
          let p := (if Bool.eqb (whd w) (sign_bit x) then x else opp x, y) in
          if (andb (F_eqb x 0) (whd w))
          then None (* special case for 0, since its opposite has the same sign; if the sign bit of 0 is 1, produce None.*)
          else Some p 
        else None
    end.

  Ltac inversion_Some_eq := match goal with [H: Some ?x = Some ?y |- _] => inversion H; subst end.

  Lemma point_dec_coordinates_onCurve : forall w p, point_dec_coordinates sign_bit w = Some p -> onCurve p.
  Proof.
    unfold point_dec_coordinates; intros.
    edestruct dec; [ | congruence].
    break_if; [ | congruence].
    break_if; [ congruence | ]. 
    break_if; inversion_Some_eq; auto using solve_onCurve, solve_opp_onCurve.
  Qed.
(*
  Definition point_dec (w : word (S sz)) : option point.
    case_eq (point_dec_coordinates w); intros; [ | apply None].
    apply Some.
    eapply mkPoint.
    eapply point_dec_coordinates_onCurve; eauto.
  Defined.
*)
  Lemma option_eq_dec : forall {A} (x y : option A), {x = y} + {x <> y}.
  Proof.
    decide equality.
  Admitted.


  Definition point_dec' w p : option point :=
    match (option_eq_dec (point_dec_coordinates sign_bit w) (Some p)) with
      | left EQ => Some (mkPoint p (point_dec_coordinates_onCurve w p EQ))
      | right _ => None (* this case is never reached *)
    end.

  Definition point_dec (w : word (S sz)) : option point :=
    match (point_dec_coordinates sign_bit w) with
    | Some p => point_dec' w p
    | None => None
    end.

  Lemma enc_first_bit_opp : forall (x : F q), x <> 0 ->
    match enc x with
    | WO => True
    | WS b n w => match enc (opp x) with
                  | WO => False
                  | WS b' _ _ => b' = negb b
                  end
    end.
  Proof.
  Admitted.

  Lemma first_bit_zero : match enc 0 with
    | WO => False
    | WS b _ _ => b = false
    end.
  Admitted.

  Lemma sign_bit_opp_negb : forall x, x <> 0 -> negb (sign_bit x) = sign_bit (opp x).
  Proof.
    intros x x_nonzero.
    unfold sign_bit.
    pose proof (enc_first_bit_opp x x_nonzero).
    pose proof (shatter_word (enc x)) as shatter_enc_x.
    pose proof (shatter_word (enc (opp x))) as shatter_enc_opp.
    destruct sz; try omega.
    rewrite shatter_enc_x, shatter_enc_opp in *.
    auto.
  Qed.

  Lemma Fq_encoding_canonical : forall w (n : F q), dec w = Some n -> enc n = w.
  Admitted.

  (* TODO : move *)
  Lemma sqrt_mod_q_0 : forall x : F q, sqrt_mod_q x = 0 -> x = 0.
  Proof.
    unfold sqrt_mod_q; intros.
    break_if.
    - match goal with [ H : ?sqrt_x ^ 2 = x, H' : ?sqrt_x = 0 |- _ ] => rewrite <-H, H' end.
      ring.
    - match goal with
      | [H : sqrt_minus1 * _ = 0 |- _ ]=>
         apply Fq_mul_zero_why in H; destruct H as [sqrt_minus1_zero | ? ];
         [ | eapply Fq_root_zero; eauto ]
      end.
      unfold sqrt_minus1 in sqrt_minus1_zero.
      rewrite sqrt_minus1_zero in sqrt_minus1_valid.
      exfalso.
      pose proof (@F_opp_spec q 1) as opp_spec_1.
      rewrite <-sqrt_minus1_valid in opp_spec_1.
      assert (((1 + 0 ^ 2) : F q) = (1 : F q)) as ring_subst by ring.
      rewrite ring_subst in *.
      apply Fq_1_neq_0; assumption.
  Qed.
    
  Lemma sign_bit_zero : sign_bit 0 = false.
  Proof.
    unfold sign_bit.
    pose proof first_bit_zero.
    destruct sz; try omega.
    pose proof (shatter_word (enc 0)) as shatter_enc0.
    simpl in shatter_enc0; rewrite shatter_enc0 in *; assumption.
  Qed.

  Lemma point_coordinates_encoding_canonical : forall w p,
    point_dec_coordinates sign_bit w = Some p -> point_enc_coordinates p = w.
  Proof.
    unfold point_dec_coordinates, point_enc_coordinates; intros ? ? coord_dec_Some.
    case_eq (dec (wtl w)); [ intros ? dec_Some | intros dec_None; rewrite dec_None in *; congruence ].
    destruct p.
    rewrite (shatter_word w).
    f_equal; rewrite dec_Some in *;
      do 2 (break_if; try congruence); inversion coord_dec_Some; subst.
    + destruct (F_eq_dec (sqrt_mod_q (solve_for_x2 f1)) 0%F) as [sqrt_0 | ?].
      - rewrite sqrt_0 in *.
        apply sqrt_mod_q_0 in sqrt_0.
        rewrite sqrt_0 in *.
        break_if; [symmetry; auto using Bool.eqb_prop | ].
        rewrite sign_bit_zero in *.
        simpl in Heqb; rewrite Heqb in *.
        discriminate.
      - break_if.
        symmetry; auto using Bool.eqb_prop.
        rewrite <- sign_bit_opp_negb by auto.
        destruct (whd w); inversion Heqb0; break_if; auto.
    + inversion coord_dec_Some; subst.
      auto using Fq_encoding_canonical.
Qed.

  Lemma point_encoding_canonical : forall w x, point_dec w = Some x -> point_enc x = w.
  Proof.
  (*
    unfold point_enc; intros.
    unfold point_dec in *.
    assert (point_dec_coordinates w = Some (proj1_sig x)). {
      set (y := point_dec_coordinates w) in *.
      revert H.
      dependent destruction y. intros.
      rewrite H0 in H.
  *)
  Admitted.

Lemma point_dec_coordinates_correct w
  : option_map (@proj1_sig _ _) (point_dec w) = point_dec_coordinates sign_bit w.
Proof.
  unfold point_dec, option_map.
  do 2 break_match; try congruence; unfold point_dec' in *;
    break_match; try congruence.
  inversion_Some_eq. 
  reflexivity.
Qed.

Lemma y_decode : forall p, dec (wtl (point_enc_coordinates p)) = Some (snd p).
Proof.
  intros.
  destruct p as [x y]; simpl.
  exact (encoding_valid y).
Qed.


Lemma wordToN_enc_neq_opp : forall x, x <> 0 -> (wordToN (enc (opp x)) <> wordToN (enc x))%N.
Proof.
  intros x x_nonzero.
  intro false_eq.
  apply x_nonzero.
  apply F_eq_opp_zero; try apply two_lt_q.
  apply wordToN_inj in false_eq.
  apply encoding_inj in false_eq.
  auto.
Qed.

Lemma sign_bit_opp : forall x y, y <> 0 ->
  (sign_bit x <> sign_bit y <-> sign_bit x = sign_bit (opp y)).
Proof.
  split; intro sign_mismatch; case_eq (sign_bit x); case_eq (sign_bit y);
    try congruence; intros y_sign x_sign; rewrite <- sign_bit_opp_negb in * by auto;
    rewrite y_sign, x_sign in *; reflexivity || discriminate.
Qed.

Lemma sign_bit_squares : forall x y, y <> 0 -> x ^ 2 = y ^ 2 ->
  sign_bit x = sign_bit y -> x = y.
Proof.
  intros ? ? y_nonzero squares_eq sign_match.
  destruct (sqrt_solutions _ _ squares_eq) as [? | eq_opp]; auto.
  assert (sign_bit x = sign_bit (opp y)) as sign_mismatch by (f_equal; auto).
  apply sign_bit_opp in sign_mismatch; auto.
  congruence.
Qed.

Lemma sign_bit_match : forall x x' y : F q, onCurve (x, y) -> onCurve (x', y) ->
  sign_bit x = sign_bit x' -> x = x'.
Proof.
  intros ? ? ? onCurve_x onCurve_x' sign_match.
  apply solve_correct in onCurve_x.
  apply solve_correct in onCurve_x'.
  destruct (F_eq_dec x' 0).
  + subst.
    rewrite Fq_pow_zero in onCurve_x' by congruence.
    rewrite <- onCurve_x' in *.
    eapply Fq_root_zero; eauto.
  + apply sign_bit_squares; auto.
    rewrite onCurve_x, onCurve_x'.
    reflexivity.
Qed.
(*
Lemma blah : forall x y, (F_eqb (sqrt_mod_q (solve_for_x2 y)) 0 && sign_bit x)%bool = true.
*)

Lemma point_encoding_coordinates_valid : forall p, onCurve p ->
   point_dec_coordinates sign_bit (point_enc_coordinates p) = Some p.
Proof.
  intros p onCurve_p.
  unfold point_dec_coordinates.
  rewrite y_decode.
  pose proof (solve_sqrt_valid p onCurve_p) as solve_sqrt_valid_p.
  unfold sqrt_valid in *.
  destruct p as [x y].
  simpl in *.
  destruct (F_eq_dec ((sqrt_mod_q (solve_for_x2 y)) ^ 2) (solve_for_x2 y)); intuition.
  break_if; f_equal.
  + case_eq (F_eqb (sqrt_mod_q (solve_for_x2 y)) 0); intros eqb_0.
(*
    SearchAbout F_eqb.

 [ | simpl in *; congruence].
    


    rewrite Bool.eqb_true_iff in Heqb.
    pose proof (solve_onCurve y solve_sqrt_valid_p).
    f_equal.
    apply (sign_bit_match _ _ y); auto.
  + rewrite Bool.eqb_false_iff in Heqb.
    pose proof (solve_opp_onCurve y solve_sqrt_valid_p).
    f_equal.
    apply sign_bit_opp in Heqb.
    apply (sign_bit_match _ _ y); auto.
    intro eq_zero.
    apply solve_correct in onCurve_p.
    rewrite eq_zero in *.
    rewrite Fq_pow_zero in solve_sqrt_valid_p by congruence.
    rewrite <- solve_sqrt_valid_p in onCurve_p.
    apply Fq_root_zero in onCurve_p.
    rewrite onCurve_p in Heqb; auto.
*)
Admitted.

Lemma point_dec'_valid : forall p,
  point_dec' (point_enc_coordinates (proj1_sig p)) (proj1_sig p) = Some p.
Proof.
  unfold point_dec'; intros.
  break_match.
  + f_equal.
    destruct p.
    apply point_eq.
    reflexivity.
  + rewrite point_encoding_coordinates_valid in n by apply (proj2_sig p).
    congruence.
Qed.

Lemma point_encoding_valid : forall p, point_dec (point_enc p) = Some p.
Proof.
  intros.
  unfold point_dec.
  replace (point_enc p) with (point_enc_coordinates (proj1_sig p)) by reflexivity.
  break_match; rewrite point_encoding_coordinates_valid in * by apply (proj2_sig p); try congruence.
  inversion_Some_eq.
  eapply point_dec'_valid.
Qed.

End PointEncoding.

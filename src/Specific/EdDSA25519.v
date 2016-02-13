Require Import ZArith.ZArith Zpower ZArith Znumtheory.
Require Import NPeano NArith.
Require Import Crypto.Galois.EdDSA Crypto.Galois.GaloisField.
Require Import Crypto.Curves.PointFormats.
Require Import Crypto.Util.NatUtil Crypto.Util.ZUtil Crypto.Util.NumTheoryUtil.
Require Import Bedrock.Word.
Require Import VerdiTactics.
Require Import Decidable.
Require Import Omega.

Module Modulus25519 <: Modulus.
  Definition two_255_19 := two_p 255 - 19.
  Lemma two_255_19_prime : prime two_255_19. Admitted.
  Definition prime25519 := exist _ two_255_19 two_255_19_prime.
  Definition modulus := prime25519.
End Modulus25519.

Lemma prime_l : prime (252 + 27742317777372353535851937790883648493). Admitted.

Local Open Scope nat_scope.

Module EdDSA25519_Params <: EdDSAParams.
  Definition q : Prime := Modulus25519.modulus.
  Ltac prime_bound := pose proof (prime_ge_2 q (proj2_sig q)); try omega.

  Lemma q_odd : (primeToZ q > 2)%Z.
  Proof.
    cbv; congruence.
  Qed.

  Module Modulus_q := Modulus25519.

  Definition b := 256.
  Lemma b_valid : (2 ^ (Z.of_nat b - 1) > q)%Z.
  Proof.
    remember 19%Z as y.
    replace (Z.of_nat b - 1)%Z with 255%Z by auto.
    assert (y > 0)%Z by (rewrite Heqy; cbv; auto).
    remember (2 ^ 255)%Z as x.
    simpl. unfold Modulus25519.two_255_19.
    rewrite two_p_equiv.
    rewrite <- Heqy.
    rewrite <- Heqx.
    omega.
  Qed.

  (* TODO *)
  Parameter H : forall {n}, word n -> word (b + b).

  Definition c := 3.
  Lemma c_valid : c = 2 \/ c = 3.
  Proof.
    right; auto.
  Qed.

  Definition n := b - 2.
  Lemma n_ge_c : n >= c.
  Proof.
    unfold n, c, b; omega.
  Qed.
  Lemma n_le_b : n <= b.
  Proof.
    unfold n, b; omega.
  Qed.

  Module GFDefs := GaloisField Modulus_q.
  Import GFDefs.
  Local Open Scope GF_scope.

  Lemma gt_div2_q_zero : (q / 2 > 0)%Z.
  Proof.
    replace (GFToZ 0) with 0%Z by auto.
    assert (0 < 2 <= primeToZ q)%Z by (pose proof q_odd; omega).
    pose proof (Z.div_str_pos (primeToZ q) 2 H0).
    omega.
  Qed.

  Definition isSquare x := exists sqrt_x, sqrt_x ^ 2 = x.

  Lemma euler_criterion_GF : forall (a : GF) (a_nonzero : a <> 0),
    (a ^ (Z.to_N (q / 2)) = 1) <-> isSquare a.
  Proof.
    assert (prime q) by apply Modulus25519.two_255_19_prime.
    assert (primeToZ q <> 2)%Z by (pose proof q_odd; omega).
    assert (primeToZ q <> 0)%Z by (pose proof q_odd; omega).
    split; intros A. {
      apply square_Zmod_GF; auto.
      eapply euler_criterion.
      + auto.
      + pose proof q_odd; unfold q in *; omega.
      + apply div2_p_1mod4; auto.
      + apply nonzero_range; auto.
      + rewrite GFexp_Zpow in A by (auto || apply Z_div_pos; prime_bound).
        rewrite inject_mod_eq in A.
        apply gf_eq in A.
        replace (GFToZ 1) with 1%Z in A by auto.
        rewrite GFToZ_inject in A.
        rewrite Z.mod_mod in A by auto.
        exact A.
    } {
      rewrite GFexp_Zpow by first [apply Z.div_pos; pose proof q_odd; omega | auto].
      apply gf_eq.
      replace (GFToZ 1) with 1%Z by auto.
      rewrite GFToZ_inject.
      apply euler_criterion; auto.
      + apply nonzero_range; auto.
      + apply square_Zmod_GF; auto.
    }
  Qed.

  Lemma euler_criterion_if : forall (a : GF),
    if (orb (Zeq_bool (a ^ (Z.to_N (q / 2)))%GF 1) (Zeq_bool a 0))
    then (isSquare a) else (forall b, b * b <> a).
  Proof.
    intros.
    unfold orb. do 2 break_if; try congruence. {
      assert (a <> 0). {
        intro eq_a_0.
        replace 1%Z with (GFToZ 1) in Heqb1 by auto.
        apply GFdecidable in Heqb1; auto.
        rewrite eq_a_0 in Heqb1.
        rewrite GFexp_0 in Heqb1; auto.
        replace 0%N with (Z.to_N 0%Z) by auto.
        rewrite <- (Z2N.inj_lt 0 (q / 2)); (omega || pose proof gt_div2_q_zero; omega).
      }
      apply euler_criterion_GF; auto.
      apply GFdecidable; auto.
    } {
      exists 0.
      replace (0 * 0)%GF with 0%GF by field.
      replace 0%Z with (GFToZ 0) in Heqb0 by auto.
      apply GFdecidable in Heqb0; auto.
      subst; field.
    } {
      intros b b_id.
      assert (a <> 0). {
        intro eq_a_0.
        replace 0%Z with (GFToZ 0) in Heqb0 by auto.
        apply GFcomplete in eq_a_0.
        congruence.
      }
      assert (Zeq_bool (GFToZ (a ^ Z.to_N (q / 2))) 1 = true); try congruence. {
        replace 1%Z with (GFToZ 1) by auto; apply GFcomplete.
        apply euler_criterion_GF; unfold isSquare; eauto.
      }
   }
  Qed.

  Definition a := GFopp 1%GF.
  Lemma a_nonzero : a <> 0%GF.
  Proof.
    unfold a, GFopp; simpl.
    intuition.
    assert (proj1_sig 0%GF = proj1_sig (0 - 1)%GF) by (rewrite H0; reflexivity).
    assert (proj1_sig 0%GF = 0%Z) by auto.
    assert (proj1_sig (0 - 1)%GF <> 0%Z). {
      simpl; intuition.
      apply Z.rem_mod_eq_0 in H3; [|unfold two_255_19; cbv; omega].
      unfold Z.rem in H3; simpl in H3.
      congruence.
    }
    omega.
  Qed.

  Lemma q_1mod4 : (q mod 4 = 1)%Z.
  Proof.
    simpl.
    unfold Modulus25519.two_255_19.
    rewrite Zminus_mod.
    simpl.
    auto.
  Qed.

  Lemma a_square : exists sqrt_a, (sqrt_a^2 = a)%GF.
  Proof.
    intros.
    pose proof (minus1_square_1mod4 q (proj2_sig q) q_1mod4).
    destruct H0.
    apply square_Zmod_GF; try apply a_nonzero.
    exists (inject x).
    rewrite GFToZ_inject.
    rewrite <- Zmult_mod.
    rewrite GF_Zmod.
    unfold a.
    replace (GFopp 1) with (inject (q - 1)) by galois.
    auto.
  Qed.

  (* TODO *)
  (* d = ((-121665)%Z / 121666%Z)%GF.*)
  Definition d : GF := 37095705934669439343138083508754565189542113879843219016388785533085940283555%Z.
  Axiom d_nonsquare : forall x, x^2 <> d.
  (* Definition d_nonsquare : (forall x, x^2 <> d) := euler_criterion_if d. <-- currently not computable in reasonable time *)

  Module CurveParameters <: TwistedEdwardsParams Modulus_q.
    Module GFDefs := GFDefs.
    Definition modulus_odd : (primeToZ Modulus_q.modulus > 2)%Z := q_odd.
    Definition a : GF := a.
    Definition a_nonzero := a_nonzero.
    Definition a_square := a_square.
    Definition d := d.
    Definition d_nonsquare := d_nonsquare.
  End CurveParameters.
  Module Facts := CompleteTwistedEdwardsFacts Modulus_q CurveParameters.
  Module Import Curve := Facts.Curve.

  (* TODO: B = decodePoint (y=4/5, x="positive") *)
  Parameter B : point.
  Axiom B_not_identity : B <> zero.

  Definition l : Prime := exist _ (252 + 27742317777372353535851937790883648493)%Z prime_l.
  Lemma l_odd : (Z.to_nat l > 2)%nat.
  Proof.
    unfold l, primeToZ, proj1_sig.
    rewrite Z2Nat.inj_add; try omega.
    apply lt_plus_trans.
    compute; omega.
  Qed.
  Axiom l_order_B : (scalarMult (Z.to_nat l) B) = zero.

  (* H' is the identity function. *)
  Definition H'_out_len (n : nat) := n.
  Definition H' {n} (w : word n) := w.

  Lemma l_bound : Z.to_nat l < pow2 b.
  Proof.
    rewrite Zpow_pow2.
    rewrite <- Z2Nat.inj_lt by first [unfold l, primeToZ, proj1_sig; omega | compute; congruence].
    reflexivity.
  Qed.

  Definition Fq_enc (x : GF) : word (b - 1) := natToWord (b - 1) (Z.to_nat x).
  Definition Fq_dec (x_ : word (b - 1)) : option GF :=
      Some (inject (Z.of_nat (wordToNat x_))).
  Lemma Fq_encoding_valid : forall x : GF, Fq_dec (Fq_enc x) = Some x.
  Proof.
    unfold Fq_dec, Fq_enc; intros.
    f_equal.
    rewrite wordToNat_natToWord_idempotent. {
      rewrite Z2Nat.id by apply GF_mod_bound.
      apply inject_eq.
    } {
      rewrite <- Nnat.N2Nat.id.
      rewrite Npow2_nat.
      apply (Nat2N_inj_lt (Z.to_nat x) (pow2 (b - 1))).
      replace (pow2 (b - 1)) with (Z.to_nat (2 ^ (Z.of_nat b - 1))%Z) by (rewrite Zpow_pow2; auto).
      pose proof (GF_mod_bound x).
      pose proof b_valid.
      pose proof q_odd.
      replace modulus with q in * by reflexivity.
      apply Z2Nat.inj_lt; try omega.
    }
  Qed.
  Definition FqEncoding : encoding of GF as word (b-1) :=
    Build_Encoding GF (word (b-1)) Fq_enc Fq_dec Fq_encoding_valid.

  Definition Fl_enc (x : {s : nat | s mod (Z.to_nat l) = s}) : word b :=
    natToWord b (proj1_sig x).
  Definition Fl_dec (x_ : word b) : option {s:nat | s mod (Z.to_nat l) = s} :=
    match (lt_dec (wordToNat x_) (Z.to_nat l)) with
    | left A => Some (exist _ _ (Nat.mod_small _ (Z.to_nat l) A))
    | _ => None
    end.
  Lemma Fl_encoding_valid : forall x, Fl_dec (Fl_enc x) = Some x.
  Proof.
    Opaque l.
    unfold Fl_enc, Fl_dec; intros.
    assert (proj1_sig x < (Z.to_nat l)). {
      destruct x; simpl.
      apply Nat.mod_small_iff in e; auto.
      pose proof l_odd; omega.
    }
    rewrite wordToNat_natToWord_idempotent by 
      (pose proof l_bound; apply Nomega.Nlt_in; rewrite Nnat.Nat2N.id; rewrite Npow2_nat; omega).
    case_eq (lt_dec (proj1_sig x) (Z.to_nat l)); intros; try omega.
    destruct x.
    do 2 (simpl in *; f_equal).
    apply Eqdep_dec.UIP_dec.
    apply eq_nat_dec.
    Transparent l.
  Qed.

  Definition FlEncoding :=
    Build_Encoding {s:nat | s mod (Z.to_nat l) = s} (word b) Fl_enc Fl_dec Fl_encoding_valid.

  Lemma q_5mod8 : (q mod 8 = 5)%Z.
  Proof.
    simpl.
    unfold two_255_19.
    rewrite Zminus_mod.
    auto.
  Qed.

  (* TODO : move to ZUtil *)
  Lemma mod2_one_or_zero : forall x, (x mod 2 = 1)%Z \/ (x mod 2 = 0)%Z.
  Proof.
    intros.
    pose proof (Zmod_even x) as mod_even.
    case_eq (Z.even x); intro x_even; rewrite x_even in mod_even; auto.
  Qed.

  (* TODO: move to GaloisField *)
  Lemma GFexp_add : forall x k j, x ^ j * x ^ k = x ^ (j + k).
  Proof.
    intros.
    apply N.peano_ind with (n := j); simpl; try field.
    intros j' IHj.
    rewrite N.add_succ_l.
    rewrite GFexp_pred by apply N.neq_succ_0.
    assert (N.succ (j' + k) <> 0)%N as neq_exp_0 by apply N.neq_succ_0.
    rewrite (GFexp_pred _ neq_exp_0).
    do 2 rewrite N.pred_succ.
    rewrite <- IHj.
    field.
  Qed.

  Lemma GFexp_compose : forall k x j, (x ^ j) ^ k = x ^ (k * j).
  Proof.
    intros k.
    apply N.peano_ind with (n := k); auto.
    intros k' IHk x j.
    rewrite Nmult_Sn_m.
    rewrite <- GFexp_add.
    rewrite <- IHk.
    rewrite GFexp_pred by apply N.neq_succ_0.
    rewrite N.pred_succ.
    field.
  Qed.

  Lemma sqrt_one : forall x, x ^ 2 = 1 -> x = 1 \/ x = GFopp 1.
  Proof.
    intros x x_squared.
    apply sqrt_solutions.
    rewrite x_squared; field.
  Qed.

  Definition sqrt_minus1 := inject 2 ^ Z.to_N (q / 4).
  (* straightforward computation once GF computations get fast *)
  Axiom sqrt_minus1_valid : sqrt_minus1 ^ 2 = GFopp 1.

  (* square root mod q relies on the fact that q is 5 mod 8 *)
  Definition sqrt_mod_q (a : GF) := 
    let b := a ^ Z.to_N (q / 8 + 1) in
    (match (GF_eq_dec (b ^ 2) a) with
    | left A => b
    | right A => sqrt_minus1 * b
    end).

  Lemma eq_b4_a2 : forall x, isSquare x ->
    ((x ^ Z.to_N (q / 8 + 1)) ^ 2) ^ 2 = x ^ 2.
  Proof.
    intros.
    destruct (GF_eq_dec x 0). {
      admit.
    } {
      rewrite GFexp_compose.
      replace (2 * 2)%N with 4%N by auto.
      rewrite GFexp_compose.
      replace (4 * Z.to_N (q / 8 + 1))%N with (Z.to_N (q / 2 + 2))%N by (cbv; auto).
      pose proof gt_div2_q_zero.
      rewrite Z2N.inj_add by omega.
      rewrite <- GFexp_add by omega.
      replace (x ^ Z.to_N (q / 2)) with 1
        by (symmetry; apply euler_criterion_GF; auto).
      replace (Z.to_N 2) with 2%N by auto.
      field.
    }
  Qed.

  Lemma sqrt_mod_q_valid : forall x, isSquare x ->
    (sqrt_mod_q x) ^ 2 = x.
  Proof.
    intros x x_square.
    destruct (sqrt_solutions x _ (eq_b4_a2 x x_square)) as [? | eq_b2_oppx];
      unfold sqrt_mod_q; break_if; intuition.
    rewrite <- GFexp_distr_mul by apply N.le_0_2.
    rewrite sqrt_minus1_valid.
    rewrite eq_b2_oppx.
    field.
  Qed.

  Definition solve_for_x (y : GF) := sqrt_mod_q ( (y ^ 2 - 1) / (d * (y ^ 2) - a)).

  Lemma d_y2_a_nonzero : forall y, d * y ^ 2 - a <> 0.
    intros ? eq_zero.
    symmetry in eq_zero.
    apply GF_minus_plus in eq_zero.
    replace (0 + a) with a in eq_zero by field.
    destruct a_square as [sqrt_a a_square].
    rewrite <- a_square in eq_zero.
    destruct (GF_eq_dec y 0). {
      subst.
      rewrite a_square in eq_zero.
      replace (d * 0 ^ 2) with 0 in eq_zero by field.
      pose proof a_nonzero; auto.
    } {
      apply GF_square_mul in eq_zero; auto.
      destruct eq_zero as [sqrt_d d_square].
      pose proof (d_nonsquare sqrt_d).
      auto.
    }
  Qed.
  
  Lemma a_d_y2_nonzero : forall y, a - d * y ^ 2 <> 0.
  Proof.
    intros y eq_zero.
    symmetry in eq_zero.
    apply GF_minus_plus in eq_zero.
    replace (0 + d * y ^ 2) with (d * y ^ 2) in eq_zero by field.
    replace a with (0 + a) in eq_zero by field.
    symmetry in eq_zero.
    apply GF_minus_plus in eq_zero.
    pose proof (d_y2_a_nonzero y).
    auto.
  Qed.

  Lemma onCurve_solve_x2 : forall x y, onCurve (x, y) ->
    x ^ 2 = (y ^ 2 - 1) / (d * (y ^ 2) - a).
  Proof.
    intros ? ? onCurve_x_y.
    unfold onCurve, CurveParameters.d, CurveParameters.a in onCurve_x_y.
    apply GF_minus_plus in onCurve_x_y.
    symmetry in onCurve_x_y.
    replace (1 + d * x ^ 2 * y ^ 2 - y ^ 2) with (1 - y ^ 2 + d * x ^ 2 * y ^ 2)
      in onCurve_x_y by ring.
    apply GF_minus_plus in onCurve_x_y.
    replace (a * x ^ 2 - d * x ^ 2 * y ^ 2) with (x ^ 2 * (a - d * y ^ 2)) in onCurve_x_y by ring.
    replace ((y ^ 2 - 1) / (d * y ^ 2 - a)) with ((1 - y ^ 2) / (a - d * y ^ 2))
      by (field; [ apply d_y2_a_nonzero | apply a_d_y2_nonzero ]).
    rewrite onCurve_x_y.
    unfold GFdiv.
    field.
    apply a_d_y2_nonzero.
  Qed.

  Lemma solve_for_x_onCurve (x y : GF): onCurve (x, y) ->
    onCurve (solve_for_x y, y).
  Proof.
    intros.
    unfold onCurve, solve_for_x, CurveParameters.d, CurveParameters.a.
    rewrite sqrt_mod_q_valid by (erewrite <- onCurve_solve_x2; unfold isSquare; eauto).
    field; apply d_y2_a_nonzero.
  Qed.

  Lemma solve_for_x_onCurve_GFopp (x y : GF) : onCurve (x, y) ->
    onCurve (GFopp (solve_for_x y), y).
  Proof.
    pose proof (solve_for_x_onCurve x y) as x_onCurve.
    unfold onCurve, CurveParameters.d, CurveParameters.a in *.
    replace ((solve_for_x y) ^ 2) with ((GFopp (solve_for_x y)) ^ 2) in x_onCurve by field.
    auto.
  Qed.

  (* 
  * Admitting these looser version of solve_for_x_onCurve and
  * solve_for_x_onCurve_GFopp for now; need to figure out how 
  * to deal with the onCurve precondition when inside point_dec.
  *)
  Lemma solve_for_x_onCurve_loose : forall y, onCurve (solve_for_x y, y).
  Admitted.

  Lemma solve_for_x_onCurve_GFopp_loose :
    forall y, onCurve (GFopp (solve_for_x y), y).
  Admitted.

  Lemma point_onCurve : forall p, onCurve (projX p, projY p).
  Proof.
    intro.
    replace (projX p, projY p) with (proj1_sig p)
      by (unfold projX, projY; apply surjective_pairing).
    apply (proj2_sig p).
  Qed.

  Lemma GFopp_x_point : forall p p', projY p = projY p' ->
    projX p = projX p' \/ projX p = GFopp (projX p').
  Proof.
    intros ?  ? projY_eq.
    pose proof (point_onCurve p) as onCurve_p.
    pose proof (point_onCurve p') as onCurve_p'.
    apply sqrt_solutions.
    rewrite projY_eq in *.
    unfold solve_for_x, onCurve, CurveParameters.a, CurveParameters.d in *.
    apply onCurve_solve_x2 in onCurve_p.
    apply onCurve_solve_x2 in onCurve_p'.
    rewrite <- onCurve_p in onCurve_p'; auto.
  Qed.

  Lemma GFopp_solve_for_x : forall p,
    solve_for_x (projY p) = projX p \/ solve_for_x (projY p) = GFopp (projX p).
  Proof.
    intros.
    pose proof (point_onCurve p).
    remember (mkPoint (solve_for_x (projY p), projY p) (solve_for_x_onCurve (projX p) (projY p) (point_onCurve p))) as q1.
    replace (solve_for_x (projY p)) with (projX q1) by (rewrite Heqq1; auto).
    apply GFopp_x_point.
    rewrite Heqq1; auto.
  Qed.

  Definition sign_bit (x : GF) := (wordToN (Fq_enc (GFopp x)) <? wordToN (Fq_enc x))%N.
  Definition point_enc (p : point) : word b := WS (sign_bit (projX p)) (Fq_enc (projY p)).
  Definition point_dec (w : word (S (b - 1))) : option point :=
    match (Fq_dec (wtl w)) with
    | None => None
    | Some y => match (Bool.eqb (whd w) (sign_bit (solve_for_x y))) with
                | true  => value (mkPoint (solve_for_x y, y) (solve_for_x_onCurve_loose y ))
                | false => value (mkPoint (GFopp (solve_for_x y), y) (solve_for_x_onCurve_GFopp_loose y))
                end
    end.


  Definition value_or_default {T} (opt : option T) d := match opt with
    | Some x => x
    | None => d
    end.

  Lemma value_or_default_inj : forall {T} (x y d : T),
    value_or_default (Some x) d = value_or_default (Some y) d -> x = y.
  Proof.
    unfold value_or_default; auto.
  Qed.

  Lemma Fq_enc_inj : forall x y, Fq_enc x = Fq_enc y -> x = y.
  Proof.
    intros ? ? enc_eq.
    pose proof (Fq_encoding_valid x) as enc_valid_x.
    rewrite enc_eq in enc_valid_x.
    pose proof (Fq_encoding_valid y) as enc_valid_y.
    rewrite enc_valid_x in enc_valid_y.
    apply value_or_default_inj with (d := 0).
    rewrite enc_valid_y; auto.
  Qed.

  Lemma sign_bit_GFopp_negb : forall x, sign_bit x = negb (sign_bit (GFopp x)) \/ x = GFopp x.
  Proof.
    intros.
    destruct (GF_eq_dec x (GFopp x)); auto.
    left.
    unfold sign_bit.
    rewrite GFopp_involutive.
    rewrite N.ltb_antisym.
    case_eq (wordToN (Fq_enc x) <=? wordToN (Fq_enc (GFopp x)))%N; intro A.
    + apply N.leb_le in A.
      apply N.lt_eq_cases in A.
      destruct A as [A | A].
      - apply N.ltb_lt in A.
        rewrite A; auto.
      - apply wordToN_inj in A.
        apply Fq_enc_inj in A.
        congruence.
   + apply N.leb_gt in A.
     rewrite N.ltb_antisym.
     apply N.lt_le_incl in A.
     apply N.leb_le in A.
     rewrite A.
     auto.
  Qed.

  Lemma point_mkPoint : forall p, p = mkPoint (proj1_sig p) (proj2_sig p).
  Proof.
    intros; destruct p; auto.
  Qed.

  Lemma onCurve_proof_eq : forall x y (P : onCurve x) (Q : onCurve y) (xyeq: x = y),
    match xyeq in (_ = y') return onCurve y' with
    | eq_refl => P
    end = Q.
  Proof.
    intros; subst.
    intros; unfold onCurve in *.
    break_let.
    apply Eqdep_dec.UIP_dec.
    exact GF_eq_dec.
  Qed.

  Lemma two_arg_eq : forall {A B} C (f : forall a: A, B a -> C) x1 y1 x2 y2 (xeq: x1 = x2),
    match xeq in (_ = x) return (B x) with
    | eq_refl => y1
    end = y2 -> f x1 y1 = f x2 y2.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Lemma point_destruct : forall p P, mkPoint (projX p, projY p) P = p.
  Proof.
    intros; rewrite point_mkPoint.
    assert ((projX p, projY p) = proj1_sig p) by
      (unfold projX, projY; simpl; symmetry; apply surjective_pairing).
    apply two_arg_eq with (xeq := H0).
    apply onCurve_proof_eq.
  Qed.

  (* There are currently two copies of mkPoint in scope. I would like to use Facts.point_eq
     here, but it is proven for Facts.Curve.mkPoint, not mkPoint. These are equivalent, but
     I have so far not managed to unify them. *)
  Lemma point_eq_copy : forall x1 x2 y1 y2, x1 = x2 -> y1 = y2 ->
    forall p1 p2, mkPoint (x1, y1) p1 = mkPoint (x2, y2) p2.
    apply Facts.point_eq.
  Qed.

  Lemma point_encoding_valid : forall p, point_dec (point_enc p) = Some p.
  Proof.
    intros.
    unfold point_dec, point_enc, wtl, whd.
    rewrite Fq_encoding_valid.
    break_if; unfold value; f_equal. {
      remember (mkPoint (solve_for_x (projY p), projY p) (solve_for_x_onCurve (projX p) (projY p) (point_onCurve p))).
      rewrite <- (point_destruct _ (point_onCurve p)).
      subst.
      apply point_eq_copy; auto.
      destruct (GFopp_solve_for_x p) as [? | A]; auto.
      rewrite A in Heqb0.
      pose proof (sign_bit_GFopp_negb (projX p)) as sign_bit_opp.
      destruct sign_bit_opp as [sign_bit_opp | opp_eq ]; [ | rewrite opp_eq; auto ].
      rewrite Bool.eqb_true_iff in Heqb0.
      rewrite Heqb0 in sign_bit_opp.
      symmetry in sign_bit_opp.
      apply Bool.no_fixpoint_negb in sign_bit_opp.
      contradiction.
    } {
      remember (mkPoint (GFopp (solve_for_x (projY p)), projY p) (solve_for_x_onCurve_GFopp (projX p) (projY p) (point_onCurve p))).
      rewrite <- (point_destruct _ (point_onCurve p)).
      subst.
      apply point_eq_copy; auto.
      destruct (GFopp_solve_for_x p) as [A | A]; try apply GFopp_swap; auto; 
        rewrite A in Heqb0; apply Bool.eqb_false_iff in Heqb0; congruence.
    }
  Qed.

  Definition PointEncoding := Build_Encoding point (word b) point_enc point_dec point_encoding_valid.

  Print Assumptions PointEncoding.

End EdDSA25519_Params.

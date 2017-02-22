Require Import Coq.ZArith.ZArith.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.CompleteEdwardsCurve.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.WordUtil.
Require Import Crypto.Util.FixCoqMistakes.
Require Crypto.Encoding.PointEncodingPre.

(* This file should fill in the following context variables from EdDSARepChange.v
   Eenc := encode_point
   Proper_Eenc := Proper_encode_point
   Edec := Fdecode_point (notation)
   eq_enc_E_iff := encode_point_decode_point_iff
   EToRep := point_phi
   Ahomom := point_phi_homomorphism
   ERepEnc := Kencode_point
   ERepEnc_correct := Kencode_point_correct
   Proper_ERepEnc := Proper_Kencode_point
   ERepDec := Kdecode_point
   ERepDec_correct := Kdecode_point_correct
*)

Section PointEncoding.
  Context {b : nat} {m : positive} {Fa Fd : F m} {prime_m : Znumtheory.prime m}
          {two_lt_m : (2 < m)%Z}
          {bound_check : (Z.to_nat m < 2 ^ b)%nat}.

  Local Infix "++" := Word.combine.
  Local Notation bit b := (Word.WS b Word.WO : Word.word 1).

  Definition sign (x : F m) : bool := Z.testbit (F.to_Z x) 0.
  Definition Fencode (x : F m) : word b := NToWord b (Z.to_N (F.to_Z x)).

  Let Fpoint := @E.point (F m) Logic.eq F.one F.add F.mul Fa Fd.

  Definition encode_point (P : Fpoint) :=
    let '(x,y) := E.coordinates P in Fencode y ++ bit (sign x).

  Import Morphisms.
  Lemma Proper_encode_point : Proper (E.eq ==> Logic.eq) encode_point.
  Proof.
    repeat intro.
    eapply @E.Proper_coordinates in H; eauto using F.field_modulo, F.eq_dec.
    cbv [encode_point].
    remember (E.coordinates x) as cx; destruct cx as [cx1 cy1].
    remember (E.coordinates y) as cy; destruct cy as [cx2 cy2].
    inversion H; cbv [fst snd] in *.
    cbv [Tuple.fieldwise'] in *.
    repeat f_equal; auto.
  Qed.

  Section RepChange.
    Context {K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            `{Kfield:@Algebra.field K Keq Kzero Kone Kopp Kadd Ksub Kmul Kinv Kdiv}
            {Keq_dec:Decidable.DecidableRel Keq}.
    Context {phi:F m->K} {phi_homomorphism : @Algebra.Ring.is_homomorphism
                                              (F m) eq F.one F.add F.mul
                                              K Keq Kone Kadd Kmul phi}.
    Context {Ka Kd : K} {phi_a : Keq (phi Fa) Ka} {phi_d : Keq (phi Fd) Kd}.
    Context {Ksign : K -> bool} {Kenc : K -> word b}
            {Ksign_correct : forall x, sign x = Ksign (phi x)}
            {Kenc_correct : forall x, Fencode x = Kenc (phi x)}.

    Context {Kpoint}
            {Kcoord_to_point : @E.point K Keq Kone Kadd Kmul Ka Kd  -> Kpoint}
            {Kpoint_to_coord : Kpoint -> (K * K)}.
    Context {Kp2c_c2p : forall pt : E.point, Tuple.fieldwise (n := 2) Keq (Kpoint_to_coord (Kcoord_to_point pt)) (E.coordinates pt)}.
    Context {Kpoint_eq : Kpoint -> Kpoint -> Prop} {Kpoint_add : Kpoint -> Kpoint -> Kpoint}.
    Context {Kpoint_eq_correct : forall p q, Kpoint_eq p q <-> Tuple.fieldwise (n := 2) Keq (Kpoint_to_coord p) (Kpoint_to_coord q)} {Kpoint_eq_Equivalence : Equivalence Kpoint_eq}.

    Context {phi_bijective : forall x y, Keq (phi x) (phi y) <-> x = y}.

    Lemma phi_onCurve : forall x y,
      eq (F.add (F.mul Fa (F.mul x x)) (F.mul y y))
         (F.add F.one (F.mul (F.mul Fd (F.mul x x)) (F.mul y y))) <->
      Keq (Kadd (Kmul Ka (Kmul (phi x) (phi x))) (Kmul (phi y) (phi y)))
          (Kadd Kone (Kmul (Kmul Kd (Kmul (phi x) (phi x))) (Kmul (phi y) (phi y)))).
    Proof.
      intros.
      rewrite <-phi_a, <-phi_d.
      rewrite <-(Algebra.Ring.homomorphism_one(phi:=phi)).
      rewrite <-!Algebra.Ring.homomorphism_mul.
      rewrite <-!Algebra.Ring.homomorphism_add.
      rewrite phi_bijective.
      reflexivity.
    Qed.

    Definition point_phi (P : Fpoint) : Kpoint := Kcoord_to_point (E.point_phi (fieldK := Kfield) (Ha := phi_a) (Hd := phi_d) P).

    Lemma Proper_point_phi : Proper (E.eq ==> Kpoint_eq) point_phi.
    Proof.
      repeat intro.
      apply Kpoint_eq_correct; cbv [point_phi].
      destruct x, y.
      repeat break_let.
      cbv [E.point_phi].
      rewrite !Kp2c_c2p.
      apply E.Proper_coordinates in H; cbv [E.coordinates proj1_sig] in H.
      inversion H; econstructor; cbv [Tuple.fieldwise' fst snd] in *; subst;
        reflexivity.
    Qed.

    Notation Fpoint_add := (@E.add _ _ _ _ _ _ _ _ _ _ (F.field_modulo m) _ Fa Fd _).
    Definition Fdecode (w : word b) : option (F m) :=
      let z := Z.of_N (wordToN w) in
      if Z_lt_dec z m then Some (F.of_Z m z) else None.

    (* The following does not build

    Context {Kpoint_add_correct : forall P Q, Kpoint_eq
                                                (point_phi (Fpoint_add P Q))
                                                (Kpoint_add (point_phi P) (point_phi Q))}.
    Context {Kdec : word b -> option K} {Ksqrt : K -> K}.
    Context {Proper_Ksqrt : Proper (Keq ==> Keq) Ksqrt}
            {Proper_Ksign : Proper (Keq ==> eq) Ksign}
            {Proper_Kenc : Proper (Keq ==> eq) Kenc}.
    Context {phi_decode : forall w,
                option_eq Keq (option_map phi (Fdecode w)) (Kdec w)}.
    Context {Fsqrt : F m -> F m}
            {phi_sqrt : forall x, Keq (phi (Fsqrt x)) (Ksqrt (phi x))}
            {Fsqrt_square : forall x root, eq x (F.mul root root) ->
                                        eq (F.mul (Fsqrt x) (Fsqrt x)) x}.

    Lemma point_phi_homomorphism: @Algebra.Monoid.is_homomorphism
                                    Fpoint E.eq Fpoint_add
                                    Kpoint Kpoint_eq Kpoint_add point_phi.
    Proof.
      econstructor; intros; auto using Kpoint_add_correct.
      apply Proper_point_phi.
    Qed.

    Definition Kencode_point (P : Kpoint) :=
      let '(x,y) := Kpoint_to_coord P in (Kenc y) ++ bit (Ksign x).

    Lemma Kencode_point_correct : forall P : Fpoint,
        encode_point P = Kencode_point (point_phi P).
    Proof.
      cbv [encode_point Kencode_point point_phi]; intros.
      destruct P as [[fx fy]]; cbv [E.coordinates proj1_sig].
      break_match.
      match goal with
      H: Kpoint_to_coord (Kcoord_to_point ?x) = (_,_) |- _ => let A := fresh "H" in
      pose proof (Kp2c_c2p x) as A; rewrite Heqp in A;
        inversion A; cbv [fst snd Tuple.fieldwise'] in * end.
      cbv [E.coordinates E.ref_phi proj1_sig] in *.
      apply (f_equal2 (fun a b => a ++ b));
        try apply (f_equal2 (fun a b => WS a b));
        rewrite ?H0, ?H1; auto.
    Qed.

    Lemma Proper_Kencode_point : Proper (Kpoint_eq ==> Logic.eq) Kencode_point.
    Proof.
      repeat intro; cbv [Kencode_point].
      apply Kpoint_eq_correct in H.
      simpl in H.
      destruct (Kpoint_to_coord x).
      destruct (Kpoint_to_coord y).
      simpl in H; destruct H.
      apply (f_equal2 (fun a b => a ++ b));
        try apply (f_equal2 (fun a b => WS a b));
        rewrite ?H0, ?H1; auto.
    Qed.


    Definition Kcoordinates_from_y sign_bit (y : K) : option (K * K) :=
      let x2 := @E.solve_for_x2 _ Kone Ksub Kmul Kdiv Ka Kd y in
      let x := Ksqrt x2 in
      if Keq_dec (Kmul x x) x2
      then
          let p := (if Bool.eqb sign_bit (Ksign x) then x else Kopp x, y) in
          if (PointEncodingPre.F_eqb x Kzero && sign_bit)%bool
          then None
          else Some p
      else None.

    Definition Kdecode_coordinates (w : word (b + 1)) : option (K * K) :=
      option_rect (fun _ => option (K * K))
                  (Kcoordinates_from_y (wlast w))
                  None
                  (Kdec (winit w)).

    Lemma onCurve_eq : forall x y,
      Keq (Kadd (Kmul Ka (Kmul x x)) (Kmul y y))
          (Kadd Kone (Kmul (Kmul Kd (Kmul x x)) (Kmul y y))) ->
      @E.onCurve _ Keq Kone Kadd Kmul Ka Kd x y.
    Proof.
      clear; tauto.
    Qed.

    Definition Kpoint_from_xy (xy : K * K) : option Kpoint :=
      let '(x,y) := xy in
      match Decidable.dec (Keq (Kadd (Kmul Ka (Kmul x x)) (Kmul y y))
                    (Kadd Kone (Kmul (Kmul Kd (Kmul x x)) (Kmul y y)))) with
        | left A => Some (Kcoord_to_point (exist _ (x,y) (onCurve_eq x y A)))
        | right _ => None
      end.

    Definition Kdecode_point (w : word (b+1)) : option Kpoint :=
      option_rect (fun _ => option Kpoint) Kpoint_from_xy None (Kdecode_coordinates w).

    Definition Fencoding : Encoding.CanonicalEncoding (F m) (word b).
    Proof.
      eapply Encoding.Build_CanonicalEncoding with (enc := Fencode) (dec := Fdecode);
        cbv [Fencode Fdecode]; intros.
      + assert (0 < m)%Z as m_pos by (ZUtil.Z.prime_bound).
        pose proof (F.to_Z_range x m_pos).
        rewrite !wordToN_NToWord_idempotent by (apply bound_check_nat_N;
          transitivity (Z.to_nat m); auto;  apply Z2Nat.inj_lt; omega).
        rewrite Z2N.id by omega.
        rewrite F.of_Z_to_Z.
        break_if; auto; omega.
      + break_if; auto; try discriminate.
        inversion H; subst. clear H.
        rewrite F.to_Z_of_Z.
        rewrite Z.mod_small by (split; try omega; auto using N2Z.is_nonneg).
        rewrite N2Z.id.
        apply NToWord_wordToN.
    Defined.

    Lemma Fdecode_encode_iff P_ P : Fencode P = P_ <-> Fdecode P_ = Some P.
    Proof.
      pose proof (@Encoding.encoding_canonical _ _ Fencoding).
      pose proof (@Encoding.encoding_valid _ _ Fencoding).
      cbv [Encoding.dec Encoding.enc Fencoding] in *.
      split; intros; subst; auto.
    Qed.

    Lemma option_rect_shuffle :
      forall {X A B C D} (x : X)
             (EQD : D -> D -> Prop) (EQC : C -> C -> Prop)
             {EquivC : Equivalence EQD} {EquivC : Equivalence EQC}
             (ab : A -> B) (bc : B -> option C) (dc : D -> option C) (ad : A -> D)
             {Proper_dc : Proper (EQD==>option_eq EQC) dc}
             (oa : X -> option A) (od : X -> option D),
      (forall x : X, option_eq EQD (option_map ad (oa x)) (od x)) ->
      (forall x : A, option_eq EQC (dc (ad x)) (bc (ab x))) ->
      option_eq EQC
        (option_rect (fun _ => option C) (fun x: D => dc x) None (od x))
        (option_rect (fun _ => option C) (fun x : A => bc (ab x)) None (oa x)).
    Proof.
      cbv; intros.
      specialize (H x).
      destruct (oa x) as [a |]; [ | repeat break_match; reflexivity || discriminate].
      destruct (od x) as [d |]; [ | contradiction ].
      pose proof (H0 a).
      assert (option_eq EQC (dc d) (dc (ad a))) by (apply Proper_dc; symmetry; auto).
      cbv [option_eq] in *.
      repeat break_match; try tauto; try reflexivity; try discriminate;
        etransitivity; eauto.
    Qed.

    Notation Fdecode_coordinates :=( @PointEncodingPre.point_dec_coordinates
                           _ eq F.zero F.one F.opp F.sub F.mul F.div
                           _ Fa Fd _ Fsqrt Fencoding sign).
    Notation Fdecode_point := (@PointEncodingPre.point_dec
                           _ eq F.zero F.one F.opp F.add F.sub F.mul F.div
                           _ Fa Fd _ Fsqrt Fencoding sign).

    Lemma phi_solve_for_x2 : forall x : F m,
      Keq (@E.solve_for_x2 _ Kone Ksub Kmul Kdiv Ka Kd (phi x))
          (phi (@E.solve_for_x2 _ F.one F.sub F.mul F.div Fa Fd x)).
    Proof.
      intros.
      cbv [E.solve_for_x2].
      rewrite Algebra.Field.homomorphism_div by apply E.a_d_y2_nonzero.
      rewrite !Algebra.Ring.homomorphism_sub.
      rewrite !Algebra.Ring.homomorphism_mul.
      rewrite Algebra.Ring.homomorphism_one.
      rewrite phi_a, phi_d.
      reflexivity.
    Qed.

    Lemma option_map_option_rect : forall {A B C} (g : B -> C) (f : A -> option B) o,
      option_map g (option_rect (fun _ : option A => _) f None o) =
      option_rect (fun _ : option A => _)
                  (fun x => option_map g (f x)) None o.
    Proof.
      intros. cbv [option_rect option_map].
      repeat (break_match; try discriminate); congruence.
    Qed.

    Notation Fcoordinates_from_y :=
      (@PointEncodingPre.coord_from_y
        _ eq F.zero F.one F.opp F.sub F.mul F.div
        _ Fa Fd Fsqrt sign).

    Definition coord_phi (p : F m* F m) := let '(x, y) := p in (phi x, phi y).

    Lemma Kcoordinates_from_y_correct : forall sign_bit y,
      option_eq (Tuple.fieldwise (n := 2) Keq)
        (Kcoordinates_from_y sign_bit (phi y))
        (option_map coord_phi (Fcoordinates_from_y sign_bit y)).
    Proof.
      cbv [Kcoordinates_from_y PointEncodingPre.coord_from_y].
      intros.
      match goal with
        |- option_eq _ _ (option_map ?f (if ?A
                                         then (if ?B then None else Some ?xy)
                                         else None)) =>
        transitivity (if A then (if B then None else Some (f xy)) else None);
          [ | repeat (break_if; auto; try discriminate); reflexivity]
      end.
      match goal with
        |- option_eq _ (if Keq_dec ?ka ?kb  then _ else _)
                       (if F.eq_dec ?fa ?fb then _ else _) =>
        destruct (Keq_dec ka kb) as [keq | keq];
          rewrite phi_solve_for_x2, <-phi_sqrt, <-Algebra.Ring.homomorphism_mul in keq;
          rewrite phi_bijective in keq;
          destruct (F.eq_dec fa fb); try congruence; try reflexivity
      end.
      clear keq e.
      match goal with
        |- option_eq _ (if ?A then _ else _) (if ?B then _ else _) => assert (A = B)
      end.
      {
        destruct (sign_bit); rewrite ?Bool.andb_true_r, ?Bool.andb_false_r; auto.
        cbv [PointEncodingPre.F_eqb].
        pose proof (@Algebra.Ring.homomorphism_is_homomorphism _ _ _ _ _ _ _ _ _ _ _ phi_homomorphism).
        pose proof (@Algebra.Group.homomorphism_id _ _  _ _ _ _ _ _  _ _ _ _ _ H).
        match goal with |- (if ?x then _ else _) = _ => destruct x as [keq | keq] end;
        rewrite phi_solve_for_x2, <-phi_sqrt, <-H0 in keq;
        rewrite phi_bijective in keq; cbv [F.zero]; break_if; try congruence; reflexivity.
      }
      rewrite H.
      break_if; try reflexivity.
      econstructor; cbv [coord_phi Tuple.fieldwise' fst snd]; try reflexivity.
      rewrite Ksign_correct, !phi_sqrt, !phi_solve_for_x2.
      break_if; rewrite ?Algebra.Ring.homomorphism_opp, ?phi_sqrt, ?phi_solve_for_x2;
        reflexivity.
    Qed.

    Global Instance Proper_solve_for_x2 : forall {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv a d}
                         {Ffield : @Algebra.field F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv},
        Proper (Feq==>Feq) (@E.solve_for_x2 F Fone Fsub Fmul Fdiv a d) | 0.
    Proof.
      repeat intro; subst.
      cbv [E.solve_for_x2].
      rewrite H. reflexivity.
    Qed.

    Lemma Proper_Kcoordinates_from_y :
      Proper (eq==>Keq ==> option_eq (Tuple.fieldwise (n := 2) Keq)) Kcoordinates_from_y.
    Proof.
      repeat intro; subst.
      cbv [Kcoordinates_from_y].
      match goal with |- option_eq _ (if ?A then _ else _) (if ?B then _ else _) =>
                      destruct A as [keq | keq]; rewrite H0 in keq;
                        destruct B; try congruence; try reflexivity end.
      destruct y; rewrite ?Bool.andb_true_r, ?Bool.andb_false_r;
        break_if; repeat break_if;
          rewrite ?@PointEncodingPre.F_eqb_iff, <-?@PointEncodingPre.F_eqb_false,
          ?Bool.eqb_true_iff, ?Bool.eqb_false_iff in *; try discriminate; try reflexivity;
            repeat match goal with
                   | H : appcontext[E.solve_for_x2 x0] |- _ => rewrite H0 in H;
                                                                 congruence end;
        simpl; rewrite H0; intuition reflexivity.
    Qed.

    Lemma Kdecode_coordinates_correct : forall w,
      option_eq (Tuple.fieldwise (n := 2) Keq)
      (Kdecode_coordinates w)
      (option_map coord_phi (Fdecode_coordinates w)).
    Proof.
      intros; cbv [Kdecode_coordinates point_phi PointEncodingPre.point_dec_coordinates].
      rewrite option_map_option_rect.
      eapply option_rect_shuffle with (EQD := Keq).
      + apply Algebra.monoid_Equivalence.
      + apply (@Tuple.Equivalence_fieldwise K _ _ 2).
      + apply Proper_Kcoordinates_from_y; auto.
      + cbv [Encoding.dec Fencoding].
        apply phi_decode.
      + apply Kcoordinates_from_y_correct.
    Qed.

    Lemma Kpoint_from_xy_correct : forall xy,
      option_eq Kpoint_eq
        (Kpoint_from_xy (coord_phi xy))
        (option_map point_phi (PointEncodingPre.point_from_xy xy)).
    Proof.
      intros; cbv [Kpoint_from_xy PointEncodingPre.point_from_xy coord_phi].
      destruct xy as [x y].
      pose proof (phi_onCurve x y).
      repeat break_match; try tauto; try reflexivity.
      simpl.
      apply Kpoint_eq_correct.
      cbv [point_phi E.ref_phi].
      rewrite !Kp2c_c2p.
      reflexivity.
    Qed.

    Lemma Proper_Kpoint_from_xy :
      Proper (Tuple.fieldwise (n := 2) Keq ==> option_eq Kpoint_eq) Kpoint_from_xy.
    Proof.
      repeat intro; cbv [Kpoint_from_xy].
      destruct x as [x1 y1].
      destruct y as [x2 y2].
      cbv [Tuple.tuple' Tuple.fieldwise Tuple.fieldwise' fst snd] in *.
      destruct H.
      break_match. {
        pose proof k as k'.
        rewrite H, H0 in k'.
        break_match; try congruence.
        simpl. apply Kpoint_eq_correct.
        repeat break_match.
        do 2 match goal with
          H: Kpoint_to_coord (Kcoord_to_point ?pt) = (_,_) |- _ =>
          let A := fresh "H" in
          pose proof (Kp2c_c2p pt) as A; rewrite H in A;
            cbv [E.coordinates proj1_sig] in *; inversion A;
              clear A H
             end.
        split;
        repeat match goal with
               | |- _ => assumption
               | |- _ => symmetry; assumption
               | |- _ => etransitivity; [ eassumption | ]
               end.
      } {
        pose proof n as k'.
        rewrite H, H0 in k'.
        break_match; congruence.
      }
    Qed.

    Lemma Kdecode_point_correct : forall w,
        option_eq Kpoint_eq (Kdecode_point w) (option_map point_phi (Fdecode_point w)).
    Proof.
      intros; cbv [Kdecode_point PointEncodingPre.point_dec].
      rewrite option_map_option_rect.
      eapply option_rect_shuffle with (EQD := Tuple.fieldwise (n := 2) Keq).
      + apply Tuple.Equivalence_fieldwise.
      + auto.
      + apply Proper_Kpoint_from_xy.
      + intros. symmetry. apply Kdecode_coordinates_correct.
      + intros. apply Kpoint_from_xy_correct.
    Qed.

    Lemma sign_zero : forall x, x = F.zero -> sign x = false.
    Proof.
      intros; subst.
      reflexivity.
    Qed.

    Lemma sign_negb : forall x : F m, x <> F.zero ->
                                      negb (sign x) = sign (F.opp x).
    Proof.
      intros.
      cbv [sign].
      rewrite !Z.bit0_odd.
      rewrite F.to_Z_opp.
      rewrite F.eq_to_Z_iff in H.
      replace (@F.to_Z m F.zero) with 0%Z in H by reflexivity.
      rewrite Z.mod_opp_l_nz by (solve [ZUtil.Z.prime_bound] ||
                                   rewrite F.mod_to_Z; auto).
      rewrite F.mod_to_Z.
      rewrite Z.odd_sub.
      destruct (ZUtil.Z.prime_odd_or_2 m prime_m) as [? | m_odd];
        [ omega | rewrite m_odd].
      rewrite <-Bool.xorb_true_l; auto.
    Qed.

    Lemma Eeq_point_eq : forall x y : option E.point,
        option_eq E.eq x y <->
        option_eq
          (@PointEncodingPre.point_eq _ eq F.one F.add F.mul Fa Fd) x y.
    Proof.
      intros.
      cbv [option_eq CompleteEdwardsCurve.E.eq E.eq E.coordinates PointEncodingPre.point_eq
                     PointEncodingPre.prod_eq]; repeat break_match;
        try reflexivity.
    Qed.
    
    Lemma enc_canonical_equiv : forall (x_enc : word b) (x : F m),
      option_eq eq (Fdecode x_enc) (Some x) ->
      Fencode x = x_enc.
    Proof.
      intros.
      cbv [option_eq] in *.
      break_match; try discriminate.
      subst.
      apply (@Encoding.encoding_canonical _ _ Fencoding).
      auto.
    Qed.

    Lemma encode_point_decode_point_iff : forall P_ P,
      encode_point P = P_ <->
      Option.option_eq E.eq (Fdecode_point P_) (Some P).
    Proof.
      pose proof (@PointEncodingPre.point_encoding_canonical
                    _ eq F.zero F.one F.opp F.add F.sub F.mul F.div
                    _ Fa Fd _ Fsqrt Fencoding enc_canonical_equiv
                    sign sign_zero sign_negb
                 ) as Hcanonical.
      let A := fresh "H" in
      match type of Hcanonical with
        ?P -> _ => assert P as A by congruence;
                     specialize (Hcanonical A); clear A end.
      intros.
      rewrite Eeq_point_eq.
      split; intros; subst.
      { apply PointEncodingPre.point_encoding_valid;
          auto using sign_zero, sign_negb;
          congruence. }
      { apply Hcanonical.
        cbv [option_eq PointEncodingPre.point_eq PointEncodingPre.prod_eq] in H |- *.
        break_match; congruence. }
    Qed.

  End RepChange.

End PointEncoding.

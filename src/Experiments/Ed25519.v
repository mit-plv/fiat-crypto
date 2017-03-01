Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Crypto.EdDSARepChange.
Require Import Crypto.MxDHRepChange. Import MxDH.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.NUtil.
Require Crypto.Specific.GF25519.
Require Crypto.Specific.GF25519Bounded.
Require Crypto.Specific.SC25519.
Require Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Crypto.Util.IterAssocOp.
Import Morphisms.
Import NPeano.

Local Coercion GF25519BoundedCommon.word64ToZ : GF25519BoundedCommon.word64 >-> Z.
Local Coercion GF25519BoundedCommon.proj1_fe25519 : GF25519BoundedCommon.fe25519 >-> GF25519.fe25519.
Local Set Printing Coercions.

Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).

Context {SHA512: forall n : nat, Word.word n -> Word.word 512}.

(* MOVE : pre-Specific, same level as other fe operations *)
Definition feSign (f :  GF25519BoundedCommon.fe25519) : bool :=
  let x := GF25519Bounded.freeze f in
  let '(x9, x8, x7, x6, x5, x4, x3, x2, x1, x0) := (x : GF25519.fe25519) in
  BinInt.Z.testbit x0 0.

Section Constants.
  Import GF25519BoundedCommon.
  Definition a' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in GF25519BoundedCommon.encode a.
  Definition a : GF25519BoundedCommon.fe25519 :=
    Eval cbv [a' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (fe25519_word64ize a').
  Definition d' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in GF25519BoundedCommon.encode d.
  Definition d : GF25519BoundedCommon.fe25519 :=
    Eval cbv [d' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (fe25519_word64ize d').
  Definition twice_d' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in (GF25519Bounded.add d d).
  Definition twice_d : GF25519BoundedCommon.fe25519 :=
    Eval cbv [twice_d' fe25519_word64ize word64ize andb opt.word64ToZ opt.word64ize opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (fe25519_word64ize twice_d').
End Constants.

Lemma phi_a : GF25519BoundedCommon.eq (GF25519BoundedCommon.encode Spec.Ed25519.a) a.
Proof. reflexivity. Qed.
Lemma phi_d : GF25519BoundedCommon.eq (GF25519BoundedCommon.encode Spec.Ed25519.d) d.
Proof. vm_decide_no_check. Qed.

Definition Erep := (@ExtendedCoordinates.Extended.point
         GF25519BoundedCommon.fe25519
         GF25519BoundedCommon.eq
         GF25519BoundedCommon.zero
         GF25519Bounded.add
         GF25519Bounded.mul
         a
         d
      ).

Local Existing Instance GF25519.homomorphism_F25519_encode.
Local Existing Instance GF25519.homomorphism_F25519_decode.
(* MOVE : mostly pre-Specific. TODO : narrow down which properties can
be proven generically and which need to be computed, then maybe create
a tactic to do the computed ones *)


Definition ZNWord sz x := Word.NToWord sz (BinInt.Z.to_N x).
Definition WordNZ {sz} (w : Word.word sz) := BinInt.Z.of_N (Word.wordToN w).

Definition SRep := SC25519.SRep.
Definition S2Rep := SC25519.S2Rep.

Lemma eq_a_minus1 : GF25519BoundedCommon.eq a (GF25519Bounded.opp GF25519BoundedCommon.one).
Proof. vm_decide. Qed.

Local Coercion Z.of_nat : nat >-> Z.
Definition ERepSel : bool -> Erep -> Erep -> Erep := fun b x y => if b then y else x.

(* TODO : figure out if and where to move this *)
Lemma nth_default_freeze_input_bound_compat : forall i,
  (nth_default 0 PseudoMersenneBaseParams.limb_widths i <
   GF25519.freeze_input_bound)%Z.
Proof.
  pose proof GF25519.freezePreconditions25519.
  intros.
  destruct (lt_dec i (length PseudoMersenneBaseParams.limb_widths)).
  { apply ModularBaseSystemProofs.B_compat.
    rewrite nth_default_eq.
    auto using nth_In. }
  { rewrite nth_default_out_of_bounds by omega.
    cbv; congruence. }
Qed.

(* TODO : This is directly implied by other lemmas and should be
easier. I'd say automate it, but given that the basesystem stuff is in
flux maybe we should leave it for now and then do a complete rewrite
later. *)
Lemma minrep_freeze : forall x,
            Pow2Base.bounded
              PseudoMersenneBaseParams.limb_widths
              (Tuple.to_list
                 (length
                    PseudoMersenneBaseParams.limb_widths)
                 (ModularBaseSystem.freeze
                    GF25519.int_width
                    (ModularBaseSystem.encode x))) /\
            ModularBaseSystemList.ge_modulus
              (Tuple.to_list
                 (length
                    PseudoMersenneBaseParams.limb_widths)
                 (ModularBaseSystem.freeze
                    GF25519.int_width
                    (ModularBaseSystem.encode x))) =
            0%Z.
Proof.
    pose proof GF25519.freezePreconditions25519.
    intros.
    match goal with
      |- appcontext [ModularBaseSystem.freeze _ ?x] =>
      pose proof (ModularBaseSystemProofs.minimal_rep_freeze x) as Hminrep end.
    match type of Hminrep with ?P -> _ => assert P end.
    { intros i ?.
      let A := fresh "H" in
      pose proof (ModularBaseSystemProofs.bounded_encode x) as A;
          rewrite Pow2BaseProofs.bounded_iff in A; specialize (A i).
      split; [ omega | ].
      eapply Z.lt_le_trans; [ solve [intuition eauto] | ].
      match goal with |- appcontext [if ?a then _ else _] => destruct a end.
      { apply Z.pow_le_mono_r; try omega.
        apply Z.lt_le_incl.
        apply nth_default_freeze_input_bound_compat. }
      { transitivity (2 ^ (Z.pred GF25519.freeze_input_bound))%Z.
          { apply Z.pow_le_mono; try omega.
            apply Z.lt_le_pred.
            apply nth_default_freeze_input_bound_compat. }
          { rewrite Z.shiftr_div_pow2 by (auto using Pow2BaseProofs.nth_default_limb_widths_nonneg, PseudoMersenneBaseParamProofs.limb_widths_nonneg).
          rewrite <- Z.pow_sub_r by (try omega; split; auto using Pow2BaseProofs.nth_default_limb_widths_nonneg, PseudoMersenneBaseParamProofs.limb_widths_nonneg, Z.lt_le_incl, nth_default_freeze_input_bound_compat).
          replace (2 ^ GF25519.freeze_input_bound)%Z
            with (2 ^ (Z.pred GF25519.freeze_input_bound + 1))%Z
            by (f_equal; omega).
          rewrite Z.pow_add_r by (omega || (cbv; congruence)).
          rewrite <-Zplus_diag_eq_mult_2.
          match goal with |- (?a <= ?a + ?b - ?c)%Z =>
                          assert (c <= b)%Z; [ | omega ] end.
          apply Z.pow_le_mono; try omega.
          rewrite <-Z.sub_1_r.
          apply Z.sub_le_mono_l.
          replace 1%Z with (Z.succ 0) by reflexivity.
          rewrite Z.le_succ_l.
          apply PseudoMersenneBaseParams.limb_widths_pos.
          rewrite nth_default_eq; apply nth_In.
          omega. } } }
    { apply Hminrep. assumption. }
Qed.

Lemma convert_freezes: forall x,
  (ModularBaseSystemList.freeze GF25519.int_width
       (Tuple.to_list
          (length PseudoMersenneBaseParams.limb_widths) x)) =
              (Tuple.to_list
                 (length
                    PseudoMersenneBaseParams.limb_widths)
                 (ModularBaseSystem.freeze
                    GF25519.int_width x)).
Proof.
  cbv [ModularBaseSystem.freeze].
  intros.
  rewrite Tuple.to_list_from_list.
  reflexivity.
Qed.
Ltac to_MBSfreeze H :=
  rewrite GF25519.freeze_correct in H;
  rewrite ModularBaseSystemOpt.freeze_opt_correct in H
    by (rewrite ?Tuple.length_to_list; reflexivity);
  erewrite convert_freezes,  Tuple.from_list_default_eq, Tuple.from_list_to_list in H.

Lemma bounded_freeze : forall x,
  Pow2Base.bounded
         PseudoMersenneBaseParams.limb_widths
         (ModularBaseSystemList.freeze
            GF25519.int_width
            (Tuple.to_list
               (length
                  PseudoMersenneBaseParams.limb_widths)
               (ModularBaseSystem.encode x))).
Proof.
  intro.
  rewrite convert_freezes.
  pose proof (minrep_freeze x).
  intuition assumption.
Qed.

Lemma ge_modulus_freeze : forall x,
  ModularBaseSystemList.ge_modulus
         (ModularBaseSystemList.freeze
            GF25519.int_width
            (Tuple.to_list
               (length
                  PseudoMersenneBaseParams.limb_widths)
               (ModularBaseSystem.encode x))) = 0%Z.
Proof.
  intro.
  rewrite convert_freezes.
  pose proof (minrep_freeze x).
  intuition assumption.
Qed.


(* TODO : automate *)
Lemma initial_bounds : forall x n,
  n < length PseudoMersenneBaseParams.limb_widths ->
  (0 <=
   nth_default 0
     (Tuple.to_list (length PseudoMersenneBaseParams.limb_widths)
        (GF25519BoundedCommon.proj1_fe25519 x)) n <
   2 ^ GF25519.freeze_input_bound -
   (if eq_nat_dec n 0%nat
    then 0
    else
     Z.shiftr (2 ^ GF25519.freeze_input_bound)
       (nth_default 0 PseudoMersenneBaseParams.limb_widths
                    (pred n))))%Z.
Proof.
  intros.
  cbv [GF25519BoundedCommon.fe25519] in *.
  repeat match goal with p : (_ * _)%type |- _ => destruct p end.
  cbv [GF25519BoundedCommon.proj1_fe25519].
  cbv [GF25519BoundedCommon.fe25519WToZ
         GF25519BoundedCommon.proj1_fe25519W
         PseudoMersenneBaseParams.limb_widths
         GF25519.params25519 length
         Tuple.to_list Tuple.to_list' nth_default] in *.
  repeat match goal with
         | [ |- appcontext[nth_error _ ?n] ]
           => is_var n; destruct n; simpl @nth_error; cbv beta iota
         end;
    simpl in *; unfold Z.pow_pos; simpl; try omega;
      match goal with
        |- appcontext [GF25519BoundedCommon.proj_word ?b] =>
        let A := fresh "H" in
        pose proof (@GF25519BoundedCommon.word_bounded _ _ b) as A;
          rewrite Bool.andb_true_iff in A; destruct A end;
      rewrite !Z.leb_le in *;
      omega.
Qed.


(* MOVE : pre-Specific *)
Lemma Proper_pack :
  Proper (Tuple.fieldwise (n := length PseudoMersenneBaseParams.limb_widths) eq ==>
                          Tuple.fieldwise (n := length GF25519.wire_widths) eq) GF25519.pack.
Proof.
  repeat intro.
  cbv [PseudoMersenneBaseParams.limb_widths GF25519.params25519 length] in *.
  cbv [Tuple.tuple] in *.
  repeat match goal with
         | p : Tuple.tuple' Z (S ?n) |- _ => destruct p
         | p : Tuple.tuple' Z 0 |- _ => cbv [Tuple.tuple'] in p
         end.
  cbv [GF25519.pack].
  cbv [GF25519.wire_widths length Tuple.fieldwise Tuple.fieldwise' fst snd] in *;
    intuition subst; reflexivity.
Qed.

Definition SRepEnc : SRep -> Word.word b := (fun x => Word.NToWord _ (Z.to_N x)).

Lemma SRepEnc_correct : forall x : ModularArithmetic.F.F l, Senc x = SRepEnc (S2Rep x).
  unfold SRepEnc, Senc, Fencode; intros; f_equal.
Qed.

Definition Fsqrt_minus1 := Eval vm_compute in ModularBaseSystem.decode (GF25519.sqrt_m1).
Definition Fsqrt := PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1.

(* MOVE : maybe make a Pre file for these bound_check things? *)
Lemma bound_check_255_helper x y : (0 <= x)%Z -> (BinInt.Z.to_nat x < 2^y <-> (x < 2^(Z.of_nat y))%Z).
Proof.
  intros.
  rewrite <-(Znat.Nat2Z.id 2) at 1.
  rewrite ZUtil.Z.pow_Z2N_Zpow by omega.
  rewrite <- Znat.Z2Nat.inj_lt by auto with zarith.
  reflexivity.
Qed.

(* MOVE : pre-Specific (general SC files?) *)
Definition Sdec : Word.word b -> option (ModularArithmetic.F.F l) :=
 fun w =>
 let z := (BinIntDef.Z.of_N (Word.wordToN w)) in
 if ZArith_dec.Z_lt_dec z (Z.pos l)
 then Some (ModularArithmetic.F.of_Z l z) else None.

(* MOVE: same place as Sdec *)
Lemma eq_enc_S_iff : forall (n_ : Word.word b) (n : ModularArithmetic.F.F l),
 Senc n = n_ <-> Sdec n_ = Some n.
Proof.
  assert (0 < Z.pos Ed25519.l)%Z as l_pos by (cbv; congruence).
  intros.
  pose proof (ModularArithmeticTheorems.F.to_Z_range n l_pos).
  unfold Senc, Fencode, Sdec; intros;
    split; break_match; intros; inversion_option; subst; f_equal;
  repeat match goal with
         | |- _ => rewrite !WordUtil.wordToN_NToWord_idempotent in *
             by (apply N.ZToN_NPow2_lt; split; try omega; eapply Z.lt_le_trans;
                 [ intuition eassumption | ]; cbv; congruence)
         | |- _ => rewrite WordUtil.NToWord_wordToN
         | |- _ => rewrite Z2N.id in * by omega
         | |- _ => rewrite N2Z.id in * by omega
         | |- _ => rewrite Z.mod_small by (split; try omega; apply N2Z.is_nonneg)
         | |- _ => rewrite ModularArithmeticTheorems.F.of_Z_to_Z in *
         | |- _ => rewrite @ModularArithmeticTheorems.F.to_Z_of_Z in *
         | |- _ => reflexivity
         | |- _ => omega
         end.
Qed.

(* MOVE : same place as Sdec *)
Definition SRepDec : Word.word b -> option SRep := fun w => option_map ModularArithmetic.F.to_Z (Sdec w).

(* MOVE : same place as Sdec *)
Lemma SRepDec_correct : forall w : Word.word b,
 @Option.option_eq SRep SC25519.SRepEq
   (@option_map (ModularArithmetic.F.F l) SRep S2Rep (Sdec w))
   (SRepDec w).
Proof.
  unfold SRepDec, S2Rep, SC25519.S2Rep; intros; reflexivity.
Qed.

Lemma Fsqrt_minus1_correct :
 ModularArithmetic.F.mul Fsqrt_minus1 Fsqrt_minus1 =
 ModularArithmetic.F.opp
   (ModularArithmetic.F.of_Z GF25519.modulus 1).
Proof.
  replace (Fsqrt_minus1) with (ModularBaseSystem.decode (GF25519.sqrt_m1)) by reflexivity.
  rewrite <-ModularBaseSystemProofs.carry_mul_rep by reflexivity.
  rewrite <-ModularBaseSystemOpt.carry_mul_opt_correct
    with (k_ := GF25519.k_) (c_ := GF25519.c_) by reflexivity.
  rewrite <-GF25519.mul_correct.
  apply GF25519.sqrt_m1_correct.
Qed.

Section bounded_by_from_is_bounded.
  Local Arguments Z.sub !_ !_.
  Local Arguments Z.pow_pos !_ !_ / .
  (* TODO : automate?*)
  Lemma bounded_by_from_is_bounded
    : forall x, GF25519BoundedCommon.is_bounded x = true
                -> ModularBaseSystemProofs.bounded_by
                     x
                     (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.freeze_input_bound)).
  Proof.
    intros x H.
    pose proof (GF25519BoundedCommon.is_bounded_to_nth_default _ H) as H'; clear H.
    unfold ModularBaseSystemProofs.bounded_by.
    intros n pf; specialize (H' n pf).
    match goal with
    | [ H : (0 <= ?y <= _)%Z |- (0 <= ?x < _)%Z ]
      => change y with x in H; generalize dependent x
    end.
    intros ? H'.
    split; [ omega | ].
    eapply Z.le_lt_trans; [ exact (proj2 H') | ].
    unfold ModularBaseSystemProofs.freeze_input_bounds, nth_default, GF25519.freeze_input_bound; simpl in *.
    repeat match goal with
           | [ |- context[nth_error _ ?n] ]
             => is_var n; destruct n; simpl
           end;
      try (vm_compute; reflexivity);
      try omega.
  Qed.
End bounded_by_from_is_bounded.

Lemma bounded_by_encode_freeze : forall x,
  ModularBaseSystemProofs.bounded_by
    (ModularBaseSystem.encode x)
    (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.freeze_input_bound)).
Proof.
  intros; apply bounded_by_from_is_bounded, GF25519BoundedCommon.encode_bounded.
Qed.

Lemma bounded_by_freeze : forall x,
  ModularBaseSystemProofs.bounded_by
    (GF25519BoundedCommon.fe25519WToZ (GF25519BoundedCommon.proj1_fe25519W x))
    (ModularBaseSystemProofs.freeze_input_bounds (B := GF25519.freeze_input_bound)).
Proof.
  intros; apply bounded_by_from_is_bounded, GF25519BoundedCommon.is_bounded_proj1_fe25519.
Qed.

Local Ltac prove_bounded_by :=
  repeat match goal with
         | [ |- ModularBaseSystemProofs.bounded_by _ _ ]
           => apply bounded_by_from_is_bounded
         | [ |- GF25519BoundedCommon.is_bounded
                  (GF25519BoundedCommon.fe25519WToZ
                     (GF25519Bounded.mulW (_, _))) = true ]
           => apply GF25519Bounded.mulW_correct_and_bounded
         | [ |- GF25519BoundedCommon.is_bounded
                  (GF25519BoundedCommon.fe25519WToZ
                     (GF25519Bounded.mulW_noinline (_, _))) = true ]
           => apply GF25519Bounded.mulW_correct_and_bounded
         | [ |- GF25519BoundedCommon.is_bounded
                  (GF25519BoundedCommon.fe25519WToZ
                     (GF25519Bounded.powW _ _)) = true ]
           => apply GF25519Bounded.powW_correct_and_bounded
         | [ |- context[GF25519BoundedCommon.fe25519WToZ (GF25519BoundedCommon.fe25519ZToW _)] ]
           => rewrite GF25519BoundedCommon.fe25519WToZ_ZToW
         | [ |- GF25519BoundedCommon.is_bounded (ModularBaseSystem.encode _) = true ]
           => apply GF25519BoundedCommon.encode_bounded
         end.

(* TODO : automate, make intermediate lemmas? This seems like it should not be so much pain *)
Lemma sqrt_correct' : forall x,
        GF25519BoundedCommon.eq
          (GF25519BoundedCommon.encode
             (PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1 (GF25519BoundedCommon.decode x)))
          (GF25519Bounded.sqrt x).
Proof.
  intros.
  cbv [GF25519BoundedCommon.eq].
  rewrite GF25519Bounded.sqrt_correct.
  cbv [GF25519Bounded.GF25519sqrt].
  cbv [LetIn.Let_In].
  repeat match goal with (* needed on Coq 8.4, should be the only default everywhere *)
           |- context[GF25519BoundedCommon.proj1_fe25519 (GF25519BoundedCommon.encode ?x)] =>
           rewrite (GF25519BoundedCommon.proj1_fe25519_encode x)
         end.
  rewrite GF25519.sqrt_correct, ModularBaseSystemOpt.sqrt_5mod8_opt_correct by reflexivity.
  cbv [ModularBaseSystem.eq].
  rewrite ModularBaseSystemProofs.encode_rep.
  symmetry.
  eapply @ModularBaseSystemProofs.sqrt_5mod8_correct;
    eauto using GF25519.freezePreconditions25519, ModularBaseSystemProofs.encode_rep, bounded_by_freeze, bounded_by_encode_freeze; prove_bounded_by; eauto using GF25519BoundedCommon.is_bounded_proj1_fe25519;
      cbv [HList.hlistP HList.hlistP'] in *;
      repeat apply conj;
      [ reflexivity |
        try lazymatch goal with
    | |- appcontext[GF25519Bounded.powW ?a ?ch] =>
      let A := fresh "H" in
      destruct (GF25519Bounded.powW_correct_and_bounded ch a) as [A ?];
      [ rewrite GF25519BoundedCommon.fe25519WToZ_ZToW;
        hnf;
          solve [eauto using GF25519BoundedCommon.is_bounded_proj1_fe25519]
        | cbv [Tuple.map List.map Tuple.on_tuple Tuple.from_list' Tuple.from_list Tuple.to_list Tuple.to_list'] in *;
          rewrite A;
          rewrite GF25519.pow_correct, ModularBaseSystemOpt.pow_opt_correct
            by reflexivity]
      end..].
  (*{ lazymatch goal with
    | |- appcontext[GF25519Bounded.powW ?a ?ch] =>
      let A := fresh "H" in
      destruct (GF25519Bounded.powW_correct_and_bounded ch a) as [A ?];
        [ rewrite GF25519BoundedCommon.fe25519WToZ_ZToW;
          hnf;
          solve [eauto using GF25519BoundedCommon.is_bounded_proj1_fe25519]
        | cbv [Tuple.map List.map Tuple.on_tuple Tuple.from_list' Tuple.from_list Tuple.to_list Tuple.to_list'] in *;
          move A at bottom;
          rewrite A, !GF25519.pow_correct
            by reflexivity(*
          rewrite GF25519.pow_correct, ModularBaseSystemOpt.pow_opt_correct
            by reflexivity*)]
    end.
    About GF25519.pow_correct.

    cbv [GF25519BoundedCommon.is_bounded fst snd GF25519BoundedCommon.is_bounded_gen].

    cbv [Tuple.map2 Tuple.on_tuple2 Tuple.to_list GF25519.length_fe25519 Tuple.to_list' map2 GF25519BoundedCommon.bounds].
    rewrite ModularBaseSystemOpt.pow_opt_correct.
    rewrite GF25519.pow_correct.
    rewrite H.
    .
    SearchAbout GF25519Bounded.mulW.
    Set Printing Coercions.
    rewrite H.

    [ rewrite GF25519BoundedCommon.fe25519WToZ_ZToW by (eapply GF25519BoundedCommon.is_bounded_proj1_fe25519); reflexivity | ].
  unfold GF25519Bounded.mulW_noinline.
  match goal with
  | |- appcontext[GF25519Bounded.mulW ?a ?b] =>
    let A := fresh "H" in
    destruct (GF25519Bounded.mulW_correct_and_bounded a b) as [A ?];
      [ auto | auto | rewrite A]
  end.
  rewrite GF25519.mul_correct, ModularBaseSystemOpt.carry_mul_opt_correct by reflexivity.
  rewrite !H.
  rewrite GF25519.pow_correct.
  cbv [ModularBaseSystem.eq].
  rewrite ModularBaseSystemProofs.carry_mul_rep by reflexivity.
  rewrite ModularBaseSystemProofs.mul_rep by reflexivity.
  apply f_equal2;
  rewrite ModularBaseSystemOpt.pow_opt_correct; reflexivity.*)
Admitted.

(* TODO : move to GF25519BoundedCommon *)
Module GF25519BoundedCommon.
  Lemma decode_encode x: GF25519BoundedCommon.decode (GF25519BoundedCommon.encode x) = x.
  Proof.
    unfold GF25519BoundedCommon.encode, GF25519BoundedCommon.decode.
    rewrite GF25519BoundedCommon.proj1_fe25519_exist_fe25519.
    erewrite ModularBaseSystemProofs.rep_decode; eauto using ModularBaseSystemProofs.encode_rep.
  Qed.
End GF25519BoundedCommon.

Lemma sqrt_correct : forall x : ModularArithmetic.F.F q,
        GF25519BoundedCommon.eq
          (GF25519BoundedCommon.encode
             (PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1 x))
          (GF25519Bounded.sqrt (GF25519BoundedCommon.encode x)).
Proof.
  intros. pose proof sqrt_correct' (GF25519BoundedCommon.encode x) as H.
  rewrite GF25519BoundedCommon.decode_encode in H; exact H.
Qed.

Local Instance Proper_sqrt :
  Proper (GF25519BoundedCommon.eq ==> GF25519BoundedCommon.eq) GF25519Bounded.sqrt.
Proof.
  intros x y Hxy.
  rewrite <-(sqrt_correct' x); symmetry; rewrite <-(sqrt_correct' y); symmetry.
  eapply f_equal. eapply f_equal. eapply f_equal. rewrite Hxy. reflexivity.
Qed.

Lemma Fhomom_inv_zero :
  GF25519BoundedCommon.eq
    (GF25519BoundedCommon.encode
       (@ModularArithmetic.F.inv GF25519.modulus
                                 (ModularArithmetic.F.of_Z GF25519.modulus 0)))
    (GF25519Bounded.inv GF25519BoundedCommon.zero).
Proof.
  vm_decide_no_check.
Qed.

Import ModularArithmetic.
Module Spec.
  Module X25519.
    Definition a : F q := F.of_Z _ 486662.
    Definition a24 : F q := ((a - F.of_Z _ 2) / F.of_Z _ 4)%F.
  End X25519.
End Spec.

Section X25519Constants.
  Import GF25519BoundedCommon.
  Definition a24' : GF25519BoundedCommon.fe25519 :=
    Eval vm_compute in GF25519BoundedCommon.encode Spec.X25519.a24.
  Definition a24 : GF25519BoundedCommon.fe25519 :=
    Eval cbv [a24' GF25519BoundedCommon.fe25519_word64ize GF25519BoundedCommon.word64ize andb GF25519BoundedCommon.opt.word64ToZ GF25519BoundedCommon.opt.word64ize GF25519BoundedCommon.opt.Zleb Z.compare CompOpp Pos.compare Pos.compare_cont] in (GF25519BoundedCommon.fe25519_word64ize a24').
  Lemma a24_correct : GF25519BoundedCommon.eq
                        (GF25519BoundedCommon.encode Spec.X25519.a24)
                        (a24).
  Proof. vm_decide_no_check. Qed.
End X25519Constants.

Definition x25519 (n:N) (x:GF25519BoundedCommon.fe25519) : GF25519BoundedCommon.fe25519 :=
  @MxDH.montladder GF25519BoundedCommon.fe25519 GF25519BoundedCommon.zero
                   GF25519BoundedCommon.one GF25519Bounded.add GF25519Bounded.sub
                   GF25519Bounded.mul GF25519Bounded.inv a24
                   (fun (H : bool)
                        (H0
                           H1 : GF25519BoundedCommon.fe25519 * GF25519BoundedCommon.fe25519)
                    => if H then (H1, H0) else (H0, H1)) 255 (N.testbit_nat n) x.

Definition x25519_correct' n x :
  GF25519BoundedCommon.eq
    (GF25519BoundedCommon.encode (MxDH.montladder 255 (N.testbit_nat n) x))
    (MxDH.montladder 255 (N.testbit_nat n) (GF25519BoundedCommon.encode x)) :=
  MxDHRepChange
      (field:=PrimeFieldTheorems.F.field_modulo GF25519.modulus)
      (impl_field:=GF25519Bounded.field25519)
      (homomorphism_inv_zero:=Fhomom_inv_zero)
      (homomorphism_a24:=a24_correct)
      (Fcswap_correct:= fun _ _ _ => (reflexivity _))
      (Kcswap_correct:= fun _ _ _ => (reflexivity _))
      (tb2_correct:=fun _ => (reflexivity _))
      255 _.

(* [B_order_l] is proven above in this file, just replace Admitted with Qed, start the build and wait for a couple of hours *)
(* [prime_q] and [prime_l] have been proven in Coq exactly as stated here, see <https://github.com/andres-erbsen/safecurves-primes> for the (lengthy) proofs *)
(* [SHA512] is outside the scope of this project, but its type is satisfied by [(fun n bits => Word.wzero 512)] *)
Definition __check_SHA512_type := [(fun n bits => Word.wzero 512); SHA512].

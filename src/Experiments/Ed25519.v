Require Import Crypto.EdDSARepChange.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Util.Decidable.
Require Crypto.Specific.GF25519.
Require Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Crypto.Encoding.PointEncoding.
Import Morphisms.

Context {H: forall n : nat, Word.word n -> Word.word (b + b)}.
(* TODO : define feSign *)
Context {feSign : GF25519.fe25519 -> bool}.
Context {feSign_correct : forall x,
            PointEncoding.sign x = feSign (ModularBaseSystem.encode x)}.
Context {Proper_feSign :  Proper (ModularBaseSystem.eq ==> eq) feSign}.

Definition a : GF25519.fe25519 :=
  Eval vm_compute in ModularBaseSystem.encode a.
Definition d : GF25519.fe25519 :=
  Eval vm_compute in ModularBaseSystem.encode d.
Definition twice_d : GF25519.fe25519 :=
  Eval vm_compute in (GF25519.add d d).

Lemma phi_a : ModularBaseSystem.eq (ModularBaseSystem.encode Ed25519.a) a.
Proof. reflexivity. Qed.
Lemma phi_d : ModularBaseSystem.eq (ModularBaseSystem.encode Ed25519.d) d.
Proof. vm_decide_no_check. Qed.

Let Erep := (@ExtendedCoordinates.Extended.point
         GF25519.fe25519
         ModularBaseSystem.eq
         GF25519.zero_
         GF25519.one_
         GF25519.add
         GF25519.mul
         ModularBaseSystem.div
         a
         d
      ).

(* TODO : prove -- use Ed25519.curve25519_params_ok *)
Lemma twedprm_ERep :
  @CompleteEdwardsCurve.E.twisted_edwards_params
   GF25519.fe25519 ModularBaseSystem.eq
   GF25519.zero_ GF25519.one_
   GF25519.add GF25519.mul a d.
Proof.
Admitted.

Definition coord_to_extended (xy : GF25519.fe25519 * GF25519.fe25519) pf :=
  ExtendedCoordinates.Extended.from_twisted
    (field := GF25519.field25519) (prm :=twedprm_ERep)
    (exist Pre.onCurve xy pf).

Definition extended_to_coord (P : Erep) : (GF25519.fe25519 * GF25519.fe25519) :=
  CompleteEdwardsCurve.E.coordinates (ExtendedCoordinates.Extended.to_twisted P).

Lemma encode_eq_iff :  forall x y : ModularArithmetic.F.F GF25519.modulus,
                    ModularBaseSystem.eq
                      (ModularBaseSystem.encode x)
                      (ModularBaseSystem.encode y) <->  x = y.
Proof.
  intros.
  cbv [ModularBaseSystem.eq].
  rewrite !ModularBaseSystemProofs.encode_rep.
  reflexivity.
Qed.

Let EToRep := PointEncoding.point_phi
      (Kfield := GF25519.field25519)
      (phi_homomorphism := GF25519.homomorphism_F25519)
      (Kpoint := Erep)
      (phi_a := phi_a)
      (phi_d := phi_d)
      (Kcoord_to_point := coord_to_extended)
      (phi_bijective := encode_eq_iff)
.

Let ZNWord sz x := Word.NToWord sz (BinInt.Z.to_N x).
Let WordNZ {sz} (w : Word.word sz) := BinInt.Z.of_N (Word.wordToN w).

(* TODO : 
   GF25519.pack does most of the work here, but the spec currently talks
   about 256-bit words and [pack] makes a sequence of short (in this case
   32- and 31-bit) Zs. We should either automate this transformation or change
   the spec.
 *)
Definition feEnc (x : GF25519.fe25519) : Word.word 255 := 
  let '(x0, x1, x2, x3, x4, x5, x6, x7) :=
      (GF25519.pack x) in
  Word.combine (ZNWord 32 x0)
    (Word.combine (ZNWord 32 x1)
      (Word.combine (ZNWord 32 x2)
        (Word.combine (ZNWord 32 x3)
          (Word.combine (ZNWord 32 x4)
            (Word.combine (ZNWord 32 x5)
              (Word.combine (ZNWord 32 x6) (ZNWord 31 x7))))))).

Definition feDec (w : Word.word 255) : option GF25519.fe25519 :=
  let w0 := Word.split1 32 _ w in
  let a0 := Word.split2 32 _ w in
  let w1 := Word.split1 32 _ a0 in
  let a1 := Word.split2 32 _ a0 in
  let w2 := Word.split1 32 _ a1 in
  let a2 := Word.split2 32 _ a1 in
  let w3 := Word.split1 32 _ a2 in
  let a3 := Word.split2 32 _ a2 in
  let w4 := Word.split1 32 _ a3 in
  let a4 := Word.split2 32 _ a3 in
  let w5 := Word.split1 32 _ a4 in
  let a5 := Word.split2 32 _ a4 in
  let w6 := Word.split1 32 _ a5 in
  let w7 := Word.split2 32 _ a5 in
  let result := (GF25519.unpack (WordNZ w0, WordNZ w1, WordNZ w2, WordNZ w3, WordNZ w4, WordNZ w5, WordNZ w6, WordNZ w7)) in
  if GF25519.ge_modulus result
  then None else (Some result).

Let ERepEnc :=
  (PointEncoding.Kencode_point
         (Ksign := feSign)
         (Kenc := feEnc)
         (Kpoint := Erep)
         (Kpoint_to_coord :=  fun P => CompleteEdwardsCurve.E.coordinates
                                (ExtendedCoordinates.Extended.to_twisted P))
  ).

Let S2Rep := fun (x : ModularArithmetic.F.F l) =>
               Tuple.map (ZNWord 32)
               (Tuple.from_list_default (BinInt.Z.of_nat 0) 8
                  (Pow2Base.encodeZ
                  (List.repeat (BinInt.Z.of_nat 32) 8)
                  (ModularArithmetic.F.to_Z x))).

Lemma eq_a_minus1 : ModularBaseSystem.eq a (GF25519.opp GF25519.one_).
Proof.
  etransitivity; [ symmetry; apply phi_a | ].
  cbv [ModularBaseSystem.eq].
  rewrite GF25519.opp_correct.
  rewrite ModularBaseSystemOpt.opp_opt_correct.
  rewrite ModularBaseSystemProofs.opp_rep with (x := ModularArithmetic.F.one) by reflexivity.
  apply ModularBaseSystemProofs.encode_rep.
Qed.

About ExtendedCoordinates.Extended.add.
Let ErepAdd :=
  (@ExtendedCoordinates.Extended.add _ _ _ _ _ _ _ _ _ _
                                     a d GF25519.field25519 twedprm_ERep _
                                     eq_a_minus1 twice_d (eq_refl _) ).

(* TODO : unclear what we're doing with the placeholder [feEnc] at the moment, so
   leaving this admitted for now *)
Lemma feEnc_correct : forall x,
    PointEncoding.Fencode x = feEnc (ModularBaseSystem.encode x).
Admitted.

(* TODO : unclear what we're doing with the placeholder [feEnc] at the moment, so
   leaving this admitted for now *)
Lemma Proper_feEnc : Proper (ModularBaseSystem.eq ==> eq) feEnc.
Admitted.

Lemma ext_to_coord_coord_to_ext : forall (P : GF25519.fe25519 * GF25519.fe25519)
                                         (pf : Pre.onCurve P),
               Tuple.fieldwise (n := 2)
                 ModularBaseSystem.eq
                 (extended_to_coord (coord_to_extended P pf))
                 P.
Proof.
  cbv [extended_to_coord coord_to_extended].
  intros.
  transitivity (CompleteEdwardsCurve.E.coordinates (exist _ P pf));
    [ | reflexivity].
  apply (CompleteEdwardsCurveTheorems.E.Proper_coordinates
           (field := GF25519.field25519) (a := a) (d := d)).
  apply ExtendedCoordinates.Extended.to_twisted_from_twisted.
Qed.

Lemma ERepEnc_correct P : Eenc P = ERepEnc (EToRep P).
Proof.
  cbv [Eenc ERepEnc EToRep sign Fencode].
  transitivity (PointEncoding.encode_point (b := 255) P);
    [ | apply (PointEncoding.Kencode_point_correct
           (Ksign_correct := feSign_correct)
           (Kenc_correct := feEnc_correct)
           (Kp2c_c2p := ext_to_coord_coord_to_ext)
           (Proper_Ksign := Proper_feSign)
           (Proper_Kenc := Proper_feEnc))
    ].
  reflexivity.
Qed.

Lemma ext_eq_correct : forall p q : Erep,
  ExtendedCoordinates.Extended.eq p q <->
  Tuple.fieldwise (n := 2) ModularBaseSystem.eq (extended_to_coord p) (extended_to_coord q).
Proof.
  cbv [extended_to_coord]; intros.
  cbv [ExtendedCoordinates.Extended.eq].
  match goal with |- _ <-> Tuple.fieldwise _
                                           (CompleteEdwardsCurve.E.coordinates ?x)
                                           (CompleteEdwardsCurve.E.coordinates ?y) =>
                  pose proof (CompleteEdwardsCurveTheorems.E.Proper_coordinates
                                (field := GF25519.field25519) (a := a) (d := d) x y)
  end.
  tauto.
Qed.

Check @sign_correct
      (* E := *) E
      (* Eeq := *) CompleteEdwardsCurveTheorems.E.eq
      (* Eadd := *) CompleteEdwardsCurve.E.add
      (* Ezero := *) CompleteEdwardsCurve.E.zero
      (* Eopp := *) CompleteEdwardsCurveTheorems.E.opp
      (* EscalarMult := *) CompleteEdwardsCurve.E.mul
      (* b := *) b
      (* H := *) H
      (* c := *) c
      (* n := *) n
      (* l := *) l
      (* B := *) B
      (* Eenc := *) Eenc
      (* Senc := *) Senc
      (* prm := *) ed25519
      (* Erep := *) Erep
      (* ErepEq := *) ExtendedCoordinates.Extended.eq
      (* ErepAdd := *) ErepAdd
      (* ErepId := *) ExtendedCoordinates.Extended.zero
      (* ErepOpp := *) ExtendedCoordinates.Extended.opp
      (* Agroup := *) ExtendedCoordinates.Extended.extended_group
      (* EToRep := *) EToRep
      (* ERepEnc := *) ERepEnc
      (* ERepEnc_correct := *) ERepEnc_correct
      (* Proper_ERepEnc := *) (PointEncoding.Proper_Kencode_point (Kpoint_eq_correct := ext_eq_correct) (Proper_Kenc := Proper_feEnc))
      (* SRep := *) (Tuple.tuple (Word.word 32) 8)
      (* SRepEq := *) (Tuple.fieldwise Logic.eq)
      (* H0 := *) Tuple.Equivalence_fieldwise
      (* S2Rep := *) S2Rep
      (* SRepDecModL := *) _
      (* SRepDecModL_correct := *) _
      (* SRepERepMul := *) _
      (* SRepERepMul_correct := *) _
      (* Proper_SRepERepMul := *) _
      (* SRepEnc := *) _
      (* SRepEnc_correct := *) _
      (* Proper_SRepEnc := *) _
      (* SRepAdd := *) _
      (* SRepAdd_correct := *) _
      (* Proper_SRepAdd := *) _
      (* SRepMul := *) _
      (* SRepMul_correct := *) _
      (* Proper_SRepMul := *) _
      (* ErepB := *) (EToRep B)
      (* ErepB_correct := *) _
      (* SRepDecModLShort := *) _
      (* SRepDecModLShort_correct := *) _
.

Definition Fsqrt_minus1 := Eval vm_compute in ModularBaseSystem.decode (GF25519.sqrt_m1).
Definition Fsqrt := PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1.
Lemma bound_check255 : BinInt.Z.to_nat GF25519.modulus < PeanoNat.Nat.pow 2 255.
Proof.
  cbv [GF25519.modulus].
  rewrite <-(Znat.Nat2Z.id 2) at 1.
  rewrite ZUtil.Z.pow_Z2N_Zpow by Omega.omega.
  apply Znat.Z2Nat.inj_lt; cbv; congruence.
Qed.

Lemma bound_check256 : BinInt.Z.to_nat GF25519.modulus < PeanoNat.Nat.pow 2 256.
Proof.
  cbv [GF25519.modulus].
  rewrite <-(Znat.Nat2Z.id 2) at 1.
  rewrite ZUtil.Z.pow_Z2N_Zpow by Omega.omega.
  apply Znat.Z2Nat.inj_lt; cbv; congruence.
Qed.

Let Edec := (@PointEncodingPre.point_dec
               _ eq
               ModularArithmetic.F.zero
               ModularArithmetic.F.one
               ModularArithmetic.F.opp
               ModularArithmetic.F.add
               ModularArithmetic.F.sub
               ModularArithmetic.F.mul
               ModularArithmetic.F.div
               _
               Ed25519.a
               Ed25519.d
               _
               Fsqrt
               (PointEncoding.Fencoding (bound_check := bound_check255))
               sign).

Let Sdec : Word.word b -> option (ModularArithmetic.F.F l) :=
 fun w =>
 let z := (BinIntDef.Z.of_N (Word.wordToN w)) in
 if ZArith_dec.Z_lt_dec z l
 then Some (ModularArithmetic.F.of_Z l z) else None.

Let ERepDec :=
    (@PointEncoding.Kdecode_point
         _
         GF25519.fe25519
         ModularBaseSystem.eq
         GF25519.zero_
         GF25519.one_
         GF25519.opp
         GF25519.add
         GF25519.sub
         GF25519.mul
         ModularBaseSystem.div
         _ a d feSign
         _ coord_to_extended
         feDec GF25519.sqrt
       ).

Check verify_correct.
Check @verify_correct
      (* E := *) E
      (* Eeq := *) CompleteEdwardsCurveTheorems.E.eq
      (* Eadd := *) CompleteEdwardsCurve.E.add
      (* Ezero := *) CompleteEdwardsCurve.E.zero
      (* Eopp := *) CompleteEdwardsCurveTheorems.E.opp
      (* EscalarMult := *) CompleteEdwardsCurve.E.mul
      (* b := *) b
      (* H := *) H
      (* c := *) c
      (* n := *) n
      (* l := *) l
      (* B := *) B
      (* Eenc := *) Eenc
      (* Senc := *) Senc
      (* prm := *) ed25519
      (* Proper_Eenc := *) PointEncoding.Proper_encode_point
      (* Edec := *) Edec
      (* eq_enc_E_iff := *) _
      (* Sdec := *) Sdec
      (* eq_enc_S_iff := *) _
      (* Erep := *) Erep
      (* ErepEq := *) ExtendedCoordinates.Extended.eq
      (* ErepAdd := *) ErepAdd
      (* ErepId := *) ExtendedCoordinates.Extended.zero
      (* ErepOpp := *) ExtendedCoordinates.Extended.opp
      (* Agroup := *) ExtendedCoordinates.Extended.extended_group
      (* EToRep := *) EToRep
      (* Ahomom := *) _
      (* ERepEnc := *) ERepEnc
      (* ERepEnc_correct := *) ERepEnc_correct
      (* Proper_ERepEnc := *) (PointEncoding.Proper_Kencode_point (Kpoint_eq_correct := ext_eq_correct) (Proper_Kenc := Proper_feEnc))
      (* ERepDec := *) ERepDec
      (* ERepDec_correct := *) _
      (* SRep := *) (Tuple.tuple (Word.word 32) 8)
      (* SRepEq := *) (Tuple.fieldwise Logic.eq)
      (* H0 := *) Tuple.Equivalence_fieldwise
      (* S2Rep := *) S2Rep
      (* SRepDecModL := *) _
      (* SRepDecModL_correct := *) _
      (* SRepERepMul := *) _
      (* SRepERepMul_correct := *) _
      (* Proper_SRepERepMul := *) _
      (* SRepDec := *) _
      (* SRepDec_correct := *) _
      (* mlen := *) _
      .

Require Import Coq.omega.Omega.
Require Import Crypto.EdDSARepChange.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Crypto.Specific.GF25519.
Require Crypto.Specific.SC25519.
Require Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Crypto.Encoding.PointEncoding.
Require Crypto.Util.IterAssocOp.
Import Morphisms.
Import NPeano.

Context {H: forall n : nat, Word.word n -> Word.word (b + b)}.

Definition feSign (x :  GF25519.fe25519) : bool :=
  let '(x9, x8, x7, x6, x5, x4, x3, x2, x1, x0) := x in
  BinInt.Z.testbit x0 0.

(* TODO *)
Context {feSign_correct : forall x,
            PointEncoding.sign x = feSign (ModularBaseSystem.encode x)}.
Context {Proper_feSign :  Proper (ModularBaseSystem.eq ==> eq) feSign}.

Definition a : GF25519.fe25519 :=
  Eval vm_compute in ModularBaseSystem.encode a.
Definition d : GF25519.fe25519 :=
  Eval vm_compute in ModularBaseSystem.encode d.
Definition twice_d : GF25519.fe25519 :=
  Eval vm_compute in (GF25519.add d d).
Locate a.
Lemma phi_a : ModularBaseSystem.eq (ModularBaseSystem.encode Spec.Ed25519.a) a.
Proof. reflexivity. Qed.
Lemma phi_d : ModularBaseSystem.eq (ModularBaseSystem.encode Spec.Ed25519.d) d.
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
  CompleteEdwardsCurve.E.coordinates (ExtendedCoordinates.Extended.to_twisted P (field:=GF25519.field25519)).

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
  let '(x7, x6, x5, x4, x3, x2, x1, x0) :=
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
                                (ExtendedCoordinates.Extended.to_twisted P (field:=GF25519.field25519)))
  ).

Let SRep := SC25519.SRep.
Let S2Rep := SC25519.S2Rep.
(*Let SRep := Tuple.tuple (Word.word 32) 8.

Let S2Rep := fun (x : ModularArithmetic.F.F l) =>
               Tuple.map (ZNWord 32)
               (Tuple.from_list_default (BinInt.Z.of_nat 0) 8
                  (Pow2Base.encodeZ
                  (List.repeat (BinInt.Z.of_nat 32) 8)
                  (ModularArithmetic.F.to_Z x))).*)

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

Local Coercion Z.of_nat : nat >-> Z.
Let SRep_testbit : SRep -> nat -> bool := Z.testbit.
Let ERepSel : bool -> Erep -> Erep -> Erep := fun b x y => if b then x else y.

Let ll := Eval vm_compute in (BinInt.Z.to_nat (BinInt.Z.log2_up l)).
Let SRepERepMul : SRep -> Erep -> Erep :=
  IterAssocOp.iter_op
    (op:=ErepAdd)
    (id:=ExtendedCoordinates.Extended.zero(field:=GF25519.field25519)(prm:=twedprm_ERep))
    (scalar:=SRep)
    SRep_testbit
    (sel:=ERepSel)
    ll
.

Lemma SRepERepMul_correct n P :
  ExtendedCoordinates.Extended.eq (field:=GF25519.field25519)
    (EToRep (CompleteEdwardsCurve.E.mul n P))
    (SRepERepMul (S2Rep (ModularArithmetic.F.of_nat l n)) (EToRep P)).
Proof.
  pose proof @IterAssocOp.iter_op_correct.
  pose proof @Algebra.ScalarMult.homomorphism_scalarmult.
Abort.

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
  ExtendedCoordinates.Extended.eq (field:=GF25519.field25519) p q <->
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

Let SRepEnc : SRep -> Word.word b := (fun x => Word.NToWord _ (Z.to_N x)).

Axiom SRepERepMul_correct:
forall (n : nat) (P : E),
 ExtendedCoordinates.Extended.eq (field:=GF25519.field25519) (EToRep (CompleteEdwardsCurve.E.mul n P))
                                 (SRepERepMul (S2Rep (ModularArithmetic.F.of_nat l n)) (EToRep P)).

Axiom Proper_SRepERepMul : Proper (SC25519.SRepEq ==> ExtendedCoordinates.Extended.eq (field:=GF25519.field25519) ==> ExtendedCoordinates.Extended.eq (field:=GF25519.field25519)) SRepERepMul.

Axiom SRepEnc_correct : forall x : ModularArithmetic.F.F l, Senc x = SRepEnc (S2Rep x).

Axiom onCurve_ERepB :
  @Pre.onCurve GF25519.fe25519 (@ModularBaseSystem.eq GF25519.modulus GF25519.params25519) GF25519.one_
    GF25519.add GF25519.mul a d
    (@ModularBaseSystem.div GF25519.modulus GF25519.params25519
       (8758491%Z, 20764389%Z, 8378388%Z, 40966398%Z, 30858332%Z, 27570973%Z, 17082669%Z, 16144682%Z,
       25909283%Z, 52811034%Z) (0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 1%Z),
    @ModularBaseSystem.div GF25519.modulus GF25519.params25519
      (26843545%Z, 40265318%Z, 13421772%Z, 53687091%Z, 6710886%Z, 26843545%Z, 20132659%Z, 13421772%Z,
      26843545%Z, 40265304%Z) (0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 1%Z)) /\
  ~
  @ModularBaseSystem.eq GF25519.modulus GF25519.params25519 (0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 1%Z)
    GF25519.zero_ /\
  @ModularBaseSystem.eq GF25519.modulus GF25519.params25519
    (GF25519.mul (0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 0%Z, 1%Z)
       (27139452%Z, 16611511%Z, 13413597%Z, 19351346%Z, 11264893%Z, 8635006%Z, 244362%Z, 39759291%Z,
       27438313%Z, 28827043%Z))
    (GF25519.mul
       (8758491%Z, 20764389%Z, 8378388%Z, 40966398%Z, 30858332%Z, 27570973%Z, 17082669%Z, 16144682%Z,
       25909283%Z, 52811034%Z)
       (26843545%Z, 40265318%Z, 13421772%Z, 53687091%Z, 6710886%Z, 26843545%Z, 20132659%Z, 13421772%Z,
       26843545%Z, 40265304%Z)).

Let ERepB : Erep.
  let rB := (eval vm_compute in (proj1_sig (EToRep B))) in
  exists rB. exact onCurve_ERepB.
Defined.

Let ERepB_correct : ExtendedCoordinates.Extended.eq (field:=GF25519.field25519) ERepB (EToRep B). vm_decide_no_check. Qed.

Axiom ERepGroup :
  @Algebra.group Erep
        (@ExtendedCoordinates.Extended.eq GF25519.fe25519
           (@ModularBaseSystem.eq GF25519.modulus GF25519.params25519) GF25519.zero_ GF25519.one_ GF25519.opp
           GF25519.add GF25519.sub GF25519.mul GF25519.inv
           (@ModularBaseSystem.div GF25519.modulus GF25519.params25519) a d GF25519.field25519
           (fun x y : GF25519.fe25519 =>
            @ModularArithmeticTheorems.F.eq_dec GF25519.modulus
              (@ModularBaseSystem.decode GF25519.modulus GF25519.params25519 x)
              (@ModularBaseSystem.decode GF25519.modulus GF25519.params25519 y))) ErepAdd
        (@ExtendedCoordinates.Extended.zero GF25519.fe25519
           (@ModularBaseSystem.eq GF25519.modulus GF25519.params25519) GF25519.zero_ GF25519.one_ 
           _ GF25519.add _ GF25519.mul _
           (@ModularBaseSystem.div GF25519.modulus GF25519.params25519) a d GF25519.field25519
           twedprm_ERep _)
        (@ExtendedCoordinates.Extended.opp GF25519.fe25519
           (@ModularBaseSystem.eq GF25519.modulus GF25519.params25519) GF25519.zero_ GF25519.one_ 
           _ GF25519.add _ GF25519.mul _
           (@ModularBaseSystem.div GF25519.modulus GF25519.params25519) a d GF25519.field25519
          twedprm_ERep _).

Let sign := @EdDSARepChange.sign E
         (@CompleteEdwardsCurveTheorems.E.eq Fq (@eq Fq) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.add q) (@ModularArithmetic.F.mul q) Spec.Ed25519.a Spec.Ed25519.d)
         (@CompleteEdwardsCurve.E.add Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q) (@ModularArithmetic.F.sub q)
            (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q) (@ModularArithmetic.F.div q)
            (@PrimeFieldTheorems.F.field_modulo q prime_q) (@ModularArithmeticTheorems.F.eq_dec q) Spec.Ed25519.a
            Spec.Ed25519.d curve_params)
         (@CompleteEdwardsCurve.E.zero Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q) (@ModularArithmetic.F.sub q)
            (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q) (@ModularArithmetic.F.div q)
            (@PrimeFieldTheorems.F.field_modulo q prime_q) (@ModularArithmeticTheorems.F.eq_dec q) Spec.Ed25519.a
            Spec.Ed25519.d curve_params)
         (@CompleteEdwardsCurveTheorems.E.opp Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0)
            (@ModularArithmetic.F.one q) (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q)
            (@ModularArithmetic.F.sub q) (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q)
            (@ModularArithmetic.F.div q) Spec.Ed25519.a Spec.Ed25519.d (@PrimeFieldTheorems.F.field_modulo q prime_q)
            (@ModularArithmeticTheorems.F.eq_dec q))
         (@CompleteEdwardsCurve.E.mul Fq (@eq Fq) (ModularArithmetic.F.of_Z q 0) (@ModularArithmetic.F.one q)
            (@ModularArithmetic.F.opp q) (@ModularArithmetic.F.add q) (@ModularArithmetic.F.sub q)
            (@ModularArithmetic.F.mul q) (@ModularArithmetic.F.inv q) (@ModularArithmetic.F.div q)
            (@PrimeFieldTheorems.F.field_modulo q prime_q) (@ModularArithmeticTheorems.F.eq_dec q) Spec.Ed25519.a
            Spec.Ed25519.d curve_params) b H c n l B Eenc Senc (@ed25519 H) Erep ERepEnc SRep SC25519.SRepDecModL
         SRepERepMul SRepEnc SC25519.SRepAdd SC25519.SRepMul ERepB SC25519.SRepDecModLShort.

Let sign_correct : forall pk sk {mlen} (msg:Word.word mlen), sign pk sk _ msg = EdDSA.sign pk sk msg :=
  @sign_correct
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
      (* Agroup := *) ERepGroup
      (* EToRep := *) EToRep
      (* ERepEnc := *) ERepEnc
      (* ERepEnc_correct := *) ERepEnc_correct
      (* Proper_ERepEnc := *) (PointEncoding.Proper_Kencode_point (Kpoint_eq_correct := ext_eq_correct) (Proper_Kenc := Proper_feEnc))
      (* SRep := *) SRep
      (* SRepEq := *) SC25519.SRepEq (*(Tuple.fieldwise Logic.eq)*)
      (* H0 := *) SC25519.SRepEquiv (* Tuple.Equivalence_fieldwise*)
      (* S2Rep := *) S2Rep
      (* SRepDecModL := *) SC25519.SRepDecModL
      (* SRepDecModL_correct := *) SC25519.SRepDecModL_Correct
      (* SRepERepMul := *) SRepERepMul
      (* SRepERepMul_correct := *) SRepERepMul_correct
      (* Proper_SRepERepMul := *) Proper_SRepERepMul
      (* SRepEnc := *) _
      (* SRepEnc_correct := *) SRepEnc_correct
      (* Proper_SRepEnc := *) _
      (* SRepAdd := *) SC25519.SRepAdd
      (* SRepAdd_correct := *) SC25519.SRepAdd_Correct
      (* Proper_SRepAdd := *) SC25519.SRepAdd_Proper
      (* SRepMul := *) SC25519.SRepMul
      (* SRepMul_correct := *) SC25519.SRepMul_Correct
      (* Proper_SRepMul := *) SC25519.SRepMul_Proper
      (* ErepB := *) ERepB
      (* ErepB_correct := *) ERepB_correct
      (* SRepDecModLShort := *) SC25519.SRepDecModLShort
      (* SRepDecModLShort_correct := *) SC25519.SRepDecModLShort_Correct
.
Print Assumptions sign_correct.

Definition Fsqrt_minus1 := Eval vm_compute in ModularBaseSystem.decode (GF25519.sqrt_m1).
Definition Fsqrt := PrimeFieldTheorems.F.sqrt_5mod8 Fsqrt_minus1.
Lemma bound_check_255_helper x y : (0 <= x)%Z -> (BinInt.Z.to_nat x < 2^y <-> (x < 2^(Z.of_nat y))%Z).
Proof.
  intros.
  rewrite <-(Znat.Nat2Z.id 2) at 1.
  rewrite ZUtil.Z.pow_Z2N_Zpow by omega.
  rewrite <- Znat.Z2Nat.inj_lt by auto with zarith.
  reflexivity.
Qed.
Lemma bound_check255 : BinInt.Z.to_nat GF25519.modulus < 2^255.
Proof.
  apply bound_check_255_helper; vm_compute; intuition congruence.
Qed.

Lemma bound_check256 : BinInt.Z.to_nat GF25519.modulus < 2^256.
Proof.
  apply bound_check_255_helper; vm_compute; intuition congruence.
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
               Spec.Ed25519.a
               Spec.Ed25519.d
               _
               Fsqrt
               (PointEncoding.Fencoding (bound_check := bound_check255))
               Spec.Ed25519.sign).

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
      (* SRep := *) SRep (*(Tuple.tuple (Word.word 32) 8)*)
      (* SRepEq := *) SC25519.SRepEq (* (Tuple.fieldwise Logic.eq)*)
      (* H0 := *) SC25519.SRepEquiv (* Tuple.Equivalence_fieldwise*)
      (* S2Rep := *) S2Rep
      (* SRepDecModL := *) SC25519.SRepDecModL
      (* SRepDecModL_correct := *) SC25519.SRepDecModL_Correct
      (* SRepERepMul := *) SRepERepMul
      (* SRepERepMul_correct := *) _
      (* Proper_SRepERepMul := *) _
      (* SRepDec := *) _
      (* SRepDec_correct := *) _
      (* mlen := *) _
.




(*** Extraction *)




Extraction Language Haskell.
Unset Extraction KeepSingleton.
Set Extraction AutoInline.
Set Extraction Optimize.
Unset Extraction AccessOpaque.

(** Eq *)

Extraction Implicit eq_rect   [ x y ].
Extraction Implicit eq_rect_r [ x y ].
Extraction Implicit eq_rec    [ x y ].
Extraction Implicit eq_rec_r  [ x y ].

Extract Inlined Constant eq_rect   => "".
Extract Inlined Constant eq_rect_r => "".
Extract Inlined Constant eq_rec    => "".
Extract Inlined Constant eq_rec_r  => "".

(** Ord *)

Extract Inductive comparison =>
  "Prelude.Ordering" ["Prelude.EQ" "Prelude.LT" "Prelude.GT"].

(** Bool, sumbool, Decidable *)

Extract Inductive bool    => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive sumbool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inductive Bool.reflect => "Prelude.Bool" ["Prelude.True" "Prelude.False"].
Extract Inlined Constant Bool.iff_reflect => "".
Extraction Inline Crypto.Util.Decidable.Decidable Crypto.Util.Decidable.dec.

(* Extract Inlined Constant Equality.bool_beq => *)
(*   "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)". *)
Extract Inlined Constant Bool.bool_dec     =>
  "((Prelude.==) :: Prelude.Bool -> Prelude.Bool -> Prelude.Bool)".

Extract Inlined Constant Sumbool.sumbool_of_bool => "".

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant orb  => "(Prelude.||)".
Extract Inlined Constant andb => "(Prelude.&&)".
Extract Inlined Constant xorb => "Data.Bits.xor".

(** Comparisons *)

Extract Inductive comparison => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].
Extract Inductive CompareSpecT => "Prelude.Ordering" [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].

(** Maybe *)

Extract Inductive option => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].
Extract Inductive sumor  => "Prelude.Maybe" ["Prelude.Just" "Prelude.Nothing"].

(** Either *)

Extract Inductive sum => "Prelude.Either" ["Prelude.Left" "Prelude.Right"].

(** List *)

Extract Inductive list => "[]" ["[]" "(:)"].

Extract Inlined Constant app             => "(Prelude.++)".
Extract Inlined Constant List.map        => "Prelude.map".
Extract         Constant List.fold_left  => "\f l z -> Data.List.foldl f z l".
Extract Inlined Constant List.fold_right => "Data.List.foldr".
Extract Inlined Constant List.find       => "Data.List.find".
Extract Inlined Constant List.length     => "Data.List.genericLength".

(** Tuple *)

Extract Inductive prod => "(,)" ["(,)"].
Extract Inductive sigT => "(,)" ["(,)"].

Extract Inlined Constant fst    => "Prelude.fst".
Extract Inlined Constant snd    => "Prelude.snd".
Extract Inlined Constant projT1 => "Prelude.fst".
Extract Inlined Constant projT2 => "Prelude.snd".

Extract Inlined Constant proj1_sig => "".

(** Unit *)

Extract Inductive unit => "()" ["()"].

(** nat *)

Extract Inductive nat => "Prelude.Integer" [ "0" "Prelude.succ" ]
  "(\fO fS n -> {- match_on_nat -} if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

Extract Inlined Constant Nat.add => "(Prelude.+)".
Extract Inlined Constant Nat.mul => "(Prelude.*)".
Extract Inlined Constant Nat.pow => "(Prelude.^)".
Extract Inlined Constant Nat.max => "Prelude.max".
Extract Inlined Constant Nat.min => "Prelude.min".
Extract Inlined Constant Nat.gcd => "Prelude.gcd".
Extract Inlined Constant Nat.lcm => "Prelude.lcm".
Extract Inlined Constant Nat.land => "(Data.Bits..&.)".
Extract Inlined Constant Init.Nat.add => "(Prelude.+)".
Extract Inlined Constant Init.Nat.mul => "(Prelude.*)".
Extract Inlined Constant Init.Nat.max => "Prelude.max".
Extract Inlined Constant Init.Nat.min => "Prelude.min".
Extract Inlined Constant PeanoNat.Nat.add => "(Prelude.+)".
Extract Inlined Constant PeanoNat.Nat.mul => "(Prelude.*)".
Extract Inlined Constant PeanoNat.Nat.max => "Prelude.max".
Extract Inlined Constant PeanoNat.Nat.min => "Prelude.min".
Extract Inlined Constant Nat.compare => "Prelude.compare".
Extract Inlined Constant PeanoNat.Nat.compare => "Prelude.compare".
Extract Inlined Constant nat_compare_alt => "Prelude.compare".
Extract Inlined Constant Nat.ltb => "(Prelude.<)".
Extract Inlined Constant Compare_dec.lt_dec => "(Prelude.<)".
Extract Inlined Constant Nat.leb => "(Prelude.<=)".
Extract Inlined Constant Compare_dec.leb => "(Prelude.<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(Prelude.<=)".
Extract Inlined Constant EqNat.beq_nat => "(Prelude.==)".
Extract Inlined Constant Nat.eqb => "(Prelude.==)".
Extract Inlined Constant EqNat.eq_nat_decide => "(Prelude.==)".
Extract Inlined Constant Peano_dec.eq_nat_dec => "(Prelude.==)".
Extract Inlined Constant Nat.odd => "Prelude.odd".
Extract Inlined Constant Nat.even => "Prelude.even".

Extract Constant Nat.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant Nat.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant Init.Nat.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant Init.Nat.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".

Extract Constant Nat.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Nat.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".
Extract Constant Init.Nat.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Init.Nat.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

(** positive *)
Require Import BinPos.

Extract Inductive positive => "Prelude.Integer" [
  "(\x -> 2 Prelude.* x Prelude.+ 1)"
  "(\x -> 2 Prelude.* x)"
  "1" ]
  "(\fI fO fH n -> {- match_on_positive -}
                   if n Prelude.== 1 then fH () else
                   if Prelude.odd n
                   then fI (n `Prelude.div` 2)
                   else fO (n `Prelude.div` 2))".

Extract Inlined Constant Pos.succ => "(1 Prelude.+)".
Extract Inlined Constant Pos.add => "(Prelude.+)".
Extract Inlined Constant Pos.mul => "(Prelude.*)".
Extract Inlined Constant Pos.pow => "(Prelude.^)".
Extract Inlined Constant Pos.max => "Prelude.max".
Extract Inlined Constant Pos.min => "Prelude.min".
Extract Inlined Constant Pos.gcd => "Prelude.gcd".
Extract Inlined Constant Pos.land => "(Data.Bits..&.)".
Extract Inlined Constant Pos.lor => "(Data.Bits..|.)".
Extract Inlined Constant Pos.compare => "Prelude.compare".
Extract Inlined Constant Pos.ltb => "(Prelude.<)".
Extract Inlined Constant Pos.leb => "(Prelude.<=)".
Extract Inlined Constant Pos.eq_dec => "(Prelude.==)".
Extract Inlined Constant Pos.eqb => "(Prelude.==)".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant Pos.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant Pos.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant Pos.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant Pos.pred => "(\n -> Prelude.max 1 (Prelude.pred n))".
Extract Constant Pos.sub => "(\n m -> Prelude.max 1 (n Prelude.- m))".

(** N *)

Extract Inlined Constant N.succ => "(1 Prelude.+)".
Extract Inlined Constant N.add => "(Prelude.+)".
Extract Inlined Constant N.mul => "(Prelude.*)".
Extract Inlined Constant N.pow => "(Prelude.^)".
Extract Inlined Constant N.max => "Prelude.max".
Extract Inlined Constant N.min => "Prelude.min".
Extract Inlined Constant N.gcd => "Prelude.gcd".
Extract Inlined Constant N.lcm => "Prelude.lcm".
Extract Inlined Constant N.land => "(Data.Bits..&.)".
Extract Inlined Constant N.lor => "(Data.Bits..|.)".
Extract Inlined Constant N.lxor => "Data.Bits.xor".
Extract Inlined Constant N.compare => "Prelude.compare".
Extract Inlined Constant N.eq_dec => "(Prelude.==)".
Extract Inlined Constant N.ltb => "(Prelude.<)".
Extract Inlined Constant N.leb => "(Prelude.<=)".
Extract Inlined Constant N.eq_dec => "(Prelude.==)".
Extract Inlined Constant N.odd => "Prelude.odd".
Extract Inlined Constant N.even => "Prelude.even".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant N.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant N.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant N.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant N.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant N.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant N.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant N.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

Extract Inductive N => "Prelude.Integer" [ "0" "(\x -> x)" ]
  "(\fO fS n -> {- match_on_N -} if n Prelude.== 0 then fO () else fS (n Prelude.- 1))".

(** Z *)
Require Import ZArith.BinInt.

Extract Inductive Z => "Prelude.Integer" [ "0" "(\x -> x)" "Prelude.negate" ]
  "(\fO fP fN n -> {- match_on_Z -}
                   if n Prelude.== 0 then fO () else
                   if n Prelude.> 0 then fP n else
                   fN (Prelude.negate n))".

Extract Inlined Constant Z.succ => "(1 Prelude.+)".
Extract Inlined Constant Z.add => "(Prelude.+)".
Extract Inlined Constant Z.sub => "(Prelude.-)".
Extract Inlined Constant Z.opp => "Prelude.negate".
Extract Inlined Constant Z.mul => "(Prelude.*)".
Extract Inlined Constant Z.pow => "(Prelude.^)".
Extract Inlined Constant Z.pow_pos => "(Prelude.^)".
Extract Inlined Constant Z.max => "Prelude.max".
Extract Inlined Constant Z.min => "Prelude.min".
Extract Inlined Constant Z.lcm => "Prelude.lcm".
Extract Inlined Constant Z.land => "(Data.Bits..&.)".
Extract Inlined Constant Z.pred => "Prelude.pred".
Extract Inlined Constant Z.land => "(Data.Bits..&.)".
Extract Inlined Constant Z.lor => "(Data.Bits..|.)".
Extract Inlined Constant Z.lxor => "Data.Bits.xor".
Extract Inlined Constant Z.compare => "Prelude.compare".
Extract Inlined Constant Z.eq_dec => "(Prelude.==)".
Extract Inlined Constant Z_ge_lt_dec => "(Prelude.>=)".
Extract Inlined Constant Z_gt_le_dec => "(Prelude.>)".
Extract Inlined Constant Z.ltb => "(Prelude.<)".
Extract Inlined Constant Z.leb => "(Prelude.<=)".
Extract Inlined Constant Z.gtb => "(Prelude.>)".
Extract Inlined Constant Z.geb => "(Prelude.>=)".
Extract Inlined Constant Z.odd => "Prelude.odd".
Extract Inlined Constant Z.even => "Prelude.even".

(* XXX: unsound -- overflow in fromIntegral *)
Extract Constant Z.shiftr => "(\w n -> Data.Bits.shiftR w (Prelude.fromIntegral n))".
Extract Constant Z.shiftl => "(\w n -> Data.Bits.shiftL w (Prelude.fromIntegral n))".
Extract Constant Z.testbit => "(\w n -> Data.Bits.testBit w (Prelude.fromIntegral n))".

Extract Constant Z.div => "(\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)".
Extract Constant Z.modulo => "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".

(** Conversions *)

Extract Inlined Constant Z.of_N => "".
Extract Inlined Constant Z.to_N => "".
Extract Inlined Constant N.to_nat => "".
Extract Inlined Constant N.of_nat => "".
Extract Inlined Constant Z.to_nat => "".
Extract Inlined Constant Z.of_nat => "".
Extract Inlined Constant Z.abs_N => "Prelude.abs".
Extract Inlined Constant Z.abs_nat => "Prelude.abs".
Extract Inlined Constant Pos.pred_N => "Prelude.pred".
Extract Inlined Constant Pos.lxor => "Data.Bits.xor".

(** Word *)
(* do not annotate every bit of a word with the number of bits after it *)
Extraction Implicit Word.WS [ 2 ].
Extraction Implicit Word.whd [ 1 ].
Extraction Implicit Word.wtl [ 1 ].
Extraction Implicit Word.bitwp [ 2 ].
Extraction Implicit Word.wand [ 1 ].
Extraction Implicit Word.wor [ 1 ].
Extraction Implicit Word.wxor [ 1 ].
Extraction Implicit Word.wordToN [ 1 ].
Extraction Implicit Word.wordToNat [ 1 ].
Extraction Implicit Word.combine [ 1 3 ].
Extraction Implicit Word.split1 [ 2 ].
Extraction Implicit Word.split2 [ 2 ].
Extraction Implicit WordUtil.cast_word [1 2 3].
Extraction Implicit WordUtil.wfirstn [ 2 4 ].
Extract Inlined Constant WordUtil.cast_word => "".

(** Let_In *)
Extraction Inline LetIn.Let_In.

(* inlining, primarily to reduce polymorphism *)
Extraction Inline dec_eq_Z dec_eq_N dec_eq_sig_hprop.
Extraction Inline Erep SRep ZNWord WordNZ.
Extraction Inline GF25519.fe25519.
Extraction Inline EdDSARepChange.sign EdDSARepChange.splitSecretPrngCurve.
Extraction Inline SRep_testbit.
Extraction Inline Crypto.Util.IterAssocOp.iter_op Crypto.Util.IterAssocOp.test_and_op.
Extraction Inline PointEncoding.Kencode_point.
Extraction Inline ExtendedCoordinates.Extended.point ExtendedCoordinates.Extended.coordinates ExtendedCoordinates.Extended.to_twisted  ExtendedCoordinates.Extended.from_twisted ExtendedCoordinates.Extended.add_coordinates ExtendedCoordinates.Extended.add ExtendedCoordinates.Extended.opp ExtendedCoordinates.Extended.zero. (* ExtendedCoordinates.Extended.zero could be precomputed *)
Extraction Inline CompleteEdwardsCurve.E.coordinates CompleteEdwardsCurve.E.zero.

(* Recursive Extraction sign. *)
  (* most of the code we want seems to be below [eq_dec1] and there is other stuff above that *)
  (* TODO: remove branching from [sRep] functions *)

(* fragment of output:

sign :: Word -> Word -> Prelude.Integer -> Word -> Word
sign pk sk mlen msg =
  let {
   sp = let {hsk = h b sk} in
        (,)
        (sRepDecModLShort
          (combine n (clearlow n c (wfirstn n ((Prelude.+) b b) hsk)) (Prelude.succ 0)
            (wones (Prelude.succ 0)))) (split2 b b hsk)}
  in
  let {r = sRepDecModL (h ((Prelude.+) b mlen) (combine b (Prelude.snd sp) mlen msg))} in
  let {r0 = sRepERepMul r eRepB} in
  combine b (eRepEnc r0) b
    (sRepEnc
      (sRepAdd r
        (sRepMul
          (sRepDecModL
            (h ((Prelude.+) b ((Prelude.+) b mlen))
              (combine b (eRepEnc r0) ((Prelude.+) b mlen) (combine b pk mlen msg)))) (Prelude.fst sp))))

sRepERepMul :: SRep0 -> Erep -> Erep
sRepERepMul sc a =
  Prelude.snd
    (funexp (\state ->
      case state of {
       (,) i acc ->
        let {acc2 = erepAdd acc acc} in
        let {acc2a = erepAdd a acc2} in
        (\fO fS n -> {- match_on_nat -} if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
          (\_ -> (,) 0
          acc)
          (\i' -> (,) i'
          (eRepSel ((\w n -> Data.Bits.testBit w (Prelude.fromIntegral n)) sc (of_nat i')) acc2 acc2a))
          i}) ((,) ll
      (case  ((,) zero_ one_) of {
        (,) x y -> (,) ((,) ((,) x y) one_) (mul3 x y)})) ll)

erepAdd :: (Point0 Fe25519) -> (Point0 Fe25519) -> Point0 Fe25519
erepAdd p q =
  case  p of {
   (,) y t1 ->
    case y of {
     (,) y0 z1 ->
      case y0 of {
       (,) x1 y1 ->
        case  q of {
         (,) y2 t2 ->
          case y2 of {
           (,) y3 z2 ->
            case y3 of {
             (,) x2 y4 ->
              let {a = mul3 (sub2 y1 x1) (sub2 y4 x2)} in
              let {b0 = mul3 (add2 y1 x1) (add2 y4 x2)} in
              let {c0 = mul3 (mul3 t1 twice_d) t2} in
              let {d = mul3 z1 (add2 z2 z2)} in
              let {e = sub2 b0 a} in
              let {f = sub2 d c0} in
              let {g = add2 d c0} in
              let {h0 = add2 b0 a} in
              let {x3 = mul3 e f} in
              let {y5 = mul3 g h0} in
              let {t3 = mul3 e h0} in let {z3 = mul3 f g} in (,) ((,) ((,) x3 y5) z3) t3}}}}}}
*)

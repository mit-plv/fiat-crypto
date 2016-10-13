Require Import Crypto.EdDSARepChange.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Util.Decidable.
Require Crypto.Specific.GF25519.
Require Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Crypto.Encoding.PointEncoding.
Import Morphisms.

Context {H: forall n : nat, Word.word n -> Word.word (b + b)}.
Context {feSign : GF25519.fe25519 -> bool}.

Definition a : GF25519.fe25519 :=
  Eval vm_compute in ModularBaseSystem.encode a.
Definition d : GF25519.fe25519 :=
  Eval vm_compute in ModularBaseSystem.encode d.

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


Global Instance Proper_onCurve {F eq one add mul a d} :
  Proper (Tuple.fieldwise (n := 2) eq==> iff) (@Pre.onCurve F eq one add mul a d) | 0.
Admitted.

Definition coord_to_extended (xy :  GF25519.fe25519 * GF25519.fe25519) : @Pre.onCurve _ (@ModularBaseSystem.eq GF25519.modulus
                           GF25519.params25519)
                        (@ModularBaseSystem.one GF25519.modulus
                           GF25519.params25519) GF25519.add
                        GF25519.mul a d xy -> Erep.
Proof.
  intros.
  destruct xy as [X Y].
  exists (X, Y, GF25519.one_, GF25519.mul X Y).
  repeat split.
  + cbv [ModularBaseSystem.div].
    rewrite !(@Algebra.Field.div_one _ _ _ _ _ _ _ _ _ _ (PrimeFieldTheorems.F.field_modulo GF25519.modulus)).
    match goal with H: Pre.onCurve (?X1, ?Y1) |- Pre.onCurve (?X2, ?Y2) =>
                    assert (Tuple.fieldwise (n := 2) ModularBaseSystem.eq (X2, Y2) (X1, Y1)) by (econstructor; cbv [fst snd Tuple.fieldwise' ModularBaseSystem.eq]; apply ModularBaseSystemProofs.encode_rep) end.
    pose proof @Proper_onCurve.
    cbv [Proper respectful] in *.
    match goal with H: Tuple.fieldwise _ ?x ?y, H1: Pre.onCurve ?y |- _  =>
                    pose proof (proj2
                                  (@Proper_onCurve _
                                  ModularBaseSystem.eq
                                  GF25519.one_
                                  GF25519.add
                                  GF25519.mul
                                  a d x y H) H1) end.
    assumption.
  + intro A. symmetry in A.
    apply (Algebra.field_is_zero_neq_one (field := GF25519.field25519)).
    rewrite GF25519.one_subst, GF25519.zero_subst.
    auto.
  + pose proof GF25519.field25519.
    rewrite (Algebra.left_identity (id := GF25519.one_)).
    reflexivity.
Defined.

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
      (* ErepAdd := *) ExtendedCoordinates.Extended.add
      (* ErepId := *) ExtendedCoordinates.Extended.zero
      (* ErepOpp := *) ExtendedCoordinates.Extended.opp
      (* Agroup := *) ExtendedCoordinates.Extended.extended_group
      (* EToRep := *) EToRep
      (* ERepEnc := *) ERepEnc
      (* ERepEnc_correct := *) PointEncoding.Kencode_point_correct
      (* Proper_ERepEnc := *) PointEncoding.Proper_Kencode_point
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
      (* ErepB := *) _
      (* ErepB_correct := *) _
      (* SRepDecModLShort := *) _
      (* SRepDecModLShort_correct := *) _
      .

Check verify_correct.

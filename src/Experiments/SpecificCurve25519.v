Require Import Coq.Classes.RelationClasses.
Require Import Crypto.Util.Notations Crypto.Util.Tactics Coq.ZArith.BinInt.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Experiments.SpecEd25519.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Require Import Crypto.CompleteEdwardsCurve.CompleteEdwardsCurveTheorems.
Require Import Crypto.Util.Decidable.

Require Import Crypto.Experiments.EdDSARefinement.
Require Import Crypto.Spec.ModularWordEncoding.
Require Import Crypto.Encoding.PointEncodingPre.

Require Import BinNat.
Require Import Crypto.Util.IterAssocOp.

Require Import Bedrock.Word.

Local Infix ">>" := Z.shiftr.
Local Infix "&" := Z.land.

Section Curve25519.
  Axiom fe25519_sign_bit : fe25519 -> bool.
  Axiom convert_fe25519_to_wire : Encoding.CanonicalEncoding fe25519 (Word.word 255).

  Definition twice_d : fe25519 := Eval vm_compute in
    @ModularBaseSystem.encode modulus params25519 (d + d)%F.
  Definition a : fe25519 := Eval vm_compute in
    @ModularBaseSystem.encode modulus params25519 a.
  Definition d : fe25519 := Eval vm_compute in
    @ModularBaseSystem.encode modulus params25519 d.

  Lemma prm25519 :
    @E.twisted_edwards_params fe25519
                              ModularBaseSystem.eq ModularBaseSystem.zero ModularBaseSystem.one add mul
                              a d.
  Proof.
  Admitted.

  Lemma Hphi : @Algebra.Ring.is_homomorphism
                 (F q) (@eq (F q)) 1%F (@F.add q) (@F.mul q) fe25519
                 (@ModularBaseSystem.eq modulus params25519) (@ModularBaseSystem.one modulus params25519) add mul
                 (@ModularBaseSystem.encode modulus params25519).
  Admitted.

  Lemma phi_nonzero : forall x : F q,
      x <> 0%F -> ~ ModularBaseSystem.eq (@ModularBaseSystem.encode _ params25519 x) ModularBaseSystem.zero.
  Admitted.

  Definition ge25519 :=
    @Extended.point
      fe25519 (@ModularBaseSystem.eq modulus params25519)
      (@ModularBaseSystem.zero modulus params25519) (@ModularBaseSystem.one modulus params25519) add mul
      (@ModularBaseSystem.div modulus params25519) a d.

  Lemma HKa : ModularBaseSystem.eq a (ModularBaseSystem.opp ModularBaseSystem.one). vm_decide_no_check. Qed.
  Lemma Hd : ModularBaseSystem.eq (ModularBaseSystem.encode SpecEd25519.d) d. vm_decide_no_check. Qed.

  Definition ge25519_from_ref : E.point -> _ := fun P => Extended.ref_phi(phi:=ModularBaseSystem.encode)(fieldF:=F.field_modulo q)(fieldK:=field25519)(Kd:=d)(Ka:=a)(Hd:=Hd)(HKa:=HKa)(HFa:=eq_refl)(Hphi:=Hphi)(phi_nonzero:=phi_nonzero) (Extended.from_twisted P).

  Definition ge25519_mul_N : N -> ge25519 -> ge25519  :=
    iter_op
      (op:=Extended.add(field:=field25519)(prm:=prm25519)(a_eq_minus1:=eq_refl)(Htwice_d:=eq_refl))
      (id:=Extended.zero(field:=field25519)(prm:=prm25519))
      N.testbit_nat
      (Z.to_nat (Z.log2_up l))
  .

  Definition twisted25519_to_wire P : Word.word 256 :=
    point_enc(F:=fe25519)(eq:=ModularBaseSystem.eq)(one:=ModularBaseSystem.one)
             (add:=GF25519.add)(mul:=GF25519.mul)(a:=a)(d:=d)(sz:=255)(sign_bit:=fe25519_sign_bit) convert_fe25519_to_wire P.

  Definition ge25519_to_wire := fun P => twisted25519_to_wire (Extended.to_twisted(field:=field25519)(*8.6: (prm:=prm25519)*) P).
  Lemma ge25519_to_wire_correct : forall P : E.point, Eenc P = ge25519_to_wire (ge25519_from_ref P).
  Admitted.
  Definition ge25519_coords_B := Eval vm_compute in proj1_sig (ge25519_from_ref B).
  Axiom admit : forall {T}, T.
  Definition ge25519_B : ge25519 := exist _ ge25519_coords_B admit.
  Definition ge25519_coords_zero := Eval vm_compute in proj1_sig (ge25519_from_ref E.zero).
  Definition ge25519_zero : ge25519 := exist _ ge25519_coords_zero admit.
  
  (*
  Time
  Definition ge25519_coords_lB := Eval native_compute in
        proj1_sig (ge25519_mul_N (Z.to_N l_Z) ge25519_B).
  (* Finished transaction in 1091.517 secs (1091.353u,0.196s) (successful) *)

  Definition twisted25519_coords_lB := Eval native_compute in proj1_sig (Extended.to_twisted(field:=field25519)(prm:=prm25519) (exist _ (ge25519_coords_lB) admit)).
  *)

  Definition SRepDecModL (h:word (b + b)): N :=
    N.modulo (wordToN h) (Z.to_N l).

  Import NPeano Nat.
  Local Infix "mod" := modulo (at level 40, no associativity).
  Lemma N_of_nat_mod a b : N.of_nat (a mod b) = N.modulo (N.of_nat a) (N.of_nat b).
  Admitted.
  
  Definition ge25519_add := @Extended.add _ _ _ _ _ _ _ _ _ _ _ _
                                          field25519 prm25519 admit admit admit.

  Definition ge25519_opp := Extended.opp(field:=field25519)(prm:=prm25519).

  (*
  Goal
    forall
      Edec
      SRepDec 
      ERepEnc
      ERepDec 
      ERepGroup ERepHomomorphism
      ERepEnc_correct ERepDec_correct SRepDecModL_correct SRepERepMul_correct
      Proper_SRepERepMul SRepDec_correct Proper_ERepEnc
      
      ,
      forall x, x =
    @verify_using_representation
(@E.point (F q) Logic.eq 1%F F.add F.mul (F.opp 1) SpecEd25519.d)
E.eq E.add E.zero E.opp E.mul b H c n l B _ _
Ed25519
Edec (@Encoding.dec _ _ FlEncoding)
ge25519 Extended.eq ge25519_add ge25519_zero ge25519_opp ERepGroup ge25519_from_ref ERepHomomorphism
ERepEnc ERepEnc_correct Proper_ERepEnc ERepDec ERepDec_correct

N Logic.eq
_ F.to_N SRepDecModL SRepDecModL_correct ge25519_mul_N
SRepERepMul_correct Proper_SRepERepMul SRepDec SRepDec_correct
-> True.
    intros; exact I.
  Qed.
   *)
End Curve25519.
Require Import Crypto.Util.Notations Coq.ZArith.BinInt.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Experiments.SpecEd25519.
Require Import Crypto.CompleteEdwardsCurve.ExtendedCoordinates.
Local Infix "<<" := Z.shiftr.
Local Infix "&" := Z.land.

Section Curve25519.

  Definition twice_d : fe25519 := Eval vm_compute in
    @ModularBaseSystem.encode modulus params25519 (d + d)%F.

  Definition ge25519_add :=
    Eval cbv beta delta [Extended.add_coordinates fe25519 add mul sub ModularBaseSystemOpt.Let_In] in
      @Extended.add_coordinates fe25519 add sub mul twice_d.
End Curve25519.
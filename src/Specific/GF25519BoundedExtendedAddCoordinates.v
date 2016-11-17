Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.Specific.GF25519.
Require Import Crypto.Specific.GF25519Bounded.
Require Import Crypto.Specific.GF25519ExtendedAddCoordinates.
Require Import Crypto.Specific.GF25519BoundedAddCoordinates.
Require Import Bedrock.Word Crypto.Util.WordUtil.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.ModularBaseSystemWord.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.HList.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

Lemma fieldwise_eq_extended_add_coordinates_full' twice_d P10 P11 P12 P13 P20 P21 P22 P23
  : Tuple.fieldwise
      (n:=4) GF25519BoundedCommon.eq
      (@GF25519BoundedAddCoordinates.add_coordinates
         twice_d P10 P11 P12 P13 P20 P21 P22 P23)
      (@ExtendedCoordinates.Extended.add_coordinates
         GF25519BoundedCommon.fe25519
         GF25519Bounded.add GF25519Bounded.sub GF25519Bounded.mul twice_d
         (P10, P11, P12, P13) (P20, P21, P22, P23)).
Proof.
  unfold GF25519BoundedCommon.eq.
  pose (add_coordinates_correct).
Admitted.

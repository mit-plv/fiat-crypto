Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.Util.Tuple Crypto.Util.CaseUtil.
Require Import ZArith.
Import PseudoMersenneBaseParams PseudoMersenneBaseParamProofs.

Generalizable All Variables.
Section s.
  Context `{prm:PseudoMersenneBaseParams m} {sc : SubtractionCoefficient m prm}.

  Definition frep := tuple Z (length PseudoMersenneBaseParamProofs.base).

  Definition mul : frep -> frep -> frep.
    refine (on_tuple2 (mul_opt k c) _).
    abstract (intros; rewrite mul_opt_correct; auto using length_mul).
  Defined.

  Definition add : frep -> frep -> frep.
    refine (on_tuple2 add_opt _).
    abstract (intros; rewrite add_opt_correct, add_length_exact; case_max; omega).
  Defined.

  Definition sub : frep -> frep -> frep.
    refine (on_tuple2 sub_opt _).
    abstract (intros; rewrite sub_opt_correct; apply length_sub; rewrite ?coeff_length; auto).
  Defined.
End S.
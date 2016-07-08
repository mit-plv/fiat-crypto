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

  Definition fe := tuple Z (length PseudoMersenneBaseParamProofs.base).

  Definition mul {k_ c_} (pfk : k = k_) (pfc:c = c_) (x y:fe) : fe :=
    carry_mul_opt_cps k_ c_ (fun xs : digits => from_list_default 0%Z (length base) xs)
      (to_list _ x) (to_list _ y).

  Definition add : fe -> fe -> fe.
    refine (on_tuple2 add_opt _).
    abstract (intros; rewrite add_opt_correct, add_length_exact; case_max; omega).
  Defined.

  Definition sub : fe -> fe -> fe.
    refine (on_tuple2 sub_opt _).
    abstract (intros; rewrite sub_opt_correct; apply length_sub; rewrite ?coeff_length; auto).
  Defined.

End s.
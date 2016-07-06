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

  About from_list.

  Lemma carry_mul_on_tuple x y :
    length (carry_mul (to_list (length base) x) (to_list (length base) y)) = length base.
  Admitted.

  Definition mul {k_ c_} (pfk : k = k_) (pfc:c = c_) (x y:fe) : fe.
    refine (carry_mul_opt_cps (fun xs => from_list _ xs) (to_list _ x) (to_list _ y) _).
    abstract (apply carry_mul_on_tuple).
  Defined.
  
  Definition add : fe -> fe -> fe.
    refine (on_tuple2 add_opt _).
    abstract (intros; rewrite add_opt_correct, add_length_exact; case_max; omega).
  Defined.

  Definition sub : fe -> fe -> fe.
    refine (on_tuple2 sub_opt _).
    abstract (intros; rewrite sub_opt_correct; apply length_sub; rewrite ?coeff_length; auto).
  Defined.
End s.
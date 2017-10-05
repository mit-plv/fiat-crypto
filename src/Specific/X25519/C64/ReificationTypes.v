Require Import Crypto.Specific.ReificationTypes.
Require Import Crypto.Specific.X25519.C64.ArithmeticSynthesisTest.

Module RP <: ReificationTypesPrePackage.
  Definition ReificationTypes_package' : { T : _ & T }.
  Proof. make_ReificationTypes_package wt sz bounds m wt_nonneg P.upper_bound_of_exponent. Defined.

  Definition ReificationTypes_package
    := Eval cbv [ReificationTypes_package' projT2] in projT2 ReificationTypes_package'.
End RP.

Module Export ReificationTypes := MakeReificationTypes RP.

Require Import Crypto.Specific.Framework.SynthesisFramework.
Require Import Crypto.Specific.X25519.C32.CurveParameters.

Module Import T := MakeSynthesisTactics Curve.

Module P <: SynthesisPrePackage.
  Definition Synthesis_package' : Synthesis_package'_Type.
  Proof. make_synthesis_package (). Defined.

  Definition Synthesis_package
    := Eval cbv [Synthesis_package' projT2] in projT2 Synthesis_package'.
End P.

Module Export S := PackageSynthesis Curve P.

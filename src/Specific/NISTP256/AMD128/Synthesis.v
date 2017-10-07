Require Import Crypto.Specific.Framework.SynthesisFramework.
Require Import Crypto.Specific.NISTP256.AMD128.CurveParameters.

Module Import T := MakeSynthesisTactics Curve.

Module P <: PrePackage.
  Definition package : Tag.Context.
  Proof. make_Synthesis_package (). Defined.
End P.

Module Export S := PackageSynthesis Curve P.

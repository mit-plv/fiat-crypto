Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.solinas32_2e256m2e224p2e192p2e96m1.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition freeze :
  { freeze : feBW -> feBW
  | forall a, phiBW (freeze a) = phiBW a }.
Proof.
  Set Ltac Profiling.
  Time synthesize_freeze ().
  Show Ltac Profile.
Time Defined.

Print Assumptions freeze.

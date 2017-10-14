Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.solinas64_2e256m2e224p2e192p2e96m1.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition square :
  { square : feBW -> feBW
  | forall a, phiBW (square a) = F.mul (phiBW a) (phiBW a) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_square ().
  Show Ltac Profile.
Time Defined.

Print Assumptions square.

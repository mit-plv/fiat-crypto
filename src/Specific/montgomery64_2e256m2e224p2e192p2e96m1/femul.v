Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.montgomery64_2e256m2e224p2e192p2e96m1.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition mul :
  { mul : feBW_small -> feBW_small -> feBW_small
  | forall a b, phiM_small (mul a b) = F.mul (phiM_small a) (phiM_small b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_mul ().
  Show Ltac Profile.
Time Defined.

Print Assumptions mul.

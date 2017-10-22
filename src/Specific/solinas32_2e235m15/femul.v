Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.solinas32_2e235m15.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition mul :
  { mul : feBW_loose -> feBW_loose -> feBW_tight
  | forall a b, phiBW_tight (mul a b) = F.mul (phiBW_loose a) (phiBW_loose b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_mul ().
  Show Ltac Profile.
Time Defined.

Print Assumptions mul.

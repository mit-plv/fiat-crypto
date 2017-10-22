Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X25519.C32.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition carry :
  { carry : feBW_loose -> feBW_tight
  | forall a, phiBW_tight (carry a) = (phiBW_loose a) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_carry ().
  Show Ltac Profile.
Time Defined.

Print Assumptions carry.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X25519.C32.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition add :
  { add : feBW_tight -> feBW_tight -> feBW_loose
  | forall a b, phiBW_loose (add a b) = F.add (phiBW_tight a) (phiBW_tight b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_add ().
  Show Ltac Profile.
Time Defined.

Print Assumptions add.

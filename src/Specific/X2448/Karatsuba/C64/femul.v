Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.X2448.Karatsuba.C64.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition mul :
  { mul : feBW -> feBW -> feBW
  | forall a b, phiBW (mul a b) = F.mul (phiBW a) (phiBW b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_mul ().
  Show Ltac Profile.
Time Defined.

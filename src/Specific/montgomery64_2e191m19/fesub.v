Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.montgomery64_2e191m19.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition sub :
  { sub : feBW_small -> feBW_small -> feBW_small
  | forall a b, phiM_small (sub a b) = F.sub (phiM_small a) (phiM_small b) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_sub ().
  Show Ltac Profile.
Time Defined.

Print Assumptions sub.

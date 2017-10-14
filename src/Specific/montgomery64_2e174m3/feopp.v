Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.montgomery64_2e174m3.Synthesis.

(* TODO : change this to field once field isomorphism happens *)
Definition opp :
  { opp : feBW_small -> feBW_small
  | forall a, phiM_small (opp a) = F.opp (phiM_small a) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_opp ().
  Show Ltac Profile.
Time Defined.

Print Assumptions opp.

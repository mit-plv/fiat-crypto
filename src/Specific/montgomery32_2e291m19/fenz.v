Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Specific.montgomery32_2e291m19.Synthesis.
Local Open Scope Z_scope.

(* TODO : change this to field once field isomorphism happens *)
Definition nonzero :
  { nonzero : feBW_small -> BoundedWord.BoundedWord 1 adjusted_bitwidth bound1
  | forall a, (BoundedWord.BoundedWordToZ _ _ _ (nonzero a) =? 0) = (if Decidable.dec (phiM_small a = F.of_Z m 0) then true else false) }.
Proof.
  Set Ltac Profiling.
  Time synthesize_nonzero ().
  Show Ltac Profile.
Time Defined.

Print Assumptions nonzero.

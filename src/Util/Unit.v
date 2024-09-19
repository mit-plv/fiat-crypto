From Coq Require Import Morphisms.
From Coq Require Import Relation_Definitions.

(* an equivalence for a relation on trivial things, like [unit] *)
Global Instance Equivalence_trivial {A} : Equivalence (fun _ _ : A => True).
Proof.
  repeat constructor.
Qed.

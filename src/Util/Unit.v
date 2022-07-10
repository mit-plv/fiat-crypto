Require Export Crypto.Util.FixCoqMistakes.
Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Coq.Relations.Relation_Definitions.

(* an equivalence for a relation on trivial things, like [unit] *)
Global Instance Equivalence_trivial {A} : Equivalence (fun _ _ : A => True).
Proof.
  repeat constructor.
Qed.

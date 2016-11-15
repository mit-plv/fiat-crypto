(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Export Crypto.Reflection.Z.InterpretationsGen.
Export Reflection.Syntax.Notations.

Module BitSize64 <: BitSize.
  Definition bit_width : nat := 64%nat.
  Lemma bit_width_pos : (0 < Z.of_nat bit_width)%Z.
  Proof. simpl; omega. Qed.
End BitSize64.

Module Interpretations64 := InterpretationsGen BitSize64.
Include Interpretations64.

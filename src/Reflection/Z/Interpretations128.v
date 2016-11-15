(** * Interpretation of PHOAS syntax for expression trees on ℤ *)
Require Import Coq.ZArith.ZArith.
Require Export Crypto.Reflection.Z.InterpretationsGen.
Export Reflection.Syntax.Notations.

Module BitSize128 <: BitSize.
  Definition bit_width : nat := 128%nat.
  Lemma bit_width_pos : (0 < Z.of_nat bit_width)%Z.
  Proof. simpl; omega. Qed.
End BitSize128.

Module Interpretations128 := InterpretationsGen BitSize128.
Include Interpretations128.

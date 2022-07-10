Require Export Crypto.Util.FixCoqMistakes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Local Open Scope Z_scope.

Module Z.
  Lemma mul_comm3 x y z : x * (y * z) = y * (x * z).
  Proof. lia. Qed.
End Z.

Module Export Hints.
  Export Crypto.Util.FixCoqMistakes.
End Hints.

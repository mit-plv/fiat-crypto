Set Loose Hint Behavior "Strict".
Require Export bbv.BinNotation.
Require Export bbv.ReservedNotations.
Require Import Coq.ZArith.BinInt.

Notation "'Ob' a" := (Z.of_N (bin a)).

Goal Ob"01000001" = 65%Z.
Proof. reflexivity. Qed.

Set Loose Hint Behavior "Strict".

Require Import Coq.ZArith.BinInt.
Require Export bbv.ReservedNotations.
Require Export bbv.OctNotation.


Notation "'Oo' a" := (Z.of_N (oct a)).

Goal Oo"52" = 42%Z.
Proof. reflexivity. Qed.

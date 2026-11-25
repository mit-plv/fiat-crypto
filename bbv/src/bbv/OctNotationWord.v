Set Loose Hint Behavior "Strict".

Require Import bbv.WordScope.
Require Export bbv.OctNotation.


Notation "'Oo' a" := (NToWord _ (oct a)) (at level 50).

Notation "sz ''o' a" := (NToWord sz (oct a)) (at level 50).

Goal 6'o"5" = WO~0~0~0~1~0~1.
Proof. reflexivity. Qed.

Goal Oo"4321" = WO~1~0~0~0~1~1~0~1~0~0~0~1.
Proof. reflexivity. Qed.

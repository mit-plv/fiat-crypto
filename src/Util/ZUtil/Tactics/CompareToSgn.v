Require Import Coq.ZArith.ZArith.
Module Z.
  Ltac compare_to_sgn :=
    repeat match goal with
           | [ H : _ |- _ ] => progress rewrite <- ?Z.sgn_neg_iff, <- ?Z.sgn_pos_iff, <- ?Z.sgn_null_iff in H
           | _ => progress rewrite <- ?Z.sgn_neg_iff, <- ?Z.sgn_pos_iff, <- ?Z.sgn_null_iff
           end.
End Z.

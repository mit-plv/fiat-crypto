From Coq Require Import Lia Znumtheory.

Module Z.
  Ltac prime_bound := match goal with
  | [ H : prime ?p |- _ ] => pose proof (prime_ge_2 p H); try lia
  end.
End Z.

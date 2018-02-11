Require Import Coq.PArith.BinPosDef.

Local Open Scope positive_scope.
(** Append two sequences *)

Fixpoint app (p q:positive) : positive :=
  match q with
  | q~0 => (app p q)~0
  | q~1 => (app p q)~1
  | 1 => p~1
  end.

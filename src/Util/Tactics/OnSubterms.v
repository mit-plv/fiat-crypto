(** Execute [progress tac] on all subterms of the goal.  Useful for things like [ring_simplify]. *)
Ltac tac_on_subterms tac :=
  repeat match goal with
         | [ |- context[?t] ]
           => progress tac t
         end.

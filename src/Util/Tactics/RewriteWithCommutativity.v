(** Rewrite with the commutative property to ensure that all appearences of an identifier show up the same way *)

Ltac rewrite_with_comm id clem x y :=
  first [ constr_eq x y; fail 1
        | repeat match goal with
                 | [ H' : context[id y x] |- _ ]
                   => rewrite clem in H'
                 | [ |- context[id y x] ]
                   => rewrite clem
                 end ].

Ltac normalize_commutative_identifier id id_comm :=
  repeat match goal with
         | [ |- context[id ?x ?y] ] => progress rewrite_with_comm id (id_comm y x) x y
         | [ H : context[id ?x ?y] |- _ ] => progress rewrite_with_comm id (id_comm y x) x y
         end.

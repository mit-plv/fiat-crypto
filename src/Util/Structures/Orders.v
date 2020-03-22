Require Import Coq.Structures.Equalities.
Require Import Coq.Structures.Orders.

Module Type UsualEqLt := UsualEq <+ HasLt.
Module Type UsualEqLe := UsualEq <+ HasLe.
Module Type UsualEqLtLe := UsualEq <+ HasLt <+ HasLe.

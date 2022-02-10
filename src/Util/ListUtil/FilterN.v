Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope list_scope.

Module List.
  Section __.
    Context {A} (f : A -> bool).
    Fixpoint filtern (l : list A) (n : nat) : list A
      := match n, l with
         | O, _ => l
         | _, [] => []
         | S n', x :: xs => if f x then filtern xs n' else x :: filtern xs n
         end.
  End __.
End List.

Require Import Crypto.Util.Option.
Require Import Crypto.Util.Notations.

Module Option.
  Module List.
    Section map.
      Context {A B}
              (f : A -> option B).

      Fixpoint map (ls : list A) : list B
        := match ls with
           | nil => nil
           | cons x xs
             => match f x with
               | Some fx => fx :: map xs
               | None => map xs
               end
           end.
    End map.

    Fixpoint bind_list {A B} (v : list (option A)) (f : list A -> option B) : option B
      := match v with
         | nil => f nil
         | x :: xs => (x <- x; @bind_list A B xs (fun xs => f (x :: xs)))
         end%option%list.

    Module Export Notations.
      Notation "A <-- X ; B" := (bind_list X (fun A => B%option)) : option_scope.
    End Notations.
  End List.
End Option.

Export Option.List.Notations.

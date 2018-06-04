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
  End List.
End Option.

(** Work around "Cannot create self-referring hypothesis" coming from
    [change x with y in *] *)
Ltac change_in_all from to :=
  change from with to;
  repeat match goal with
         | [ H : _ |- _ ] => progress change from with to in H
         end.

(** Work around "Cannot create self-referring hypothesis" coming from
    [change x with y in *] *)
Ltac change_in_all from to :=
  change from with to;
  repeat match goal with
         | [ H : _ |- _ ] => progress change from with to in H
         end.

Ltac change_with_compute_in_all c :=
  let c' := (eval compute in c) in
  change c with c' in *.

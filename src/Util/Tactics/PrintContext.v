Ltac print_context _ :=
  lazymatch goal with
  | [ H : ?T |- False ]
    => try ((clear H || fail 10000 "Anomaly in print_context: could not clear" H); print_context (); fail);
       match goal with
       | _ => let body := (eval cbv delta [H] in H) in
              idtac H ":=" body ":" T
       | _ => idtac H ":" T
       end
  | [ |- False ] => idtac
  | [ |- _ ] => try (exfalso; print_context (); fail)
  end.

(** [clear_free term] clears all hypotheses which are not required for typing [term] *)
Ltac clear_free term :=
  idtac;
  let H := fresh in
  let T := lazymatch goal with |- ?T => T end in
  simple notypeclasses refine (match term return T with H => _ end);
  repeat match goal with
         | [ H' : _ |- _ ] => tryif constr_eq H H' then fail else clear H'
         end;
  clear H.

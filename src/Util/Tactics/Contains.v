(** [contains x expr] succeeds iff [x] appears in [expr] *)
Ltac contains search_for in_term :=
  idtac;
  lazymatch in_term with
  | context[search_for] => idtac
  end.

Ltac free_in x y :=
  idtac;
  match y with
    | context[x] => fail 1 x "appears in" y
    | _ => idtac
  end.

Ltac subst_let := repeat match goal with | x := _ |- _ => subst x end.

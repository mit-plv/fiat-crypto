(** * Evar-normalize terms *)
(** Useful for working around things like COQBUG(https://github.com/coq/coq/issues/10044) *)
Local Definition dummy := Set.
Ltac evar_normalize term := (eval cbv delta [dummy] in term).

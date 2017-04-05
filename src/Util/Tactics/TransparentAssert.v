(** [transparent assert (H : T)] is like [assert (H : T)], but leaves the body transparent. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" :=
  simple refine (let name := (_ : type) in _).

(** [transparent eassert] is like [transparent assert], but allows holes in the type, which will be turned into evars. *)
Tactic Notation "transparent" "assert" "(" ident(name) ":" constr(type) ")" "by" tactic3(tac) := transparent assert (name : type); [ solve [ tac ] | ].
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" := transparent assert (name : type).
Tactic Notation "transparent" "eassert" "(" ident(name) ":" open_constr(type) ")" "by" tactic3(tac) := transparent assert (name : type) by tac.

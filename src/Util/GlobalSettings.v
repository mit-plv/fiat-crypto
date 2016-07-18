(** * Settings *)
(** Putting the settings together in this file makes it easy to import them. *)

(** Make the build process quieter in Coq >= 8.6.  We should replace
    [appcontext] with [context] when we drop support for Coq 8.4, and
    we should possibly do something about overridden notation
    warnings, maybe? *)
Global Set Warnings "-notation-overridden -deprecated-appcontext".

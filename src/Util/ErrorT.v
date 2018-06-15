Require Import Crypto.Util.Notations.

Inductive ErrorT {ErrT T} :=
| Success (v : T)
| Error (msg : ErrT).

Global Arguments ErrorT : clear implicits.
Delimit Scope error_scope with error.
Bind Scope error_scope with ErrorT.

Definition invert_result {ErrT T} (v : ErrorT ErrT T)
  := match v return match v with Success _ => T | _ => ErrT end with
     | Success v => v
     | Error msg => msg
     end.

Definition bind {A B ErrT} (x : ErrorT ErrT A) (k : A -> ErrorT ErrT B) : ErrorT ErrT B
  := match x with
     | Success v => k v
     | Error msg => Error msg
     end.

Notation "x <- y ; f" := (bind y (fun x => f%error)) : error_scope.

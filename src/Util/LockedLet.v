(** * A version of [let] that doesn't disappear under βδζ unless you also have ι and remove opacity *)
Require Import Crypto.Util.Notations.

Definition locked_let {A} (x : A) : bool * A := let y := x in (true, y).
Definition unlock_let {A} (x : A) : locked_let x = (true, x) := eq_refl.
Global Opaque locked_let.
Global Arguments locked_let : simpl never.

Notation "'llet' x := A 'in' b" := (let '(_, x) := locked_let A in b).

(** * Global Settings across the project *)

(** Compatibility with 8.4 so we can write, e.g., [match p with
    ex_intro x y => _ end], rather than [match p with ex_intro _ x y
    => _ end]. *)
Global Set Asymmetric Patterns.

(** Enforce uniform parameters *)
Global Set Uniform Inductive Parameters.

(** Consider also: *)
(** Judgmental η for records, faster projections *)
(** Set Primitive Projections. *)

(** Don't use non-imported hints *)
(** Set Loose Hint Behavior "Strict". *)

(** Universes *)
(** Set Universe Polymorphism. *)
(** Set Strict Universe Declaration. *)
(** Unset Universe Minimization ToSet. *)

(** Better control of unfolding in [rewrite] and [setoid_rewrite] *)
(** Set Keyed Unification. *)

(** Better-behaved [simpl] *)
(** Set SimplIsCbn. *)

(** Faster printing *)
Global Set Fast Name Printing.

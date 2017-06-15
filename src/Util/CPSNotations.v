Require Import Crypto.Util.Notations.

(** [x <- f ; C] encodes a call to function [f] with [C] as the
  continuation. In [C], [x] refers to the output of [f]. *)

(* [cpscall] is a marker to get Coq to print code using this notation only when it was actually used *)
Definition cpscall {R} (f:forall{T}(continuation:R->T),T) {T} (continuation:R->T)
:= @f T continuation.
Notation "x' <- v ; C" := (cpscall v (fun x' => C)).

(** A value of type [~>R] accepts a continuation that takes an
     argument of type [R].  It is meant to be used in [Definition] and
     such; for example:
<<
     Definition add_cps (a b:nat) : ~> nat.
>>
     The return type of the continuation is not yet specified; every
     [~> R] is universally quantified over the possible return types
     of the continuations that it can be applied to.
 *)
Notation "~> R" := (forall {T} (_:R->T), T).

(** The type [A ~> R] contains functions that takes an argument of
  type [A] and pass a value of type [R] to the continuation. Functions
  that take multiple arguments can be encoded as [A -> B ~> C] or [A
  ~> B ~>C] -- the first form requires both arguments to be specified
  before its output can be CPS-bound, the latter must be bound once it
  is partially applied to one argument. *)
Notation "A ~> R" := (A -> ~>R).

(* [cpsreturn] is a marker to get Coq to print loop notations before a [return] *)
Definition cpsreturn {T} (x:T) := x.
(** [return x] passes [x] to the continuation implicit in the previous notations. *)
Notation "'return' x" := (cpsreturn (fun {T} (continuation:_->T) => continuation x)).
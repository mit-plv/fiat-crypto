Require Import Crypto.Util.Notations.
Local Set Universe Polymorphism.

(** [x <- f ; C] encodes a call to function [f] with [C] as the
  continuation. In [C], [x] refers to the output of [f]. *)

Delimit Scope cps_scope with cps.

(* [cpscall] is a marker to get Coq to print code using this notation only when it was actually used *)
Definition cpscall {R} (f:forall{T}(continuation:R->T),T) {T} (continuation:R->T)
:= @f T continuation.
Notation "x' <- v ; C" := (cpscall v%cps (fun x' => C%cps)) : cps_scope.

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
Notation "~> R" := (forall {T} (_:R->T), T) : type_scope.

(** The type [A ~> R] contains functions that takes an argument of
  type [A] and pass a value of type [R] to the continuation. Functions
  that take multiple arguments can be encoded as [A -> B ~> C] or [A
  ~> B ~>C] -- the first form requires both arguments to be specified
  before its output can be CPS-bound, the latter must be bound once it
  is partially applied to one argument. *)
Notation "A ~> R" := (A -> ~>R) : type_scope.

(* [cpsreturn] is a marker to get Coq to print loop notations before a [return] *)
Definition cpsreturn {T} (x:T) := x.
(** [return x] passes [x] to the continuation implicit in the previous notations. *)
Notation "'return' x" := (cpsreturn (fun {T} (continuation:_->T) => continuation x)) : cps_scope.

Definition cpsbind {A B} (v:~> A) (f:A ~> B) : ~> B
  := fun T k => (a <- v; fa <- f a; k fa)%cps.
Notation "x' <--- v ; C" := (cpsbind v%cps (fun x' => C%cps)) : cps_scope.

Definition cps_option_bind {A B} (v:~> option A) (f:A ~> option B) : ~> option B
  := cpsbind v (fun x' T k => match x' with Some x' => f x' T k | None => k None end).
Notation "x' <-- v ; C" := (cps_option_bind v%cps (fun x' => C%cps)) : cps_scope.

Module CPSBindNotations.
  Notation "x' <- v ; C" := (cpsbind v%cps (fun x' => C%cps)) : cps_scope.
End CPSBindNotations.

(** * Definition and Notations for [do { body }] *)
Require Import Coq.omega.Omega.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.

(* TODO: move *)
Module CPSNotations.
  (** [x <- f ; C] encodes a call to function [f] with [C] as the
  continuation. In [C], [x] refers to the output of [f]. *)

  (* TODO: [cpscall] is a marker to get Coq to print code using this notation only when it was actually used *)
  Definition cpscall {R} (f:forall{T}(continuation:R->T),T) {T} (continuation:R->T)
    := @f T continuation.
  Notation "x <- v ; C" := (cpscall v (fun x => C)) (at level 70, right associativity, format "'[v' x  <-  v ; '/' C ']'").

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
  Notation "~> R" := (forall {T} (_:R->T), T) (at level 70).

  (** The type [A ~> R] contains functions that takes an argument of
  type [A] and pass a value of type [R] to the continuation. Functions
  that take multiple arguments can be encoded as [A -> B ~> C] or [A
  ~> B ~>C] -- the first form requires both arguments to be specified
  before its output can be CPS-bound, the latter must be bound once it
  is partially applied to one argument. *)
  Notation "A ~> R" := (A -> ~>R) (at level 99).
  
  (* TODO: [cpsreturn] is a marker to get Coq to print loop notations before a [return] *)
  Definition cpsreturn {T} (x:T) := x.
  (** [return x] passes [x] to the continuation implicit in the previous notations. *)
  Notation "'return' x" := (cpsreturn (fun {T} (continuation:_->T) => continuation x)) (at level 70, format "'return'  x").
End CPSNotations.

Section with_state.
  Import CPSNotations.
  Context {state : Type}.

  Definition loop_cps_step
             (loop_cps
              : forall (max_iter : nat)
                       (initial : state)
                       (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
                 ~> state)
             (max_iter : nat)
    : forall (initial : state)
             (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
      ~> state
    := fun st body
       => match max_iter with
          | 0
            => (return st)
          | S max_iter'
            => fun T ret
               => body st T (fun st' => @loop_cps max_iter' st' body _ ret) ret
          end.

  Fixpoint loop_cps (max_iter : nat)
    : forall (initial : state)
             (body : state -> forall {T} (continue : state -> T) (break : state -> T), T),
      ~> state
    := loop_cps_step loop_cps max_iter.

  Lemma unfold_loop_cps
        (max_iter : nat)
    : loop_cps max_iter
      = loop_cps_step loop_cps max_iter.
  Proof.
    destruct max_iter; reflexivity.
  Qed.

  Theorem loop_cps_def (max_iter : nat)
          (initial : state)
          (body : state -> forall {T} (continue : state -> T) (break : state -> T), T)
          T ret
    : loop_cps (S max_iter) initial body T ret =
      body initial (fun st' => @loop_cps max_iter st' body _ ret) ret.
  Proof.
    reflexivity.
  Qed.

  Theorem loop_cps_ind
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue break,
             (forall v, invariant v -> P (continue v))
             -> (forall v, invariant v -> P (break v))
             -> invariant v
             -> P (body v T continue break))
      -> (forall v, invariant v -> P (rest v))
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0 rest.
    induction n as [|n IHn]; intros v0 rest Hinv Hbody HP; simpl; cbv [cpsreturn]; auto.
  Qed.

  Local Hint Extern 2 => omega.

  Theorem loop_cps_wf_ind
          (measure : state -> nat)
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue,
             invariant v
             -> (forall break,
                    (forall v', measure v' < measure v -> invariant v' -> P (continue v'))
                    -> P (body v T continue break))
                \/ P (body v T continue rest))
      -> measure v0 < n
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0 rest.
    induction n as [|n IHn]; intros v0 rest Hinv Hbody Hmeasure; simpl; try omega.
    edestruct Hbody as [Hbody'|Hbody']; eauto.
  Qed.
End with_state.

(* N.B., Coq doesn't yet print this *)
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue , break ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue break => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break )  {{ '//' body ']' '//' }} ; '//' rest").

Section LoopTest.
  Import CPSNotations.
  Check loop _{ 10 } (x = 0) labels (continue, break) {{ continue (x + 1) }} ; x.
                                                                                      
  Check
    loop _{ 1234 } ('(i, a) = (0, 0)) labels (continue, break)
    {{
        if i <? 10
        then 
          continue (i + 1, a+1)
        else
          break (0, a)
    }};
    a.

  Context (f:nat~>nat).

  Check x <- f 0 ; return x + x.
  Check x <- f 0 ; y <- f x; z <- f y; return (x,y,z).

 Check loop _{ 10 } (x = 0) labels (continue, break) {{ continue (x + 1) }} ;
   return x.

 Check loop _{ 10 } (x = 0) labels (continue, break) {{ continue (x + 1) }} ; 
   x <- f x;
   return x.
  
  (* TODO: the loop notation should print here. *)
  Check loop _{ 10 } (x = 0) labels (continue, break) {{ x <- f x; continue (x) }} ; x.

  (*
  (* TODO LATER: something like these notations would be nice, desugaring to a [state := nat * T] *)
  for ( i = s; i < f; i++) updating (P = zero) labels (continue, break)
  {{
      continue (P+P)
  }};
  P.

  for ( i = s; i < f; i++) updating (P = zero) labels (continue)
  {{
      continue (P+P)
  }};
  P.
  *)
End LoopTest.

Require Import Crypto.Util.Tuple Crypto.Util.CPSUtil.
Section ScalarMult.
  Import CPSNotations.

  Context {G} (zero:G) (op_tbl : nat -> Z -> G ~> G). (* a monoid with a precomputed table *)
  Context (k w : nat) (nth_limb : nat ~> Z). (* k w-bit limbs *)

  (*
   table of xi*(32^i)*B
        for 
        0 <= xi <= 8 (with sign flips, -8 <= xi <= 8)
        0 <= i <= 31
   *)

  Definition ScalarMultBase :=
    loop _{k} ('(i, P_s) = (0, zero)) labels (continue, break)
    {{  if negb (i <? k) then break (i, P_s) else
        let i' := i + 1 in
        x <- nth_limb i;
        P_s <- op_tbl i x P_s;
        continue (i', P_s)
    }};
  return P_s.
  Print ScalarMultBase. (* TODO: the loop notation should print here *)
End ScalarMult.
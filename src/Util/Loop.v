(** * Definition and Notations for [do { body }] *)
Require Import Coq.omega.Omega.
Require Import Crypto.Util.Notations.

Section with_state.
  (** TODO: MOVE ME *)
  Local Notation "'return' x" := (fun {T} (continuation:_->T) => continuation x) (at level 70).
  Local Notation "x <- v ; C" := (v _ (fun x => C)) (at level 70, right associativity, format "'[v' x  <-  v ; '/' C ']'").
  Local Notation "~> R" := (forall {T} (_:R->T), T) (at level 70).
  Local Notation "A ~> R" := (forall (_:A) {T} (_:R->T), T) (at level 99).

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
    induction n as [|n IHn]; intros v0 rest Hinv Hbody HP; simpl; auto.
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
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'via' ( continue , break ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue break => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder, rest at level 10,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'via'  ( continue ,  break )  {{ '//' body ']' '//' }} ; '//' rest").

Check loop _{ 10 } (x = 0) via (continue, break) {{ continue (x + 1) }} ; x.

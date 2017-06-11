(** * Definition and Notations for [do { body }] *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.SpecializeBy.

(* TODO: move *)
Module CPSNotations.
  (** [x <- f ; C] encodes a call to function [f] with [C] as the
  continuation. In [C], [x] refers to the output of [f]. *)

  (* TODO: [cpscall] is a marker to get Coq to print code using this notation only when it was actually used *)
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

  (* TODO: [cpsreturn] is a marker to get Coq to print loop notations before a [return] *)
  Definition cpsreturn {T} (x:T) := x.
  (** [return x] passes [x] to the continuation implicit in the previous notations. *)
  Notation "'return' x" := (cpsreturn (fun {T} (continuation:_->T) => continuation x)).
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

  (** TODO(andreser): Remove this if we don't need it *)
  Theorem loop_cps_wf_ind_break
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

  Theorem loop_cps_wf_ind
          (measure : state -> nat)
          (invariant : state -> Prop)
          T (P : T -> Prop) n v0 body rest
    : invariant v0
      -> (forall v continue,
             invariant v
             -> ((forall v', measure v' < measure v -> invariant v' -> P (continue v'))
                 -> P (body v T continue rest)))
      -> measure v0 < n
      -> P (loop_cps n v0 body T rest).
  Proof.
    revert v0.
    induction n as [|n IHn]; intros v0 Hinv Hbody Hmeasure; simpl; try omega.
    eauto.
  Qed.
End with_state.

(** N.B. If the body is polymorphic (that is, if the type argument
    shows up in the body), then we need to bind the name of the type
    parameter somewhere in the notation for it to show up; we have a
    separate notation for this case. *)
(** TODO: When these notations are finalized, reserve them in Notations.v and moving the level and formatting rules there *)
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue , break , @ T ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue break => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break ,  @ T )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue , break ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue break => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'loop' _{ fuel } ( state1 .. staten = initial ) 'labels' ( continue ) {{ body }} ; rest"
  := (@loop_cps _ fuel initial
                (fun state1 => .. (fun staten => id (fun T continue _ => body)) .. )
                _ (fun state1 => .. (fun staten => rest) .. ))
       (at level 200, state1 binder, staten binder,
        format "'[v  ' 'loop' _{ fuel }  ( state1 .. staten  =  initial )  'labels'  ( continue )  {{ '//' body ']' '//' }} ; '//' rest").

Section with_for_state.
  Import CPSNotations.
  Context {state : Type}.

  Section with_loop_params.
    Context (test : Z -> Z -> bool) (i_final : Z) (upd_i : Z -> Z)
            (body : state -> Z -> forall {T} (continue : state -> T) (break : state -> T), T).

    (* we assume that [upd_i] is linear to compute the fuel *)
    Definition for_cps (i0 : Z) (initial : state)
      : ~> state
      := fun T ret
         => @loop_cps
              (Z * state)
              (S (S (Z.to_nat ((i_final - i0) / (upd_i 0%Z)))))
              (i0, initial)
              (fun '(i, st) T continue break
               => if test i i_final
                  then @body st i T
                             (fun st' => continue (upd_i i, st')%Z)
                             (fun st' => break (i, st'))
                  else break (i, st))
              T (fun '(i, st) => ret st).

    Section lemmas.
      Local Open Scope Z_scope.
      Context (upd_linear : forall x, upd_i x = upd_i 0 + x)
              (upd_signed : forall i0, test i0 i_final = true -> 0 < (i_final - i0) / (upd_i 0)).

      (** TODO: Strengthen this to take into account the value of
                  the loop counter at the end of the loop; based on
                  [ForLoop.v], it should be something like [(finish -
                  Z.sgn (finish - i0 + step - Z.sgn step) * (Z.abs
                  (finish - i0 + step - Z.sgn step) mod Z.abs step) +
                  step - Z.sgn step)] *)
      Theorem for_cps_ind
              (invariant : Z -> state -> Prop)
              T (P : (*Z ->*) T -> Prop) i0 v0 rest
        : invariant i0 v0
          -> (forall i v continue,
                 test i i_final = true
                 -> (forall v, invariant (upd_i i) v -> P (continue v))
                 -> invariant i v
                 -> P (@body v i T continue rest))
          -> (forall i v, test i i_final = false -> invariant i v -> P (rest v))
          -> P (for_cps i0 v0 T rest).
      Proof.
        unfold for_cps, cpscall, cpsreturn.
        intros Hinv IH Hrest.
        eapply @loop_cps_wf_ind with (T:=T)
                                       (invariant := fun '(i, s) => invariant i s)
                                       (measure := fun '(i, s) => S (Z.to_nat ((i_final - i) / upd_i 0)));
          [ assumption
          |
          | omega ].
        intros [i st] continue Hinv' IH'.
        destruct (test i i_final) eqn:Hi; [ | solve [ eauto ] ].
        pose proof (upd_signed _ Hi) as upd_signed'.
        assert (upd_i 0 <> 0)
          by (intro H'; rewrite H' in upd_signed'; autorewrite with zsimplify in upd_signed';
              omega).
        specialize (IH i st (fun st' => continue (upd_i i, st')) Hi).
        specialize (fun v pf => IH' (upd_i i, v) pf).
        cbv beta iota in *.
        specialize (fun pf v => IH' v pf).
        rewrite upd_linear in IH'.
        replace ((i_final - (upd_i 0 + i)) / upd_i 0)
        with ((i_final - i) / upd_i 0 - 1)
          in IH'
          by (Z.div_mod_to_quot_rem; nia).
        rewrite <- upd_linear, Z2Nat.inj_sub in IH' by omega.
        assert ((Z.to_nat 0 < Z.to_nat ((i_final - i) / upd_i 0))%nat)
          by (apply Z2Nat.inj_lt; omega).
        change (Z.to_nat 0) with 0%nat in *.
        change (Z.to_nat 1) with 1%nat in *.
        auto with omega.
      Qed.
    End lemmas.
  End with_loop_params.
End with_for_state.

Delimit Scope for_upd_scope with for_upd.
Delimit Scope for_test_scope with for_test.
Notation "i += k" := (Z.add i k) : for_upd_scope.
Notation "i -= k" := (Z.sub i k) : for_upd_scope.
Notation "i ++" := (i += 1)%for_upd : for_upd_scope.
Notation "i --" := (i -= 1)%for_upd : for_upd_scope.
Notation "<" := Z.ltb (at level 71) : for_test_scope.
Notation ">" := Z.gtb (at level 71) : for_test_scope.
Notation "<=" := Z.leb (at level 71) : for_test_scope.
Notation ">=" := Z.geb (at level 71) : for_test_scope.
Notation "≤" := Z.leb (at level 71) : for_test_scope.
Notation "≥" := Z.geb (at level 71) : for_test_scope.
Definition force_idZ (f : Z -> Z) (pf : f = id) {T} (v : T) := v.
(** [lhs] and [cmp_expr] go at level 9 so that they bind more tightly
    than application (so that [i (<)] sticks [i] in [lhs] and [(<)] in
    [cmp_expr], rather than sticking [i (<)] in [lhs] and then
    complaining about a missing value for [cmp_expr].  Unfortunately,
    because the comparison operators need to be at level > 70 to not
    conflict with their infix versions, putting [cmp_expr] at level 9
    forces us to wrap parentheses around the comparison operator. *)
(** TODO(andreser): If it's worth it, duplicate these notations for
      each value of [cmp_expr] so that we don't need to wrap the
      comparison operator in parentheses. *)
(** TODO: When these notations are finalized, reserve them in Notations.v and moving the level and formatting rules there *)
Notation "'for' ( i1 .. i2 = i0 ; lhs cmp_expr final ; upd_expr ) 'updating' ( state1 .. staten = initial ) 'labels' ( continue , break , @ T ) {{ body }} ; rest"
  := (force_idZ
        (fun i1 => .. (fun i2 => lhs) ..)
        eq_refl
        (@for_cps _ cmp_expr%for_test
                  final
                  (fun i1 => .. (fun i2 => upd_expr%for_upd) .. )
                  (fun state1 => .. (fun staten => id (fun i1 => .. (fun i2 => id (fun T continue break => body)) .. )) .. )
                  i0
                  initial
                  _ (fun state1 => .. (fun staten => rest) .. )))
       (at level 200, state1 binder, staten binder, i1 binder, i2 binder, lhs at level 9, cmp_expr at level 9,
        format "'[v  ' 'for'  ( i1 .. i2  =  i0 ;  lhs  cmp_expr  final ;  upd_expr )  'updating'  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break ,  @ T )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'for' ( i1 .. i2 = i0 ; lhs cmp_expr final ; upd_expr ) 'updating' ( state1 .. staten = initial ) 'labels' ( continue , break ) {{ body }} ; rest"
  := (force_idZ
        (fun i1 => .. (fun i2 => lhs) ..)
        eq_refl
        (@for_cps _ cmp_expr%for_test
                  final
                  (fun i1 => .. (fun i2 => upd_expr%for_upd) .. )
                  (fun state1 => .. (fun staten => id (fun i1 => .. (fun i2 => id (fun T continue break => body)) .. )) .. )
                  i0
                  initial
                  _ (fun state1 => .. (fun staten => rest) .. )))
       (at level 200, state1 binder, staten binder, i1 binder, i2 binder, lhs at level 9, cmp_expr at level 9,
        format "'[v  ' 'for'  ( i1 .. i2  =  i0 ;  lhs  cmp_expr  final ;  upd_expr )  'updating'  ( state1 .. staten  =  initial )  'labels'  ( continue ,  break )  {{ '//' body ']' '//' }} ; '//' rest").
Notation "'for' ( i1 .. i2 = i0 ; lhs cmp_expr final ; upd_expr ) 'updating' ( state1 .. staten = initial ) 'labels' ( continue ) {{ body }} ; rest"
  := (force_idZ
        (fun i1 => .. (fun i2 => lhs) ..)
        eq_refl
        (@for_cps _ cmp_expr%for_test
                  final
                  (fun i1 => .. (fun i2 => upd_expr%for_upd) .. )
                  (fun state1 => .. (fun staten => id (fun i1 => .. (fun i2 => id (fun T continue break => body)) .. )) .. )
                  i0
                  initial
                  _ (fun state1 => .. (fun staten => rest) .. )))
       (at level 200, state1 binder, staten binder, i1 binder, i2 binder, lhs at level 9, cmp_expr at level 9,
        format "'[v  ' 'for'  ( i1 .. i2  =  i0 ;  lhs  cmp_expr  final ;  upd_expr )  'updating'  ( state1 .. staten  =  initial )  'labels'  ( continue )  {{ '//' body ']' '//' }} ; '//' rest").

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

  Check loop _{ 10 } (x = 0) labels (continue, break) {{ x <- f x ; continue (x) }} ; x.


  Axiom s F : Z.
  Axiom zero : nat.
  Check for ( i = s; i (<) F; i++) updating (P = zero) labels (continue, break)
  {{
      continue (P+P)
  }};
  P.

  Check for ( i = s; i (<) F; i++) updating (P = zero) labels (continue)
  {{
      continue (P+P)
  }};
  P.
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
  Print ScalarMultBase.
End ScalarMult.

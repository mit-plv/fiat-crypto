Require Import Crypto.Util.Tuple.
Require Import Crypto.Compilers.Syntax.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}.

  Local Notation flat_type := (flat_type base_type_code).

  Section interp.
    Section flat_type.
      Context {interp_base_type : base_type_code -> Type}.
      Local Notation interp_flat_type := (interp_flat_type interp_base_type).

      Fixpoint flat_interp_tuple' {T n} : interp_flat_type (tuple' T n) -> Tuple.tuple' (interp_flat_type T) n
        := match n return interp_flat_type (tuple' T n) -> Tuple.tuple' (interp_flat_type T) n with
           | O => fun x => x
           | S n' => fun '((x, y) : interp_flat_type (tuple' T n' * T))
                     => (@flat_interp_tuple' _ n' x, y)
           end.
      Definition flat_interp_tuple {T n} : interp_flat_type (tuple T n) -> Tuple.tuple (interp_flat_type T) n
        := match n return interp_flat_type (tuple T n) -> Tuple.tuple (interp_flat_type T) n with
           | O => fun x => x
           | S n' => @flat_interp_tuple' T n'
           end.
      Fixpoint flat_interp_untuple' {T n} : Tuple.tuple' (interp_flat_type T) n -> interp_flat_type (tuple' T n)
        := match n return Tuple.tuple' (interp_flat_type T) n -> interp_flat_type (tuple' T n) with
           | O => fun x => x
           | S n' => fun '((x, y) : Tuple.tuple' _ n' * _)
                     => (@flat_interp_untuple' _ n' x, y)
           end.
      Definition flat_interp_untuple {T n} : Tuple.tuple (interp_flat_type T) n -> interp_flat_type (tuple T n)
        := match n return Tuple.tuple (interp_flat_type T) n -> interp_flat_type (tuple T n) with
           | O => fun x => x
           | S n' => @flat_interp_untuple' T n'
           end.
      Lemma flat_interp_untuple'_tuple' {T n v}
        : @flat_interp_untuple' T n (flat_interp_tuple' v) = v.
      Proof using Type. induction n; [ reflexivity | simpl; destruct v; rewrite IHn; reflexivity ]. Qed.
      Lemma flat_interp_untuple_tuple {T n v}
        : flat_interp_untuple (@flat_interp_tuple T n v) = v.
      Proof using Type. destruct n; [ reflexivity | apply flat_interp_untuple'_tuple' ]. Qed.
      Lemma flat_interp_tuple'_untuple' {T n v}
        : @flat_interp_tuple' T n (flat_interp_untuple' v) = v.
      Proof using Type. induction n; [ reflexivity | simpl; destruct v; rewrite IHn; reflexivity ]. Qed.
      Lemma flat_interp_tuple_untuple {T n v}
        : @flat_interp_tuple T n (flat_interp_untuple v) = v.
      Proof using Type. destruct n; [ reflexivity | apply flat_interp_tuple'_untuple' ]. Qed.
    End flat_type.
  End interp.

  Section interp2.
    Section flat_type.
      Context {interp_base_type1 interp_base_type2 : base_type_code -> Type}.
      Local Notation interp_flat_type1 := (interp_flat_type interp_base_type1).
      Local Notation interp_flat_type2 := (interp_flat_type interp_base_type2).

      Definition tuple_map {A B n} (f : interp_flat_type1 A -> interp_flat_type2 B) (v : interp_flat_type1 (tuple A n))
        : interp_flat_type2 (tuple B n)
        := flat_interp_untuple (Tuple.map f (flat_interp_tuple v)).
    End flat_type.
  End interp2.
End language.
Global Arguments flat_interp_tuple' {_ _ _ _} _.
Global Arguments flat_interp_tuple {_ _ _ _} _.
Global Arguments flat_interp_untuple' {_ _ _ _} _.
Global Arguments flat_interp_untuple {_ _ _ _} _.
Global Arguments tuple_map {_ _ _ _ _ n} _ _.

Ltac unfold_flat_interp_tuple _ :=
  let handle n :=
      ltac:(let n' := (eval cbv in n) in
            progress change n with n') in
  repeat match goal with
         | [ |- context[@flat_interp_tuple _ _ _ ?n] ]
           => handle n
         | [ |- context[@flat_interp_tuple' _ _ _ ?n] ]
           => handle n
         | [ |- context[@flat_interp_untuple _ _ _ ?n] ]
           => handle n
         | [ |- context[@flat_interp_untuple' _ _ _ ?n] ]
           => handle n
         | [ |- context[@tuple _ _ ?n] ]
           => handle n
         | [ |- context[@tuple' _ _ ?n] ]
           => handle n
         end;
  cbv [flat_interp_tuple flat_interp_tuple' flat_interp_untuple flat_interp_untuple' tuple tuple'].

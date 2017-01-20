Require Import Crypto.Util.Tuple.
Require Import Crypto.Reflection.Syntax.

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
           | S n' => fun xy => (@flat_interp_tuple' _ n' (fst xy), snd xy)
           end.
      Definition flat_interp_tuple {T n} : interp_flat_type (tuple T n) -> Tuple.tuple (interp_flat_type T) n
        := match n return interp_flat_type (tuple T n) -> Tuple.tuple (interp_flat_type T) n with
           | O => fun x => x
           | S n' => @flat_interp_tuple' T n'
           end.
      Fixpoint flat_interp_untuple' {T n} : Tuple.tuple' (interp_flat_type T) n -> interp_flat_type (tuple' T n)
        := match n return Tuple.tuple' (interp_flat_type T) n -> interp_flat_type (tuple' T n) with
           | O => fun x => x
           | S n' => fun xy => (@flat_interp_untuple' _ n' (fst xy), snd xy)
           end.
      Definition flat_interp_untuple {T n} : Tuple.tuple (interp_flat_type T) n -> interp_flat_type (tuple T n)
        := match n return Tuple.tuple (interp_flat_type T) n -> interp_flat_type (tuple T n) with
           | O => fun x => x
           | S n' => @flat_interp_untuple' T n'
           end.
      Lemma flat_interp_untuple'_tuple' {T n v}
        : @flat_interp_untuple' T n (flat_interp_tuple' v) = v.
      Proof. induction n; [ reflexivity | simpl; rewrite IHn; destruct v; reflexivity ]. Qed.
      Lemma flat_interp_untuple_tuple {T n v}
        : flat_interp_untuple (@flat_interp_tuple T n v) = v.
      Proof. destruct n; [ reflexivity | apply flat_interp_untuple'_tuple' ]. Qed.
      Lemma flat_interp_tuple'_untuple' {T n v}
        : @flat_interp_tuple' T n (flat_interp_untuple' v) = v.
      Proof. induction n; [ reflexivity | simpl; rewrite IHn; destruct v; reflexivity ]. Qed.
      Lemma flat_interp_tuple_untuple {T n v}
        : @flat_interp_tuple T n (flat_interp_untuple v) = v.
      Proof. destruct n; [ reflexivity | apply flat_interp_tuple'_untuple' ]. Qed.

      Definition tuple_map {A B n} (f : interp_flat_type A -> interp_flat_type B) (v : interp_flat_type (tuple A n))
        : interp_flat_type (tuple B n)
        := let fv := Tuple.map f (flat_interp_tuple v) in
           match n return interp_flat_type (tuple A n) -> Tuple.tuple (interp_flat_type B) n -> interp_flat_type (tuple B n) with
           | 0 => fun v x => x
           | S _ => fun v fv => flat_interp_untuple' fv
           end v fv.
    End flat_type.
  End interp.
End language.
Global Arguments flat_interp_tuple' {_ _ _ _} _.
Global Arguments flat_interp_tuple {_ _ _ _} _.
Global Arguments flat_interp_untuple' {_ _ _ _} _.
Global Arguments flat_interp_untuple {_ _ _ _} _.
Global Arguments tuple_map {_ _ _ _ n} _ _.

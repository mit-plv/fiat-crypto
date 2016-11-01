Require Import Crypto.Reflection.Syntax.

Section language.
  Context {base_type : Type}
          {interp_base_type : base_type -> Type}
          {op : flat_type base_type -> flat_type base_type -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}.
  Fixpoint count_binders (t : type base_type) : nat
    := match t with
       | Arrow A B => S (count_binders B)
       | Tflat _ => 0
       end.

  Fixpoint remove_binders' (n : nat) (t : type base_type) {struct t} : type base_type
    := match t, n with
       | Tflat _, _ => t
       | Arrow _ B, 0 => B
       | Arrow A B, S n'
         => remove_binders' n' B
       end.

  Definition remove_binders (n : nat) (t : type base_type) : type base_type
    := match n with
       | 0 => t
       | S n' => remove_binders' n' t
       end.

  Fixpoint binders_for' (n : nat) (t : type base_type) (var : base_type -> Type) {struct t}
    := match n, t return Type with
       | 0, Arrow A B => var A
       | S n', Arrow A B => var A * binders_for' n' B var
       | _, _ => unit
       end%type.
  Definition binders_for (n : nat) (t : type base_type) (var : base_type -> Type)
    := match n return Type with
       | 0 => unit
       | S n' => binders_for' n' t var
       end.

  Definition all_binders_for (t : type base_type) (var : base_type -> Type)
    := binders_for (count_binders t) t var.

  Fixpoint Apply' n {var t} (x : @expr base_type interp_base_type op var t)
    : forall (args : binders_for' n t var),
      @expr base_type interp_base_type op var (remove_binders' n t)
    := match x in (@expr _ _ _ _ t), n return (binders_for' n t var -> @expr _ _ _ _ (remove_binders' n t)) with
       | Return _ _ as y, _ => fun _ => y
       | Abs _ _ f, 0 => f
       | Abs src dst f, S n' => fun args => @Apply' n' var dst (f (fst args)) (snd args)
       end.

  Definition Apply n {var t} (x : @expr base_type interp_base_type op var t)
    : forall (args : binders_for n t var),
      @expr base_type interp_base_type op var (remove_binders n t)
    := match n return binders_for n t var -> @expr _ _ _ _ (remove_binders n t) with
       | 0 => fun _ => x
       | S n' => @Apply' n' var t x
       end.

  Fixpoint ApplyInterped' n {t} {struct t}
    : forall (x : interp_type interp_base_type t)
             (args : binders_for' n t interp_base_type),
      interp_type interp_base_type (remove_binders' n t)
    := match t, n return (forall (x : interp_type interp_base_type t)
                                 (args : binders_for' n t interp_base_type),
                             interp_type interp_base_type (remove_binders' n t)) with
       | Tflat _, _ => fun x _ => x
       | Arrow s d, 0 => fun x => x
       | Arrow s d, S n' => fun f args => @ApplyInterped' n' d (f (fst args)) (snd args)
       end.

  Definition ApplyInterped (n : nat) {t} (x : interp_type interp_base_type t)
    : forall (args : binders_for n t interp_base_type),
      interp_type interp_base_type (remove_binders n t)
    := match n return (binders_for n t interp_base_type -> interp_type interp_base_type (remove_binders n t)) with
       | 0 => fun _ => x
       | S n' => @ApplyInterped' n' t x
       end.
End language.

Arguments all_binders_for {_} !_ _ / .
Arguments count_binders {_} !_ / .
Arguments binders_for {_} !_ !_ _ / .
Arguments remove_binders {_} !_ !_ / .
(* Work around bug #5175 *)
Arguments Apply {_ _ _ _ _ _} _ _ , {_ _ _} _ {_ _} _ _.
Arguments Apply _ _ _ !_ _ _ !_ !_ / .
Arguments ApplyInterped {_ _ !_ !_} _ _ / .

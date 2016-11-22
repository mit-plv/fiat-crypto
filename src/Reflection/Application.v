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

  Fixpoint remove_all_binders (t : type base_type) : flat_type base_type
    := match t with
       | Tflat T => T
       | Arrow A B => remove_all_binders B
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

  Fixpoint all_binders_for (t : type base_type)
    := match t return match t with
                      | Tflat _ => unit
                      | _ => flat_type base_type
                      end with
       | Tflat T => tt
       | Arrow A B
         => match B return match B with Tflat _ => _ | _ => _ end -> _ with
            | Tflat T => fun _ => Tbase A
            | Arrow _ _ => fun T => Tbase A * T
            end%ctype (all_binders_for B)
       end.

  Definition interp_all_binders_for T var
    := match T return Type with
       | Tflat _ => unit
       | Arrow A B => interp_flat_type var (all_binders_for (Arrow A B))
       end.

  Fixpoint interp_all_binders_for' (T : type base_type) var
    := match T return Type with
       | Tflat _ => unit
       | Arrow A B => var A * interp_all_binders_for' B var
       end%type.

  Fixpoint interp_all_binders_for_of' T var {struct T}
    : interp_all_binders_for' T var -> interp_all_binders_for T var
    := match T return interp_all_binders_for' T var -> interp_all_binders_for T var with
       | Tflat _ => fun x => x
       | Arrow A B =>
         match B
               return (interp_all_binders_for' B var -> interp_all_binders_for B var)
                      -> interp_all_binders_for' (Arrow A B) var
                      -> interp_all_binders_for (Arrow A B) var
         with
         | Tflat _ => fun _ => @fst _ _
         | Arrow C D => fun interp x => (fst x, interp (snd x))
         end (@interp_all_binders_for_of' B var)
       end.

  Fixpoint interp_all_binders_for_to' T var {struct T}
    : interp_all_binders_for T var -> interp_all_binders_for' T var
    := match T return interp_all_binders_for T var -> interp_all_binders_for' T var with
       | Tflat _ => fun x => x
       | Arrow A B =>
         match B
               return (interp_all_binders_for B var -> interp_all_binders_for' B var)
                      -> interp_all_binders_for (Arrow A B) var
                      -> interp_all_binders_for' (Arrow A B) var
         with
         | Tflat _ => fun _ x => (x, tt)
         | Arrow C D => fun interp x => (fst x, interp (snd x))
         end (@interp_all_binders_for_to' B var)
       end.

  Definition fst_binder {A B var} (args : interp_flat_type var (all_binders_for (Arrow A B))) : var A
    := match B return interp_flat_type var (all_binders_for (Arrow A B)) -> var A with
       | Tflat _ => fun x => x
       | Arrow _ _ => fun x => fst x
       end args.
  Definition snd_binder {A B var} (args : interp_flat_type var (all_binders_for (Arrow A B)))
    : interp_all_binders_for B var
    := match B return interp_flat_type var (all_binders_for (Arrow A B))
                      -> interp_all_binders_for B var
       with
       | Tflat _ => fun _ => tt
       | Arrow _ _ => fun x => snd x
       end args.

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

  Fixpoint ApplyAll {var t} (x : @expr base_type interp_base_type op var t)
    : forall (args : interp_all_binders_for t var),
      @exprf base_type interp_base_type op var (remove_all_binders t)
    := match x in @expr _ _ _ _ t
             return (forall (args : interp_all_binders_for t var),
                        @exprf base_type interp_base_type op var (remove_all_binders t))
       with
       | Return _ x => fun _ => x
       | Abs src dst f => fun args => @ApplyAll var dst (f (fst_binder args)) (snd_binder args)
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

  Fixpoint ApplyInterpedAll {t}
    : forall  (x : interp_type interp_base_type t)
              (args : interp_all_binders_for t interp_base_type),
      interp_flat_type interp_base_type (remove_all_binders t)
    := match t return (forall (x : interp_type _ t)
                              (args : interp_all_binders_for t _),
                          interp_flat_type _ (remove_all_binders t))
       with
       | Tflat _ => fun x _ => x
       | Arrow A B => fun f x => @ApplyInterpedAll B (f (fst_binder x)) (snd_binder x)
       end.
End language.

Arguments all_binders_for {_} !_ / .
Arguments interp_all_binders_for {_} !_ _ / .
Arguments interp_all_binders_for_of' {_ !_ _} !_ / .
Arguments interp_all_binders_for_to' {_ !_ _} !_ / .
Arguments count_binders {_} !_ / .
Arguments binders_for {_} !_ !_ _ / .
Arguments remove_binders {_} !_ !_ / .
(* Work around bug #5175 *)
Arguments Apply {_ _ _ _ _ _} _ _ , {_ _ _} _ {_ _} _ _.
Arguments Apply _ _ _ !_ _ _ !_ !_ / .
Arguments ApplyInterped {_ _ !_ !_} _ _ / .
Arguments ApplyAll {_ _ _ _ !_} !_ _ / .
Arguments ApplyInterpedAll {_ _ !_} _ _ / .

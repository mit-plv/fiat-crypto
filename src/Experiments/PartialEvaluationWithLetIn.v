Require Import Crypto.Util.Notations.

(** Notes:

1. pattern out identifiers and types.
   - type := arrow (_:type) (_:type) | type_base (_:base_type) -- the latter is a parameter
   - literal is an identifier
   - expr cases: var, abs, app, letin, ident -- ident is a parameter
2. add prenex polymorphism for identifiers (type variables)
   -
   - ident is indexed by typecodes, perhaps cases: arrow | base | typevar
*)

Module type.
  Inductive type (base_type : Type) := base (t : base_type) | arrow (s d : type base_type).
  Global Arguments base {_}.
  Global Arguments arrow {_} s d.
End type.
Notation type := type.type.
Delimit Scope etype_scope with etype.
Bind Scope etype_scope with type.type.
Infix "->" := type.arrow : etype_scope.
Module base.
  Module type.
    Inductive type := nat | prod (A B : type).
  End type.
  Notation type := type.type.
End base.
Bind Scope etype_scope with base.type.
Infix "*" := base.type.prod : etype_scope.

Fixpoint upperboundT (t : base.type) : Type
  := match t with
     | base.type.nat => option nat
     | base.type.prod A B => upperboundT A * upperboundT B
     end.

Module expr.
  Section with_var.
    Context {base_type : Type}.
    Local Notation type := (type base_type).
    Context {ident : type -> Type}
            {var : type -> Type}.

    Inductive expr : type -> Type :=
    | Ident {t} (idc : ident t) : expr t
    | Var {t} (v : var t) : expr t
    | Abs {s d} (f : var s -> expr d) : expr (s -> d)
    | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
    | LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
    .
  End with_var.

  Module Export Notations.
    Delimit Scope expr_scope with expr.
    Bind Scope expr_scope with expr.
    Infix "@" := App : expr_scope.
    Reserved Notation "\ x .. y , t" (at level 200, x binder, y binder, right associativity, format "\  x .. y , '//' t").
    Notation "\ x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "'λ' x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "'expr_let' x := A 'in' b" := (LetIn A (fun x => b%expr)) : expr_scope.
    Notation "'$' x" := (Var x) (at level 9, format "'$' x") : expr_scope.
    Notation "' x" := (Ident x) (at level 9, x at level 10, format "' x") : expr_scope.
  End Notations.
End expr.
Import expr.Notations.
Notation expr := expr.expr.

Module ident.
  Local Notation type := (type base.type).
  Section with_base.
    Let type_base (x : base.type) : type := type.base x.
    Local Coercion type_base : base.type >-> type.

    Inductive ident : type -> Type :=
    | Literal (v : nat) : ident base.type.nat
    | Plus : ident (base.type.nat -> base.type.nat -> base.type.nat)
    | Pair {A B : base.type} : ident (A -> B -> A * B)
    | Fst {A B} : ident (A * B -> A)
    | Snd {A B} : ident (A * B -> B)
    | Cast {T} (upper_bound : upperboundT T) : ident (T -> T)
    .
  End with_base.

  Module Export Notations.
    Delimit Scope ident_scope with ident.
    Bind Scope ident_scope with ident.
    Global Arguments expr.Ident {base_type%type ident%function var%function t%etype} idc%ident.
    Notation "( x , y , .. , z )" := (expr.App (expr.App (expr.Ident Pair) .. (expr.App (expr.App (expr.Ident Pair) x%expr) y%expr) .. ) z%expr) : expr_scope.
    Notation "x + y" := ('Plus @ x @ y)%expr : expr_scope.
    Notation "` x" := (Literal x) (at level 9, x at level 10, format "` x") : ident_scope.
    Notation "` x" := (expr.Ident (Literal x)) (at level 9, x at level 10, format "` x") : expr_scope.
  End Notations.
End ident.
Import ident.Notations.
Notation ident := ident.ident.

Module UnderLets.
  Section with_var.
    Context {base_type : Type}.
    Local Notation type := (type base_type).
    Context {ident : type -> Type}
            {var : type -> Type}.
    Local Notation expr := (@expr base_type ident var).

    Inductive UnderLets {T : Type} :=
    | Base (v : T)
    | UnderLet {A} (x : expr A) (f : var A -> UnderLets).

    Fixpoint splice {A B} (x : @UnderLets A) (e : A -> @UnderLets B) : @UnderLets B
      := match x with
         | Base v => e v
         | UnderLet A x f => UnderLet x (fun v => @splice _ _ (f v) e)
         end.

    Fixpoint to_expr {t} (x : @UnderLets (expr t)) : expr t
      := match x with
         | Base v => v
         | UnderLet A x f
           => expr.LetIn x (fun v => @to_expr _ (f v))
         end.
  End with_var.
  Global Arguments UnderLets : clear implicits.
End UnderLets.
Delimit Scope under_lets_scope with under_lets.
Bind Scope under_lets_scope with UnderLets.UnderLets.
Notation "x <-- y ; f" := (UnderLets.splice y (fun x => f%under_lets)) : under_lets_scope.

Module partial.
  Import UnderLets.
  Section with_var.
    Context {base_type : Type}.
    Local Notation type := (type base_type).
    Let type_base (x : base_type) : type := type.base x.
    Local Coercion type_base : base_type >-> type.
    Context {ident : type -> Type}
            {var : type -> Type}.
    Local Notation expr := (@expr base_type ident).
    Local Notation UnderLets := (@UnderLets base_type ident var).
    Context (base_value : base_type -> Type)
            (stateT' : base_type -> Type)
            (annotate : forall t, stateT' t -> option (ident (t -> t)))
            (intersect_state : forall A, stateT' A -> stateT' A -> stateT' A)
            (bottom : forall A, stateT' A)
            (state_of_base_value : forall t, base_value t -> stateT' t)
            (base_reify : forall t, base_value t -> @expr var t).

    Fixpoint value (t : type)
      := match t with
         | type.base t
           => stateT' t * @expr var t + base_value t
         | type.arrow s d
           => value s -> UnderLets (value d)
         end%type.
    Definition value_with_lets (t : type)
      := UnderLets (value t).

    Context (interp_ident : forall t, ident t -> value t).

    Definition stateT (t : type)
      := match t with
         | type.base t => stateT' t
         | type.arrow s d => unit
         end.

    Fixpoint reify {t} : value t -> @expr var t
      := match t return value t -> @expr var t with
         | type.base t
           => fun v
              => match v with
                 | inl (st, e)
                   => match annotate _ st with
                      | None => e
                      | Some cst => 'cst @ e
                      end%expr
                 | inr v => base_reify _ v
                 end
         | type.arrow s d
           => fun f => λ x , (UnderLets.to_expr
                                (fx <-- f (@reflect _ (expr.Var x));
                                   Base (@reify _ fx)))
         end%core%expr
    with reflect {t} : @expr var t -> value t
         := match t return @expr var t -> value t with
            | type.base t
              => fun e => inl (bottom _, e)
            | type.arrow s d
              => fun e v
                 => Base (@reflect d (e @ (@reify s v)))%expr
            end.

    Fixpoint state_of_value {t} : value t -> stateT t
      := match t return value t -> stateT t with
         | type.base t
           => fun v
              => match v with
                 | inl (st, _) => st
                 | inr n => state_of_base_value _ n
                 end
         | type.arrow s d => fun _ => tt
         end.

    Definition put_state {t} : stateT t -> @expr var t -> value t
      := match t return stateT t -> expr t -> value t with
         | type.base t
           => fun st e => inl (st, e)
         | type.arrow s d
           => fun _ e => reflect e
         end.

    Fixpoint interp {t} (e : @expr value_with_lets t) : value_with_lets t
      := match e in expr.expr t return value_with_lets t with
         | expr.Ident t idc => Base (interp_ident t idc)
         | expr.Var t v => v
         | expr.Abs s d f => Base (fun x => @interp d (f (Base x)))
         | expr.App s d f x
           => (x' <-- @interp s x;
                 f' <-- @interp (s -> d)%etype f;
                 f' x')
         | expr.LetIn A B x f
           => (x' <-- @interp _ x;
                 UnderLet
                   (reify x')
                   (fun x'v
                    => @interp _ (f (Base (put_state (state_of_value x') (expr.Var x'v))))))
         end%under_lets.

    Definition eval {t} (e : @expr value_with_lets t) : expr t
      := UnderLets.to_expr (e' <-- interp e; Base (reify e')).

    Definition eval_with_bound {s d} (e : @expr value_with_lets (s -> d))
               (st : stateT s)
      : expr (s -> d)
      := UnderLets.to_expr
           (e' <-- interp e;
              Base
                (expr.Abs
                   (fun x
                    => UnderLets.to_expr
                         (e'' <-- e' (put_state st (expr.Var x));
                            Base (reify e''))))).
  End with_var.

  Module ident.
    Section with_var.
      Local Notation type := (type base.type).
      Let type_base (x : base.type) : type := type.base x.
      Local Coercion type_base : base.type >-> type.
      Context {var : type -> Type}.
      Local Notation expr := (@expr base.type ident).
      Local Notation UnderLets := (@UnderLets base.type ident var).
      Context (stateT' : base.type -> Type)
              (annotate : forall t, stateT' t -> option (ident (t -> t)))
              (add_state : stateT' base.type.nat -> stateT' base.type.nat -> stateT' base.type.nat)
              (fst_state : forall A B, stateT' (base.type.prod A B) -> stateT' A)
              (snd_state : forall A B, stateT' (base.type.prod A B) -> stateT' B)
              (state_of_literal : nat -> stateT' base.type.nat)
              (pair_state : forall A B, stateT' A -> stateT' B -> stateT' (base.type.prod A B))
              (intersect_state : forall A, stateT' A -> stateT' A -> stateT' A)
              (update_literal_with_state : stateT' base.type.nat -> nat -> nat)
              (state_of_upperbound : forall T, upperboundT T -> stateT' T)
              (bottom : forall A, stateT' A).

      Fixpoint base_value (t : base.type)
        := match t return Type with
           | base.type.nat as t
             => nat
           | base.type.prod A B as t
             => (stateT' A * @expr var A + base_value A) * (stateT' B * @expr var B + base_value B)
           end%type.

      Fixpoint state_of_base_value {t} : base_value t -> stateT' t
        := match t return base_value t -> stateT' t with
           | base.type.nat => state_of_literal
           | base.type.prod A B
             => fun '(a, b)
                => let sta := match a with
                              | inl (st, _) => st
                              | inr a' => @state_of_base_value A a'
                              end in
                   let stb := match b with
                              | inl (st, _) => st
                              | inr b' => @state_of_base_value B b'
                              end in
                   pair_state _ _ sta stb
           end.

      Fixpoint base_reify {t} : base_value t -> @expr var t
        := match t return base_value t -> expr t with
           | base.type.nat
             => fun v => expr.Ident (ident.Literal v)
           | base.type.prod A B
             => fun '(a, b)
                => let ea := match a with
                             | inl (st, e)
                               => match annotate _ st with
                                  | None => e
                                  | Some cst => 'cst @ e
                                  end%expr
                             | inr v => @base_reify _ v
                             end in
                   let eb := match b with
                             | inl (st, e)
                               => match annotate _ st with
                                  | None => e
                                  | Some cst => 'cst @ e
                                  end%expr
                             | inr v => @base_reify _ v
                             end in
                   ('ident.Pair @ ea @ eb)%expr
           end.

      Fixpoint intersect_state_base_value {t} : stateT' t -> base_value t -> base_value t
        := match t return stateT' t -> base_value t -> base_value t with
           | base.type.nat => update_literal_with_state
           | base.type.prod _ _
             => fun st '(a, b)
                => let sta := fst_state _ _ st in
                   let stb := snd_state _ _ st in
                   let a' := match a with
                             | inl (sta', e) => inl (intersect_state _ sta sta', e)
                             | inr v => inr (@intersect_state_base_value _ sta v)
                             end in
                   let b' := match b with
                             | inl (stb', e) => inl (intersect_state _ stb stb', e)
                             | inr v => inr (@intersect_state_base_value _ stb v)
                             end in
                   (a', b')
           end.


      Local Notation value := (@value base.type ident var base_value stateT').
      Local Notation stateT := (@stateT base.type stateT').

      Definition intersect_state_value {t} : stateT t -> value t -> value t
        := match t with
           | type.base t
             => fun st e
                => match e with
                   | inl (st', e) => inl (intersect_state _ st st', e)
                   | inr v => inr (intersect_state_base_value st v)
                   end
           | type.arrow s d => fun _ e => e
           end.

      Local Notation state_of_value := (@state_of_value base.type ident var base_value stateT' (@state_of_base_value)).
      Local Notation reify := (@reify base.type ident var base_value stateT' annotate bottom (@base_reify)).

      Definition interp {t} (idc : ident t) : value t
        := match idc in ident.ident t return value t with
           | ident.Literal v => inr v
           | ident.Plus
             => fun x'
                => Base
                     (fun y'
                      => Base
                           match x', y' with
                           | inr xv, inr yv => inr (xv + yv)
                           | _, _ => inl
                                       (add_state (@state_of_value base.type.nat x')
                                                  (@state_of_value base.type.nat y'),
                                        ('ident.Plus
                                           @ (@reify base.type.nat x')
                                           @ (@reify base.type.nat y'))%expr)
                           end)
           | ident.Pair A B
             => fun a'
                => Base
                     (fun b'
                      => Base
                           (inr (a', b')))
           | ident.Fst A B
             => fun x'
                => Base
                     match x' return value (type.base _) with
                     | inl (st, e) => inl (fst_state _ _ st, ('ident.Fst @ e)%expr)
                     | inr (a, b) => a
                     end
           | ident.Snd A B
             => fun x'
                => Base
                     match x' return value (type.base _) with
                     | inl (st, e) => inl (snd_state _ _ st, ('ident.Snd @ e)%expr)
                     | inr (a, b) => b
                     end
           | ident.Cast T bound
             => fun e'
                => Base (intersect_state_value (t:=T) (state_of_upperbound _ bound) e')
           end.

      Local Notation value_with_lets := (@value_with_lets base.type ident var base_value stateT').

      Definition eval {t} (e : @expr value_with_lets t) : @expr var t
        := @eval base.type ident var base_value stateT' annotate bottom (@state_of_base_value) (@base_reify) (@interp) t e.

      Definition eval_with_bound {s d} (e : @expr value_with_lets (s -> d))
                 (st : stateT s)
        : expr (s -> d)
        := @eval_with_bound base.type ident var base_value stateT' annotate bottom (@state_of_base_value) (@base_reify) (@interp) s d e st.
    End with_var.
  End ident.
End partial.

Section specialized.
  Local Notation stateT' := upperboundT.
  Local Notation stateT := (@partial.stateT base.type stateT').
  Notation expr := (@expr base.type ident).
  Local Notation type := (type base.type).
  Let type_base (x : base.type) : type := type.base x.
  Local Coercion type_base : base.type >-> type.
  Definition annotate t (st : stateT' t) : option (ident (t -> t))
    := Some (ident.Cast st).
  Fixpoint bottom T : stateT' T
    := match T return stateT' T with
       | base.type.nat => None
       | base.type.prod A B => (bottom _, bottom _)
       end.
  Definition add_state : stateT' base.type.nat -> stateT' base.type.nat -> stateT' base.type.nat
    := fun x y
       => match x, y with
          | Some x', Some y' => Some (x' + y')
          | _, _ => None
          end.
  Definition fst_state : forall A B : base.type, stateT' (A * B)%etype -> stateT' A
    := fun _ _ => @fst _ _.
  Definition snd_state : forall A B : base.type, stateT' (A * B)%etype -> stateT' B
    := fun _ _ => @snd _ _.
  Definition state_of_literal : nat -> stateT' base.type.nat
    := @Some _.
  Definition pair_state : forall A B, stateT' A -> stateT' B -> stateT' (base.type.prod A B)
    := fun _ _ => @pair _ _.
  Fixpoint intersect_state A : stateT' A -> stateT' A -> stateT' A
    := match A return stateT' A -> stateT' A -> stateT' A with
       | base.type.nat
         => fun x y
            => match x, y with
               | Some x', Some y' => Some (Nat.min x' y')
               | Some x', None | None, Some x' => Some x'
               | None, None => None
               end
       | base.type.prod A B
         => fun '(x, y) '(x', y') => (@intersect_state _ x x', @intersect_state _ y y')
       end.
  Axiom evil : nat -> nat.
  Definition update_literal_with_state : stateT' base.type.nat -> nat -> nat
    := fun upperbound n
       => match upperbound with
        | Some upperbound'
          => if Nat.leb n upperbound' then n else evil n
        | None => n
        end.
  Definition state_of_upperbound : forall T, upperboundT T -> stateT' T
    := fun _ x => x.

  Print partial.ident.eval.

  Definition eval {var} {t} (e : @expr _ t) : expr t
    := (@partial.ident.eval)
         var stateT' annotate add_state fst_state snd_state state_of_literal pair_state intersect_state update_literal_with_state state_of_upperbound bottom t e.
  Definition eval_with_bound {var} {s d} (e : @expr _ (s -> d)) (bound : stateT s) : expr (s -> d)
    := (@partial.ident.eval_with_bound)
         var stateT annotate add_state fst_state snd_state state_of_literal pair_state intersect_state update_literal_with_state state_of_upperbound bottom s d e bound.

  Import expr.
  Import ident.
  Compute eval ('Fst @ (expr_let x := `10 in ($x, $x)))%expr.

  Compute eval ((\ x , expr_let y := `5 in 'Fst @ $x + ('Fst @ $x + ($y + $y)))
                  @ (`1, `1))%expr.

  Compute eval ((\ x , expr_let y := `5 in $y + ($y + ('Fst @ $x + 'Snd @ $x)))
                  @ (`1, `7))%expr.


  Eval cbv in eval_with_bound
                (\z , ((\ x , expr_let y := `5 in $y + ($z + ('Fst @ $x + 'Snd @ $x)))
                         @ (`1, `7)))%expr
                (Some 100).
End specialized.

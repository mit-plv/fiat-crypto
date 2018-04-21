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
  Inductive type := nat | prod (A B : type) | arrow (s d : type).
End type.
Notation type := type.type.
Delimit Scope etype_scope with etype.
Bind Scope etype_scope with type.type.
Infix "->" := type.arrow : etype_scope.
Infix "*" := type.prod : etype_scope.


Fixpoint upperboundT (t : type) : Type
  := match t with
     | type.nat => option nat
     | type.prod A B => upperboundT A * upperboundT B
     | type.arrow s d => unit
     end.

Module expr.
  Section with_var.
    Context {var : type -> Type}.

    Inductive expr : type -> Type :=
    | Literal (v : nat) : expr type.nat
    | Var {t} (v : var t) : expr t
    | Plus (x y : expr type.nat) : expr type.nat
    | Abs {s d} (f : var s -> expr d) : expr (s -> d)
    | App {s d} (f : expr (s -> d)) (x : expr s) : expr d
    | Pair {A B} (a : expr A) (b : expr B) : expr (A * B)
    | Fst {A B} (x : expr (A * B)) : expr A
    | Snd {A B} (x : expr (A * B)) : expr B
    | LetIn {A B} (x : expr A) (f : var A -> expr B) : expr B
    | Cast {T} (upper_bound : upperboundT T) (e : expr T) : expr T
    .
  End with_var.

  Module Export Notations.
    Delimit Scope expr_scope with expr.
    Bind Scope expr_scope with expr.
    Infix "@" := App : expr_scope.
    Reserved Notation "\ x .. y , t" (at level 200, x binder, y binder, right associativity, format "\  x .. y , '//' t").
    Notation "\ x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "'λ' x .. y , f" := (Abs (fun x => .. (Abs (fun y => f%expr)) .. )) : expr_scope.
    Notation "( x , y , .. , z )" := (Pair .. (Pair x%expr y%expr) .. z%expr) : expr_scope.
    Notation "'expr_let' x := A 'in' b" := (LetIn A (fun x => b%expr)) : expr_scope.
    Infix "+" := Plus : expr_scope.
    Notation "' x" := (Literal x) (at level 9, format "' x") : expr_scope.
    Notation "'$' x" := (Var x) (at level 9, format "'$' x") : expr_scope.
  End Notations.
End expr.
Import expr.Notations.
Notation expr := expr.expr.

Module UnderLets.
  Section with_var.
    Context {var : type -> Type}.

    Inductive UnderLets {T : Type} :=
    | Base (v : T)
    | UnderLet {A} (x : @expr var A) (f : var A -> UnderLets).

    Fixpoint splice {A B} (x : @UnderLets A) (e : A -> @UnderLets B) : @UnderLets B
      := match x with
         | Base v => e v
         | UnderLet A x f => UnderLet x (fun v => @splice _ _ (f v) e)
         end.

    Fixpoint to_expr {t} (x : @UnderLets (@expr var t)) : @expr var t
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
    Context (var : type -> Type)
            (stateT : type -> Type)
            (cast : forall t, stateT t -> @expr var t -> @expr var t)
            (add_state : stateT type.nat -> stateT type.nat -> stateT type.nat)
            (fst_state : forall A B, stateT (type.prod A B) -> stateT A)
            (snd_state : forall A B, stateT (type.prod A B) -> stateT B)
            (state_of_literal : nat -> stateT type.nat)
            (pair_state : forall A B, stateT A -> stateT B -> stateT (type.prod A B))
            (intersect_state : forall A, stateT A -> stateT A -> stateT A)
            (update_literal_with_state : stateT type.nat -> nat -> nat)
            (state_of_upperbound : forall T, upperboundT T -> stateT T)
            (bottom : forall A, stateT A).

    Fixpoint value (t : type)
      := match t with
         | type.nat as t
           => stateT t * @expr var t + nat
         | type.prod A B as t
           => stateT t * @expr var t + value A * value B
         | type.arrow s d
           => value s -> UnderLets var (value d)
         end%type.
    Definition value_with_lets (t : type)
      := UnderLets var (value t).

    Fixpoint state_of_value {t} : value t -> stateT t
      := match t return value t -> stateT t with
         | type.nat
           => fun v
              => match v with
                 | inl (st, _) => st
                 | inr n => state_of_literal n
                 end
         | type.prod A B
           => fun v
              => match v with
                 | inl (st, _) => st
                 | inr (a, b)
                   => pair_state
                        _ _
                        (@state_of_value A a) (@state_of_value B b)
                 end
         | type.arrow s d => fun _ => bottom _
         end.

    Fixpoint reify {t} : value t -> @expr var t
      := match t return value t -> expr t with
         | type.nat
           => fun v
              => match v with
                 | inl (st, e) => cast _ st e
                 | inr n => expr.Literal n
                 end
         | type.prod A B
           => fun v
              => match v with
                 | inl (st, e) => cast _ st e
                 | inr (a, b)
                   => expr.Pair (@reify _ a) (@reify _ b)
                 end
         | type.arrow s d
           => fun f => λ x , (UnderLets.to_expr
                                (fx <-- f (@reflect _ (expr.Var x));
                                   Base (@reify _ fx)))
         end%core%expr
    with reflect {t} : @expr var t -> value t
         := match t return expr t -> value t with
            | type.nat
            | type.prod _ _
              => fun e => inl (bottom _, e)
            | type.arrow s d
              => fun e v
                 => Base (@reflect d (e @ (@reify s v)))%expr
            end.

    Definition put_state {t} : stateT t -> @expr var t -> value t
      := match t return stateT t -> expr t -> value t with
         | type.nat
         | type.prod _ _
           => fun st e => inl (st, e)
         | type.arrow s d
           => fun st e => reflect e
         end.

    Fixpoint intersect_state_value {t} : stateT t -> value t -> value t
      := match t return stateT t -> value t -> value t with
         | type.nat
           => fun st e
              => match e with
                 | inl (st', e) => inl (intersect_state _ st st', e)
                 | inr v => inr (update_literal_with_state st v)
                 end
         | type.prod _ _
           => fun st e
              => match e with
                 | inl (st', e) => inl (intersect_state _ st st', e)
                 | inr (a, b) => inr (@intersect_state_value _ (fst_state _ _ st) a,
                                      @intersect_state_value _ (snd_state _ _ st) b)
                 end
         | type.arrow s d
           => fun st e => e
         end.

    Fixpoint interp {t} (e : @expr value_with_lets t) : value_with_lets t
      := match e in expr.expr t return value_with_lets t with
         | expr.Literal v => Base (inr v)
         | expr.Var t v => v
         | expr.Plus x y
           => (x' <-- @interp _ x;
                 y' <-- @interp _ y;
                 Base (match x', y' with
                       | inr xv, inr yv => inr (xv + yv)
                       | _, _ => put_state
                                   (add_state (state_of_value x') (state_of_value y'))
                                   (expr.Plus (@reify type.nat x')
                                              (@reify type.nat y'))
                       end))
         | expr.Abs s d f => Base (fun x => @interp d (f (Base x)))
         | expr.App s d f x
           => (x' <-- @interp s x;
                 f' <-- @interp (s -> d)%etype f;
                 f' x')
         | expr.Pair A B a b
           => (a' <-- @interp A a;
                 b' <-- @interp B b;
                 Base (inr (a', b')))
         | expr.Fst A B x
           => (x' <-- @interp _ x;
                 Base match x' return value _ with
                      | inl (st, e) => put_state (fst_state _ _ st) (expr.Fst e)
                      | inr (a, b) => a
                      end)
         | expr.Snd A B x
           => (x' <-- @interp _ x;
                 Base match x' return value _ with
                      | inl (st, e) => put_state (snd_state _ _ st) (expr.Snd e)
                      | inr (a, b) => b
                      end)
         | expr.LetIn A B x f
           => (x' <-- @interp _ x;
                 UnderLet
                   (reify x')
                   (fun x'v
                    => @interp _ (f (Base (put_state (state_of_value x') (expr.Var x'v))))))
         | expr.Cast T bound e
           => (e' <-- @interp _ e;
                 Base (intersect_state_value (state_of_upperbound _ bound) e'))
         end%under_lets.

    Definition eval {t} (e : @expr value_with_lets t) : @expr var t
      := UnderLets.to_expr (e' <-- interp e; Base (reify e')).

    Definition eval_with_bound {s d} (e : @expr value_with_lets (s -> d))
               (st : stateT s)
      : @expr var (s -> d)
      := UnderLets.to_expr
           (e' <-- interp e;
              Base
                (expr.Abs
                   (fun x
                    => UnderLets.to_expr
                         (e'' <-- e' (put_state st (expr.Var x));
                            Base (reify e''))))).
  End with_var.
End partial.

Local Notation stateT := upperboundT.
Definition cast {var} t (st : stateT t) (e : @expr var t) : @expr var t
  := expr.Cast st e.
Fixpoint bottom T : stateT T
  := match T return stateT T with
     | type.nat => None
     | type.prod A B => (bottom _, bottom _)
     | type.arrow s d => tt
     end.
Definition add_state : stateT type.nat -> stateT type.nat -> stateT type.nat
  := fun x y
     => match x, y with
        | Some x', Some y' => Some (x' + y')
        | _, _ => None
        end.
Definition fst_state : forall A B : type, stateT (A * B)%etype -> stateT A
  := fun _ _ => @fst _ _.
Definition snd_state : forall A B : type, stateT (A * B)%etype -> stateT B
  := fun _ _ => @snd _ _.
Definition state_of_literal : nat -> stateT type.nat
  := @Some _.
Definition pair_state : forall A B, stateT A -> stateT B -> stateT (type.prod A B)
  := fun _ _ => @pair _ _.
Fixpoint intersect_state A : stateT A -> stateT A -> stateT A
  := match A return stateT A -> stateT A -> stateT A with
     | type.nat
       => fun x y
          => match x, y with
             | Some x', Some y' => Some (Nat.min x' y')
             | Some x', None | None, Some x' => Some x'
             | None, None => None
             end
     | type.prod A B
       => fun '(x, y) '(x', y') => (@intersect_state _ x x', @intersect_state _ y y')
     | type.arrow s d => fun _ _ => tt
     end.
Axiom evil : nat -> nat.
Definition update_literal_with_state : stateT type.nat -> nat -> nat
  := fun upperbound n
     => match upperbound with
        | Some upperbound'
          => if Nat.leb n upperbound' then n else evil n
        | None => n
        end.
Definition state_of_upperbound : forall T, upperboundT T -> stateT T
  := fun _ x => x.

Print partial.eval.

Definition eval {var} {t} (e : @expr _ t) : expr t
  := @partial.eval
              var stateT cast add_state fst_state snd_state state_of_literal pair_state intersect_state update_literal_with_state state_of_upperbound bottom t e.
Definition eval_with_bound {var} {s d} (e : @expr _ (s -> d)) (bound : stateT s) : expr (s -> d)
  := @partial.eval_with_bound
              var stateT cast add_state fst_state snd_state state_of_literal pair_state intersect_state update_literal_with_state state_of_upperbound bottom s d e bound.

Import expr.
Compute eval (Fst (LetIn (Literal 10) (fun x => Pair (Var x) (Var x)))).

Compute eval ((\ x , expr_let y := '5 in Fst $x + (Fst $x + ($y + $y)))
                @ ('1, '1))%expr.

Compute eval ((\ x , expr_let y := '5 in $y + ($y + (Fst $x + Snd $x)))
                @ ('1, '7))%expr.


Eval cbv in eval_with_bound
              (\z , ((\ x , expr_let y := '5 in $y + ($z + (Fst $x + Snd $x)))
                       @ ('1, '7)))%expr
              (Some 100).

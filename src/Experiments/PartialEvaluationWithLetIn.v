Require Import Crypto.Util.Notations.

Module type.
  Inductive type := nat | prod (A B : type) | arrow (s d : type).
End type.
Notation type := type.type.
Delimit Scope etype_scope with etype.
Bind Scope etype_scope with type.type.
Infix "->" := type.arrow : etype_scope.
Infix "*" := type.prod : etype_scope.

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
    Context (var : type -> Type).
    Definition value_step (value : type -> Type) (t : type)
      := match t with
         | type.nat as t
           => @expr var t + nat
         | type.prod A B as t
           => @expr var t + value A * value B
         | type.arrow s d
           => value s -> value d
         end%type.
    Fixpoint value' (t : type)
      := UnderLets var (value_step value' t).
    Definition value (t : type)
      := UnderLets var (value_step value' t).

    Coercion value'_of_value {t} (x : value t) : value' t. destruct t; exact x. Defined.
    Coercion value_of_value' {t} (x : value' t) : value t. destruct t; exact x. Defined.


    Fixpoint reify {t} : value t -> @expr var t
      := fun v
         => UnderLets.to_expr
              (v' <-- v;
                 Base
                   (match t return value_step value' t -> expr t with
                    | type.nat
                      => fun v''
                         => match v'' with
                            | inl e => e
                            | inr n => expr.Literal n
                            end
                    | type.prod A B
                      => fun v''
                         => match v'' with
                            | inl e => e
                            | inr (a, b)
                              => expr.Pair (@reify _ a) (@reify _ b)
                            end
                    | type.arrow s d
                      => fun f => λ x , @reify _ (f (@reflect _ (expr.Var x)))
                    end%core%expr v'))
    with reflect {t} : @expr var t -> value t
         := match t return expr t -> value t with
            | type.nat
            | type.prod _ _
              => fun e => Base (inl e)
            | type.arrow s d
              => fun e => Base (fun v : value' s
                                => (@reflect d (e @ (@reify s v)) : value' d))%expr
            end.

    Fixpoint interp {t} (e : @expr value t) : value t
      := match e in expr.expr t return value t with
         | expr.Literal v => Base (inr v)
         | expr.Var t v => v
         | expr.Plus x y
           => (x' <-- @interp _ x;
                 y' <-- @interp _ y;
                 Base (match x', y' with
                       | inr xv, inr yv => inr (xv + yv)
                       | _, _ => inl (expr.Plus (@reify type.nat (Base x'))
                                                (@reify type.nat (Base y')))
                       end))
         | expr.Abs s d f => Base (fun x : value' _ => value'_of_value (@interp d (f x)))
         | expr.App s d f x
           => (x' <-- @interp s x;
                 f' <-- @interp (s -> d)%etype f;
                 (f' (Base x' : value s) : value d))
         | expr.Pair A B a b
           => (a' <-- @interp A a;
                 b' <-- @interp B b;
                 Base (inr (value'_of_value (Base a'),
                            value'_of_value (Base b'))))
         | expr.Fst A B x
           => (x' <-- @interp _ x;
                 match x' return value _ with
                 | inl e => @reflect _ (expr.Fst e)
                 | inr (a, b) => a
                 end)
         | expr.Snd A B x
           => (x' <-- @interp _ x;
                 match x' return value _ with
                 | inl e => @reflect _ (expr.Snd e)
                 | inr (a, b) => b
                 end)
         | expr.LetIn A B x f
           => (x' <-- @interp _ x;
                 UnderLet
                   (reify (Base x'))
                   (fun x'v
                    => @interp _ (f (reflect (expr.Var x'v)))))
         end%under_lets.

    Definition eval {t} (e : @expr value t) : @expr var t
      := reify (interp e).
  End with_var.
End partial.

Import expr.
Compute partial.eval _ (Fst (LetIn (Literal 10) (fun x => Pair (Var x) (Var x)))).

Compute partial.eval _ ((\ x , expr_let y := '5 in Fst $x + (Fst $x + ($y + $y)))
                          @ ('1, '1))%expr.

Compute partial.eval _ ((\ x , expr_let y := '5 in $y + ($y + (Fst $x + Snd $x)))
                          @ ('1, '7))%expr.


Eval cbv in partial.eval _ (\z , ((\ x , expr_let y := '5 in $y + ($z + (Fst $x + Snd $x)))
                          @ ('1, '7)))%expr.

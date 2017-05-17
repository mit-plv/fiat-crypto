(** * Named Representation of Gallina *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Delimit Scope nexpr_scope with nexpr.
Module Export Named.
  Section language.
    Context (base_type_code : Type)
            (interp_base_type : base_type_code -> Type)
            (op : flat_type base_type_code -> flat_type base_type_code -> Type)
            (Name : Type).

    Local Notation flat_type := (flat_type base_type_code).
    Local Notation type := (type base_type_code).
    Local Notation interp_type := (interp_type interp_base_type).
    Local Notation interp_flat_type_gen := interp_flat_type.
    Local Notation interp_flat_type := (interp_flat_type interp_base_type).

    Inductive exprf : flat_type -> Type :=
    | TT : exprf Unit
    | Var {t : base_type_code} : Name -> exprf (Tbase t)
    | Op {t1 tR} : op t1 tR -> exprf t1 -> exprf tR
    | LetIn : forall {tx}, interp_flat_type_gen (fun _ => Name) tx -> exprf tx -> forall {tC}, exprf tC -> exprf tC
    | Pair : forall {t1}, exprf t1 -> forall {t2}, exprf t2 -> exprf (Prod t1 t2).
    Bind Scope nexpr_scope with exprf.
    Inductive expr : type -> Type :=
    | Abs {src dst} : interp_flat_type_gen (fun _ => Name) src -> exprf dst -> expr (Arrow src dst).
    Bind Scope nexpr_scope with expr.
    Definition Abs_name {t} (e : expr t) : interp_flat_type_gen (fun _ => Name) (domain t)
      := match e with Abs _ _ n f => n end.
    Definition invert_Abs {t} (e : expr t) : exprf (codomain t)
      := match e with Abs _ _ n f => f end.

    Section with_val_context.
      Context (Context : Context Name interp_base_type)
              (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Fixpoint interpf
               {t} (ctx : Context) (e : exprf t)
        : option (interp_flat_type t)
        := match e in exprf t return option (interp_flat_type t) with
           | Var t' x => lookupb t' ctx x
           | TT => Some tt
           | Pair _ ex _ ey
             => match @interpf _ ctx ex, @interpf _ ctx ey with
                | Some xv, Some yv => Some (xv, yv)%core
                | None, _ | _, None => None
                end
           | Op _ _ opc args
             => option_map (@interp_op _ _ opc) (@interpf _ ctx args)
           | LetIn _ n ex _ eC
             => match @interpf _ ctx ex with
                | Some xv
                  => dlet x := xv in
                     @interpf _ (extend ctx n x) eC
                | None => None
                end
           end.

      Definition interp {t} (ctx : Context) (e : expr t)
        : interp_flat_type (domain t) -> option (interp_flat_type (codomain t))
        := fun v => @interpf _ (extend ctx (Abs_name e) v) (invert_Abs e).

      Definition Interp {t} (e : expr t)
        : interp_flat_type (domain t) -> option (interp_flat_type (codomain t))
        := interp empty e.
    End with_val_context.
  End language.
End Named.

Global Arguments TT {_ _ _}.
Global Arguments Var {_ _ _ _} _.
Global Arguments Op {_ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _} _ _ _ {_} _.
Global Arguments Pair {_ _ _ _} _ {_} _.
Global Arguments Abs {_ _ _ _ _} _ _.
Global Arguments invert_Abs {_ _ _ _} _.
Global Arguments Abs_name {_ _ _ _} _.
Global Arguments interpf {_ _ _ _ _ interp_op t ctx} _.
Global Arguments interp {_ _ _ _ _ interp_op t ctx} _ _.
Global Arguments Interp {_ _ _ _ _ interp_op t} _ _.

Notation "'nlet' x := A 'in' b" := (LetIn _ x A%nexpr b%nexpr) : nexpr_scope.
Notation "'nlet' x : tx := A 'in' b" := (LetIn tx%ctype x%core A%nexpr b%nexpr) : nexpr_scope.
Notation "'λn'  x .. y , t" := (Abs x .. (Abs y t%nexpr) .. ) : nexpr_scope.
Notation "( x , y , .. , z )" := (Pair .. (Pair x%nexpr y%nexpr) .. z%nexpr) : nexpr_scope.
Notation "()" := TT : nexpr_scope.

(** * Named Representation of Gallina *)
Require Import Coq.Classes.RelationClasses.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Tuple.
(*Require Import Crypto.Util.Tactics.*)
Require Import Crypto.Util.Notations.
Require Import Crypto.Util.LetIn.

Record Context {base_type_code} (Name : Type) (var : base_type_code -> Type) :=
  { ContextT : Type;
    lookupb : ContextT -> Name -> forall {t : base_type_code}, option (var t);
    extendb : ContextT -> Name -> forall {t : base_type_code}, var t -> ContextT;
    removeb : ContextT -> Name -> base_type_code -> ContextT;
    empty : ContextT }.
Coercion ContextT : Context >-> Sortclass.
Arguments ContextT {_ _ _ _}, {_ _ _} _.
Arguments lookupb {_ _ _ _} _ _ {_}, {_ _ _ _} _ _ _.
Arguments extendb {_ _ _ _} _ _ [_] _.
Arguments removeb {_ _ _ _} _ _ _.
Arguments empty {_ _ _ _}.

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

    Section with_context.
      Context {var : base_type_code -> Type}
              {Context : Context Name var}.

      Fixpoint extend (ctx : Context) {t : flat_type}
               (n : interp_flat_type_gen (fun _ => Name) t) (v : interp_flat_type_gen var t)
        : Context
        := match t return interp_flat_type_gen (fun _ => Name) t -> interp_flat_type_gen var t -> Context with
           | Tbase t => fun n v => extendb ctx n v
           | Unit => fun _ _ => ctx
           | Prod A B => fun n v
                         => let ctx := @extend ctx A (fst n) (fst v) in
                            let ctx := @extend ctx B (snd n) (snd v) in
                            ctx
           end n v.

      Fixpoint remove (ctx : Context) {t : flat_type}
               (n : interp_flat_type_gen (fun _ => Name) t)
        : Context
        := match t return interp_flat_type_gen (fun _ => Name) t -> Context with
           | Tbase t => fun n => removeb ctx n t
           | Unit => fun _ => ctx
           | Prod A B => fun n
                         => let ctx := @remove ctx A (fst n) in
                            let ctx := @remove ctx B (snd n) in
                            ctx
           end n.

      Definition lookup (ctx : Context) {t}
        : interp_flat_type_gen (fun _ => Name) t -> option (interp_flat_type_gen var t)
        := smart_interp_flat_map
             (g := fun t => option (interp_flat_type_gen var t))
             (fun t v => lookupb ctx v)
             (Some tt)
             (fun A B x y => match x, y with
                             | Some x', Some y' => Some (x', y')%core
                             | _, _ => None
                             end).
    End with_context.

    Section with_val_context.
      Context (Context : Context Name interp_base_type)
              (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Fixpoint interpf
               (ctx : Context) {t} (e : exprf t)
        : option (interp_flat_type t)
        := match e in exprf t return option (interp_flat_type t) with
           | Var t' x => lookupb ctx x t'
           | TT => Some tt
           | Pair _ ex _ ey
             => match @interpf ctx _ ex, @interpf ctx _ ey with
                | Some xv, Some yv => Some (xv, yv)%core
                | None, _ | _, None => None
                end
           | Op _ _ opc args
             => option_map (@interp_op _ _ opc) (@interpf ctx _ args)
           | LetIn _ n ex _ eC
             => match @interpf ctx _ ex with
                | Some xv
                  => dlet x := xv in
                     @interpf (extend ctx n x) _ eC
                | None => None
                end
           end.

      Definition interp (ctx : Context) {t} (e : expr t)
        : interp_flat_type (domain t) -> option (interp_flat_type (codomain t))
        := fun v => @interpf (extend ctx (Abs_name e) v) _ (invert_Abs e).
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
Global Arguments extend {_ _ _ _} ctx {_} _ _.
Global Arguments remove {_ _ _ _} ctx {_} _.
Global Arguments lookup {_ _ _ _} ctx {_} _, {_ _ _ _} ctx _ _.
Global Arguments interpf {_ _ _ _ _ interp_op ctx t} _.
Global Arguments interp {_ _ _ _ _ interp_op ctx t} _ _.

Notation "'slet' x := A 'in' b" := (LetIn _ x A%nexpr b%nexpr) : nexpr_scope.
Notation "'λn'  x .. y , t" := (Abs x .. (Abs y t%nexpr) .. ) : nexpr_scope.
Notation "( x , y , .. , z )" := (Pair .. (Pair x%nexpr y%nexpr) .. z%nexpr) : nexpr_scope.
Notation "()" := TT : nexpr_scope.

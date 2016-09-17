(** * Named Representation of Gallina *)
Require Import Coq.Classes.RelationClasses.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Class Context {base_type_code} (Name : Type) (var : base_type_code -> Type) :=
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
    Let Tbase := @Tbase base_type_code.
    Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
    Local Notation interp_type := (interp_type interp_base_type).
    Local Notation interp_flat_type := (interp_flat_type_gen interp_base_type).


    Section expr_param.
      Section expr.
        Inductive exprf : flat_type -> Type :=
        | Const {t : flat_type} : interp_type t -> exprf t
        | Var {t : base_type_code} : Name -> exprf t
        | Op {t1 tR} : op t1 tR -> exprf t1 -> exprf tR
        | LetIn : forall {tx}, interp_flat_type_gen (fun _ => Name) tx -> exprf tx -> forall {tC}, exprf tC -> exprf tC
        | Pair : forall {t1}, exprf t1 -> forall {t2}, exprf t2 -> exprf (Prod t1 t2).
        Bind Scope nexpr_scope with exprf.
        Inductive expr : type -> Type :=
        | Return {t} : exprf t -> expr t
        | Abs {src dst} : Name -> expr dst -> expr (Arrow src dst).
        Bind Scope nexpr_scope with expr.
        Global Coercion Return : exprf >-> expr.
        (** [SmartVar] is like [Var], except that it inserts
          pair-projections and [Pair] as necessary to handle
          [flat_type], and not just [base_type_code] *)
        Definition SmartVar {t} : interp_flat_type_gen (fun _ => Name) t -> exprf t
          := smart_interp_flat_map (f:=fun _ => Name) (g:=exprf) _ (fun t => Var) (fun A B x y => Pair x y).
        Definition SmartConst {t} : interp_flat_type t -> @interp_flat_type_gen base_type_code exprf t
          := smart_interp_flat_map (g:=@interp_flat_type_gen base_type_code exprf) _ (fun t => Const (t:=t)) (fun A B x y => pair x y).
      End expr.

      Section with_context.
        Context {var : base_type_code -> Type}
                {Context : Context Name var}.

        Fixpoint extend (ctx : Context) {t : flat_type}
                 (n : interp_flat_type_gen (fun _ => Name) t) (v : interp_flat_type_gen var t)
          : Context
          := match t return interp_flat_type_gen (fun _ => Name) t -> interp_flat_type_gen var t -> Context with
             | Syntax.Tbase t => fun n v => extendb ctx n v
             | Prod A B => fun n v
                           => let ctx := @extend ctx A (fst n) (fst v) in
                              let ctx := @extend ctx B (snd n) (snd v) in
                              ctx
             end n v.

        Fixpoint remove (ctx : Context) {t : flat_type}
                 (n : interp_flat_type_gen (fun _ => Name) t)
          : Context
          := match t return interp_flat_type_gen (fun _ => Name) t -> Context with
             | Syntax.Tbase t => fun n => removeb ctx n t
             | Prod A B => fun n
                           => let ctx := @remove ctx A (fst n) in
                              let ctx := @remove ctx B (snd n) in
                              ctx
             end n.

        Definition lookup (ctx : Context) {t}
          : interp_flat_type_gen (fun _ => Name) t -> option (interp_flat_type_gen var t)
          := smart_interp_flat_map
               base_type_code
               (g := fun t => option (interp_flat_type_gen var t))
               (fun t v => lookupb ctx v)
               (fun A B x y => match x, y with
                               | Some x', Some y' => Some (x', y')%core
                               | _, _ => None
                               end).

        Section wf.
          Fixpoint wff (ctx : Context) {t} (e : exprf t) : option pointed_Prop
            := match e with
               | Const _ x => Some trivial
               | Var t n => match lookupb ctx n t return bool with
                            | Some _ => true
                            | None => false
                            end
               | Op _ _ op args => @wff ctx _ args
               | LetIn _ n ex _ eC => @wff ctx _ ex /\ inject (forall v, prop_of_option (@wff (extend ctx n v) _ eC))
               | Pair _ ex _ ey => @wff ctx _ ex /\ @wff ctx _ ey
               end%option_pointed_prop.

          Fixpoint wf (ctx : Context) {t} (e : expr t) : Prop
            := match e with
               | Return _ x => prop_of_option (wff ctx x)
               | Abs src _ n f => forall v, @wf (extend ctx (t:=src) n v) _ f
               end.
        End wf.

        Section interp_gen.
          Context (output_interp_flat_type : flat_type -> Type)
                  (interp_const : forall t, interp_flat_type t -> output_interp_flat_type t)
                  (interp_var : forall t, var t -> output_interp_flat_type t)
                  (interp_op : forall src dst, op src dst -> output_interp_flat_type src -> output_interp_flat_type dst)
                  (interp_let : forall (tx : flat_type) (ex : output_interp_flat_type tx)
                                       tC (eC : interp_flat_type_gen var tx -> output_interp_flat_type tC),
                      output_interp_flat_type tC)
                  (interp_pair : forall (tx : flat_type) (ex : output_interp_flat_type tx)
                                        (ty : flat_type) (ey : output_interp_flat_type ty),
                      output_interp_flat_type (Prod tx ty)).

          Fixpoint interp_genf (ctx : Context) {t} (e : exprf t)
            : prop_of_option (wff ctx e) -> output_interp_flat_type t
            := match e in exprf t return prop_of_option (wff ctx e) -> output_interp_flat_type t with
               | Const _ x => fun _ => interp_const _ x
               | Var t' x => match lookupb ctx x t' as v
                                   return prop_of_option (match v return bool with
                                                          | Some _ => true
                                                          | None => false
                                                          end)
                                          -> output_interp_flat_type t'
                             with
                             | Some v => fun _ => interp_var _ v
                             | None => fun bad => match bad : False with end
                             end
               | Op _ _ op args => fun good => @interp_op _ _ op (@interp_genf ctx _ args good)
               | LetIn _ n ex _ eC => fun good => let goodxC := proj1 (@prop_of_option_and _ _) good in
                                                  let x := @interp_genf ctx _ ex (proj1 goodxC) in
                                                  interp_let _ x _ (fun x => @interp_genf (extend ctx n x) _ eC (proj2 goodxC x))
               | Pair _ ex _ ey => fun good => let goodxy := proj1 (@prop_of_option_and _ _) good in
                                               let x := @interp_genf ctx _ ex (proj1 goodxy) in
                                               let y := @interp_genf ctx _ ey (proj2 goodxy) in
                                               interp_pair _ x _ y
               end.
        End interp_gen.
      End with_context.

      Section with_val_context.
        Context (Context : Context Name interp_base_type)
                (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).
        Definition interpf
          : forall (ctx : Context) {t} (e : exprf t),
            prop_of_option (wff ctx e) -> interp_flat_type t
          := @interp_genf
               interp_base_type Context interp_flat_type
               (fun _ x => x) (fun _ x => x) interp_op (fun _ y _ f => let x := y in f x)
               (fun _ x _ y => (x, y)%core).

        Fixpoint interp (ctx : Context) {t} (e : expr t)
          : wf ctx e -> interp_type t
          := match e in expr t return wf ctx e -> interp_type t with
             | Return _ x => interpf ctx x
             | Abs _ _ n f => fun good v => @interp _ _ f (good v)
             end.
      End with_val_context.
    End expr_param.
  End language.
End Named.

Global Arguments Const {_ _ _ _ _} _.
Global Arguments Var {_ _ _ _ _} _.
Global Arguments SmartVar {_ _ _ _ _} _.
Global Arguments SmartConst {_ _ _ _ _} _.
Global Arguments Op {_ _ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _} _ {_} _ {_} _.
Global Arguments Pair {_ _ _ _ _} _ {_} _.
Global Arguments Return {_ _ _ _ _} _.
Global Arguments Abs {_ _ _ _ _ _} _ _.
Global Arguments extend {_ _ _ _} ctx {_} _ _.
Global Arguments remove {_ _ _ _} ctx {_} _.
Global Arguments lookup {_ _ _ _} ctx {_} _, {_ _ _ _} ctx _ _.
Global Arguments wff {_ _ _ _ _ _} ctx {t} _.
Global Arguments wf {_ _ _ _ _ _} ctx {t} _.
Global Arguments interp_genf {_ _ _ _ var _} _ _ _ _ _ _ {ctx t} _ _.
Global Arguments interpf {_ _ _ _ _ interp_op ctx t} _ _.
Global Arguments interp {_ _ _ _ _ interp_op ctx t} _ _.

Notation "'slet' x := A 'in' b" := (LetIn _ x A%nexpr b%nexpr) : nexpr_scope.
Notation "'λn'  x .. y , t" := (Abs x .. (Abs y t%nexpr) .. ) : nexpr_scope.
Notation "( x , y , .. , z )" := (Pair .. (Pair x%nexpr y%nexpr) .. z%nexpr) : nexpr_scope.

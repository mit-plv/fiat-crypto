(** * Named Representation of Gallina *)
Require Import Crypto.Util.Notations.

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
Record ContextOk {base_type_code Name var} (Context : @Context base_type_code Name var) :=
  { lookupb_extendb_Some
    : forall (ctx : Context) n n' t t' v v',
      lookupb (extendb ctx n (t:=t) v) n' t' = Some v'
      <-> ((n = n' /\ exists pf : t = t',
               eq_rect _ var v _ pf = v')
           \/ (n <> n' /\ lookupb ctx n' t' = Some v'));
    lookupb_extendb_None
    : forall (ctx : Context) n n' t t' v,
        lookupb (extendb ctx n (t:=t) v) n' t' = None
        <-> ((n = n' /\ t <> t')
             \/ (n <> n' /\ lookupb ctx n' t' = None));
    lookupb_removeb : forall (ctx : Context) n n' t t', n <> n' -> lookupb (removeb ctx n t) n' t'
                                                                   = lookupb ctx n' t';
    lookupb_empty : forall n t, lookupb (@empty _ _ _ Context) n t = None }.

Delimit Scope nexpr_scope with nexpr.
Module Export Named.
  Section language.
    Context (base_type_code : Type)
            (op : base_type_code -> base_type_code -> base_type_code -> Type)
            (interp_base_type : base_type_code -> Type)
            (Name : Type).

    Inductive exprf : base_type_code -> Type :=
    | Var {t} : Name -> exprf t
    | BinOp {t1 t2 tR} (_:op t1 t2 tR) : exprf t1 -> exprf t2 -> exprf tR
    | LetIn : forall {tx}, Name -> exprf tx -> forall {tC}, exprf tC -> exprf tC.
    Bind Scope nexpr_scope with exprf.

    Section with_context_interp.
      Context (Context : Context Name interp_base_type)
              (interp_op : forall src1 src2 dst, op src1 src2 dst -> interp_base_type src1 -> interp_base_type src2 -> interp_base_type dst).

      Fixpoint interpf
               (ctx : Context) {t} (e : exprf t)
        : option (interp_base_type t)
        := match e in exprf t return option (interp_base_type t) with
           | Var t' x => lookupb ctx x t'
           | BinOp _ _ _ o arg1 arg2
             => match @interpf ctx _ arg1, @interpf ctx _ arg2 with
                | Some a1, Some a2 => Some (@interp_op _ _ _ o a1 a2)
                | None, _ | _, None => None
                end
           | LetIn _ n ex _ eC
             => match @interpf ctx _ ex with
                | Some xv
                  => let x := xv in
                     @interpf (extendb ctx n x) _ eC
                | None => None
                end
           end.
    End with_context_interp.
  End language.
End Named.

Global Arguments Var {_ _ _ _} _.
Global Arguments BinOp {_ _ _ _ _ _} _ _ _.
Global Arguments LetIn {_ _ _ _} _ _ {_} _.
Global Arguments interpf {_ _ _ _ _ interp_op ctx t} _.

Notation "'slet' x := A 'in' b" := (LetIn _ x A%nexpr b%nexpr) : nexpr_scope.

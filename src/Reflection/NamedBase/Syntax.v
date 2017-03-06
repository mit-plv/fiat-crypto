(** * Named Representation of Gallina *)
Require Import Crypto.Util.PointedProp.
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

Delimit Scope nexpr_scope with nexpr.
Module Export Named.
  Section language.
    Context (base_type_code : Type)
            (interp_base_type : base_type_code -> Type)
            (Name : Type).

    Inductive exprf : base_type_code -> Type :=
    | Var {t} : Name -> exprf t
    | BinOp {t1 t2 tR} : exprf t1 -> exprf t2 -> exprf tR
    | LetIn : forall {tx}, Name -> exprf tx -> forall {tC}, exprf tC -> exprf tC.
    Bind Scope nexpr_scope with exprf.

    Section with_context_interp.
      Context (Context : Context Name interp_base_type)
              (interp_op : forall src1 src2 dst, interp_base_type src1 -> interp_base_type src2 -> interp_base_type dst).

      Fixpoint interpf
               (ctx : Context) {t} (e : exprf t)
        : option (interp_base_type t)
        := match e in exprf t return option (interp_base_type t) with
           | Var t' x => lookupb ctx x t'
           | BinOp _ _ _ arg1 arg2
             => match @interpf ctx _ arg1, @interpf ctx _ arg1 with
                | Some a1, Some a2 => Some (@interp_op _ _ _ a1 a2)
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

    Section with_context.
      Context {var : base_type_code -> Type}
              {Context : Context Name var}.

      Fixpoint wff (ctx : Context) {t} (e : exprf t) : option pointed_Prop
        := match e with
           | Var t n => match lookupb ctx n t return bool with
                        | Some _ => true
                        | None => false
                        end
           | BinOp _ _ _ arg1 arg2
             => @wff ctx _ arg1 /\ @wff ctx _ arg2
           | LetIn tx n ex _ eC
             => @wff ctx _ ex
                /\ inject (forall v, prop_of_option (@wff (extendb (t:=tx) ctx n v) _ eC))
           end%option_pointed_prop.

      Section interp_gen.
          Context (output_interp_base_type : base_type_code -> Type)
                  (interp_var : forall t, var t -> output_interp_base_type t)
                  (interp_op : forall src1 src2 dst, output_interp_base_type src1 -> output_interp_base_type src2 -> output_interp_base_type dst)
                  (interp_let : forall tx (ex : output_interp_base_type tx)
                                       tC (eC : var tx -> output_interp_base_type tC),
                      output_interp_base_type tC).

          Fixpoint interp_genf (ctx : Context) {t} (e : exprf t)
            : prop_of_option (wff ctx e) -> output_interp_base_type t
            := match e in exprf t return prop_of_option (wff ctx e) -> output_interp_base_type t with
               | Var t' x => match lookupb ctx x t' as v
                                   return prop_of_option (match v return bool with
                                                          | Some _ => true
                                                          | None => false
                                                          end)
                                          -> output_interp_base_type t'
                             with
                             | Some v => fun _ => interp_var _ v
                             | None => fun bad => match bad : False with end
                             end
               | BinOp _ _ _ arg1 arg2
                 => fun good
                    => let good12 := proj1 (@prop_of_option_and _ _) good in
                       @interp_op _ _ _
                                  (@interp_genf ctx _ arg1 (proj1 good12))
                                  (@interp_genf ctx _ arg2 (proj2 good12))
               | LetIn _ n ex _ eC => fun good => let goodxC := proj1 (@prop_of_option_and _ _) good in
                                                  let x := @interp_genf ctx _ ex (proj1 goodxC) in
                                                  interp_let _ x _ (fun x => @interp_genf (extendb ctx n x) _ eC (proj2 goodxC x))
               end.
      End interp_gen.
    End with_context.
  End language.
End Named.

Global Arguments Var {_ _ _} _.
Global Arguments BinOp {_ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _} _ _ {_} _.
Global Arguments wff {_ _ _ _} ctx {t} _.
Global Arguments interp_genf {_ _ var _} _ _ _ _ {ctx t} _ _.
Global Arguments interpf {_ _ _ _ interp_op ctx t} _.

Notation "'slet' x := A 'in' b" := (LetIn _ x A%nexpr b%nexpr) : nexpr_scope.

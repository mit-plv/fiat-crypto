(** * PHOAS Representation of Gallina, in [Set] *)
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Notations.
Require Import Crypto.Compilers.Syntax.

(** Universes are annoying.  See, e.g.,
    [bug#5996](https://github.com/coq/coq/issues/5996), where using
    [pattern] and [constr:(...)] to replace [Set] with [Type] breaks
    things.  Because we need to get reflective syntax by patterning [Z
    : Set], we make a version of [exprf] in [Set].  We build the
    minimial infrastructure needed to get this sort of expression into
    the [Type]-based one. *)

Delimit Scope set_expr_scope with set_expr.
Local Open Scope set_expr_scope.
Section language.
  Context (base_type_code : Set).

  Local Notation flat_type := (flat_type base_type_code).

  Let Tbase' := @Tbase base_type_code.
  Local Coercion Tbase' : base_type_code >-> flat_type.

  Section interp.
    Context (interp_base_type : base_type_code -> Set).
    Fixpoint interp_flat_type (t : flat_type) :=
      match t with
      | Tbase t => interp_base_type t
      | Unit => unit
      | Prod x y => prod (interp_flat_type x) (interp_flat_type y)
      end.
  End interp.

  Section expr_param.
    Context (interp_base_type : base_type_code -> Set).
    Context (op : flat_type (* input tuple *) -> flat_type (* output type *) -> Set).
    Local Notation interp_flat_type_gen := interp_flat_type.
    Local Notation interp_flat_type := (interp_flat_type interp_base_type).
    Section expr.
      Context {var : base_type_code -> Set}.

      Inductive exprf : flat_type -> Set :=
      | TT : exprf Unit
      | Var {t} (v : var t) : exprf t
      | Op {t1 tR} (opc : op t1 tR) (args : exprf t1) : exprf tR
      | LetIn {tx} (ex : exprf tx) {tC} (eC : interp_flat_type_gen var tx -> exprf tC) : exprf tC
      | Pair {tx} (ex : exprf tx) {ty} (ey : exprf ty) : exprf (Prod tx ty).
      Bind Scope set_expr_scope with exprf.
    End expr.

    Section interp.
      Context (interp_op : forall src dst, op src dst -> interp_flat_type src -> interp_flat_type dst).

      Definition interpf_step
                 (interpf : forall {t} (e : @exprf interp_flat_type t), interp_flat_type t)
                 {t} (e : @exprf interp_flat_type t) : interp_flat_type t
        := match e in exprf t return interp_flat_type t with
           | TT => tt
           | Var _ x => x
           | Op _ _ op args => @interp_op _ _ op (@interpf _ args)
           | LetIn _ ex _ eC => dlet x := @interpf _ ex in @interpf _ (eC x)
           | Pair _ ex _ ey => (@interpf _ ex, @interpf _ ey)
           end.

      Fixpoint interpf {t} e
        := @interpf_step (@interpf) t e.
    End interp.
  End expr_param.
End language.
Global Arguments Var {_ _ _ _} _.
Global Arguments TT {_ _ _}.
Global Arguments Op {_ _ _ _ _} _ _.
Global Arguments LetIn {_ _ _ _} _ {_} _.
Global Arguments Pair {_ _ _ _} _ {_} _.
Global Arguments Abs {_ _ _ _ _} _.
Global Arguments interp_flat_type {_} _ _.
Global Arguments interpf {_ _ _} interp_op {t} _.

Module Export Notations.
  Notation "'slet' x .. y := A 'in' b" := (LetIn A%set_expr (fun x => .. (fun y => b%set_expr) .. )) : set_expr_scope.
  Notation "( x , y , .. , z )" := (Pair .. (Pair x%set_expr y%set_expr) .. z%set_expr) : set_expr_scope.
  Notation "( )" := TT : set_expr_scope.
  Notation "()" := TT : set_expr_scope.
End Notations.

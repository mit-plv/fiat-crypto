(** * Changing the interp function on PHOAS Representation of Gallina *)
Require Import Coq.Strings.String Coq.Classes.RelationClasses.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Notations.

Local Open Scope ctype_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code : Type}
          {interp_base_type1 interp_base_type2 : base_type_code -> Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (f : forall t, interp_base_type1 t -> interp_base_type2 t).

  Section with_var.
    Context {var : base_type_code -> Type}.

    Fixpoint mapf_interp {t} (e : @exprf base_type_code interp_base_type1 op var t)
      : @exprf base_type_code interp_base_type2 op var t
      := match e in exprf _ _ _ t return exprf _ _ _ t with
         | Const tx x => Const (mapf_interp_flat_type_gen _ f x)
         | Var _ x => Var x
         | Op _ _ op args => Op op (@mapf_interp _ args)
         | LetIn _ ex _ eC => LetIn (@mapf_interp _ ex) (fun x => @mapf_interp _ (eC x))
         | Pair _ ex _ ey => Pair (@mapf_interp _ ex) (@mapf_interp _ ey)
         end.

    Fixpoint map_interp {t} (e : @expr base_type_code interp_base_type1 op var t)
      : @expr base_type_code interp_base_type2 op var t
      := match e in expr _ _ _ t return expr _ _ _ t with
         | Return _ x => Return (mapf_interp x)
         | Abs _ _ f => Abs (fun x => @map_interp _ (f x))
         end.
  End with_var.

  Definition MapInterp {t} (e : @Expr base_type_code interp_base_type1 op t)
    : @Expr base_type_code interp_base_type2 op t
    := fun var => map_interp (e _).
End language.
Global Arguments mapf_interp {_ _ _ _} f {_ t} e.
Global Arguments map_interp {_ _ _ _} f {_ t} e.
Global Arguments MapInterp {_ _ _ _} f {t} e _.

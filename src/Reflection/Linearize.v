(** * Linearize: Place all and only operations in let binders *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.Tactics.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation Tbase := (@Tbase base_type_code).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}.
    Local Notation exprf := (@exprf base_type_code op var).
    Local Notation expr := (@expr base_type_code op var).

    Section under_lets.
      Fixpoint under_letsf {t} (e : exprf t)
        : forall {tC} (C : interp_flat_type var t -> exprf tC), exprf tC
        := match e in Syntax.exprf _ _ t return forall {tC} (C : interp_flat_type var t -> exprf tC), exprf tC with
           | LetIn _ ex _ eC
             => fun _ C => @under_letsf _ ex _ (fun v => @under_letsf _ (eC v) _ C)
           | TT => fun _ C => C tt
           | Var _ x => fun _ C => C x
           | Op _ _ op args as e => fun _ C => LetIn e C
           | Pair A x B y => fun _ C => @under_letsf A x _ (fun x =>
                                        @under_letsf B y _ (fun y =>
                                        C (x, y)))
           end.
    End under_lets.

    Fixpoint linearizef {t} (e : exprf t) : exprf t
      := match e in Syntax.exprf _ _ t return exprf t with
         | LetIn _ ex _ eC
           => under_letsf (@linearizef _ ex) (fun x => @linearizef _ (eC x))
         | TT => TT
         | Var _ x => Var x
         | Op _ _ op args
           => under_letsf (@linearizef _ args) (fun args => LetIn (Op op (SmartVarf args)) SmartVarf)
         | Pair A ex B ey
           => under_letsf (@linearizef _ ex) (fun x =>
              under_letsf (@linearizef _ ey) (fun y =>
              SmartVarf (t:=Prod A B) (x, y)))
         end.

    Definition linearize {t} (e : expr t) : expr t
      := match e in Syntax.expr _ _ t return expr t with
         | Abs _ _ f => Abs (fun x => linearizef (f x))
         end.
  End with_var.

  Definition Linearize {t} (e : Expr t) : Expr t
    := fun var => linearize (e _).
End language.

Global Arguments under_letsf {_ _ _ _} _ {tC} _.
Global Arguments linearizef {_ _ _ _} _.
Global Arguments linearize {_ _ _ _} _.
Global Arguments Linearize {_ _ _} _ var.

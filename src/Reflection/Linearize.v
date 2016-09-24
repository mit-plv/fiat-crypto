(** * Linearize: Place all and only operations in let binders *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Tactics.

Local Open Scope ctype_scope.
Section language.
  Context (base_type_code : Type).
  Context (interp_base_type : base_type_code -> Type).
  Context (op : flat_type base_type_code -> flat_type base_type_code -> Type).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Let interp_type := interp_type interp_base_type.
  Let interp_flat_type := interp_flat_type_gen interp_base_type.
  Local Notation Expr := (@Expr base_type_code interp_base_type op).

  Section with_var.
    Context {var : base_type_code -> Type}.
    Local Notation exprf := (@exprf base_type_code interp_base_type op var).
    Local Notation expr := (@expr base_type_code interp_base_type op var).

    Section under_lets.
      Fixpoint let_bind_const {t} (e : interp_flat_type t) {struct t}
        : forall {tC} (C : interp_flat_type_gen var t -> exprf tC), exprf tC
        := match t return forall (e : interp_flat_type t) {tC} (C : interp_flat_type_gen var t -> exprf tC), exprf tC with
           | Prod A B => fun e _ C => @let_bind_const A (fst e) _ (fun x =>
                                      @let_bind_const B (snd e) _ (fun y =>
                                      C (x, y)))
           | Syntax.Tbase _ => fun e _ C => LetIn (Const e) C
           end e.

      Fixpoint under_letsf {t} (e : exprf t)
        : forall {tC} (C : interp_flat_type_gen var t -> exprf tC), exprf tC
        := match e in Syntax.exprf _ _ _ t return forall {tC} (C : interp_flat_type_gen var t -> exprf tC), exprf tC with
           | LetIn _ ex _ eC
             => fun _ C => @under_letsf _ ex _ (fun v => @under_letsf _ (eC v) _ C)
           | Const _ x => fun _ C => let_bind_const x C
           | Var _ x => fun _ C => C x
           | Op _ _ op args as e => fun _ C => LetIn e C
           | Pair A x B y => fun _ C => @under_letsf A x _ (fun x =>
                                        @under_letsf B y _ (fun y =>
                                        C (x, y)))
           end.
    End under_lets.

    Fixpoint linearizef {t} (e : exprf t) : exprf t
      := match e in Syntax.exprf _ _ _ t return exprf t with
         | LetIn _ ex _ eC
           => under_letsf (@linearizef _ ex) (fun x => @linearizef _ (eC x))
         | Const _ x => Const x
         | Var _ x => Var x
         | Op _ _ op args
           => under_letsf (@linearizef _ args) (fun args => LetIn (Op op (SmartVar args)) SmartVar)
         | Pair A ex B ey
           => under_letsf (@linearizef _ ex) (fun x =>
              under_letsf (@linearizef _ ey) (fun y =>
              SmartVar (t:=Prod A B) (x, y)))
         end.

    Fixpoint linearize {t} (e : expr t) : expr t
      := match e in Syntax.expr _ _ _ t return expr t with
         | Return _ x => linearizef x
         | Abs _ _ f => Abs (fun x => @linearize _ (f x))
         end.
  End with_var.

  Definition Linearize {t} (e : Expr t) : Expr t
    := fun var => linearize (e _).
End language.

Global Arguments let_bind_const {_ _ _ _ t} _ {tC} _.
Global Arguments under_letsf {_ _ _ _ _} _ {tC} _.
Global Arguments linearizef {_ _ _ _ _} _.
Global Arguments linearize {_ _ _ _ _} _.
Global Arguments Linearize {_ _ _ _} _ var.

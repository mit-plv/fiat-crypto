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
           | Syntax.Tbase _ => fun e _ C => Let (Const e) C
           end e.

      Fixpoint under_letsf {t} (e : exprf t)
        : forall {tC} (C : interp_flat_type_gen var t -> exprf tC), exprf tC
        := match e in Syntax.exprf _ _ _ t return forall {tC} (C : interp_flat_type_gen var t -> exprf tC), exprf tC with
           | Let _ ex _ eC
             => fun _ C => @under_letsf _ ex _ (fun v => @under_letsf _ (eC v) _ C)
           | Const _ x => fun _ C => let_bind_const x C
           | Var _ x => fun _ C => C x
           | Op _ _ op args as e => fun _ C => Let e C
           | Pair A x B y => fun _ C => @under_letsf A x _ (fun x =>
                                        @under_letsf B y _ (fun y =>
                                        C (x, y)))
           end.
    End under_lets.

    Fixpoint linearizef {t} (e : exprf t) : exprf t
      := match e in Syntax.exprf _ _ _ t return exprf t with
         | Let _ ex _ eC
           => under_letsf (@linearizef _ ex) (fun x => @linearizef _ (eC x))
         | Const _ x => Const x
         | Var _ x => Var x
         | Op _ _ op args
           => under_letsf (@linearizef _ args) (fun args => Let (Op op (SmartVar args)) SmartVar)
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

  Section inline.
    Context {var : base_type_code -> Type}.
    Local Notation exprf := (@exprf base_type_code interp_base_type op).
    Local Notation expr := (@expr base_type_code interp_base_type op).

    Fixpoint inline_constf {t} (e : @exprf (@exprf var) t) : @exprf var t
      := match e in Syntax.exprf _ _ _ t return @exprf var t with
         | Let _ ex tC eC
           => match @inline_constf _ ex in Syntax.exprf _ _ _ t' return (interp_flat_type_gen _ t' -> @exprf var tC) -> @exprf var tC with
              | Const _ x => fun eC => eC (SmartConst (op:=op) (var:=var) x)
              | ex => fun eC => Let ex (fun x => eC (SmartVarVar x))
              end (fun x => @inline_constf _ (eC x))
         | Var _ x => x
         | Const _ x => Const x
         | Pair _ ex _ ey => Pair (@inline_constf _ ex) (@inline_constf _ ey)
         | Op _ _ op args => Op op (@inline_constf _ args)
         end.

    Fixpoint inline_const {t} (e : @expr (@exprf var) t) : @expr var t
      := match e in Syntax.expr _ _ _ t return @expr var t with
         | Return _ x => Return (inline_constf x)
         | Abs _ _ f => Abs (fun x => @inline_const _ (f (Var x)))
         end.
  End inline.

  Definition Linearize {t} (e : Expr t) : Expr t
    := fun var => linearize (e _).
  Definition InlineConst {t} (e : Expr t) : Expr t
    := fun var => inline_const (e _).
End language.

Global Arguments under_letsf {_ _ _ _ _} _ {tC} _.
Global Arguments linearizef {_ _ _ _ _} _.
Global Arguments linearize {_ _ _ _ _} _.
Global Arguments Linearize {_ _ _ _} _ var.
Global Arguments inline_constf {_ _ _ _ _} _.
Global Arguments inline_const {_ _ _ _ _} _.
Global Arguments InlineConst {_ _ _ _} _ var.

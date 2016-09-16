(** * Inline: Remove some [Let] expressions *)
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
  End with_var.

  Definition InlineConst {t} (e : Expr t) : Expr t
    := fun var => inline_const (e _).
End language.

Global Arguments inline_constf {_ _ _ _ _} _.
Global Arguments inline_const {_ _ _ _ _} _.
Global Arguments InlineConst {_ _ _ _} _ var.

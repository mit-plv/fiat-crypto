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
  Local Notation exprf := (@exprf base_type_code interp_base_type op).
  Local Notation expr := (@expr base_type_code interp_base_type op).
  Local Notation Expr := (@Expr base_type_code interp_base_type op).

  Section with_var.
    Context {var : base_type_code -> Type}.
    Context (postprocess : forall {t}, @exprf var t -> @exprf var t).

    Fixpoint inline_const_genf {t} (e : @exprf (@exprf var) t) : @exprf var t
      := match e in Syntax.exprf _ _ _ t return @exprf var t with
         | Let _ ex tC eC
           => match postprocess _ (@inline_const_genf _ ex) in Syntax.exprf _ _ _ t' return (interp_flat_type_gen _ t' -> @exprf var tC) -> @exprf var tC with
              | Const _ x => fun eC => eC (SmartConst (op:=op) (var:=var) x)
              | Var _ x => fun eC => eC (Var x)
              | ex => fun eC => Let ex (fun x => eC (SmartVarVar x))
              end (fun x => @inline_const_genf _ (eC x))
         | Var _ x => x
         | Const _ x => Const x
         | Pair _ ex _ ey => Pair (@inline_const_genf _ ex) (@inline_const_genf _ ey)
         | Op _ _ op args => Op op (@inline_const_genf _ args)
         end.

    Fixpoint inline_const_gen {t} (e : @expr (@exprf var) t) : @expr var t
      := match e in Syntax.expr _ _ _ t return @expr var t with
         | Return _ x => Return (inline_const_genf x)
         | Abs _ _ f => Abs (fun x => @inline_const_gen _ (f (Var x)))
         end.
  End with_var.
  Definition inline_constf {var t} := @inline_const_genf var (fun _ x => x) t.
  Definition inline_const {var t} := @inline_const_gen var (fun _ x => x) t.

  Definition InlineConstGen (postprocess : forall var t, @exprf var t -> @exprf var t)
             {t} (e : Expr t) : Expr t
    := fun var => inline_const_gen (postprocess _) (e _).
  Definition InlineConst {t} := @InlineConstGen (fun _ _ x => x) t.
End language.

Global Arguments inline_const_genf {_ _ _ _} postprocess {_} _.
Global Arguments inline_const_gen {_ _ _ _} postprocess {_} _.
Global Arguments InlineConstGen {_ _ _} postprocess {_} _ var.
Global Arguments inline_constf {_ _ _ _ _} _.
Global Arguments inline_const {_ _ _ _ _} _.
Global Arguments InlineConst {_ _ _ _} _ var.

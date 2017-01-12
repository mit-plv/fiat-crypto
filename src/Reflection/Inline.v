(** * Inline: Remove some [Let] expressions *)
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Util.Tactics.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Let Tbase := @Tbase base_type_code.
  Local Coercion Tbase : base_type_code >-> Syntax.flat_type.
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}.

    Inductive inline_directive : flat_type -> Type :=
    | default_inline {t} (e : @exprf var t) : inline_directive t
    | inline {t : base_type_code} (e : @exprf var t) : inline_directive t
    | no_inline {t} (e : @exprf var t) : inline_directive t.

    Definition exprf_of_inline_directive {t} (v : inline_directive t) : @exprf var t
      := match v with
         | default_inline t e => e
         | inline t e => e
         | no_inline t e => e
         end.

    Context (postprocess : forall {t}, @exprf var t -> inline_directive t).

    Fixpoint inline_const_genf {t} (e : @exprf (@exprf var) t) : @exprf var t
      := match e in Syntax.exprf _ _ t return @exprf var t with
         | LetIn tx ex tC eC
           => match postprocess _ (@inline_const_genf _ ex) in inline_directive t' return (interp_flat_type _ t' -> @exprf var tC) -> @exprf var tC with
              | default_inline _ ex
                => match ex in Syntax.exprf _ _ t' return (interp_flat_type _ t' -> @exprf var tC) -> @exprf var tC with
                   | TT => fun eC => eC tt
                   | Var _ x => fun eC => eC (Var x)
                   | ex => fun eC => LetIn ex (fun x => eC (SmartVarVarf x))
                   end
              | no_inline _ ex
                => fun eC => LetIn ex (fun x => eC (SmartVarVarf x))
              | inline _ ex => fun eC => eC ex
              end (fun x => @inline_const_genf _ (eC x))
         | Var _ x => x
         | TT => TT
         | Pair _ ex _ ey => Pair (@inline_const_genf _ ex) (@inline_const_genf _ ey)
         | Op _ _ op args => Op op (@inline_const_genf _ args)
         end.

    Definition inline_const_gen {t} (e : @expr (@exprf var) t) : @expr var t
      := match e in Syntax.expr _ _ t return @expr var t with
         | Abs _ _ f => Abs (fun x => inline_const_genf (f (SmartVarVarf x)))
         end.

    Section with_is_const.
      Context (is_const : forall s d, op s d -> bool).

      Definition postprocess_for_const (t : flat_type) (v : @exprf var t) : inline_directive t
        := if match v with Op _ _ op _ => @is_const _ _ op | _ => false end
           then match t return @exprf _ t -> inline_directive t with
                | Syntax.Tbase _ => @inline _
                | _ => @default_inline _
                end v
           else default_inline v.
    End with_is_const.
  End with_var.

  Definition inline_constf is_const {var t}
    := @inline_const_genf var (postprocess_for_const is_const) t.
  Definition inline_const is_const {var t}
    := @inline_const_gen var (postprocess_for_const is_const) t.

  Definition InlineConstGen (postprocess : forall var t, @exprf var t -> @inline_directive var t)
             {t} (e : Expr t) : Expr t
    := fun var => inline_const_gen (postprocess _) (e _).
  Definition InlineConst is_const {t}
    := @InlineConstGen (fun var => postprocess_for_const is_const) t.
End language.

Global Arguments inline_directive {_} _ _ _, {_ _ _} _.
Global Arguments no_inline {_ _ _ _} _.
Global Arguments inline {_ _ _ _} _.
Global Arguments default_inline {_ _ _ _} _.
Global Arguments inline_const_genf {_ _ _} postprocess {_} _.
Global Arguments inline_const_gen {_ _ _} postprocess {_} _.
Global Arguments InlineConstGen {_ _} postprocess {_} _ var.
Global Arguments inline_constf {_ _} is_const {_ t} _.
Global Arguments inline_const {_ _} is_const {_ t} _.
Global Arguments InlineConst {_ _} is_const {_} _ var.

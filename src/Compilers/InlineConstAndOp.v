(** * Inline: Remove some [Let] expressions, inline constants, interpret constant operations *)
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Inline.
Require Import Crypto.Compilers.ExprInversion.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          (interp_op : forall s d, op s d -> interp_flat_type interp_base_type s -> interp_flat_type interp_base_type d).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op).
  Local Notation expr := (@expr base_type_code op).
  Local Notation Expr := (@Expr base_type_code op).

  Section with_var.
    Context {var : base_type_code -> Type}
            (invert_Const : forall s d, op s d -> @exprf var s -> option (interp_flat_type interp_base_type d))
            (Const : forall t, interp_base_type t -> @exprf var (Tbase t)).

    Local Notation invert_PairsConst' T
      := (@invert_PairsConst base_type_code interp_base_type op var invert_Const T).
    Local Notation invert_PairsConst
      := (invert_PairsConst' _).

    Fixpoint postprocess_for_const_and_op {t} (e : exprf t)
      : inline_directive (var:=var) (op:=op) t
      := match e with
         | TT => inline (t:=Unit) tt
         | Var t v => inline (t:=Tbase _) (Var v)
         | Op t1 tR opc args as e
           => match invert_PairsConst args with
              | Some args
                => inline (SmartVarfMap Const (interp_op _ _ opc args))
              | None
                => no_inline e
              end
         | LetIn _ _ _ _ as e
           => no_inline e
         | Pair tx ex ty ey as e
           => match @postprocess_for_const_and_op _ ex in inline_directive tx, @postprocess_for_const_and_op _ ey in inline_directive ty
                    return inline_directive (Prod tx ty) -> inline_directive (Prod tx ty)
              with
              | inline tx ex, inline ty ey
                => fun _ => inline (t:=Prod tx ty) (ex, ey)
              | partial_inline tx tC ex eC, partial_inline ty tC' ey eC'
                => fun _ => partial_inline
                              (tC:=Prod _ _)
                              (Pair ex ey)
                              (fun xy : interp_flat_type _ _ * interp_flat_type _ _
                               => (eC (fst xy), eC' (snd xy)))
              | no_inline _ ex, no_inline _ ey
                => fun _ => no_inline (Pair ex ey)
              | no_inline tx ex, inline ty ey
                => fun _ => partial_inline
                              (tC:=Prod _ _)
                              ex (fun x => (SmartVarVarf x, ey))
              | inline tx ex, no_inline ty ey
                => fun _ => partial_inline
                              (tC:=Prod _ _)
                              ey (fun y => (ex, SmartVarVarf y))
              | partial_inline tx tC ex eC, inline ty ey
                => fun _ => partial_inline
                              (tC:=Prod _ _)
                              ex (fun x => (eC x, ey))
              | inline tx ex, partial_inline ty tC ey eC
                => fun _ => partial_inline
                              (tC:=Prod _ _)
                              ey (fun y => (ex, eC y))
              | partial_inline tx tC ex eC, no_inline ty ey
                => fun _ => partial_inline
                              (tC:=Prod _ _)
                              (Pair ex ey)
                              (fun xy : interp_flat_type _ _ * interp_flat_type _ _
                               => (eC (fst xy), SmartVarVarf (snd xy)))
              | no_inline tx ex, partial_inline ty tC ey eC
                => fun _ => partial_inline
                              (tC:=Prod _ _)
                              (Pair ex ey)
                              (fun xy : interp_flat_type _ _ * interp_flat_type _ _
                               => (SmartVarVarf (fst xy), eC (snd xy)))
              | default_inline _ ex, default_inline _ ey
                => fun d => d
              | default_inline _ _, _
              | _, default_inline _ _
                => fun d => d
              end (default_inline e)
         end.

    Definition inline_const_and_op_genf {t}
      := @inline_const_genf base_type_code op var (@postprocess_for_const_and_op) t.

    Definition inline_const_and_op_gen {t}
      := @inline_const_gen base_type_code op var (@postprocess_for_const_and_op) t.
  End with_var.

  Section const_unit.
    Context {var : base_type_code -> Type}
            (OpConst : forall t, interp_base_type t -> op Unit (Tbase t)).

    Definition invert_ConstUnit' {s d} : op s d -> option (interp_flat_type interp_base_type d)
      := match s with
         | Unit
           => fun opv => Some (interp_op _ _ opv tt)
         | _ => fun _ => None
         end.
    Definition invert_ConstUnit {s d} (opv : op s d) (e : @exprf var s)
      : option (interp_flat_type interp_base_type d)
      := invert_ConstUnit' opv.

    Definition Const {t} v := Op (var:=var) (OpConst t v) TT.

    Definition inline_const_and_opf {t}
      := @inline_const_and_op_genf var (@invert_ConstUnit) (@Const) t.
    Definition inline_const_and_op {t}
      := @inline_const_and_op_gen var (@invert_ConstUnit) (@Const) t.
  End const_unit.

  Definition InlineConstAndOpGen
             (invert_Const : forall var s d, op s d -> @exprf var s -> option (interp_flat_type interp_base_type d))
             (Const : forall var t, interp_base_type t -> @exprf var (Tbase t))
             {t} (e : Expr t)
    : Expr t
    := @InlineConstGen
         base_type_code op
         (fun var => @postprocess_for_const_and_op var (invert_Const _) (Const _))
         t
         e.

  Definition InlineConstAndOp
             (OpConst : forall t, interp_base_type t -> op Unit (Tbase t))
             {t} (e : Expr t)
    : Expr t
    := @InlineConstGen
         base_type_code op
         (fun var => @postprocess_for_const_and_op var (@invert_ConstUnit _) (@Const _ OpConst))
         t
         e.
End language.

Global Arguments inline_const_and_op_genf {_ _ _} interp_op {var} invert_Const Const {t} _ : assert.
Global Arguments inline_const_and_op_gen {_ _ _} interp_op {var} invert_Const Const {t} _ : assert.
Global Arguments inline_const_and_opf {_ _ _} interp_op {var} OpConst {t} _ : assert.
Global Arguments inline_const_and_op {_ _ _} interp_op {var} OpConst {t} _ : assert.
Global Arguments InlineConstAndOpGen {_ _ _} interp_op invert_Const Const {t} _ var : assert.
Global Arguments InlineConstAndOp {_ _ _} interp_op OpConst {t} _ var : assert.

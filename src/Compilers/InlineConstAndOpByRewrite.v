Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.ExprInversion.
Require Import Crypto.Compilers.Rewriter.

Module Export Rewrite.
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

      Definition rewrite_for_const_and_op src dst (opc : op src dst) (args : @exprf var src)
        : @exprf var dst
        := match invert_PairsConst args with
           | Some argsv
             => SmartPairf (SmartVarfMap Const (interp_op _ _ opc argsv))
           | None => Op opc args
           end.

      Definition inline_const_and_op_genf {t} (e : @exprf var t) : @exprf var t
        := @rewrite_opf base_type_code op var rewrite_for_const_and_op t e.
      Definition inline_const_and_op_gen {t} (e : @expr var t) : @expr var t
        := @rewrite_op base_type_code op var rewrite_for_const_and_op t e.
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
      := @RewriteOp
           base_type_code op
           (fun var => @rewrite_for_const_and_op var (invert_Const _) (Const _))
           t
           e.

    Definition InlineConstAndOp
               (OpConst : forall t, interp_base_type t -> op Unit (Tbase t))
               {t} (e : Expr t)
      : Expr t
      := @RewriteOp
           base_type_code op
           (fun var => @rewrite_for_const_and_op var (@invert_ConstUnit _) (@Const _ OpConst))
           t
           e.
  End language.

  Global Arguments inline_const_and_op_genf {_ _ _} interp_op {var} invert_Const Const {t} _ : assert.
  Global Arguments inline_const_and_op_gen {_ _ _} interp_op {var} invert_Const Const {t} _ : assert.
  Global Arguments inline_const_and_opf {_ _ _} interp_op {var} OpConst {t} _ : assert.
  Global Arguments inline_const_and_op {_ _ _} interp_op {var} OpConst {t} _ : assert.
  Global Arguments InlineConstAndOpGen {_ _ _} interp_op invert_Const Const {t} _ var : assert.
  Global Arguments InlineConstAndOp {_ _ _} interp_op OpConst {t} _ var : assert.
End Rewrite.

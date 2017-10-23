Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.InlineConstAndOpByRewrite.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.

Module Export Rewrite.
  Definition inline_const_and_opf {var} {t} (e : exprf _ _ t) : @exprf base_type op var t
    := @inline_const_and_opf base_type op interp_base_type (@interp_op) var make_const t e.
  Definition inline_const_and_op {var} {t} (e : expr _ _ t) : @expr base_type op var t
    := @inline_const_and_op base_type op interp_base_type (@interp_op) var make_const t e.
  Definition InlineConstAndOp {t} (e : Expr t) : Expr t
    := @InlineConstAndOp base_type op interp_base_type interp_op make_const t e.
End Rewrite.

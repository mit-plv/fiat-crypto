Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.InlineConstAndOp.
Require Import Crypto.Compilers.ZExtended.Syntax.

Definition InlineConstAndOp {t} (e : Expr t) : Expr t
  := @InlineConstAndOp base_type op interp_base_type (@interp_op) (@Const) t e.

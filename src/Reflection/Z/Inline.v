Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Inline.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Z.Syntax.Util.

Definition InlineConst {t} (e : Expr base_type op t) : Expr base_type op t
  := @InlineConst base_type op (is_const) t e.

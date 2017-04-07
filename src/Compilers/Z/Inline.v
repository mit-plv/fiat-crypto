Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Inline.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.

Definition InlineConst {t} (e : Expr base_type op t) : Expr base_type op t
  := @InlineConst base_type op (is_const) t e.

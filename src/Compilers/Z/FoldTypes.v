Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Z.Syntax.
Require Import Crypto.Compilers.Z.Syntax.Util.
Require Import Crypto.Compilers.FoldTypes.

Section min_or_max.
  Context (f : base_type -> base_type -> base_type)
          (init : base_type).

  Definition TypeFold {t} (e : Expr t) : base_type
    := TypeFold (fun t => t) f init e.
End min_or_max.

Definition MaxTypeUsed {t} (e : Expr t) : base_type
  := TypeFold base_type_max (TWord 0) e.
Definition MinTypeUsed {t} (e : Expr t) : base_type
  := TypeFold base_type_min TZ e.

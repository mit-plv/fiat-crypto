(** * Generalize [var] in [exprf] *)
Require Import Coq.ZArith.BinInt.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.GeneralizeVar.
Require Import Crypto.Compilers.Z.Syntax.

(** N.B. This procedure only works when there are no nested lets,
    i.e., nothing like [let x := let y := z in w] in the PHOAS syntax
    tree.  This is a limitation of [compile]. *)

Definition GeneralizeVar {t} (e : @Syntax.expr base_type op _ t)
  : option (@Z.Syntax.Expr (domain t -> codomain t))
  := @GeneralizeVar base_type op base_type_beq internal_base_type_dec_bl
                    (fun _ t => Op (OpConst 0%Z) TT)
                    t e.

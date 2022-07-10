Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Saturated.Core.
Require Import Crypto.Arithmetic.Saturated.MulSplit.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.MulSplit.
Require Import Crypto.Util.ZUtil.CPS.
Require Import Crypto.Util.Tuple.
Local Notation "A ^ n" := (tuple A n) : type_scope.

(* Define wrapper definitions that use Columns representation
internally but with input and output in Positonal representation.*)
Module Columns.
  Section Wrappers.
    Context (weight : nat->Z).

    Definition add_cps {n1 n2 n3} (p : Z^n1) (q : Z^n2)
               {T} (f : (Z*Z^n3)->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.to_associational_cps weight q
        (fun Q => Columns.from_associational_cps weight n3 (P++Q)
        (fun R => Columns.compact_cps (div_cps:=@div_cps) (modulo_cps:=@modulo_cps) (add_get_carry_cps:=@Z.add_get_carry_full_cps) weight R f))).

    Definition unbalanced_sub_cps {n1 n2 n3} (p : Z^n1) (q:Z^n2)
               {T} (f : (Z*Z^n3)->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.negate_snd_cps weight q
        (fun nq => B.Positional.to_associational_cps weight nq
        (fun Q => Columns.from_associational_cps weight n3 (P++Q)
        (fun R => Columns.compact_cps (div_cps:=@div_cps) (modulo_cps:=@modulo_cps) (add_get_carry_cps:=@Z.add_get_carry_full_cps) weight R f)))).

    Definition mul_cps {n1 n2 n3} s (p : Z^n1) (q : Z^n2)
               {T} (f : (Z*Z^n3)->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.to_associational_cps weight q
        (fun Q => B.Associational.sat_mul_cps (mul_split_cps := @Z.mul_split_cps') s P Q
        (fun PQ => Columns.from_associational_cps weight n3 PQ
        (fun R => Columns.compact_cps (div_cps:=@div_cps) (modulo_cps:=@modulo_cps) (add_get_carry_cps:=@Z.add_get_carry_full_cps) weight R f)))).

    Definition conditional_add_cps {n1 n2 n3} mask cond (p:Z^n1) (q:Z^n2)
               {T} (f:_->T) :=
      B.Positional.select_cps mask cond q
                 (fun qq => add_cps (n3:=n3) p qq f).

  End Wrappers.
End Columns.

Ltac basesystem_partial_evaluation_unfolder t :=
  let t := (eval cbv delta [Columns.add_cps Columns.unbalanced_sub_cps Columns.mul_cps Columns.conditional_add_cps] in t) in
  let t := Saturated.MulSplit.basesystem_partial_evaluation_unfolder t in
  let t := Saturated.Core.basesystem_partial_evaluation_unfolder t in
  let t := Arithmetic.Core.basesystem_partial_evaluation_unfolder t in
  t.

Module Export Hints.
  Export Crypto.Arithmetic.Core.Hints.
  Export Crypto.Arithmetic.Saturated.Core.Hints.
  Export Crypto.Arithmetic.Saturated.MulSplit.Hints.
  Export Crypto.Util.ZUtil.Definitions.Hints.
  Export Crypto.Util.ZUtil.MulSplit.Hints.
  Export Crypto.Util.ZUtil.CPS.Hints.
  Export Crypto.Util.Tuple.Hints.
  Ltac Arithmetic.Core.basesystem_partial_evaluation_default_unfolder t ::=
    basesystem_partial_evaluation_unfolder t.
  Global Hint Unfold
         Columns.conditional_add_cps
         Columns.add_cps
         Columns.unbalanced_sub_cps
         Columns.mul_cps.

  Global Hint Unfold
         Columns.add_cps Columns.unbalanced_sub_cps Columns.mul_cps Columns.conditional_add_cps
    : basesystem_partial_evaluation_unfolder.
End Hints.

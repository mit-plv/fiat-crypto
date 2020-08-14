Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Semantics.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZRange.

Section Representation.
  Context {p : Types.parameters}.
  Context (n : nat) (weight : nat -> Z)
          (loose_bounds tight_bounds : list (option zrange)).

  Definition eval_words : list word -> Z :=
    fun ws =>
      Positional.eval weight n (map word.unsigned ws).

  Instance frep : FieldRepresentation :=
  { felem := list word;
    feval := eval_words;
    FElem := Bignum n;
    bounds := list (option zrange);
    bounded_by :=
      fun bs ws =>
        list_Z_bounded_by bs (map word.unsigned ws);
    loose_bounds := loose_bounds;
    tight_bounds := tight_bounds;
  }.
End Representation.

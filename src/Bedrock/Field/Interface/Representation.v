Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Semantics.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZRange.

Section Representation.
  Context {p : Types.parameters} {field_parameters : FieldParameters}
          {p_ok : Types.ok}.
  Context (n : nat) (weight : nat -> Z)
          (loose_bounds tight_bounds : list (option zrange))
          (relax_bounds :
             forall X : list Z,
               list_Z_bounded_by tight_bounds X ->
               list_Z_bounded_by loose_bounds X).
  Existing Instance semantics_ok.

  Definition eval_words : list word -> F M_pos :=
    fun ws =>
      F.of_Z _ (Positional.eval weight n (map word.unsigned ws)).

  Definition eval_bytes : list byte -> F M_pos :=
    fun bs =>
      F.of_Z _ (Positional.eval
                           (ModOps.weight 8 1)
                           (Z.to_nat word_size_in_bytes)
                           (map byte.unsigned bs)).

  Local Instance frep : FieldRepresentation :=
    { felem := list word;
      feval := eval_words;
      feval_bytes := eval_bytes;
      felem_size_in_bytes := word_size_in_bytes;
      FElem := Bignum n;
      FElemBytes := EncodedBignum n;
      bounds := list (option zrange);
      bounded_by :=
        fun bs ws =>
          list_Z_bounded_by bs (map word.unsigned ws);
      loose_bounds := loose_bounds;
      tight_bounds := tight_bounds;
    }.

  Local Instance frep_ok : FieldRepresentation_ok.
  Proof.
    constructor.
    { cbn [felem_size_in_bytes frep].
      rewrite word_size_in_bytes_eq.

      (* TODO: should this be upstreamed to bedrock2? *)
      assert (0 < bytes_per_word width).
      { cbv [bytes_per_word].
        pose proof word.width_pos.
        apply Z.div_str_pos; auto with zarith. }

      cbn [bytes_per]. rewrite Z2Nat.id by auto with zarith.
      apply Z.mod_same; auto with zarith. }
    { cbn [bounded_by frep]; intros.
      apply relax_bounds; auto. }
  Qed.
End Representation.

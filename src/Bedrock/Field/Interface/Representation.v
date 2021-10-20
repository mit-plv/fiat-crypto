Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Semantics.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.ZUtil.Tactics.ZeroBounds.

Section Representation.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {field_parameters : FieldParameters}
          {p_ok : Types.ok}.
  Context (n n_bytes : nat) (weight : nat -> Z)
          (loose_bounds tight_bounds byte_bounds : list (option zrange))
          (relax_bounds :
             forall X : list Z,
               list_Z_bounded_by tight_bounds X ->
               list_Z_bounded_by loose_bounds X).

  Definition eval_words : list word -> F M_pos :=
    fun ws =>
      F.of_Z _ (Positional.eval weight n (map word.unsigned ws)).

  Definition eval_bytes : list byte -> F M_pos :=
    fun bs =>
      F.of_Z _ (Positional.eval
                           (ModOps.weight 8 1)
                           n_bytes
                           (map byte.unsigned bs)).

  Local Instance frep : FieldRepresentation := {
      feval := eval_words;
      feval_bytes := eval_bytes;
      felem_size_in_words := n;
      encoded_felem_size_in_bytes := n_bytes;
      bytes_in_bounds bs := list_Z_bounded_by byte_bounds (map byte.unsigned bs);
      bounds := list (option zrange);
      bounded_by bs ws := list_Z_bounded_by bs (map word.unsigned ws);
      loose_bounds := loose_bounds;
      tight_bounds := tight_bounds;
    }.

  Local Instance frep_ok : FieldRepresentation_ok.
  Proof. split. cbn [bounded_by frep]; intros. apply relax_bounds; auto. Qed.
End Representation.

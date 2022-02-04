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
          (bounds : Type)
          (list_in_bounds : bounds -> list Z -> Prop)
          (loose_bounds tight_bounds byte_bounds : bounds)
          (relax_bounds :
             forall X : list Z,
               list_in_bounds tight_bounds X ->
               list_in_bounds loose_bounds X)
          (*Transformation to applied to list before evaluating. For Solinas, this is the identity,
            and for word-by-word Montgomery, the argument must be pulled out of the Montgomery domain*)
          (eval_transformation : list Z -> list Z).


  Definition eval_words : list word -> F M_pos :=
    fun ws =>
      F.of_Z _ (Positional.eval weight n (eval_transformation (map word.unsigned ws))).

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
      bytes_in_bounds bs := list_in_bounds byte_bounds (map byte.unsigned bs);
      bounds := bounds;
      bounded_by bs ws := list_in_bounds bs (map word.unsigned ws);
      loose_bounds := loose_bounds;
      tight_bounds := tight_bounds;
    }.

  Local Instance frep_ok : FieldRepresentation_ok.
  Proof. split. cbn [bounded_by frep]; intros. apply relax_bounds; auto. Qed.
End Representation.

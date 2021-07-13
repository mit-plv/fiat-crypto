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
  Context {p : Types.parameters} {field_parameters : FieldParameters}
          {p_ok : Types.ok}.
  Context (n n_bytes : nat) (weight : nat -> Z)
          (loose_bounds tight_bounds byte_bounds : list (option zrange))
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
                           n_bytes
                           (map byte.unsigned bs)).

  Local Instance frep : FieldRepresentation :=
    { felem := list word;
      feval := eval_words;
      feval_bytes := eval_bytes;
      felem_size_in_bytes :=
        Z.of_nat n * bytes_per_word Semantics.width;
      encoded_felem_size_in_bytes := n_bytes;
      bytes_in_bounds :=
        fun bs => list_Z_bounded_by byte_bounds (map byte.unsigned bs);
      FElem := Bignum n;
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
      push_Zmod. autorewrite with zsimplify_fast.
      reflexivity. }
    { cbv [Placeholder FElem felem_size_in_bytes frep].
      repeat intro.
      assert (word_size_in_bytes = bytes_per_word width).
      { pose proof word.width_pos.
        rewrite word_size_in_bytes_eq; cbn [bytes_per].
        apply Z2Nat.id. cbv [bytes_per_word].
        Z.zero_bounds. }
      cbv [Lift1Prop.ex1]; split; intros;
        repeat match goal with
               | H : anybytes _ _ _ |- _ =>
                 apply Array.anybytes_to_array_1 in H
               | H : exists _, _ |- _ => destruct H
               | H : _ /\ _ |- _ => destruct H
               end.
      { match goal with
          | H : Array.array _ _ _ _ _ |- _ =>
            eapply Bignum_of_bytes with (n0:=n) in H;
              [ destruct H | (idtac + destruct Semantics.width_cases); nia.. ]
        end.
        eexists; eauto. }
      {
        pose proof word_size_in_bytes_pos.
        let H := match goal with
                 | H : Bignum _ _ _ _ |- _ => H end in
        eapply Bignum_to_bytes in H.
        sepsimpl.
        let H := match goal with
                 | H : Array.array _ _ _ _ _ |- _ => H end in
        eapply Array.array_1_to_anybytes in H.
        match goal with
        | H : anybytes ?p ?n1 ?m |- anybytes ?p ?n2 ?m =>
          replace n2 with n1 by nia; assumption
        end. } }
    { cbn [bounded_by frep]; intros.
      apply relax_bounds; auto. }
  Qed.
End Representation.

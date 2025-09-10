From Coq Require Import ZArith.
From Coq Require Import List.
From Coq Require Import Lia.
Require Import coqutil.Datatypes.List.
Require Import bedrock2.Array.
Require Import bedrock2.ArrayCasts.
Require Import bedrock2.Scalars.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Local Open Scope Z_scope.

Section Bignum.
  Import bedrock2.Memory.
  Context  {width} {word : Interface.word width} {mem : map.map word Init.Byte.byte}.

  Definition Bignum (n : nat) (px : word) (x : list word) : mem -> Prop :=
    sep (emp (length x = n)) (array scalar (word.of_Z (bytes_per_word width)) px x).

  Definition EncodedBignum
             (n_bytes : nat) (px : word) (x : list Byte.byte)
    : mem -> Prop :=
    sep (emp (length x = n_bytes)) (array ptsto (word.of_Z 1) px x).

  Section Proofs.
    Context {word_ok : @word.ok width word} {map_ok : @map.ok word Init.Byte.byte mem}
      {BW : coqutil.Word.Bitwidth.Bitwidth width}.

    Lemma Bignum_of_bytes n :
      forall addr bs,
        length bs = (n * Z.to_nat (bytes_per_word width))%nat ->
        Lift1Prop.iff1
          (array ptsto (word.of_Z 1) addr bs)
          (Bignum n addr (bs2ws (Z.to_nat (bytes_per_word width)) bs)).
    Proof.
      pose Types.word_size_in_bytes_pos.

      cbv [Bignum].
      intros. rewrite words_of_bytes.
      2: { rewrite H. apply Nat.Div0.mod_mul. }
      unfold bytes_per in *.
      replace (Z.of_nat (BinIntDef.Z.to_nat (bytes_per_word width))) with (bytes_per_word width) in *; try lia.
      change BinIntDef.Z.to_nat with Z.to_nat in *.
      split; intros.
      {
        extract_ex1_and_emp_in_goal. split.
        - assumption.
        - rewrite bs2ws_length; try lia.
          + rewrite H. apply Nat.div_mul. lia.
          + rewrite H. apply Nat.Div0.mod_mul.
      }
      {
        extract_ex1_and_emp_in H0.
        assumption.
      }
    Qed.

    Lemma Bignum_to_bytes n :
      forall addr x,
        Lift1Prop.iff1
          (Bignum n addr x)
          (sep (emp (length (ws2bs (Z.to_nat (bytes_per_word width)) x) = (n * Z.to_nat (bytes_per_word width))%nat))
          (array ptsto (word.of_Z 1) addr (ws2bs (Z.to_nat (bytes_per_word width)) x))).
    Proof.
      intros.
      cbv [Bignum]. rewrite <- bytes_of_words.

      assert (length (ws2bs (Z.to_nat (bytes_per_word width)) x) = ((length x) * Z.to_nat (bytes_per_word width))%nat).
      { rewrite ws2bs_length. lia. }

      pose Types.word_size_in_bytes_pos.
      unfold bytes_per in *.
      replace (Z.of_nat (BinIntDef.Z.to_nat (bytes_per_word width))) with (bytes_per_word width) in *; try lia.
      change BinIntDef.Z.to_nat with Z.to_nat in *.
      split.
      { intros. extract_ex1_and_emp_in_hyps. extract_ex1_and_emp_in_goal. split.
        {assumption. }
        {lia. }
      }
      { intros. extract_ex1_and_emp_in_goal. extract_ex1_and_emp_in_hyps. split.
        {assumption. }
        { nia. }
      }
    Qed.
  End Proofs.
End Bignum.
Notation BignumSuchThat :=
  (fun n addr ws P =>
     let xs := map word.unsigned ws in
     sep (emp (P xs)) (Bignum n addr ws)).
Notation EncodedBignumSuchThat :=
  (fun n addr ws P =>
     let xs := map Byte.byte.unsigned ws in
     sep (emp (P xs)) (EncodedBignum n addr ws)).

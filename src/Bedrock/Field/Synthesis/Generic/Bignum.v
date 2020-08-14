Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.Map.Separation.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Common.Arrays.MaxBounds.
Require Import Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Local Open Scope Z_scope.

Section Bignum.
  Context {p : Types.parameters}.

  Definition Bignum
             (n : nat) (px : Semantics.word) (x : list Semantics.word)
    : Semantics.mem -> Prop :=
    sep (emp (length x = n)) (array scalar (word.of_Z word_size_in_bytes) px x).

  Definition EncodedBignum
             (n_bytes : nat) (px : Semantics.word) (x : list Byte.byte)
    : Semantics.mem -> Prop :=
    sep (emp (length x = n_bytes)) (array ptsto (word.of_Z 1) px x).

  Section Proofs.
    Context {ok : Types.ok}.
    Existing Instance semantics_ok.

    (* TODO: lemmas along these lines might be convenient for stack allocation
    Lemma Bignum_of_bytes n addr bs :
      length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
      Lift1Prop.iff1
        (array ptsto (word.of_Z 1) addr bs)
        (Bignum n addr (map word.of_Z
                            (eval_bytes (width:=Semantics.width) bs))).
    Admitted.

    Lemma Bignum_to_bytes n addr x :
      list_Z_bounded_by (max_bounds n) (map word.unsigned x) ->
      Lift1Prop.iff1
        (Bignum n addr x)
        (array ptsto (word.of_Z 1) addr (encode_bytes x)).
    Admitted.
    *)
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

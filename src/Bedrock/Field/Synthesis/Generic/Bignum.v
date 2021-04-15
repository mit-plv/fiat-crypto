Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Array.
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

    (* TODO: factor this proof into a more general form that says if subarrays
    of your arrays form a different kind of element, then you have an array of
    the other type *)
    Lemma Bignum_of_bytes n :
      forall addr bs,
        length bs = (n * Z.to_nat word_size_in_bytes)%nat ->
        Lift1Prop.impl1
          (array ptsto (word.of_Z 1) addr bs)
          (Lift1Prop.ex1 (Bignum n addr)).
    Proof.
      cbv [Bignum].
      induction n; intros.
      { destruct bs; cbn [length] in *; try lia; [ ].
        repeat intro. exists nil.
        cbn [array length] in *. sepsimpl; eauto. }
      { rewrite <-(firstn_skipn (Z.to_nat word_size_in_bytes) bs).
        rewrite array_append.
        rewrite Scalars.scalar_of_bytes with (l:=List.firstn _ _);
          lazymatch goal with
          | [ |- _ <= Semantics.width ] => destruct Semantics.width_cases; lia
          | _ => idtac
          end.
        2:{
          rewrite word_size_in_bytes_eq in *.
          etransitivity;
            [ symmetry; apply bits_per_word_eq_width;
              solve [eauto using width_0mod_8] | ].
          rewrite firstn_length, Min.min_l by lia.
          lia. }
        intros ? Hsep. destruct Hsep as [? [? [? [Hsca Harr]]]].
        cbv [Lift1Prop.impl1] in *.
        pose proof word_size_in_bytes_pos.
        rewrite word.unsigned_of_Z_1, Z.mul_1_l in Harr.
        rewrite firstn_length, Min.min_l in Harr by nia.
        rewrite Z2Nat.id in Harr by lia.
        match type of Harr with
        | array _ _ _ (List.skipn ?sz ?xs) _ =>
          match goal with
          | H : length xs = (S ?n * sz)%nat |- _ =>
            assert (length (List.skipn sz xs) = (n * sz)%nat);
              [ rewrite skipn_length, H; nia | ]
          end
        end.
        specialize (IHn _ _ ltac:(eauto) _ Harr).
        destruct IHn; sepsimpl.
        match goal with
        | Htl : array scalar _ _ ?t _,
                Hhd : scalar _ ?h _ |- _ =>
          exists (h :: t)
        end.
        cbn [length array].
        sepsimpl; eauto; [ ].
        do 2 eexists.
        eauto. }
    Qed.

    Lemma Bignum_to_bytes n :
      forall addr x,
        Lift1Prop.impl1
          (Bignum n addr x)
          (Lift1Prop.ex1
             (fun bs =>
                sep (emp (length bs = (n * Z.to_nat word_size_in_bytes)%nat))
                    (array ptsto (word.of_Z 1) addr bs))).
    Proof.
      cbv [Bignum].
      induction n; repeat intro; sepsimpl; destruct x;
        cbn [length array] in *; try lia;
        [ exists nil; cbn in *; sepsimpl; solve [eauto] | ].
      match goal with
      | H : sep _ _ _ |- _ =>
        seprewrite_in scalar_to_bytes H
      end.
      match goal with
      | H : sep _ _ _ |- _ =>
        cbv [sep] in H; cleanup
      end.
      match goal with
      | H : array scalar _ ?addr ?xs ?m |- _ =>
        specialize (IHn addr xs m);
          match type of IHn with ?P -> _ =>
                                 assert P by (sepsimpl; auto; lia) end;
          specialize (IHn ltac:(assumption))
      end.
      destruct IHn as [bs ?].
      sepsimpl.
      match goal with
      | Htl : array ptsto _ _ bs _,
              Hhd : array ptsto _ _ ?h _ |- _ =>
        exists (h ++ bs)
      end.
      sepsimpl; [ | ].
      { rewrite app_length.
        rewrite HList.tuple.length_to_list.
        rewrite word_size_in_bytes_eq in *.
        rewrite !Nat2Z.id in *. lia. }
      { apply array_append.
        pose proof word_size_in_bytes_pos.
        rewrite word.unsigned_of_Z_1, Z.mul_1_l.
        rewrite HList.tuple.length_to_list.
        rewrite <-word_size_in_bytes_eq.
        do 2 eexists. eauto. }
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

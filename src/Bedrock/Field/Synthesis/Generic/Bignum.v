Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Datatypes.List.
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
  Import bedrock2.Memory bedrock2.ptsto_bytes.
  Context  {width} {word : Interface.word width} {mem : map.map word Init.Byte.byte}.

  Local Notation k := (bytes_per_word width).
  Definition Bignum (n : nat) (px : word) (x : list word) : mem -> Prop :=
    sep (emp (length x = n)) (array scalar (word.of_Z k) px x).

  Definition EncodedBignum
             (n_bytes : nat) (px : word) (x : list Byte.byte)
    : mem -> Prop :=
    sep (emp (length x = n_bytes)) (array ptsto (word.of_Z 1) px x).

  Section Proofs.
    Context {word_ok : @word.ok width word} {map_ok : @map.ok word Init.Byte.byte mem}
      {BW : coqutil.Word.Bitwidth.Bitwidth width}.

    Local Notation lew_combine := (fun c => word.of_Z (LittleEndianList.le_combine c)).
    Local Notation lew_split := (fun w => LittleEndianList.le_split (Z.to_nat k) (word.unsigned w)).

    Lemma Bignum_of_bytes n :
      forall addr bs,
        length bs = (n * Z.to_nat (bytes_per_word width))%nat ->
        Lift1Prop.iff1
          (array ptsto (word.of_Z 1) addr bs)
          (Bignum n addr (map lew_combine (chunk (Z.to_nat k) bs))).
    Proof.
      cbv [Bignum].
      induction n; intros.
      { destruct bs; cbn [length] in *; try lia; [ ].
        repeat intro. intuition sepsimpl; eauto. }
      { rewrite <-(firstn_skipn (Z.to_nat k) bs).
        rewrite array_append.
        rewrite Scalars.scalar_of_bytes with (l:=List.firstn _ _);
          lazymatch goal with
          | [ |- _ <= width ] => destruct Bitwidth.width_cases; lia
          | _ => idtac
          end.
        2:{
          rewrite firstn_length, Min.min_l by lia.
          destruct Bitwidth.width_cases; subst width; trivial. }
        rewrite chunk_app_chunk; cycle 1.
        { destruct Bitwidth.width_cases; subst width; cbv; inversion 1. }
        { rewrite firstn_length; lia. }
        cbn [length array map]; progress (cancel; cbv [seps]).
        unshelve erewrite (_ : forall n m, (S n = S m <-> n = m)).
        { clear; intros; split; congruence. }
        rewrite <-IHn by (rewrite skipn_length; lia); clear IHn.
        Morphisms.f_equiv. f_equal. f_equal.
        rewrite word.unsigned_of_Z_1, Z.mul_1_l, firstn_length, H.
        destruct Bitwidth.width_cases; subst width; cbn; lia. }
    Qed.

    (* TODO: move to coqutil.List.Datatypes *)
    Lemma chunk_flat_map_exact {A B} k (Hk : k <> O)
      (f : A -> list B) (Hf : forall a : A, length (f a) = k) xs
      : chunk k (flat_map f xs) = map f xs.
    Proof.
      induction xs; trivial; cbn [flat_map map].
      rewrite ?chunk_app_chunk, IHxs; trivial.
    Qed.

    Lemma Bignum_to_bytes n :
      forall addr x,
        Lift1Prop.iff1
          (Bignum n addr x)
          (sep (emp (length (flat_map lew_split x) = (n * Z.to_nat k)%nat))
          (array ptsto (word.of_Z 1) addr (flat_map lew_split x))).
    Proof.
      intros.
      assert (length (flat_map lew_split x) = (length x * Z.to_nat k)%nat).
      { erewrite flat_map_const_length, Nat.mul_comm;
        auto using LittleEndianList.length_le_split. }
      rewrite Bignum_of_bytes by eassumption; cbv [Bignum].
      rewrite chunk_flat_map_exact, map_map; cycle 1.
      { destruct Bitwidth.width_cases; subst width; inversion 1. }
      { intros; apply LittleEndianList.length_le_split. }
      erewrite List.map_ext with (g:=fun x=>x), map_id; try cancel; cbv [seps].
      { rewrite sep_emp_emp. setoid_rewrite H. 
        cbv [Lift1Prop.iff1 emp]; intuition (
          destruct Bitwidth.width_cases; subst width; subst; cbn in *; try nia). }
      intros.
      (* note: this mess could be cleaned up now that we use LittleEndianList *)
      destruct Bitwidth.width_cases; subst width; simpl k; simpl length(*+arguments*);
        rewrite ?LittleEndianList.le_combine_split; try exact eq_refl;
        rewrite Z.mod_small, word.of_Z_unsigned;
        trivial; eapply word.unsigned_range.
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

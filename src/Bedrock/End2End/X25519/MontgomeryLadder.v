From Coq Require Import String.
From Coq Require Import List.
From Coq Require Import ZArith.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Spec.MontgomeryCurve.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import bedrock2Examples.memmove.
Require Import bedrock2.SepAutoArray.
Require Import compiler.Pipeline.
Require Import compiler.Symbols.
Require Import compiler.MMIO.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.End2End.X25519.clamp.
Local Open Scope string_scope.
Import ListNotations.

Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.
Derive ladderstep SuchThat (ladderstep = ladderstep_body) As ladderstep_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Derive montladder SuchThat (montladder = montladder_body (Z.to_nat (Z.log2 Curve25519.order)))
       As montladder_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Require Import bedrock2.NotationsCustomEntry.

Definition x25519 := func! (out, sk, pk) {
  stackalloc 32 as K;
  memmove(K, sk, $32);
  clamp(K);
  stackalloc 40 as U;
  fe25519_from_bytes(U, pk);
  stackalloc 40 as OUT;
  montladder(OUT, K, U);
  fe25519_to_bytes(out, OUT)
}.

Definition x25519_base := func! (out, sk) {
  stackalloc 32 as K;
  memmove(K, sk, $32);
  clamp(K);
  stackalloc 40 as U;
  fe25519_from_word(U, $9);
  stackalloc 40 as OUT;
  montladder(OUT, K, U);
  fe25519_to_bytes(out, OUT)
}.

Import LittleEndianList.
Local Coercion F.to_Z : F >-> Z.
Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.Syntax bedrock2.Map.SeparationLogic.
From Coq.Init Require Import Byte.
Require Import coqutil.Byte.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Definition x25519_spec s P := le_split 32 (M.X0 (Curve25519.M.scalarmult (Curve25519.clamp (le_combine s)) P)).
Lemma length_x25519_spec s P : length (x25519_spec s P) = 32%nat. Proof. apply length_le_split. Qed.

Global Instance spec_of_x25519 : spec_of "x25519" :=
  fnspec! "x25519" out sk pk / (o s p : list Byte.byte) P (R : _ -> Prop),
  { requires t m := m =* s$@sk * p$@pk * o$@out * R /\
      length s = 32%nat /\ length p = 32%nat /\ length o = 32%nat /\
      byte.unsigned (nth 31 p x00) <= 0x7f /\ Field.feval_bytes(field_parameters:=field_parameters) p = Curve25519.M.X0 P;
    ensures t' m := t=t' /\ m=* s$@sk ⋆ p$@pk ⋆ R ⋆ (x25519_spec s P)$@out }.

Global Instance spec_of_x25519_base : spec_of "x25519_base" :=
  fnspec! "x25519_base" out sk / (o s : list Byte.byte) (R : _ -> Prop),
  { requires t m := m =* s$@sk * o$@out * R /\ length s = 32%nat /\ length o = 32%nat;
    ensures t' m := t=t' /\ m=* s$@sk ⋆ R ⋆ (x25519_spec s Curve25519.M.B)$@out }.

Local Instance spec_of_memmove_array : spec_of "memmove" := spec_of_memmove_array.
Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.
Local Instance spec_of_fe25519_from_bytes : spec_of "fe25519_from_bytes" := Field.spec_of_from_bytes.
Local Instance spec_of_fe25519_to_bytes : spec_of "fe25519_to_bytes" := Field.spec_of_to_bytes.
Local Instance spec_of_montladder : spec_of "montladder" :=
  spec_of_montladder (Z.to_nat (Z.log2 Curve25519.order)).

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.

Lemma x25519_ok : program_logic_goal_for_function! x25519.
Proof.
  repeat straightline.

  straightline_call; ssplit; try ecancel_assumption; repeat straightline; try listZnWords; [].
  straightline_call; ssplit; try ecancel_assumption; repeat straightline; try listZnWords; [].


  straightline_call; ssplit.
  { eexists. ecancel_assumption. }
  { ecancel_assumption_impl. }

  { unfold Field.bytes_in_bounds, frep25519, field_representation, Signature.field_representation, Representation.frep.
    match goal with |- ?P ?x ?z => let y := eval cbv in x in change (P y z) end; cbn.
    repeat (destruct p as [|? p]; try (cbn [length] in *;discriminate); []).
    cbn; cbn [nth] in *.
    cbv [COperationSpecifications.list_Z_bounded_by FoldBool.fold_andb_map map seq]; cbn.
    pose proof byte.unsigned_range as HH. setoid_rewrite <-Le.Z.le_sub_1_iff in HH. cbn in HH.
    setoid_rewrite Zle_is_le_bool in HH. setoid_rewrite <-Bool.andb_true_iff in HH.
    rewrite 31HH; cbn.
    eapply Bool.andb_true_iff; split; trivial.
    eapply Bool.andb_true_iff; split; eapply Zle_is_le_bool; trivial.
    eapply byte.unsigned_range. }
  repeat straightline.

  seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a2) H24. { transitivity 40%nat; trivial. }

  straightline_call; ssplit.
  { unfold FElem in *; extract_ex1_and_emp_in_goal; ssplit; try ecancel_assumption_impl.
    all: eauto.
    instantiate (1:=None). exact I. }
  { reflexivity. }
  { rewrite ?length_le_split. vm_compute. inversion 1. }
  repeat straightline.
  lazymatch goal with
  | H : Field.feval_bytes ?x = M.X0 ?P, H' : context [montladder_gallina] |- _ =>
      rewrite H in H'; unfold M.X0 in H'
  end.
  lazymatch goal with
  | H : context [montladder_gallina] |- _ =>
      rewrite (@montladder_gallina_equiv_affine (Curve25519.p) _ _ (Curve25519.field)) with
      (b_nonzero:=Curve25519.M.b_nonzero) (char_ge_3:=Curve25519.char_ge_3) in H;
      [ unfold FElem, Field.FElem in H; extract_ex1_and_emp_in H | Lia.lia | vm_decide | apply M.a2m4_nonsq ]
  end.
  straightline_call; ssplit.
  { ecancel_assumption. }
  { transitivity 32%nat; auto. }
  { eexists.
    unfold FElem, Field.FElem in *; extract_ex1_and_emp_in_goal; ssplit.
    ecancel_assumption. }
  { intuition idtac. }
  repeat straightline_cleanup.
  repeat straightline.

  cbv [Field.FElem] in *.
  repeat seprewrite_in @Bignum.Bignum_to_bytes H32; extract_ex1_and_emp_in H32.
  pose proof length_le_split 32 (Curve25519.clamp (le_combine s)).
  repeat straightline.
  cbv [x25519_spec].
  use_sep_assumption; cancel.
  rewrite H36, le_combine_split.
  do 7 Morphisms.f_equiv.
  pose proof clamp_range (le_combine s).
  change (Z.of_nat (Z.to_nat (Z.log2 (Z.pos order)))) with 255.
  (rewrite_strat bottomup Z.mod_small); [ reflexivity | .. ]; try Lia.lia.
Qed.

Lemma x25519_base_ok : program_logic_goal_for_function! x25519_base.
Proof.
  repeat straightline.

  straightline_call; ssplit; try ecancel_assumption; repeat straightline; try listZnWords; [].
  straightline_call; ssplit; try ecancel_assumption; repeat straightline; try listZnWords; [].

  straightline_call; ssplit.
  { cbv [Field.FElem]. cbn. cbv [n]. ecancel_assumption_impl. }
  repeat straightline.

  seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a2) H21. { transitivity 40%nat; trivial. }

  straightline_call; ssplit.
  { unfold FElem, Field.FElem in *; extract_ex1_and_emp_in_goal; ssplit.
       { use_sep_assumption. cancel; repeat ecancel_step.
       cancel_seps_at_indices 0%nat 0%nat; trivial. cbn [seps]. reflexivity. }
    all : eauto.
    { instantiate (1:=None). exact I. } }
  { reflexivity. }
  { rewrite length_le_split. vm_compute. inversion 1. }
  repeat straightline.
  unfold FElem in H26. extract_ex1_and_emp_in H26.
  straightline_call; ssplit.
  { ecancel_assumption. }
  { transitivity 32%nat; auto. }
  { eexists. ecancel_assumption. }
  { intuition idtac. }
  repeat straightline_cleanup.
  repeat straightline.

  cbv [Field.FElem] in *.
  seprewrite_in @Bignum.Bignum_to_bytes H29.
  seprewrite_in @Bignum.Bignum_to_bytes H29.
  extract_ex1_and_emp_in H29.
  pose proof length_le_split 32 (Curve25519.clamp (le_combine s)).

  repeat straightline; intuition eauto.
  cbv [x25519_spec].
  use_sep_assumption; cancel.
  rewrite H33, le_combine_split.
  do 7 Morphisms.f_equiv.
  pose proof clamp_range (le_combine s).
  change (Z.of_nat (Z.to_nat (Z.log2 (Z.pos order)))) with 255.
  (rewrite_strat bottomup Z.mod_small); [ | Lia.lia .. ].
  lazymatch goal with
  | |- montladder_gallina _ _ _ ?x = _ => change x with (M.X0 M.B)
  end.
  unfold M.X0.
  rewrite (@montladder_gallina_equiv_affine (Curve25519.p) _ _ (Curve25519.field)) with
      (b_nonzero:=Curve25519.M.b_nonzero) (char_ge_3:=Curve25519.char_ge_3);
    [ | Lia.lia | vm_decide | apply M.a2m4_nonsq ].
  change (Z.of_nat (Z.to_nat (Z.log2 (Z.pos order)))) with 255.
  (rewrite_strat bottomup Z.mod_small); [ | Lia.lia .. ].
  reflexivity.
Qed.

Require Import coqutil.Word.Naive.
Require Import coqutil.Macros.WithBaseName.

Definition felem_cswap := CSwap.felem_cswap(word:=word32)(field_parameters:=field_parameters)(field_representaton:=field_representation n s c).
Definition fe25519_inv := fe25519_inv(word:=word32)(field_parameters:=field_parameters).

Definition funcs :=
  &[,x25519; x25519_base;
    montladder;
    fe25519_to_bytes;
    fe25519_from_bytes;
    fe25519_from_word;
    felem_cswap;
    fe25519_copy;
    fe25519_inv;
    ladderstep;
    fe25519_mul;
    fe25519_add;
    fe25519_sub;
    fe25519_square;
    fe25519_scmula24;
    clamp;
    memmove ].

Require Import bedrock2.ToCString.
Definition montladder_c_module := list_byte_of_string (ToCString.c_module funcs).

Lemma link_montladder : spec_of_montladder (map.of_list funcs).
Proof.
  unfold spec_of_montladder, ScalarMult.MontgomeryLadder.spec_of_montladder.
  unfold funcs.
  (* use montladder correctness proof *)
  rewrite montladder_defn.
  eapply @montladder_correct; try (typeclasses eauto).
  { reflexivity. }
  { Decidable.vm_decide. }
  { Decidable.vm_decide. }
  { reflexivity. }
  { eapply CSwap.cswap_body_correct; [|exact I|reflexivity].
    unfold field_representation, Signature.field_representation, Representation.frep; cbn; unfold n; cbv; trivial. }
  { eapply fe25519_copy_correct. reflexivity. }
  { eapply fe25519_from_word_correct. reflexivity. }
  {
    cbv [LadderStep.spec_of_ladderstep]; intros.
    rewrite ladderstep_defn.
    eapply @LadderStep.ladderstep_correct; try (typeclasses eauto).
    { cbv [Core.__rupicola_program_marker]; tauto. }
    { reflexivity. }
    { apply fe25519_mul_correct. reflexivity. }
    { apply fe25519_add_correct. reflexivity. }
    { apply fe25519_sub_correct. reflexivity. }
    { apply fe25519_square_correct. reflexivity. }
    { apply fe25519_scmula24_correct. reflexivity. }
    { ecancel_assumption. } }
  { unshelve eapply AdditionChains.fe25519_inv_correct_exp; [exact I|reflexivity| | ].
    { apply fe25519_square_correct. reflexivity. }
    { apply fe25519_mul_correct. reflexivity. } }
  { apply fe25519_mul_correct. reflexivity. }
Qed.
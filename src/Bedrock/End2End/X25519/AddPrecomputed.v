Require Import bedrock2.Array.
Require Import bedrock2.FE310CSemantics.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Scalars.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ZnWords.
Require Import compiler.MMIO.
Require Import compiler.Pipeline.
Require Import compiler.Symbols.
Require Import coqutil.Byte.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.OfListWord.
From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import Coq.Init.Byte.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Spec.Curve25519.
Require Import Curves.Edwards.XYZT.Precomputed.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

Local Existing Instance field_parameters.
Local Instance frep25519 : Field.FieldRepresentation := field_representation n Field25519.s c.
Local Existing Instance frep25519_ok.

Definition add_precomputed := func! (ox, oy, oz, ot, X1, Y1, Z1, T1, ypx2, ymx2, xy2d2) {
  stackalloc 40 as YpX1;
  fe25519_add(YpX1, Y1, X1);
  stackalloc 40 as YmX1;
  fe25519_sub(YmX1, Y1, X1);
  stackalloc 40 as A;
  fe25519_mul(A, YpX1, ypx2);
  stackalloc 40 as B;
  fe25519_mul(B, YmX1, ymx2);
  stackalloc 40 as C;
  fe25519_mul(C, xy2d2, T1);
  stackalloc 40 as Two;
  fe25519_from_word(Two, $2);
  stackalloc 40 as D;
  fe25519_mul(D, Z1, Two); (* TODO: Should be Z1 + Z1, but mul has tighter bounds *)
  fe25519_sub(ox, A, B);
  fe25519_add(oy, A, B);
  fe25519_add(oz, D, C);
  fe25519_sub(ot, D, C);
  fe25519_mul(ox, ox, ot);
  fe25519_mul(oy, oy, oz);
  fe25519_mul(oz, ot, oz);
  fe25519_mul(ot, ox, oy)
}.

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.

Local Coercion F.to_Z : F >-> Z.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
Local Notation word := (Naive.word 32).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).


Global Instance spec_of_add_precomputed : spec_of "add_precomputed" :=
  fnspec! "add_precomputed"
    (oxK oyK ozK otK X1K Y1K Z1K T1K ypx2K ymx2K xy2d2K : word) /
    (ox oy oz ot X1 Y1 Z1 T1 ypx2 ymx2 xy2d2 : felem) (R : _ -> Prop),
  { requires t m :=
      bounded_by tight_bounds X1 /\
      bounded_by tight_bounds Y1 /\
      bounded_by loose_bounds Z1 /\
      bounded_by loose_bounds T1 /\
      bounded_by loose_bounds ypx2 /\
      bounded_by loose_bounds ymx2 /\
      bounded_by loose_bounds xy2d2 /\
      m =* (FElem X1K X1) * (FElem Y1K Y1) * (FElem Z1K Z1) * (FElem T1K T1) * (FElem ypx2K ypx2) * (FElem ymx2K ymx2) * (FElem xy2d2K xy2d2) * (FElem oxK ox) * (FElem oyK oy) * (FElem ozK oz) * (FElem otK ot) * R;
    ensures t' m' :=
      t = t' /\
      exists ox' oy' oz' ot',
        ((feval ox'), (feval oy'), (feval oz'), (feval ot')) = (@m1add_precomputed_coordinates (F M_pos) (F.add) (F.sub) (F.mul) ((feval X1), (feval Y1), (feval Z1), (feval T1)) ((feval ypx2), (feval ymx2), (feval xy2d2))) /\
        bounded_by loose_bounds ox' /\
        bounded_by loose_bounds oy' /\
        bounded_by loose_bounds oz' /\
        bounded_by loose_bounds ot' /\
        m' =* (FElem X1K X1) * (FElem Y1K Y1) * (FElem Z1K Z1) * (FElem T1K T1) * (FElem ypx2K ypx2) * (FElem ymx2K ymx2) * (FElem xy2d2K xy2d2) * (FElem oxK ox') * (FElem oyK oy') * (FElem ozK oz') * (FElem otK ot') * R }.


Local Instance spec_of_fe25519_square : spec_of "fe25519_square" := Field.spec_of_UnOp un_square.
Local Instance spec_of_fe25519_mul : spec_of "fe25519_mul" := Field.spec_of_BinOp bin_mul.
Local Instance spec_of_fe25519_add : spec_of "fe25519_add" := Field.spec_of_BinOp bin_add.
Local Instance spec_of_fe25519_sub : spec_of "fe25519_sub" := Field.spec_of_BinOp bin_sub.
Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.

Local Ltac cbv_bounds H :=
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_sub un_outbounds bin_outbounds] in H;
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_sub un_outbounds bin_outbounds].

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by loose_bounds ?x => apply relax_bounds
  | H: bounded_by _ ?x |- bounded_by _ ?x => cbv_bounds H
  end.

Local Ltac solve_mem :=
  repeat match goal with
  | |- exists _ : _ -> Prop, _%sep _ => eexists
  | |- _%sep _ => ecancel_assumption
  end.

Local Ltac solve_stack :=
  (* Rewrites the `stack$@a` term in H to use a Bignum instead *)
  cbv [FElem];
  match goal with
  | H: _%sep ?m |- (Bignum.Bignum felem_size_in_words ?a _ * _)%sep ?m =>
       seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a) H
  end;
  [> transitivity 40%nat; trivial | ];
  (* proves the memory matches up *)
  use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat; cbn; [> trivial | eapply RelationClasses.reflexivity].

Local Ltac single_step :=
  repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_stack.

(* An example that demonstrates why we need to set Strategy in add_precomputed_ok below *)
Example demo_strategy : forall x,
  (@Field.bounded_by field_parameters (Zpos (xO (xO (xO (xO (xO xH))))))
        BW32 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
        (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
           (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
           byte) frep25519
        (@loose_bounds field_parameters (Zpos (xO (xO (xO (xO (xO xH))))))
           BW32 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
           (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
              (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
              byte) frep25519) x =
          @Field.bounded_by field_parameters (Zpos (xO (xO (xO (xO (xO xH))))))
        BW32 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
        (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
           (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
           byte) frep25519
        (@bin_outbounds (Zpos (xO (xO (xO (xO (xO xH)))))) BW32
           (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
           (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
              (Naive.word (Zpos (xO (xO (xO (xO (xO xH))))))) Naive.word32_ok
              byte) field_parameters frep25519 (@add field_parameters)
           (@bin_add (Zpos (xO (xO (xO (xO (xO xH)))))) BW32
              (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
              (@SortedListWord.map (Zpos (xO (xO (xO (xO (xO xH))))))
                 (Naive.word (Zpos (xO (xO (xO (xO (xO xH)))))))
                 Naive.word32_ok byte) field_parameters frep25519)) x).
Proof.
  (* reflexivity. *) (* Does not complete within 1 minute. *)
  (* Now set Strategy precedence... *)
  Strategy -1000 [bin_outbounds bin_add].
  reflexivity. (* ...and completes immediately *)
Qed.

Lemma add_precomputed_ok : program_logic_goal_for_function! add_precomputed.
Proof.
  (* Without this, resolution of cbv stalls out Qed. *)
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_sub un_outbounds bin_outbounds].

  (* Unwrap each call in the program. *)
  (* Each binop produces 2 memory goals on the inputs, 2 bounds goals on the inputs, and 1 memory goal on the output. *)
  single_step. (* fe25519_add(YpX1, Y1, X1) *)
  single_step. (* fe25519_sub(YmX1, Y1, X1) *)
  single_step. (* fe25519_mul(A, YpX1, ypx2) *)
  single_step. (* fe25519_mul(B, YmX1, ymx2) *)
  single_step. (* fe25519_mul(C, xy2d2, T1) *)
  single_step. (* fe25519_from_word(Two, $2) *)
  single_step. (* fe25519_mul(D, Z1, Two) *)
  single_step. (* fe25519_sub(ox, A, B) *)
  single_step. (* fe25519_add(oy, A, B) *)
  single_step. (* fe25519_add(oz, D, C) *)
  single_step. (* fe25519_sub(ot, D, C) *)
  single_step. (* fe25519_mul(ox, ox, ot) *)
  single_step. (* fe25519_mul(oy, oy, oz) *)
  single_step. (* fe25519_mul(oz, ot, oz) *)
  single_step. (* fe25519_mul(ot, ox, oy) *)

  (* Solve the postconditions *)
  repeat straightline.
  (* Rewrites the FElems for the stack (in H96) to be about bytes instead *)
    cbv [FElem] in *.
    (* Prevent output from being rewritten by seprewrite_in *) 
    remember (Bignum.Bignum felem_size_in_words otK _) as Pt in H96.
    remember (Bignum.Bignum felem_size_in_words ozK _) as Pz in H96.
    remember (Bignum.Bignum felem_size_in_words oyK _) as Py in H96.
    remember (Bignum.Bignum felem_size_in_words oxK _) as Px in H96.
    do 7 (seprewrite_in @Bignum.Bignum_to_bytes H96).
    subst Pt Pz Py Px.
    extract_ex1_and_emp_in H96.

  (* Solve stack/memory stuff *)
  repeat straightline.

  (* Post-conditions *)
  exists x10,x11,x12,x13; ssplit. 2,3,4,5:solve_bounds.
  { (* Correctness: result matches Gallina *)
    cbv [bin_model bin_mul bin_add bin_sub] in *.
    cbv match beta delta [m1add_precomputed_coordinates].
    assert ((feval Z1 * F.of_Z M_pos (word.of_Z(width:=32) 2))%F = (feval Z1 + feval Z1)%F) as <-.
    { rewrite word.unsigned_of_Z_nowrap by lia. apply F.eq_to_Z_iff. rewrite F.to_Z_mul. rewrite F.to_Z_add. 
      rewrite F.to_Z_of_Z. f_equal. rewrite Z.mod_small. all:lia. }
    congruence.
  }
  (* Safety: memory is what it should be *)
  ecancel_assumption.
Qed.

End WithParameters.

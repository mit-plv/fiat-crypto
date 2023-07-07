Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
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
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.FE310CSemantics bedrock2.Semantics .
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import bedrock2.ZnWords.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.NotationsCustomEntry.
Require Import Curves.Edwards.XYZT.Precomputed.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import ListNotations.

Local Instance frep25519 : Field.FieldRepresentation(field_parameters:=field_parameters) := field_representation n Field25519.s c.

(* Better way to represent points in Bedrock2? *)
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
  stackalloc 40 as D;
  fe25519_mul(D, Z1, $2); (* Should be Z1 + Z1, but mul has tighter bounds *)
  fe25519_sub(ox, A, B);
  fe25519_add(oy, A, B);
  fe25519_add(oz, D, C);
  fe25519_sub(ot, D, C);
  fe25519_mul(ox, ox, ot);
  fe25519_mul(oy, oy, oz);
  fe25519_mul(oz, ot, oz);
  fe25519_mul(ot, ox, oy)
}.

Definition add_precomputed_partial := func! (ox, oy, X1, Y1, T1, ypx2, ymx2, xy2d2) {
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
  (* stackalloc 40 as Two;
  fe25519_from_word(Two, $2);
  stackalloc 40 as D;
  fe25519_mul(D, Z1, Two); *)
  fe25519_sub(ox, A, B);
  fe25519_add(oy, A, B)
}.

Section WithParameters.
  Check _: FieldRepresentation.

Import LittleEndianList.
Local Coercion F.to_Z : F >-> Z.
Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.Syntax bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.OfListWord Coq.Init.Byte coqutil.Byte.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing) (* experiment*).
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
        (* Need to specify implicit parameters? *)
        ((feval ox'), (feval oy'), (feval oz'), (feval ot')) = (@m1add_precomputed_coordinates (F M_pos) (F.add) (F.sub) (F.mul) ((feval X1), (feval Y1), (feval Z1), (feval T1)) ((feval ypx2), (feval ymx2), (feval xy2d2))) /\
        bounded_by loose_bounds ox' /\
        bounded_by loose_bounds oy' /\
        bounded_by loose_bounds oz' /\
        bounded_by loose_bounds ot' /\
        m' =* (FElem X1K X1) * (FElem Y1K Y1) * (FElem Z1K Z1) * (FElem T1K T1) * (FElem ypx2K ypx2) * (FElem ymx2K ymx2) * (FElem xy2d2K xy2d2) * (FElem oxK ox') * (FElem oyK oy') * (FElem ozK oz') * (FElem otK ot') * R }.

Global Instance spec_of_add_precomputed_partial : spec_of "add_precomputed_partial" :=
  fnspec! "add_precomputed_partial"
    (oxK oyK X1K Y1K T1K ypx2K ymx2K xy2d2K : word) /
    (ox oy X1 Y1 T1 ypx2 ymx2 xy2d2 : felem) (R : _ -> Prop),
  { requires t m :=
      bounded_by tight_bounds X1 /\
      bounded_by tight_bounds Y1 /\
      bounded_by loose_bounds T1 /\
      bounded_by loose_bounds ypx2 /\
      bounded_by loose_bounds ymx2 /\
      bounded_by loose_bounds xy2d2 /\
      m =* (FElem X1K X1) * (FElem Y1K Y1) * (FElem T1K T1) * (FElem ypx2K ypx2) * (FElem ymx2K ymx2) * (FElem xy2d2K xy2d2) * (FElem oxK ox) * (FElem oyK oy) * R;
    ensures t' m' :=
      t = t' /\
      exists ox' oy',
        bounded_by loose_bounds ox' /\
        bounded_by loose_bounds oy' /\
        m' =* (FElem X1K X1) * (FElem Y1K Y1) * (FElem T1K T1) * (FElem ypx2K ypx2) * (FElem ymx2K ymx2) * (FElem xy2d2K xy2d2) * (FElem oxK ox') * (FElem oyK oy') * R }.


Local Instance spec_of_fe25519_square : spec_of "fe25519_square" := Field.spec_of_UnOp un_square.
Local Instance spec_of_fe25519_mul : spec_of "fe25519_mul" := Field.spec_of_BinOp bin_mul.
Local Instance spec_of_fe25519_add : spec_of "fe25519_add" := Field.spec_of_BinOp bin_add.
Local Instance spec_of_fe25519_sub : spec_of "fe25519_sub" := Field.spec_of_BinOp bin_sub.

Import WeakestPrecondition.

From coqutil.Tactics Require Import Tactics letexists eabstract rdelta reference_to_string ident_of_string.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Loops.
Require Import bedrock2.Map.SeparationLogic bedrock2.Scalars.

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
  | H: bounded_by _ ?x |- bounded_by _ ?x => cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_sub un_outbounds bin_outbounds] in *
  end.

Local Ltac solve_mem :=
  repeat match goal with
  | |- exists _ : _ -> Prop, _%sep _ => eexists
  | |- _%sep _ => ecancel_assumption
  end.

Local Ltac unwrap_fn_step := repeat straightline; straightline_call; ssplit.

(* Local Ltac solve_stack := *)

Local Ltac solve_stack a :=
  (* Rewrites the `stack$@a` term in H to use a Bignum instead *)
  cbv [FElem];
  match goal with
  | H: _%sep ?m |- (Bignum.Bignum felem_size_in_words a _ * _)%sep ?m =>
       seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a) H
  end;
  [> transitivity 40%nat; trivial | ];
  (* proves the memory matches up *)
  use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat; cbn; [> trivial | eapply RelationClasses.reflexivity].

Lemma add_precomputed_partial_ok : program_logic_goal_for_function! add_precomputed_partial.
Proof.
  (* Unwrap each call in the program. *)
  (* Each produces 2 memory goals about the inputs, 2 bounds preconditions on the inputs, and 1 memory goal about the output. *)
  unwrap_fn_step. 3,4:solve_mem. 1,2:solve_bounds. solve_stack a.
  unwrap_fn_step. 3,4:solve_mem. 1,2:solve_bounds. solve_stack a2.
  unwrap_fn_step. 3,4:solve_mem. 1,2:solve_bounds. solve_stack a0.
  unwrap_fn_step. 3,4:solve_mem. 1,2:solve_bounds. solve_stack a4.
  unwrap_fn_step. 3,4:solve_mem. 1,2:solve_bounds. solve_stack a7.
  unwrap_fn_step. 3,4:solve_mem. 1,2:solve_bounds. ecancel_assumption.
  unwrap_fn_step. 3,4:solve_mem. 1,2:solve_bounds. ecancel_assumption.

  (* Solve the postconditions *)
  repeat straightline.
  (* Rewrites the FElem about `a` in H11 to be about bytes instead, so we can use it to prove things about `a` as bytes *)
    cbv [FElem] in *.
    (* seprewrite_in (@Bignum.Bignum_to_bytes felem_size_in_words a7 x3) H55. *) (* Ought to be able to specify a7, but types don't match *)
    seprewrite_in @Bignum.Bignum_to_bytes H55.
    seprewrite_in @Bignum.Bignum_to_bytes H55.
    seprewrite_in @Bignum.Bignum_to_bytes H55.
    seprewrite_in @Bignum.Bignum_to_bytes H55.
    seprewrite_in @Bignum.Bignum_to_bytes H55.
    seprewrite_in @Bignum.Bignum_to_bytes H55.
    seprewrite_in @Bignum.Bignum_to_bytes H55.
    extract_ex1_and_emp_in H55.

    (* Solve stack/memory stuff *)
    repeat straightline.

    (* Post-conditions *)
    exists x4,x5; (* eexists? *) ssplit. 1,2:solve_bounds.
    seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 oxK) H55. { transitivity 40%nat; trivial. }
    seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 oyK) H55. { transitivity 40%nat; trivial. }
    use_sep_assumption. cancel. cancel_seps_at_indices 0%nat 1%nat; cbn.
    (* Bignum.Bignum 10 oyK (map (c => word.of_Z (le_combine c)) (List.chunk (Pos.to_nat 4) (flat_map (w => le_split (Pos.to_nat 4) w) x5))) = Bignum.Bignum n oyK x5 *)
    admit.
    (* Bignum.Bignum 10 oxK (map (c => word.of_Z (le_combine c)) (List.chunk (Pos.to_nat 4) (flat_map (w => le_split (Pos.to_nat 4) w) x4))) = Bignum.Bignum n oyK x4 *)
    admit.
Admitted.

Lemma add_precomputed_ok : program_logic_goal_for_function! add_precomputed.
Proof.
  repeat straightline.
  unwrap_calls.
  - apply H14. (* bounded_by bin_xbounds Y1 *) (* solve_bounds. *)
  - apply H13. (* bounded_by bin_ybounds X1 *) (* solve_bounds. *)
  - eexists. ecancel_assumption.
  - eexists. ecancel_assumption.
  - shelve. (* (FElem a ?out ⋆ ?Rr)%sep m *)
  - auto. (* 40 mod bytes_per_word 32 = 0 *)
  - apply H14. (* bounded_by bin_xbounds ?x@{a1:=a0; H29:=H30; mCombined:=a1} *)
  - apply H13. (* bounded_by bin_ybounds ?y@{a1:=a0; H29:=H30; mCombined:=a1} *)
  - eexists. ecancel_assumption. (* exists Rx : SortedListWord.map word Init.Byte.byte -> Prop, (FElem Y1K Y1 ⋆ Rx)%sep a1 *)
  - eexists.  ecancel_assumption. (* exists Ry : SortedListWord.map word Init.Byte.byte -> Prop, (FElem X1K X1 ⋆ Ry)%sep a1 *)
  - (* (FElem a2 ?out0@{a1:=a0; H29:=H30; mCombined:=a1} ⋆ ?Rr0@{a1:=a0; H29:=H30; mCombined:=a1})%sep a1 *)
  - (* 40 mod bytes_per_word 32 = 0 *)
  - (* bounded_by bin_xbounds ?x@{a1:=a5; H29:=H37; mCombined:=a1; a4:=a3; H34:=H35; mCombined0:=a4} *)

 (* (FElem a ?out ⋆ FElem Y1K ?x0)%sep m *) eexists. exists m. split. solve_mem.

 all: try solve_bounds.
  (* post-conditions *)
  - exists x1. split. 2:split.
    + (* math adds up *) simpl in H9. simpl in H6. rewrite H6 in H9. simpl. apply H9. (* Definitely better tactics for this *)
    + (* postcondition bounds on out *) simpl in H10. simpl. apply H10. (* should just work to apply H10... *)
    + (* postcondition mem sep *) ecancel_assumption.
Qed.

End WithParameters.

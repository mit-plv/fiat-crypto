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
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import ListNotations.

Local Instance frep25519 : Field.FieldRepresentation(field_parameters:=field_parameters) := field_representation n Field25519.s c.

Require Import bedrock2.NotationsCustomEntry.

Definition square_and_add := func! (o, x, y) {
  fe25519_square(o, x);
  fe25519_add(o, o, y)
}.

Definition mul_and_add := func! (o, x, y) {
  fe25519_mul(o, x, x);
  fe25519_add(o, o, y)
}.

Require Import bedrock2.FE310CSemantics bedrock2.Semantics .
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array bedrock2.Scalars.
Require Import bedrock2.ZnWords.
Require Import coqutil.Tactics.Tactics.

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

Global Instance spec_of_square_and_add : spec_of "square_and_add" :=
  fnspec! "square_and_add" (out xk yk: word) / (o x y : felem) (R : _ -> Prop),
  { requires t m :=
      bounded_by loose_bounds x /\
      bounded_by tight_bounds y /\
      m =* (FElem xk x) * (FElem yk y) * (FElem out o) * R;
    ensures t' m' :=
      t=t' /\
      exists o', feval o' = F.add (F.pow (feval x) 2) (feval y)
        /\ bounded_by loose_bounds o'
        /\ m' =* (FElem xk x) * (FElem yk y) * (FElem out o') * R }.

Global Instance spec_of_mul_and_add : spec_of "mul_and_add" :=
  fnspec! "mul_and_add" (out xk yk: word) / (o x y : felem) (R : _ -> Prop),
  { requires t m :=
      bounded_by loose_bounds x /\
      bounded_by tight_bounds y /\
      m =* (FElem xk x) * (FElem yk y) * (FElem out o) * R;
    ensures t' m' :=
      t=t' /\
      exists o', feval o' = F.add (F.mul (feval x) (feval x)) (feval y)
        /\ bounded_by loose_bounds o'
        /\ m' =* (FElem xk x) * (FElem yk y) * (FElem out o') * R }.

Local Instance spec_of_fe25519_square : spec_of "fe25519_square" := Field.spec_of_UnOp un_square.
Local Instance spec_of_fe25519_mul : spec_of "fe25519_mul" := Field.spec_of_BinOp bin_mul.
Local Instance spec_of_fe25519_add : spec_of "fe25519_add" := Field.spec_of_BinOp bin_add.

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
Lemma square_and_add_ok : program_logic_goal_for_function! square_and_add.
Proof.
  repeat straightline.
  repeat match goal with
  | |- _ /\ _ => split
  | |- call _ _ _ _ _ _ => straightline_call
  | _ => straightline
  end.
  (* square *)
  - (* square precondition bounds on x *) apply H1.
  - (* mem sep for x *) eexists. ecancel_assumption.
  - (* mem sep for out *) ecancel_assumption.
  (* add *)
  - (* add precondition bounds on x^2 *) apply H7.
  - (* add precondition bounds on y *) apply H2.
  - (* mem sep for o (holding x^2) *) eexists. ecancel_assumption.
  - (* mem sep for y *) eexists. ecancel_assumption.
  - (* mem sep for o (holding x^2+y) *) ecancel_assumption.
  (* post-conditions *)
  - exists x1. split. 2:split.
    + (* math adds up *) simpl in H9. simpl in H6. rewrite H6 in H9. simpl. apply H9. (* Definitely better tactics for this *)
    + (* postcondition bounds on out *) simpl in H10. simpl. apply H10. (* should just work to apply H10... *)
    + (* postcondition mem sep *) ecancel_assumption.
Qed.

Local Ltac unwrap_calls :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- call _ _ _ _ _ _ => straightline_call
  | _ => straightline
  end.

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds _ |- bounded_by loose_bounds _ => apply H
  | H: bounded_by tight_bounds _ |- bounded_by tight_bounds _ => apply H
  | H: bounded_by _ _ |- bounded_by _ _ => cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add un_outbounds bin_outbounds] in *
  end.

Local Ltac solve_mem :=
  repeat match goal with
  | |- exists _, _%sep _ => eexists
  | |- _%sep _ => ecancel_assumption
  end.

Lemma square_and_add_ok2 : program_logic_goal_for_function! square_and_add.
Proof.
  repeat straightline.
  unwrap_calls.
  all: try solve_mem. all: try solve_bounds.
  (* post-conditions *)
  - exists x1. split. 2:split.
    + (* math adds up *) simpl in H9. simpl in H6. rewrite H6 in H9. simpl. apply H9. (* Definitely better tactics for this *)
    + (* postcondition bounds on out *) simpl in H10. simpl. apply H10. (* should just work to apply H10... *)
    + (* postcondition mem sep *) ecancel_assumption.
Qed.

Lemma mul_and_add_ok : program_logic_goal_for_function! mul_and_add.
Proof.
  repeat straightline.
  repeat match goal with
  | |- _ /\ _ => split
  | |- call _ _ _ _ _ _ => straightline_call
  | _ => straightline
  end.
  (* square *)
  - (* mul precondition bounds on x *) apply H1.
  - (* same bounds gain *) apply H1.
  - (* mem sep for x *) eexists. ecancel_assumption.
  - (* same mem sep again *) eexists. ecancel_assumption.
  - (* mem sep for out *) ecancel_assumption.
  (* add *)
  - (* add precondition bounds on x^2 *) apply H7.
  - (* add precondition bounds on y *) apply H2.
  - (* mem sep for o (holding x^2) *) eexists. ecancel_assumption.
  - (* mem sep for y *) eexists. ecancel_assumption.
  - (* mem sep for o (holding x^2+y) *) ecancel_assumption.
  (* post-conditions *)
  - exists x1. split. 2:split.
    + (* math adds up *) simpl in H9. simpl in H6. rewrite H6 in H9. simpl. apply H9. (* Definitely better tactics for this *)
    + (* postcondition bounds on out *) simpl in H10. simpl. apply H10. (* should just work to apply H10... *)
    + (* postcondition mem sep *) ecancel_assumption.
Qed.


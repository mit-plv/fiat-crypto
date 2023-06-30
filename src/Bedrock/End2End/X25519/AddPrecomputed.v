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

Definition add_precomputed_partial := func! (X1, Y1) {
  stackalloc 40 as YpX1;
  fe25519_add(YpX1, Y1, X1);
  stackalloc 40 as YmX1;
  fe25519_sub(YmX1, Y1, X1)
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
    (X1K Y1K : word) /
    (X1 Y1 : felem) (R : _ -> Prop),
  { requires t m :=
      bounded_by tight_bounds X1 /\
      bounded_by tight_bounds Y1 /\
      m =* (FElem X1K X1) * (FElem Y1K Y1) * R;
    ensures t' m' :=
      t = t' /\
      m' =* (FElem X1K X1) * (FElem Y1K Y1) * R }.


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
Local Ltac unwrap_calls :=
  repeat match goal with
  | |- _ /\ _ => split
  | |- call _ _ _ _ _ _ => straightline_call
  | _ => straightline
  end.

Local Ltac solve_stack :=
  match goal with
  | |- 40 mod bytes_per_word 32 = 0 => auto
  end.

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds _ |- bounded_by loose_bounds _ => apply H
  | H: bounded_by tight_bounds _ |- bounded_by tight_bounds _ => apply H
  | H: bounded_by _ _ |- bounded_by _ _ => cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_sub un_outbounds bin_outbounds] in *
  end.

Local Ltac solve_mem :=
  repeat match goal with
  | |- exists _ : _ -> Prop, _%sep _ => eexists
  | |- _%sep _ => ecancel_assumption
  end.

Lemma add_precomputed_partial_ok : program_logic_goal_for_function! add_precomputed_partial.
Proof.
  repeat straightline.
  unwrap_calls.
  all: try solve_stack. (* all: try solve_mem. all: try solve_bounds *) (* Too aggressive somewhere... *)
  3: solve_mem. 3: solve_mem.
  solve_bounds. solve_bounds.
  - (* (FElem a ?out ⋆ ?Rr)%sep m *)
    (* Rewrites the `stack$@a` term in H3 to use a Bignum instead *)
    cbv [FElem].
    seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a) H3. { transitivity 40%nat; trivial. }
    use_sep_assumption.
    cancel. cancel_seps_at_indices 0%nat 0%nat; cbn; trivial.
    eapply RelationClasses.reflexivity.
  - apply H2. (* bounded_by bin_xbounds ?x@{a1:=a0; H12:=H13; mCombined:=a1} *)
  - apply H1. (* bounded_by bin_ybounds ?y@{a1:=a0; H12:=H13; mCombined:=a1} *)
  - solve_mem.
  - solve_mem.
  - (* (FElem a2 ?out@{a1:=a0; H12:=H13; mCombined:=a1} ⋆ ?Rr@{a1:=a0; H12:=H13; mCombined:=a1})%sep a1 *)
    cbv [FElem].
    seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 10 a2) H12. { transitivity 40%nat; trivial. }
    use_sep_assumption.
    cancel. repeat ecancel_step. cancel_seps_at_indices 0%nat 0%nat; cbn. admit. (* I think context of evars is causing problems? *)
    eapply RelationClasses.reflexivity.
  - (* exists m' mStack' : SortedListWord.map word Init.Byte.byte,
  anybytes a 40 mStack' /\
  map.split a1 m' mStack' /\ list_map (get l0) [] (fun rets : list word => rets = [] /\ a0 = a0 /\ (FElem X1K X1 ⋆ FElem Y1K Y1 ⋆ R)%sep m') *)
    (* Rewrites the FElem about `a` in H11 to be about bytes instead, so we can use it to prove things about `a` as bytes *)
    cbv [FElem] in *.
    seprewrite_in @Bignum.Bignum_to_bytes H17.
    seprewrite_in @Bignum.Bignum_to_bytes H17.
    extract_ex1_and_emp_in H17.

    repeat straightline; intuition eauto.
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

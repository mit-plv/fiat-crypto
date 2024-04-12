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
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.End2End.Secp256k1.Field256k1.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.Decidable.
Require Import Curves.Weierstrass.Jacobian.Jacobian.
Require Import Curves.Weierstrass.Jacobian.CoZ.
Require Import Lia.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import LittleEndianList.
Import ListNotations.
Import ProgramLogic.Coercions.
Import WeakestPrecondition.

Local Existing Instance field_parameters.
Local Instance frep256k1 : Field.FieldRepresentation := field_representation Field256k1.m.
Local Existing Instance frep256k1_ok.

(* P = (X1, Y1, Z1)
   Q = (X2, Y2, Z2)
   Returns P + Q = (OX1, OY1, OZ1)
           P     = (OX2, OY2, OZ2)
*)
Definition secp256k1_zaddu :=
  func! (OX1, OY1, OZ1, OX2, OY2, OZ2, X1, Y1, Z1, X2, Y2, Z2) {
    stackalloc 32 as T1;
    stackalloc 32 as T2;
    stackalloc 32 as T3;
    stackalloc 32 as T4;
    stackalloc 32 as T5;
    stackalloc 32 as T6;
    secp256k1_felem_copy(T1, X1);
    secp256k1_felem_copy(T2, Y1);
    secp256k1_felem_copy(T3, Z1);
    secp256k1_felem_copy(T4, X2);
    secp256k1_felem_copy(T5, Y2);
    secp256k1_sub(T6, T1, T4);     (* let t6 := t1 - t4 in *)
    secp256k1_mul(T3, T3, T6);     (* let t3 := t3 * t6 in *)
    secp256k1_square(T6, T6);      (* let t6 := t6^2 in *)
    secp256k1_mul(T1, T1, T6);     (* let t1 := t1 * t6 in *)
    secp256k1_mul(T6, T6, T4);     (* let t6 := t6 * t4 in *)
    secp256k1_sub(T5, T2, T5);     (* let t5 := t2 - t5 in *)
    secp256k1_square(T4, T5);      (* let t4 := t5^2 in *)
    secp256k1_sub(T4, T4, T1);     (* let t4 := t4 - t1 in *)
    secp256k1_sub(T4, T4, T6);     (* let t4 := t4 - t6 in *)
    secp256k1_sub(T6, T1, T6);     (* let t6 := t1 - t6 in *)
    secp256k1_mul(T2, T2, T6);     (* let t2 := t2 * t6 in *)
    secp256k1_sub(T6, T1, T4);     (* let t6 := t1 - t4 in *)
    secp256k1_mul(T5, T5, T6);     (* let t5 := t5 * t6 in *)
    secp256k1_sub(T5, T5, T2);     (* let t5 := t5 - t2 in *)
    secp256k1_felem_copy(OX1, T4); (* ((t4, t5, t3), (t1, t2, t3)) *)
    secp256k1_felem_copy(OY1, T5);
    secp256k1_felem_copy(OZ1, T3);
    secp256k1_felem_copy(OX2, T1);
    secp256k1_felem_copy(OY2, T2);
    secp256k1_felem_copy(OZ2, T3)
}.

(* Compute ToCString.c_func ("secp256k1_zaddu", secp256k1_zaddu). *)

Section WithParameters.
  Context {two_lt_M: 2 < M_pos}.
  (* TODO: Can we provide actual values/proofs for these, rather than just sticking them in the context? *)
  Context {char_ge_3 : (@Ring.char_ge (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul (BinNat.N.succ_pos BinNat.N.two))}.
  Context {field:@Algebra.Hierarchy.field (F M_pos) Logic.eq F.zero F.one F.opp F.add F.sub F.mul F.inv F.div}.
  Context {a b : F M_pos}
          {zero_a : a = F.zero}
          {seven_b : b = F.of_Z _ 7}.

  Local Coercion F.to_Z : F >-> Z.
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
  Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

  Local Notation FElem := (FElem(FieldRepresentation:=frep256k1)).
  Local Notation word := (Naive.word 32).
  Local Notation felem := (felem(FieldRepresentation:=frep256k1)).
  Local Notation point := (Jacobian.point(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)(Feq_dec:=F.eq_dec)).
  Local Notation co_z := (Jacobian.co_z(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fadd:=F.add)(Fmul:=F.mul)(a:=a)(b:=b)(Feq_dec:=F.eq_dec)).
  Local Notation zaddu :=
    (Jacobian.zaddu(F:=F M_pos)(Feq:=Logic.eq)(Fzero:=F.zero)(Fone:=F.one)
       (Fopp:=F.opp)(Fadd:=F.add)(Fsub:=F.sub)(Fmul:=F.mul)(Finv:=F.inv)(Fdiv:=F.div)
       (a:=a)(b:=b)(field:=field)(Feq_dec:=F.eq_dec)).

  Global Instance spec_of_zaddu : spec_of "secp256k1_zaddu" :=
    fnspec! "secp256k1_zaddu"
      (OX1K OY1K OZ1K OX2K OY2K OZ2K X1K Y1K Z1K X2K Y2K Z2K : word) /
      (OX1 OY1 OZ1 OX2 OY2 OZ2 X1 Y1 Z1 X2 Y2 Z2 : felem) (P Q : point)
      (HPQ : co_z P Q) (R : _ -> Prop),
    { requires t m :=
        proj1_sig P = ((feval X1), (feval Y1), (feval Z1)) /\
        proj1_sig Q = ((feval X2), (feval Y2), (feval Z2)) /\
        (* bounded_by loose_bounds X1 /\ *)
        (* bounded_by loose_bounds Y1 /\ *)
        (* bounded_by loose_bounds Z1 /\ *)
        (* bounded_by loose_bounds X2 /\ *)
        (* bounded_by loose_bounds Y2 /\ *)
        (* bounded_by loose_bounds Z2 /\ *)
        m =* (FElem OX1K OX1) * (FElem OY1K OY1) * (FElem OZ1K OZ1) *
             (FElem OX2K OX2) * (FElem OY2K OY2) * (FElem OZ2K OZ2) *
             (FElem X1K X1) * (FElem Y1K Y1) * (FElem Z1K Z1) *
             (FElem X2K X2) * (FElem Y2K Y2) * (FElem Z2K Z2) * R;
      ensures t' m' :=
        t = t' /\
        exists OX1' OY1' OZ1' OX2' OY2' OZ2',
        proj1_sig (fst (zaddu P Q HPQ)) = ((feval OX1'), (feval OY1'), (feval OZ1')) /\
        proj1_sig (snd (zaddu P Q HPQ)) = ((feval OX2'), (feval OY2'), (feval OZ2')) /\
        (* bounded_by tight_bounds OX1' /\ *)
        (* bounded_by tight_bounds OY1' /\ *)
        (* bounded_by tight_bounds OZ1' /\ *)
        (* bounded_by tight_bounds OX2' /\ *)
        (* bounded_by tight_bounds OY2' /\ *)
        (* bounded_by tight_bounds OZ2' /\ *)
        m' =* (FElem OX1K OX1') * (FElem OY1K OY1') * (FElem OZ1K OZ1') *
              (FElem OX2K OX2') * (FElem OY2K OY2') * (FElem OZ2K OZ2') *
              (FElem X1K X1) * (FElem Y1K Y1) * (FElem Z1K Z1) *
              (FElem X2K X2) * (FElem Y2K Y2) * (FElem Z2K Z2) * R
    }.

  Local Instance spec_of_secp256k1_opp : spec_of "secp256k1_opp" := Field.spec_of_UnOp un_opp.
  Local Instance spec_of_secp256k1_square : spec_of "secp256k1_square" := Field.spec_of_UnOp un_square.
  Local Instance spec_of_secp256k1_mul : spec_of "secp256k1_mul" := Field.spec_of_BinOp bin_mul.
  Local Instance spec_of_secp256k1_add : spec_of "secp256k1_add" := Field.spec_of_BinOp bin_add.
  Local Instance spec_of_secp256k1_sub : spec_of "secp256k1_sub" := Field.spec_of_BinOp bin_carry_sub.
  Local Instance spec_of_secp256k1_felem_copy : spec_of "secp256k1_felem_copy" := Field.spec_of_felem_copy.

  Local Arguments word.rep : simpl never.
  Local Arguments word.wrap : simpl never.
  Local Arguments word.unsigned : simpl never.
  Local Arguments word.of_Z : simpl never.

  Local Ltac solve_mem :=
    repeat match goal with
      | |- exists _ : _ -> Prop, _%sep _ => eexists
      | |- _%sep _ => ecancel_assumption
      end.

  Local Ltac cbv_bounds H :=
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
    cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

  Local Ltac solve_bounds :=
    repeat match goal with
      | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
      | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
      | H: bounded_by tight_bounds ?x |- bounded_by loose_bounds ?x => apply relax_bounds
      | H: bounded_by _ ?x |- bounded_by _ ?x => cbv_bounds H
      end.

  Local Ltac solve_stack :=
    (* Rewrites the `stack$@a` term in H to use a Bignum instead *)
    cbv [FElem];
    match goal with
    | H: _%sep ?m |- (Bignum.Bignum felem_size_in_words ?a _ * _)%sep ?m =>
        seprewrite_in (@Bignum.Bignum_of_bytes _ _ _ _ _ _ 8 a) H
    end;
    [> transitivity 32%nat; trivial | ];
    (* proves the memory matches up *)
    use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat; cbn; [> trivial | eapply RelationClasses.reflexivity].

  Local Ltac single_step :=
    repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_stack.

  Lemma zaddu_ok : program_logic_goal_for_function! secp256k1_zaddu.
  Proof.
    Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub un_outbounds bin_outbounds].
    Compute felem_copy.
    single_step.

    repeat straightline.
    eapply Proper_call; cycle -1;
      [ | try eabstract (solve [ Morphisms.solve_proper ]).. ];
      [ .. | intros ? ? ? ? ].
    eapply H12.



    eapply Proper_call; [try eabstract (solve [ Morphisms.solve_proper ]).. |].
    intros ? ? ? ?. eexists. split. cbv.


    unfold program_logic_goal_for. intros.
    unfold spec_of_zaddu. intros. eapply Proper_call; cycle -1.
    eapply start_func; eauto. unfold func.
    


    repeat straightline.
    eapply Proper_call; cycle -1.
    unfold call.
    eapply spec_of_secp256k1_sub.

    straightline_call.
    single_step.




Compute (ToCString.c_func ("ZADDU", ZADDU)).

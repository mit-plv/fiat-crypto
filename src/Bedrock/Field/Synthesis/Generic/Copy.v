Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Specialized.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.X25519_64.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import bedrock2.Semantics.

Require Import Crypto.Bedrock.Field.Interface.Representation.

Import ListNotations.
Import Syntax.Coercions.
Local Open Scope Z_scope.

Existing Instances
         Defaults64.default_parameters names
         curve25519_bedrock2_funcs curve25519_bedrock2_specs
         curve25519_bedrock2_correctness.
Local Open Scope string_scope.

(* Notations to make spec more readable *)
Local Notation n := X25519_64.n.
Local Notation s := X25519_64.s.
Local Notation c := X25519_64.c.
Local Notation machine_wordsize := X25519_64.machine_wordsize.
Local Notation M := (UnsaturatedSolinas.m s c).
Local Notation weight :=
  (ModOps.weight (QArith_base.Qnum
                    (UnsaturatedSolinasHeuristics.limbwidth n s c))
                 (Z.pos (QArith_base.Qden
                           (UnsaturatedSolinasHeuristics.limbwidth n s c)))).
Local Notation eval := (Positional.eval weight n).
Local Notation loose_bounds := (UnsaturatedSolinasHeuristics.loose_bounds n s c).
Local Notation tight_bounds := (UnsaturatedSolinasHeuristics.tight_bounds n s c).
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Util.ZRange.

Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.


  Lemma anybytes_S pout n 
    : Lift1Prop.iff1 (anybytes pout (bytes_per_word width * Z.of_nat (S n)))%sep
                     (Lift1Prop.ex1(fun x =>(anybytes pout (bytes_per_word width * Z.of_nat n))
                                            * (Scalars.scalar
           (word.add pout
                     (word.of_Z
                        (bytes_per_word width * Z.of_nat n))) x)))%sep.
  Proof using.
  Admitted.

Section FImpl.
  Context {field_parameters : FieldParameters}.
  Context (sz : nat) (weight : nat -> Z)
          (loose_bounds tight_bounds : list (option zrange))
          (relax_bounds :
             forall X : list Z,
               list_Z_bounded_by tight_bounds X ->
               list_Z_bounded_by loose_bounds X).

  Local Definition frep := (frep sz weight loose_bounds tight_bounds).
  
  Existing Instance field_parameters.
  Existing Instance semantics.
  Existing Instance frep.
  Existing Instance frep_ok.

  Definition copy_spec :=
    (@spec_of_felem_copy semantics field_parameters frep).
  Existing Instance copy_spec.

   Fixpoint rep (n : nat) (cmdf : nat -> cmd) : cmd :=
    match n with
    | O => cmd.skip
    | S n' => cmd.seq (cmdf n') (rep n' cmdf)
    end.

  Local Definition incr_nat x n :=
    expr.op bopname.add x ((Memory.bytes_per_word Semantics.width) * Z.of_nat n).

 
  Lemma Bignum_0 px x : Lift1Prop.iff1 (Bignum 0 px x) (emp (x =[])).
  Proof using.
    unfold Bignum.
    destruct x.
    {
      etransitivity.
      {
        eapply sep_emp_emp.
      }
      {
        apply Proper_emp_iff.
        simpl; easy.
      }
    }
    {
      split;
        intros; sepsimpl;
        match goal with
        | H : _ = 0%nat |- _ => inversion H
        | H : _ = [] |- _ => inversion H
        end.
    }
  Qed.

  
  Lemma anybytes_0 (x : word.rep) : Lift1Prop.iff1 (anybytes x 0) (emp True).
  Proof. Admitted.

  
  Lemma Bignum_snoc n px x a
    : Lift1Prop.iff1 (Bignum (S n) px (x++[a]))
                     (Bignum n px x
                      * Scalars.scalar
                          (word.add px
              (word.of_Z (word_size_in_bytes * Z.of_nat n)))  a)%sep.
  Proof using.
    unfold Bignum.
    intro mem; split; intro H; sepsimpl;
      try 
      match goal with
      | [H : Datatypes.length ?x = ?n
         |- Datatypes.length (?x++ [_]) = S ?n] =>
        rewrite app_length;
        rewrite Nat.add_comm; simpl; f_equal; exact H
      | [H : Datatypes.length (?x++ [_]) = S ?n
        |- _] =>
        rewrite app_length in H;
        rewrite Nat.add_comm in H;
        inversion H; subst; try reflexivity
      end.
    {
      seprewrite_in
          (array_append Scalars.scalar
                        (word.of_Z word_size_in_bytes) x [a] px)
          H0.
      sepsimpl.
      cbn [WeakestPrecondition.dexpr
            WeakestPrecondition.expr WeakestPrecondition.expr_body
            array incr_nat] in *.
      rewrite word.unsigned_of_Z in H0.
      rewrite Core.word.wrap_small in H0.
      {
         change (@Naive.rep (Zpos (xO (xO (xO (xO (xO (xO xH))))))))
              with (@word.rep (@width (@semantics Defaults64.default_parameters))
                     (@word (@semantics Defaults64.default_parameters))).
        ecancel_assumption.
      }
      { easy. }
    }    
    {
      seprewrite
          (array_append Scalars.scalar
                        (word.of_Z word_size_in_bytes) x [a] px).
      sepsimpl; auto.
      cbn [WeakestPrecondition.dexpr
            WeakestPrecondition.expr WeakestPrecondition.expr_body
            array incr_nat] in *.
      rewrite word.unsigned_of_Z.
      rewrite Core.word.wrap_small; [subst; ecancel_assumption| easy].
    }
  Qed.

  Lemma Bignum_nth_load l vx px n x y a R mem
    : Interface.map.get l vx = Some px ->
      (Bignum (S n) px x * R)%sep mem ->
      x = (y++[a])%list ->
      WeakestPrecondition.dexpr mem l
          bedrock_expr:(load( constr:(incr_nat (expr.var vx) n))) a.
  Proof using.
    intros; subst.
    seprewrite_in (Bignum_snoc n px y a) H0.
     exists px; split; auto.
     exists a; split; auto.
     cbn [interp_binop].
     change (bytes_per_word width) with word_size_in_bytes.
     eapply Scalars.load_word_of_sep.
     ecancel_assumption.
  Qed.

  
  Lemma Bignum_S n px x mem
    : Bignum (S n) px x mem -> exists a x', x = (x'++ [a])%list.
  Proof.
    unfold Bignum; intros; sepsimpl.
    assert (x <>[]).
    {
      destruct x; inversion H; easy.
    }
    apply exists_last in H1; repeat destruct H1 as [? H1].
    rewrite H1.
    eauto.
  Qed.

    
  Lemma copy_satisfies_spec :
    (let args := ["out"; "x"] in
     let rets := [] in
     let copy_body :=  (rep sz
                          (fun n =>
                             cmd.store access_size.word
                                     (incr_nat "out" n)
                                     (expr.load access_size.word (incr_nat "x" n)))) in
     let felem_copy := (felem_copy, (args, rets, copy_body)) in
     program_logic_goal_for
       felem_copy
       (forall functions : list (string * (list string * list string * cmd)),
           copy_spec (felem_copy :: functions))).
  Proof.
    
    unfold copy_spec.
    unfold spec_of_felem_copy.
    intro functions.
    intros; WeakestPrecondition.unfold1_call_goal; cbv beta match delta [WeakestPrecondition.call_body].
    lazymatch goal with
     | |- if ?x =? ?x then ?T else _ => rewrite (String.eqb_refl x); change_no_check T
    end; cbv beta match delta [WeakestPrecondition.func].
    repeat straightline.
    (*TODO: remember 0%nat as szup.*)
    revert R x mem H.
    cbv [FElem frep Representation.frep felem Placeholder felem_size_in_bytes rep].
    induction sz.
    {
      intros.
      split; [ reflexivity|].
      repeat seprewrite Bignum_0.
      seprewrite_in Bignum_0 H.
      sepsimpl; subst; auto.
      rewrite Z.mul_0_r in H0.
      pose proof (anybytes_0 pout).
      cbn -[Interface.map.rep width word Semantics.mem] in H0.
      seprewrite_in H H0.
      sepsimpl; assumption.
    }
    {
      intros.
      repeat straightline.
      assert (exists a x', x = (x'++[a])%list).
      {
        cbn -[Interface.map.rep width word Semantics.mem Z.of_nat].
        repeat destruct H as [? H].
        destruct H as [ H' H].
        repeat destruct H as [? H].
        destruct H as [H H2].
        repeat destruct H as [? H].
        destruct H as [H3 H].
        destruct H as [? ?].
        eapply Bignum_S; eauto.
      }
      repeat destruct H0 as [? H0]; subst.
      exists x0; split.
      {
        eapply Bignum_nth_load; auto.
        { reflexivity. }
        {
          ecancel_assumption.
        }
      }
      cbn -[Interface.map.rep width word Semantics.mem Z.of_nat] in H.
      seprewrite_in (anybytes_S pout n) H.
      unfold Lift1Prop.ex1 in H1.
      cbv beta in H1.
      match type of H1 with
        | context H'[fun m : ?M => exists x : ?X , @?P m x] =>
          let x' := fresh "x" in
          assert (exists x' : X,
                           ltac:(let T := context H'[fun m : M => P m x'] in
                            exact T))
        end.
      {
        repeat (destruct H1 as [? H1]).
        destruct H0 as [wd H0].
        exists wd.
        exists x.
        exists x2.
        split; eauto.
        split; auto.
        exists x3.
        exists x4.
        auto.
      }
      clear H1.
      destruct H as [wd H].
      eapply Scalars.store_word_of_sep.
      {
        instantiate (2:=wd).
        unfold a.
        cbn -[Interface.map.rep width word Semantics.mem Z.of_nat] in *.
        change (fun b => ?f b) with f in H.
        ecancel_assumption.
      }
      {
        intros.
        eapply WeakestPreconditionProperties.Proper_cmd.
        { eapply WeakestPreconditionProperties.Proper_call. }
        2:{ apply IHn.
            clear H mem.
            pose proof (Bignum_snoc n px x1 x0).
            cbv [Defaults64.default_parameters semantics] in *.
            seprewrite_in H H0.
            clear H.
            ecancel_assumption.
        }
        {
          clear m H0 mem H.
          unfold Morphisms.pointwise_relation.
          unfold Basics.impl.
          unfold WeakestPrecondition.list_map.
          unfold WeakestPrecondition.list_map_body.
          unfold Notations.postcondition_func_norets.
          unfold Notations.postcondition_func.
          intros; destruct H; subst.
          split; auto.
          sepsimpl; auto.
          seprewrite Bignum_snoc.
          seprewrite Bignum_snoc.
          unfold a in *; clear a.
          change (bytes_per_word width) with word_size_in_bytes in H0.
          cbn -[Interface.map.rep width word Semantics.mem Z.of_nat] in *.
          ecancel_assumption.
        }
      }
    }
  Qed.
   
  
 

Require Import Bedrock.Word.
Require Import Crypto.Assembly.QhasmCommon Crypto.Assembly.QhasmEvalCommon.
Require Import Crypto.Assembly.Pseudo Crypto.Assembly.Qhasm Crypto.Assembly.AlmostQhasm Crypto.Assembly.Conversion Crypto.Assembly.Language.
Require Import Crypto.Assembly.PseudoConversion Crypto.Assembly.AlmostConversion Crypto.Assembly.StringConversion.
Require Import Crypto.Assembly.Wordize Crypto.Assembly.Vectorize Crypto.Assembly.Pseudize.
Require Import Crypto.Util.Notations.

Module Pipeline.
  Export AlmostQhasm Qhasm QhasmString.
  Export Pseudo.

  Transparent Pseudo.Program AlmostQhasm.Program Qhasm.Program QhasmString.Program.
  Transparent Pseudo.Params AlmostQhasm.Params Qhasm.Params QhasmString.Params.

  Definition toAlmost {w s n m} (p: @Pseudo w s n m) : option AlmostProgram :=
    PseudoConversion.convertProgram (mkParams w s n m) tt p.

  Definition toQhasm {w s n m} (p: @Pseudo w s n m) : option (list QhasmStatement) :=
    omap (toAlmost p) (AlmostConversion.convertProgram tt tt).

  Definition toString {w s n m} (p: @Pseudo w s n m) : option string :=
    omap (toQhasm p) (StringConversion.convertProgram tt tt).
End Pipeline.

Module PipelineExamples.
  Import Pipeline ListNotations StateCommon EvalUtil ListState.

  Local Notation "v [[ i ]]" := (nth i v (wzero _)).
  Local Notation "$$ v" := (natToWord _ v).

  Section Example1.
    Definition f1 : Curried N N 2 1 := fun x y =>
      [N.add (N.land x (N.ones 15)) (N.land y (N.ones 15))].

    Lemma wordF1: wordeq 64 f1.
    Proof. unfold f1; wordize. Defined.

    Definition listF1 := curriedToListF (wzero _) (proj1_sig wordF1).

    Definition pseudo1: @pseudeq 64 W64 2 1 listF1.
      (* TODO: get this to work on 8.4 *)
      (* unfold listF1; simpl'; pseudo_solve. *)
    Admitted.

    Definition asm1 :=
      (Pipeline.toString (proj1_sig pseudo1)).
  End Example1.

  Section Example2.
    Definition f2 : Curried N N 2 1 := fun x y =>
      [N.mul (N.land x (N.ones 15)) (N.land y (N.ones 15))]. 

    Lemma wordF2: wordeq 32 f2.
    Proof. unfold f2; wordize. Defined.

    Definition listF2 := curriedToListF (wzero _) (proj1_sig wordF2).

    Definition pseudo2: @pseudeq 32 W32 2 1 listF2.
      (* TODO: get this to work on 8.4 *)
      (* unfold listF2; simpl'; pseudo_solve. *)
    Admitted.

    Definition asm2 :=
      (Pipeline.toString (proj1_sig pseudo2)).
  End Example2.

  Section Example1305.
    Definition f1305 : Curried Z Z 10 5.
      intros f0 f1 f2 f3 f4 g0 g1 g2 g3 g4.
      apply (tupleToList 5).
      refine (add (f0, f1, f2, f3, f4) (g0, g1, g2, g3, g4)).
    Defined.

    Definition g1305 : nateq f1305.
      unfold f1305; solve_nateq.
    Defined.

    Lemma wordF1305: maskeq 64 (proj1_sig g1305) [25;25;25;25;25;25;25;25;25;25].
    Proof.
      unfold g1305; simpl'.
      standardize_maskeq.
      wordize_intro.
      unfold_bounds.
      simpl in *.
      repeat wordize_iter;
        match goal with
        | [|- (_ < _)%N] => bound_compute
        | [|- (_ <= _)%N] => bound_compute
        | [|- _ = _] => unfold curriedToListF; simpl';
          repeat match goal with
          | [ |- context[nth ?k ?x ?d] ] => generalize (nth k x d); intro
          end; try reflexivity
        end.
    Defined.

    Definition listF1305 := curriedToListF (wzero _) (proj1_sig wordF1305).

    Definition pseudo1305: @pseudeq 64 W64 2 1 listF1305.
      (* TODO: get this to work on 8.4 *)
      (* unfold listF1305; simpl.
        unfold curriedToListF, maskeq_kill_arg''; simpl.
        pseudo_solve. *)
    Admitted.

    Definition asm1305 :=
      (Pipeline.toString (proj1_sig pseudo2)).
  End Example1305.

End PipelineExamples.

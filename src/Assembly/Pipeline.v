Require Import Bedrock.Word ZArith NArith PArith.
Require Import QhasmCommon QhasmEvalCommon.
Require Import Pseudo Qhasm AlmostQhasm Conversion Language.
Require Import PseudoConversion AlmostConversion StringConversion.
Require Import Wordize Pseudize Natize.
Require Import Crypto.Specific.GF1305.

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

  Local Notation "v [[ i ]]" := (nth i v (wzero _)) (at level 40).
  Local Notation "$$ v" := (natToWord _ v) (at level 40).

  Section Example1.
    Definition f1 : Curried N N 2 1 := fun x y =>
      [N.add (N.land x (N.ones 15)) (N.land y (N.ones 15))].

    Lemma wordF1: wordeq 64 f1.
    Proof. unfold f1; wordize. Defined.

    Definition listF1 := curriedToListF (wzero _) (proj1_sig wordF1).

    Definition pseudo1: @pseudeq 64 W64 2 1 listF1.
      unfold listF1; simpl'; pseudo_solve.
    Defined.

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
      unfold listF2; simpl'; pseudo_solve.
    Defined.

    Definition asm2 :=
      (Pipeline.toString (proj1_sig pseudo2)).
  End Example2.

  Section Example1305.
    Definition f1305 : Curried Z Z 10 5 :=
      fun f0 f1 f2 f3 f4 g0 g1 g2 g3 g4 =>
        proj1_sig (GF1305Base26_add_formula f0 f1 f2 f3 f4 g0 g1 g2 g3 g4).

    Definition g1305 : nateq f1305.
      unfold f1305; solve_nateq.
    Defined.

    Lemma wordF1305: maskeq 64 (proj1_sig g1305) (List.repeat 15 10).
    Proof. unfold g1305; wordize_masked. Defined.

    Definition listF1305 := curriedToListF (wzero _) (proj1_sig wordF1305).

    Definition pseudo1305: @pseudeq 64 W64 2 1 listF1305.
      unfold listF1305; simpl'.
      (* unfolding struggles... pseudo_solve. *)
    Admitted.

    Definition asm1305 :=
      (Pipeline.toString (proj1_sig pseudo2)).
  End Example1305.

End PipelineExamples.

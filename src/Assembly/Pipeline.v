Require Import Bedrock.Word.
Require Import QhasmCommon QhasmEvalCommon.
Require Import Pseudo Qhasm AlmostQhasm Conversion Language.
Require Import PseudoConversion AlmostConversion StringConversion.
Require Import Wordize Vectorize Pseudize.

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

  (*
  Definition add_example: @pseudeq 32 W32 1 1 (fun v =>
      plet a := $$ 1 in
      plet b := v[[0]] in
      [a ^+ b]).
    pseudo_solve.
  Defined.

  Definition add_ex_str :=
    (Pipeline.toString (proj1_sig add_example)).

  Definition and_example: @pseudeq 32 W32 1 1 (fun v =>
      plet a := $$ 1 in
      plet b := v[[0]] in
      [a ^& b]).
    pseudo_solve.
  Defined.

  Definition and_ex_str :=
    (Pipeline.toString (proj1_sig and_example)).

  Definition mult_example: @pseudeq 32 W32 1 1 (fun v =>
      plet a := $$ 1 in
      plet b := v[[0]] in

      (* NOTE: we want the lets in this format to unify with
               pseudo_mult_dual *)  
      plet c := multHigh a b in
      plet d := a ^* b in

      [b ^& d]).
    pseudo_solve.
  Defined.

  Definition mult_ex_str :=
    (Pipeline.toString (proj1_sig mult_example)).

  Definition comb_example: @pseudeq 32 W32 1 1 (fun v =>
      plet a := $$ 7 in
      plet b := v[[0]] in
      ([b ^& a; a ^+ b])).
    pseudo_solve.
  Admitted.

  Definition comb_ex_str :=
    (Pipeline.toString (proj1_sig comb_example)).
  *)

End PipelineExamples.

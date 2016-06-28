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

  Definition comb_example: @pseudeq 32 W32 1 2 (fun v =>
      plet a := natToWord _ 7 in
      plet b := nth 0 v (wzero _) in
      ([a; b])).
    pseudo_solve.
  Qed.

  Definition mult_ex_str :=
    (Pipeline.toString (proj1_sig mult_example)).

  Ltac gen_evar_local_defs :=
    repeat match goal with |- context[?V] => is_evar V; set V end.

  Definition comb_ex_str :=
    (Pipeline.toString (proj1_sig comb_example)).

End PipelineExamples.

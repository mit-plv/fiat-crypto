Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.MulSplitUnfolder.
Require Import Crypto.Arithmetic.Saturated.Wrappers.

Hint Unfold Wrappers.Columns.add_cps Wrappers.Columns.unbalanced_sub_cps Wrappers.Columns.mul_cps : arithmetic_cps_unfolder.

Module Columns.
  (**
<<
#!/bin/bash
for i in add_cps unbalanced_sub_cps mul_cps conditional_add_cps; do
    echo "  Definition ${i}_sig := parameterize_sig (@Wrappers.Columns.${i}).";
    echo "  Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "  Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "  Hint Unfold ${i} : basesystem_partial_evaluation_unfolder.";
    echo "  Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
echo "End Columns."
>> *)
  Definition add_cps_sig := parameterize_sig (@Wrappers.Columns.add_cps).
  Definition add_cps := parameterize_from_sig add_cps_sig.
  Definition add_cps_eq := parameterize_eq add_cps add_cps_sig.
  Hint Unfold add_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- add_cps_eq : pattern_runtime.

  Definition unbalanced_sub_cps_sig := parameterize_sig (@Wrappers.Columns.unbalanced_sub_cps).
  Definition unbalanced_sub_cps := parameterize_from_sig unbalanced_sub_cps_sig.
  Definition unbalanced_sub_cps_eq := parameterize_eq unbalanced_sub_cps unbalanced_sub_cps_sig.
  Hint Unfold unbalanced_sub_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- unbalanced_sub_cps_eq : pattern_runtime.

  Definition mul_cps_sig := parameterize_sig (@Wrappers.Columns.mul_cps).
  Definition mul_cps := parameterize_from_sig mul_cps_sig.
  Definition mul_cps_eq := parameterize_eq mul_cps mul_cps_sig.
  Hint Unfold mul_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- mul_cps_eq : pattern_runtime.

  Definition conditional_add_cps_sig := parameterize_sig (@Wrappers.Columns.conditional_add_cps).
  Definition conditional_add_cps := parameterize_from_sig conditional_add_cps_sig.
  Definition conditional_add_cps_eq := parameterize_eq conditional_add_cps conditional_add_cps_sig.
  Hint Unfold conditional_add_cps : basesystem_partial_evaluation_unfolder.
  Hint Rewrite <- conditional_add_cps_eq : pattern_runtime.

End Columns.

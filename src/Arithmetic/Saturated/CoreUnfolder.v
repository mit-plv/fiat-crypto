Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.Core.

Global Hint Unfold Core.Columns.compact_digit_cps Core.Columns.compact_step_cps Core.Columns.compact_cps : arithmetic_cps_unfolder.

Module Columns.
  (**
<<
#!/bin/bash
for i in eval eval_from compact_digit_cps compact_digit compact_step_cps compact_step compact_cps compact cons_to_nth_cps cons_to_nth nils from_associational_cps from_associational; do
    echo "  Definition ${i}_sig := parameterize_sig (@Core.Columns.${i}).";
    echo "  Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "  Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "  Hint Unfold ${i} : basesystem_partial_evaluation_unfolder.";
    echo "  Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
echo "End Columns."
>> *)
  Definition eval_sig := parameterize_sig (@Core.Columns.eval).
  Definition eval := parameterize_from_sig eval_sig.
  Definition eval_eq := parameterize_eq eval eval_sig.
  Global Hint Unfold eval : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- eval_eq : pattern_runtime.

  Definition eval_from_sig := parameterize_sig (@Core.Columns.eval_from).
  Definition eval_from := parameterize_from_sig eval_from_sig.
  Definition eval_from_eq := parameterize_eq eval_from eval_from_sig.
  Global Hint Unfold eval_from : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- eval_from_eq : pattern_runtime.

  Definition compact_digit_cps_sig := parameterize_sig (@Core.Columns.compact_digit_cps).
  Definition compact_digit_cps := parameterize_from_sig compact_digit_cps_sig.
  Definition compact_digit_cps_eq := parameterize_eq compact_digit_cps compact_digit_cps_sig.
  Global Hint Unfold compact_digit_cps : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- compact_digit_cps_eq : pattern_runtime.

  Definition compact_digit_sig := parameterize_sig (@Core.Columns.compact_digit).
  Definition compact_digit := parameterize_from_sig compact_digit_sig.
  Definition compact_digit_eq := parameterize_eq compact_digit compact_digit_sig.
  Global Hint Unfold compact_digit : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- compact_digit_eq : pattern_runtime.

  Definition compact_step_cps_sig := parameterize_sig (@Core.Columns.compact_step_cps).
  Definition compact_step_cps := parameterize_from_sig compact_step_cps_sig.
  Definition compact_step_cps_eq := parameterize_eq compact_step_cps compact_step_cps_sig.
  Global Hint Unfold compact_step_cps : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- compact_step_cps_eq : pattern_runtime.

  Definition compact_step_sig := parameterize_sig (@Core.Columns.compact_step).
  Definition compact_step := parameterize_from_sig compact_step_sig.
  Definition compact_step_eq := parameterize_eq compact_step compact_step_sig.
  Global Hint Unfold compact_step : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- compact_step_eq : pattern_runtime.

  Definition compact_cps_sig := parameterize_sig (@Core.Columns.compact_cps).
  Definition compact_cps := parameterize_from_sig compact_cps_sig.
  Definition compact_cps_eq := parameterize_eq compact_cps compact_cps_sig.
  Global Hint Unfold compact_cps : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- compact_cps_eq : pattern_runtime.

  Definition compact_sig := parameterize_sig (@Core.Columns.compact).
  Definition compact := parameterize_from_sig compact_sig.
  Definition compact_eq := parameterize_eq compact compact_sig.
  Global Hint Unfold compact : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- compact_eq : pattern_runtime.

  Definition cons_to_nth_cps_sig := parameterize_sig (@Core.Columns.cons_to_nth_cps).
  Definition cons_to_nth_cps := parameterize_from_sig cons_to_nth_cps_sig.
  Definition cons_to_nth_cps_eq := parameterize_eq cons_to_nth_cps cons_to_nth_cps_sig.
  Global Hint Unfold cons_to_nth_cps : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- cons_to_nth_cps_eq : pattern_runtime.

  Definition cons_to_nth_sig := parameterize_sig (@Core.Columns.cons_to_nth).
  Definition cons_to_nth := parameterize_from_sig cons_to_nth_sig.
  Definition cons_to_nth_eq := parameterize_eq cons_to_nth cons_to_nth_sig.
  Global Hint Unfold cons_to_nth : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- cons_to_nth_eq : pattern_runtime.

  Definition nils_sig := parameterize_sig (@Core.Columns.nils).
  Definition nils := parameterize_from_sig nils_sig.
  Definition nils_eq := parameterize_eq nils nils_sig.
  Global Hint Unfold nils : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- nils_eq : pattern_runtime.

  Definition from_associational_cps_sig := parameterize_sig (@Core.Columns.from_associational_cps).
  Definition from_associational_cps := parameterize_from_sig from_associational_cps_sig.
  Definition from_associational_cps_eq := parameterize_eq from_associational_cps from_associational_cps_sig.
  Global Hint Unfold from_associational_cps : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- from_associational_cps_eq : pattern_runtime.

  Definition from_associational_sig := parameterize_sig (@Core.Columns.from_associational).
  Definition from_associational := parameterize_from_sig from_associational_sig.
  Definition from_associational_eq := parameterize_eq from_associational from_associational_sig.
  Global Hint Unfold from_associational : basesystem_partial_evaluation_unfolder.
#[global]
  Hint Rewrite <- from_associational_eq : pattern_runtime.

End Columns.

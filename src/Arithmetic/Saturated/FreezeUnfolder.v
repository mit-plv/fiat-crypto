Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.WrappersUnfolder.
Require Import Crypto.Arithmetic.Saturated.Freeze.

(**
<<
#!/bin/bash
for i in freeze freeze_cps; do
    echo "Definition ${i}_sig := parameterize_sig (@Freeze.${i}).";
    echo "Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
>> *)
Definition freeze_cps_sig := parameterize_sig (@Freeze.freeze_cps).
Definition freeze_cps := parameterize_from_sig freeze_cps_sig.
Definition freeze_cps_eq := parameterize_eq freeze_cps freeze_cps_sig.
Hint Rewrite <- freeze_cps_eq : pattern_runtime.

Definition freeze_sig := parameterize_sig (@Freeze.freeze).
Definition freeze := parameterize_from_sig freeze_sig.
Definition freeze_eq := parameterize_eq freeze freeze_sig.
Hint Rewrite <- freeze_eq : pattern_runtime.

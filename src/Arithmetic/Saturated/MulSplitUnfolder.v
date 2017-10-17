Require Import Crypto.Arithmetic.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.CoreUnfolder.
Require Import Crypto.Arithmetic.Saturated.MulSplit.

Module B.
  Module Associational.
(**
<<
#!/bin/bash
for i in sat_multerm_cps sat_multerm sat_mul_cps sat_mul; do
    echo "    Definition ${i}_sig := parameterize_sig (@MulSplit.B.Associational.${i}).";
    echo "    Definition ${i} := parameterize_from_sig ${i}_sig.";
    echo "    Definition ${i}_eq := parameterize_eq ${i} ${i}_sig.";
    echo "    Hint Rewrite <- ${i}_eq : pattern_runtime."; echo "";
done
echo "  End Associational."
echo "End B."
>> *)
    Definition sat_multerm_cps_sig := parameterize_sig (@MulSplit.B.Associational.sat_multerm_cps).
    Definition sat_multerm_cps := parameterize_from_sig sat_multerm_cps_sig.
    Definition sat_multerm_cps_eq := parameterize_eq sat_multerm_cps sat_multerm_cps_sig.
    Hint Rewrite <- sat_multerm_cps_eq : pattern_runtime.

    Definition sat_multerm_sig := parameterize_sig (@MulSplit.B.Associational.sat_multerm).
    Definition sat_multerm := parameterize_from_sig sat_multerm_sig.
    Definition sat_multerm_eq := parameterize_eq sat_multerm sat_multerm_sig.
    Hint Rewrite <- sat_multerm_eq : pattern_runtime.

    Definition sat_mul_cps_sig := parameterize_sig (@MulSplit.B.Associational.sat_mul_cps).
    Definition sat_mul_cps := parameterize_from_sig sat_mul_cps_sig.
    Definition sat_mul_cps_eq := parameterize_eq sat_mul_cps sat_mul_cps_sig.
    Hint Rewrite <- sat_mul_cps_eq : pattern_runtime.

    Definition sat_mul_sig := parameterize_sig (@MulSplit.B.Associational.sat_mul).
    Definition sat_mul := parameterize_from_sig sat_mul_sig.
    Definition sat_mul_eq := parameterize_eq sat_mul sat_mul_sig.
    Hint Rewrite <- sat_mul_eq : pattern_runtime.

  End Associational.
End B.

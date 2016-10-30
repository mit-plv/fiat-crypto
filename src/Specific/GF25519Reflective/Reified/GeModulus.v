Require Import Crypto.Specific.GF25519Reflective.Common.

Definition rge_modulusZ_sig : rexpr_unop_FEToZ_sig ge_modulus. Proof. reify_sig. Defined.

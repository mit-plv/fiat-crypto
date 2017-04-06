Require Import Coq.ZArith.Zpower Coq.ZArith.ZArith.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Require Import Coq.Lists.List.

Local Open Scope Z_scope.

Section Pow2Base.
  Context (limb_widths : list Z).
  Local Notation "w[ i ]" := (nth_default 0 limb_widths i).
  Fixpoint base_from_limb_widths limb_widths :=
    match limb_widths with
    | nil => nil
    | w :: lw => 1 :: map (Z.mul (two_p w)) (base_from_limb_widths lw)
    end.
  Local Notation base := (base_from_limb_widths limb_widths).
  Definition bounded us := forall i, 0 <= nth_default 0 us i < 2 ^ w[i].
  Definition upper_bound := 2 ^ (sum_firstn limb_widths (length limb_widths)).
End Pow2Base.

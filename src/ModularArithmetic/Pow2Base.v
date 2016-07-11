Require Import Zpower ZArith.
Require Import Crypto.Util.ListUtil.
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

  Fixpoint decode_bitwise' us i acc :=
    match i with
    | O => acc
    | S i' => decode_bitwise' us i' (Z.lor (nth_default 0 us i') (Z.shiftl acc w[i']))
    end.

  Definition decode_bitwise us := decode_bitwise' us (length us) 0.

  (* i is current index, counts down *)
  Fixpoint encode' z i :=
    match i with
    | O => nil
    | S i' => let lw := sum_firstn limb_widths in
       encode' z i' ++ (Z.shiftr (Z.land z (Z.ones (lw i))) (lw i')) :: nil
    end.

  (* max must be greater than input; this is used to truncate last digit *)
  Definition encodeZ x:= encode' x (length limb_widths).

End Pow2Base.

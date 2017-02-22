Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ListUtil.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Class PseudoMersenneBaseParams (modulus : positive) := {
  limb_widths : list Z;
  limb_widths_pos : forall w, In w limb_widths -> 0 < w;
  limb_widths_nonnil : limb_widths <> nil;
  limb_widths_good : forall i j, (i + j < length limb_widths)%nat ->
    sum_firstn limb_widths (i + j) <=
    sum_firstn limb_widths i + sum_firstn limb_widths j;
  prime_modulus : Znumtheory.prime (Z.pos modulus);
  k := sum_firstn limb_widths (length limb_widths);
  c := 2 ^ k - (Z.pos modulus);
  c_pos : 0 < c;
  limb_widths_match_modulus : forall i j,
    (i < length limb_widths)%nat ->
    (j < length limb_widths)%nat ->
    (i + j >= length limb_widths)%nat ->
    let w_sum := sum_firstn limb_widths in
    k + w_sum (i + j - length limb_widths)%nat <= w_sum i + w_sum j
}.

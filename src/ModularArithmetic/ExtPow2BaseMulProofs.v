Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Crypto.BaseSystem.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Import Crypto.ModularArithmetic.ExtendedBaseVector.
Require Import Crypto.Util.ListUtil.

Local Open Scope Z_scope.

Section ext_mul.
  Context (limb_widths : list Z)
          (limb_widths_nonnegative : forall x, In x limb_widths -> 0 <= x).
  Local Notation k := (sum_firstn limb_widths (length limb_widths)).
  Local Notation base := (base_from_limb_widths limb_widths).
  Context (bv : BaseVector base)
          (limb_widths_match_modulus : forall i j,
              (i < length limb_widths)%nat ->
              (j < length limb_widths)%nat ->
              (i + j >= length limb_widths)%nat ->
              let w_sum := sum_firstn limb_widths in
              k + w_sum (i + j - length limb_widths)%nat <= w_sum i + w_sum j).

  Local Hint Resolve firstn_us_base_ext_base ExtBaseVector bv.

  Lemma mul_rep_extended : forall (us vs : BaseSystem.digits),
      (length us <= length base)%nat ->
      (length vs <= length base)%nat ->
      (BaseSystem.decode base us) * (BaseSystem.decode base vs) = BaseSystem.decode (ext_base limb_widths) (BaseSystem.mul (ext_base limb_widths) us vs).
  Proof.
    intros; apply mul_rep_two_base; auto;
      distr_length.
  Qed.
End ext_mul.

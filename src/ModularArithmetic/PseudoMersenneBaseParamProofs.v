Require Import Zpower ZArith.
Require Import List.
Require Import Crypto.Util.ListUtil Crypto.Util.CaseUtil Crypto.Util.ZUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import VerdiTactics.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.Pow2Base.
Require Import Crypto.ModularArithmetic.Pow2BaseProofs.
Require Crypto.BaseSystem.
Local Open Scope Z_scope.

Section PseudoMersenneBaseParamProofs.
  Context `{prm : PseudoMersenneBaseParams}.
  Local Notation base := (base_from_limb_widths limb_widths).

  Lemma limb_widths_nonneg : forall w, In w limb_widths -> 0 <= w.
  Proof. auto using Z.lt_le_incl, limb_widths_pos. Qed.

  Lemma k_nonneg : 0 <= k.
  Proof. apply sum_firstn_limb_widths_nonneg, limb_widths_nonneg. Qed.

  Global Instance bv : BaseSystem.BaseVector base := {
    base_positive := base_positive limb_widths_nonneg;
    b0_1 := fun x => b0_1 x limb_widths_nonnil;
    base_good := base_good limb_widths_nonneg limb_widths_good
  }.

End PseudoMersenneBaseParamProofs.

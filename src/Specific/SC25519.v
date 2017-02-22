Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.EdDSARepChange.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZBounded.
Require Import Crypto.ModularArithmetic.ZBoundedZ.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.WordUtil.
Import NPeano.

Local Notation modulusv := (2^252 + 27742317777372353535851937790883648493)%positive.
Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).
Local Notation eta4' x := (eta (fst x), eta (snd x)).
Local Open Scope Z_scope.

Section Z.
  Definition SRep := Z. (*tuple x86.W (256/n).*)
  Definition SRepEq : Relation_Definitions.relation SRep := Logic.eq.
  Local Instance SRepEquiv : RelationClasses.Equivalence SRepEq := _.
  Local Notation base := 2%Z.
  Local Notation kv := 256%Z.
  Local Notation offsetv := 8%Z.
  Lemma smaller_bound_smaller : (0 <= kv - offsetv <= 256)%Z. Proof. vm_compute; intuition congruence. Qed.
  Lemma modulusv_in_range : 0 <= modulusv < 2 ^ 256. Proof. vm_compute; intuition congruence. Qed.
  Lemma modulusv_pos : 0 < modulusv. Proof. vm_compute; reflexivity. Qed.
  Section params_gen.
    Import BarrettBundled.
    Local Instance x86_25519_Barrett : BarrettParameters
      := { m := modulusv;
           b := base;
           k := kv;
           offset := offsetv;
           ops := _;
           μ' := base ^ (2 * kv) / modulusv }.
    Local Instance x86_25519_BarrettProofs
      : BarrettParametersCorrect x86_25519_Barrett
      := { props := _ }.
    Proof.
      vm_compute; reflexivity.
      vm_compute; reflexivity.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; clear; abstract intuition congruence.
      vm_compute; reflexivity.
    Defined.
  End params_gen.
  Local Existing Instance x86_25519_Barrett.
  Local Existing Instance x86_25519_BarrettProofs.
  Declare Reduction srep := cbv [barrett_reduce_function_bundled barrett_reduce_function BarrettBundled.m BarrettBundled.b BarrettBundled.k BarrettBundled.offset BarrettBundled.μ' ZBounded.ConditionalSubtractModulus ZBounded.CarrySubSmall  ZBounded.Mod_SmallBound ZBounded.Mod_SmallBound ZBounded.Mul ZBounded.DivBy_SmallBound ZBounded.DivBy_SmallerBound  ZBounded.modulus_digits x86_25519_Barrett BarrettBundled.ops ZZLikeOps ZBounded.CarryAdd Z.pow2_mod].
  Definition SRepDecModL : Word.word (256 + 256) -> SRep
    := Eval srep in
        fun w => dlet w := (Z.of_N (Word.wordToN w)) in barrett_reduce_function_bundled w.
  Definition S2Rep : ModularArithmetic.F.F l -> SRep := F.to_Z.
  Local Ltac transitivity_refl x := transitivity x; [ | reflexivity ].
  Local Ltac pose_barrett_bounds H x :=
    pose proof (fun pf => proj1 (barrett_reduce_correct_bundled x pf)) as H;
    unfold ZBounded.medium_valid, BarrettBundled.props, x86_25519_BarrettProofs, ZZLikeProperties, BarrettBundled.k in H;
    simpl in H.
  Local Ltac fold_modulusv :=
    let m := (eval vm_compute in modulusv) in
    change m with modulusv in *.
  Local Ltac fold_Z_pow_pos :=
    repeat match goal with
           | [ |- context[Z.pow_pos ?b ?e] ]
             => let e2 := (eval compute in (Z.pos e / 2)%Z) in
                change (Z.pow_pos b e) with (b^(e2 + e2))
           end;
    repeat simpl (Z.pos _ + Z.pos _) in *.
  Local Ltac transitivity_barrett_bounds :=
    let LHS := match goal with |- ?R ?LHS ?RHS => LHS end in
    let RHS := match goal with |- ?R ?LHS ?RHS => RHS end in
    let H := fresh in
    first [ match LHS with
            | context[barrett_reduce_function_bundled ?x]
              => etransitivity; [ pose_barrett_bounds H x | ]
            end
          | match RHS with
            | context[barrett_reduce_function_bundled ?x]
              => symmetry; etransitivity; [ pose_barrett_bounds H x | ]
            end ];
    [ apply H; clear H | ];
    instantiate;
    rewrite ?Z.pow2_mod_spec in * by omega;
    fold_modulusv; fold_Z_pow_pos.
  Lemma Z_of_nat_lt_helper x b e : (x < b^e)%nat <-> x < b^e.
  Proof. rewrite Nat2Z.inj_lt, Z.pow_Zpow; reflexivity. Qed.
  Lemma SRepDecModL_Correct : forall w : Word.word (b + b), SRepEq (S2Rep (ModularArithmetic.F.of_nat l (Word.wordToNat w))) (SRepDecModL w).
  Proof.
    intro w; unfold SRepEq, S2Rep, b in *.
    pose proof (Word.wordToNat_bound w) as H'.
    transitivity_refl (barrett_reduce_function_bundled (Z.of_N (Word.wordToN w))).
    transitivity_barrett_bounds;
      rewrite ?Word.wordToN_nat, ?nat_N_Z, ?WordUtil.pow2_id in *.
    { apply Z_of_nat_lt_helper in H'.
      rewrite Nat2Z.inj_add in H'.
      auto with zarith. }
    { reflexivity. }
  Qed.
  Definition SRepAdd : SRep -> SRep -> SRep
    := Eval srep in
        let work_around_bug_5198
            := fun x y => barrett_reduce_function_bundled (snd (ZBounded.CarryAdd x y))
        in work_around_bug_5198.
  Lemma SRepAdd_Correct : forall x y : ModularArithmetic.F.F l, SRepEq (S2Rep (ModularArithmetic.F.add x y)) (SRepAdd (S2Rep x) (S2Rep y)).
  Proof.
    intros x y; unfold SRepEq, S2Rep, b in *; simpl.
    transitivity_refl (let work_around_bug_5198
                           := fun x y => barrett_reduce_function_bundled (snd (ZBounded.CarryAdd x y))
                       in work_around_bug_5198 (F.to_Z x) (F.to_Z y)).
    pose proof (ModularArithmeticTheorems.F.to_Z_range x).
    pose proof (ModularArithmeticTheorems.F.to_Z_range y).
    unfold l in *; specialize_by auto using modulusv_pos.
    assert (F.to_Z x + F.to_Z y < 2 * modulusv - 1) by omega.
    assert (2 * modulusv - 1 <= 2 ^ (kv + kv)) by (vm_compute; clear; intuition congruence).
    assert (2 * modulusv - 1 < 2^((kv + offsetv) + (kv + offsetv))) by (vm_compute; clear; intuition congruence).
    transitivity_barrett_bounds.
    { Z.rewrite_mod_small; omega. }
    { rewrite (Z.mod_small _ (base^_)) by zutil_arith.
      reflexivity. }
  Qed.
  Global Instance SRepAdd_Proper : Proper (SRepEq ==> SRepEq ==> SRepEq) SRepAdd.
  Proof. unfold SRepEq; repeat intro; subst; reflexivity. Qed.
  Definition SRepMul : SRep -> SRep -> SRep
    := Eval srep in
        let work_around_bug_5198
            := fun x y => barrett_reduce_function_bundled (ZBounded.Mul x y)
        in work_around_bug_5198.
  Lemma SRepMul_Correct : forall x y : ModularArithmetic.F.F l, SRepEq (S2Rep (ModularArithmetic.F.mul x y)) (SRepMul (S2Rep x) (S2Rep y)).
  Proof.
    intros x y; unfold SRepEq, S2Rep, b in *; simpl.
    transitivity_refl (let work_around_bug_5198
                           := fun x y => barrett_reduce_function_bundled (ZBounded.Mul x y)
                       in work_around_bug_5198 (F.to_Z x) (F.to_Z y)).
    pose proof (ModularArithmeticTheorems.F.to_Z_range x).
    pose proof (ModularArithmeticTheorems.F.to_Z_range y).
    unfold l in *; specialize_by auto using modulusv_pos.
    assert (0 <= F.to_Z x * F.to_Z y < modulusv * modulusv) by nia.
    assert (modulusv * modulusv <= 2 ^ (kv + kv)) by (vm_compute; clear; intuition congruence).
    assert (2^(kv + kv) < 2^((kv + offsetv) + (kv + offsetv))) by (vm_compute; clear; intuition congruence).
    transitivity_barrett_bounds.
    { Z.rewrite_mod_small; omega. }
    { reflexivity. }
  Qed.
  Global Instance SRepMul_Proper : Proper (SRepEq ==> SRepEq ==> SRepEq) SRepMul.
  Proof. unfold SRepEq; repeat intro; subst; reflexivity. Qed.
  Definition SRepDecModLShort : Word.word (n + 1) -> SRep
    := Eval srep in
        fun w => dlet w := (Z.of_N (Word.wordToN w)) in barrett_reduce_function_bundled w.
  Lemma SRepDecModLShort_Correct : forall w : Word.word (n + 1), SRepEq (S2Rep (ModularArithmetic.F.of_nat l (Word.wordToNat w))) (SRepDecModLShort w).
  Proof.
    intros w; unfold SRepEq, S2Rep, n, b in *; simpl.
    transitivity_refl (barrett_reduce_function_bundled (Z.of_N (Word.wordToN w))).
    transitivity_barrett_bounds.
    { pose proof (Word.wordToNat_bound w) as H.
      rewrite Word.wordToN_nat, nat_N_Z.
      rewrite WordUtil.pow2_id in H.
      apply Z_of_nat_lt_helper in H.
      rewrite Nat2Z.inj_add in H; simpl @Z.of_nat in *.
      split; auto with zarith.
      etransitivity; [ eassumption | instantiate; vm_compute; reflexivity ]. }
    { rewrite Word.wordToN_nat, nat_N_Z; reflexivity. }
  Qed.
End Z.

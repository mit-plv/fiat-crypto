Require Import Coq.ZArith.ZArith Coq.micromega.Psatz Coq.Classes.Morphisms Coq.Classes.RelationClasses.
Require Import Crypto.Spec.Ed25519.
Require Import Crypto.Specific.X86.Core.
Require Import Crypto.EdDSARepChange.
Require Import Crypto.BoundedArithmetic.Interface.
Require Import Crypto.BoundedArithmetic.X86ToZLike.
Require Import Crypto.BoundedArithmetic.X86ToZLikeProofs.
Require Import Crypto.BoundedArithmetic.Eta.
Require Import Crypto.ModularArithmetic.BarrettReduction.ZBounded.
Require Import Crypto.ModularArithmetic.ZBoundedZ.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.WordUtil.
Import NPeano.

Local Notation modulusv := (2^252 + 27742317777372353535851937790883648493)%Z.
Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).
Local Notation eta4' x := (eta (fst x), eta (snd x)).

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
  Section gen.
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
  End gen.
  Local Existing Instance x86_25519_Barrett.
  Local Existing Instance x86_25519_BarrettProofs.
  Declare Reduction srep := cbv [barrett_reduce_function_bundled barrett_reduce_function BarrettBundled.m BarrettBundled.b BarrettBundled.k BarrettBundled.offset BarrettBundled.μ' ZBounded.ConditionalSubtractModulus ZBounded.CarrySubSmall  ZBounded.Mod_SmallBound ZBounded.Mod_SmallBound ZBounded.Mul ZBounded.DivBy_SmallBound ZBounded.DivBy_SmallerBound  ZBounded.modulus_digits x86_25519_Barrett BarrettBundled.ops ZZLikeOps ZBounded.CarryAdd Z.pow2_mod].
  Definition SRepDecModL : Word.word (256 + 256) -> SRep
    := Eval srep in
        fun w => dlet w := (Z.of_N (Word.wordToN w)) in barrett_reduce_function_bundled w.
  (*Local Arguments SRepDecModL' / _.
  Ltac change_values v :=
    match v with
    | context vv[2 * ?x]
      => let x2 := (eval vm_compute in (2 * x)) in
         let v' := context vv[x2] in
         change_values v'
    | context vv[Z.pos ?x + Z.pos ?y]
      => let x2 := (eval vm_compute in (Z.pos x + Z.pos y)) in
         let v' := context vv[x2] in
         change_values v'
    | context vv[Z.pos ?x - Z.pos ?y]
      => let x2 := (eval vm_compute in (Z.pos x - Z.pos y)) in
         let v' := context vv[x2] in
         change_values v'
    | context vv[Z.pos ?x / Z.pos ?y]
      => let x2 := (eval vm_compute in (Z.pos x / Z.pos y)) in
         let v' := context vv[x2] in
         change_values v'
    | context vv[Z.ones (Z.pos ?x)]
      => let x2 := (eval vm_compute in (Z.ones (Z.pos x))) in
         let v' := context vv[x2] in
         change_values v'
    | context vv[2^?x]
      => let x2 := (eval vm_compute in (2^x)) in
         let v' := context vv[x2] in
         change_values v'
    | _ => v
    end.
  Definition SRepDecModL : Word.word (256 + 256) -> SRep.
  Proof.
    let v' := (eval cbv [SRepDecModL'] in SRepDecModL') in
    let v' := (eval cbv beta iota delta [Let_In] in v') in
    let v := (*change_values*) v' in
    unify v v';
      exact v.
  Defined.*)
  Check @sign_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
  Check @verify_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
  Definition S2Rep : ModularArithmetic.F.F l -> SRep := F.to_Z.
  (* TODO: Move me to WordUtil and find a better name, or just inline the rewrites below, or make a hintdb for word conversions *)
  Lemma Z_of_nat_of_word_eq_Z_of_N_of_word
    : forall (n : nat) (w : Word.word n), Z.of_nat (Word.wordToNat w) = Z.of_N (Word.wordToN w).
  Proof. intros; rewrite Word.wordToN_nat, nat_N_Z; reflexivity. Qed.
  Lemma SRepDecModL_Correct : forall w : Word.word (b + b), SRepEq (S2Rep (ModularArithmetic.F.of_nat l (Word.wordToNat w))) (SRepDecModL w).
  Proof.
    intro w; change (SRepDecModL w) with (barrett_reduce_function_bundled (Z.of_N (Word.wordToN w))).
    unfold SRepEq, S2Rep, b in *.
    pose proof (barrett_reduce_correct_bundled (Z.of_N (Word.wordToN w))) as H.
    unfold ZBounded.medium_valid, BarrettBundled.props, x86_25519_BarrettProofs, ZZLikeProperties, BarrettBundled.k in H.
    simpl in H; destruct H as [H _].
    { pose proof (Word.wordToNat_bound w).
      rewrite Word.wordToN_nat, nat_N_Z.
      rewrite WordUtil.pow2_id in H.
      apply inj_lt in H.
      rewrite Z.pow_Zpow, Nat2Z.inj_add in H; simpl @Z.of_nat in *.
      split; auto with zarith. }
    { simpl in *; rewrite H; clear H.
      rewrite Z_of_nat_of_word_eq_Z_of_N_of_word; reflexivity. }
  Qed.
  Definition SRepAdd : SRep -> SRep -> SRep
    := Eval srep in fun x y => barrett_reduce_function_bundled (snd (ZBounded.CarryAdd x y)).
  Lemma SRepAdd_Correct : forall x y : ModularArithmetic.F.F l, SRepEq (S2Rep (ModularArithmetic.F.add x y)) (SRepAdd (S2Rep x) (S2Rep y)).
  Proof.
    intros x y; change (SRepAdd ?x ?y) with (barrett_reduce_function_bundled (snd (ZBounded.CarryAdd x y))).
    unfold SRepEq, S2Rep, b in *; simpl.
    match goal with
    | [ |- context[barrett_reduce_function_bundled ?x] ]
      => pose proof (barrett_reduce_correct_bundled x) as H
    end.
    pose proof (ModularArithmeticTheorems.F.to_Z_range x).
    pose proof (ModularArithmeticTheorems.F.to_Z_range y).
    unfold l in *.
    specialize_by auto using modulusv_pos.
    assert (F.to_Z x + F.to_Z y < 2 * modulusv - 1) by omega.
    assert (2 * modulusv - 1 <= 2 ^ (kv + kv)) by (vm_compute; clear; intuition congruence).
    assert (2^(kv + kv) < 2^((kv + offsetv) + (kv + offsetv))) by (vm_compute; clear; intuition congruence).
    assert (0 <= F.to_Z x + F.to_Z y < 2^(((kv + offsetv) + (kv + offsetv)))) by omega.
    simpl in H; destruct H as [H _].
    { rewrite Z.pow2_mod_spec by omega; Z.rewrite_mod_small.
      simpl in *; omega. }
    { simpl in H |- *; rewrite H; clear H.
      rewrite Z.pow2_mod_spec by omega; Z.rewrite_mod_small.
      reflexivity. }
  Qed.
  Global Instance SRepAdd_Proper : Proper (SRepEq ==> SRepEq ==> SRepEq) SRepAdd.
  Proof. unfold SRepEq; repeat intro; subst; reflexivity. Qed.
  Definition SRepMul : SRep -> SRep -> SRep
    := Eval srep in fun x y => barrett_reduce_function_bundled (ZBounded.Mul x y).
  Lemma SRepMul_Correct : forall x y : ModularArithmetic.F.F l, SRepEq (S2Rep (ModularArithmetic.F.mul x y)) (SRepMul (S2Rep x) (S2Rep y)).
  Proof.
    intros x y; change (SRepMul ?x ?y) with (barrett_reduce_function_bundled (ZBounded.Mul x y)).
    unfold SRepEq, S2Rep, b in *; simpl.
    match goal with
    | [ |- context[barrett_reduce_function_bundled ?x] ]
      => pose proof (barrett_reduce_correct_bundled x) as H
    end.
    pose proof (ModularArithmeticTheorems.F.to_Z_range x).
    pose proof (ModularArithmeticTheorems.F.to_Z_range y).
    unfold l in *.
    specialize_by auto using modulusv_pos.
    assert (0 <= F.to_Z x * F.to_Z y < modulusv * modulusv) by nia.
    assert (modulusv * modulusv <= 2 ^ (kv + kv)) by (vm_compute; clear; intuition congruence).
    assert (2^(kv + kv) < 2^((kv + offsetv) + (kv + offsetv))) by (vm_compute; clear; intuition congruence).
    simpl in H; destruct H as [H _].
    { set (k := modulusv) in *; compute in k.
      let v := (eval unfold k in k) in change v with k.
      match goal with
      | [ |- context[Z.pow_pos ?b ?e] ]
        => let e2 := (eval compute in (Z.pos e / 2)%Z) in
           change (Z.pow_pos b e) with (b^(e2 + e2))
      end.
      omega. }
    { simpl in H |- *; rewrite H; clear H.
      reflexivity. }
  Qed.
  Global Instance SRepMul_Proper : Proper (SRepEq ==> SRepEq ==> SRepEq) SRepMul.
  Proof. unfold SRepEq; repeat intro; subst; reflexivity. Qed.
  Definition SRepDecModLShort : Word.word (n + 1) -> SRep
    := Eval srep in
        fun w => dlet w := (Z.of_N (Word.wordToN w)) in barrett_reduce_function_bundled w.
  Lemma SRepDecModLShort_Correct : forall w : Word.word (n + 1), SRepEq (S2Rep (ModularArithmetic.F.of_nat l (Word.wordToNat w))) (SRepDecModLShort w).
  Proof.
    intro w; change (SRepDecModLShort w) with (barrett_reduce_function_bundled (Z.of_N (Word.wordToN w))).
    unfold SRepEq, S2Rep, n, b in *.
    pose proof (barrett_reduce_correct_bundled (Z.of_N (Word.wordToN w))) as H.
    simpl in H; destruct H as [H _].
    { pose proof (Word.wordToNat_bound w).
      rewrite Word.wordToN_nat, nat_N_Z.
      rewrite WordUtil.pow2_id in H.
      apply inj_lt in H.
      rewrite Z.pow_Zpow, Nat2Z.inj_add in H; simpl @Z.of_nat in *.
      split; auto with zarith.
      etransitivity; [ eassumption | vm_compute; reflexivity ]. }
    { simpl in *; rewrite H; clear H.
      rewrite Z_of_nat_of_word_eq_Z_of_N_of_word; reflexivity. }
  Qed.
  Arguments Algebra.group : clear implicits.
  Check @sign_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
  Check @verify_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
End Z.

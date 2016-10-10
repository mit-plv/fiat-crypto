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
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.LetIn.
Import NPeano.

Local Notation modulusv := (2^252 + 27742317777372353535851937790883648493)%Z.
Local Coercion Z.of_nat : nat >-> Z.
Local Notation eta x := (fst x, snd x).
Local Notation eta3 x := (eta (fst x), snd x).
Local Notation eta4 x := (eta3 (fst x), snd x).
Local Notation eta4' x := (eta (fst x), eta (snd x)).

Section x86.
  Axiom admit : forall {T}, T.
  Definition SRep := Z. (*tuple x86.W (256/n).*)
  Definition SRepEq : Relation_Definitions.relation SRep := Logic.eq.
  Local Instance SRepEquiv : RelationClasses.Equivalence SRepEq := _.
  Local Notation base := 2%Z (* TODO(@andres-erbsen): Is this the correct base, or are we using something else? *).
  Local Notation smaller_bound_exp := 250%Z (* TODO(@andres-erbsen): Is this the correct smaller size (2^250), or are we using something else? *).
  Lemma smaller_bound_smaller : (0 <= smaller_bound_exp <= 256)%Z. Proof. vm_compute; intuition congruence. Qed.
  Lemma modulusv_in_range : 0 <= modulusv < 2 ^ 256. Proof. vm_compute; intuition congruence. Qed.
  Lemma modulusv_pos : 0 < modulusv. Proof. vm_compute; reflexivity. Qed.
  Section gen.
    Lemma full_width_pos : (0 < 256)%Z. Proof. omega. Qed.
    Let offset'0 := Eval compute in ((256 - smaller_bound_exp) / 2)%Z.
    Let k'0 := Eval compute in ((256 - offset'0) / Z.log2 base)%Z.
    Section params_gen.
      Import BarrettBundled.
      Let offset' := Eval compute in offset'0.
      Let k' := Eval compute in k'0.
      Local Instance x86_25519_Barrett : BarrettParameters
        := { m := modulusv;
             b := base;
             k := k';
             offset := offset';
             ops := _;
             μ' := base ^ (2 * k') / modulusv }.
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
  Definition SRepDecModL' : Word.word (256 + 256) -> SRep
    := Eval srep in
        fun w => dlet w := (Z.of_N (Word.wordToN w)) in barrett_reduce_function_bundled w.
  Local Arguments SRepDecModL' / _.
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
  Defined.
  (* TODO(jadep):what's S2Rep? *)
  (*Lemma SRepDecModL_Correct : forall w : Word.word (b + b), SRepEq (S2Rep (ModularArithmetic.F.of_nat l (Word.wordToNat w))) (SRepDecModL w).*)
  Definition SRepAdd : SRep -> SRep -> SRep
    := Eval srep in fun x y => barrett_reduce_function_bundled (snd (ZBounded.CarryAdd x y)).
  (*Lemma SRepAdd_Correct forall x y : ModularArithmetic.F.F l, SRepEq (S2Rep (ModularArithmetic.F.add x y)) (SRepAdd (S2Rep x) (S2Rep y))).*)
  Global Instance SRepAdd_Proper : Proper (SRepEq ==> SRepEq ==> SRepEq) SRepAdd.
  Proof. unfold SRepEq; repeat intro; subst; reflexivity. Qed.
  Definition SRepMul : SRep -> SRep -> SRep
    := Eval srep in fun x y => barrett_reduce_function_bundled (ZBounded.Mul x y).
  (*Lemma SRepMul_Correct : forall x y : ModularArithmetic.F.F l, SRepEq (S2Rep (ModularArithmetic.F.mul x y)) (SRepMul (S2Rep x) (S2Rep y)). *)
  Global Instance SRepMul_Proper : Proper (SRepEq ==> SRepEq ==> SRepEq) SRepMul.
  Proof. unfold SRepEq; repeat intro; subst; reflexivity. Qed.
  Definition SRepDecModLShort : Word.word (256 + 1) -> SRep
    := Eval srep in
        fun w => dlet w := (Z.of_N (Word.wordToN w)) in barrett_reduce_function_bundled w.
  (*Lemma SRepDecModLShort_Correct : forall w : Word.word (n + 1), SRepEq (S2Rep (ModularArithmetic.F.of_nat l (Word.wordToNat w))) (SRepDecModLShort w). *)
  Arguments Algebra.group : clear implicits.
  Check @sign_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
  Check @verify_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ ed25519.
End x86.

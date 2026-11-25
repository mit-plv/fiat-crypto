Set Loose Hint Behavior "Strict".
(* This should be in the Coq library *)
Require Import Coq.Classes.Morphisms Coq.Classes.Morphisms_Prop.
Require Import Coq.Arith.Arith Coq.NArith.NArith Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Lemma N_to_Z_to_nat: forall (a: N), Z.to_nat (Z.of_N a) = N.to_nat a.
Proof.
  intros. rewrite <- (N2Z.id a) at 2.
  rewrite Z_N_nat. reflexivity.
Qed.

Module N2Nat.

  Lemma inj_mod: forall (a b: N),
      (b <> 0)%N ->
      N.to_nat (a mod b)%N = (N.to_nat a) mod (N.to_nat b).
  Proof.
    intros.
    rewrite <-? N_to_Z_to_nat.
    rewrite N2Z.inj_mod by assumption.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_mod.
    rewrite? Z2Nat.id; try apply N2Z.is_nonneg.
    - reflexivity.
    - pose proof (Z.mod_pos_bound (Z.of_N a) (Z.of_N b)) as Q.
      destruct Q as [Q _].
      + destruct b; try contradiction. simpl. constructor.
      + exact Q.
  Qed.

End N2Nat.

Module Nat2Z.

  Lemma inj_pow: forall n m : nat,
      Z.of_nat (n ^ m) = (Z.of_nat n ^ Z.of_nat m)%Z.
  Proof.
    intros. induction m.
    - reflexivity.
    - rewrite Nat2Z.inj_succ.
      rewrite Z.pow_succ_r by (apply Nat2Z.is_nonneg).
      rewrite <- IHm.
      rewrite <- Nat2Z.inj_mul.
      reflexivity.
  Qed.

End Nat2Z.

Module Z2Nat.

  Lemma inj_pow: forall n m : Z,
      (0 <= n)%Z ->
      (0 <= m)%Z ->
      Z.to_nat (n ^ m) = Z.to_nat n ^ Z.to_nat m.
  Proof.
    intros.
    pose proof (Nat2Z.inj_pow (Z.to_nat n) (Z.to_nat m)) as P.
    rewrite? Z2Nat.id in P by assumption.
    rewrite <- P.
    apply Nat2Z.id.
  Qed.

End Z2Nat.

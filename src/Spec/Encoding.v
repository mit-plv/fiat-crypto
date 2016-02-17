Require Import ZArith.ZArith Zpower ZArith.
Require Import NPeano.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems Crypto.ModularArithmetic.ModularArithmeticTheorems.
Require Import Bedrock.Word.
Require Import VerdiTactics.
Require Import Crypto.Util.NatUtil.

Class Encoding (T B:Type) := {
  enc : T -> B ;
  dec : B -> option T ;
  encoding_valid : forall x, dec (enc x) = Some x
}.
Notation "'encoding' 'of' T 'as' B" := (Encoding T B) (at level 50).

Local Open Scope nat_scope.

Section ModularWordEncoding.
  Context {m : Z} {sz : nat} {m_pos : (0 < m)%Z} {bound_check : Z.to_nat m < 2 ^ sz}.

  Definition Fm_enc (x : F m) : word sz := natToWord sz (Z.to_nat (FieldToZ x)).

  Definition Fm_dec (x_ : word sz) : option (F m) :=
    let z := Z.of_nat (wordToNat (x_)) in
    if Z_lt_dec z m
      then Some (ZToField z)
      else None
  .

  Lemma bound_check_N : forall x : F m, (N.of_nat (Z.to_nat x) < Npow2 sz)%N.
  Proof.
    intro.
    pose proof (FieldToZ_range x m_pos) as x_range.
    rewrite <- Nnat.N2Nat.id.
    rewrite Npow2_nat.
    apply (Nat2N_inj_lt (Z.to_nat x) (pow2 sz)).
    rewrite ZUtil.Zpow_pow2.
    destruct x_range as [x_low x_high].
    apply Z2Nat.inj_lt in x_high; try omega.
    rewrite <- ZUtil.pow_Z2N_Zpow by omega.
    replace (Z.to_nat 2) with 2%nat by auto.
    omega.
  Qed.

  Lemma Fm_encoding_valid : forall x, Fm_dec (Fm_enc x) = Some x.
  Proof.
    unfold Fm_dec, Fm_enc; intros.
    pose proof (FieldToZ_range x m_pos).
    rewrite wordToNat_natToWord_idempotent by apply bound_check_N.
    rewrite Z2Nat.id by omega.
    rewrite ZToField_idempotent.
    break_if; auto; omega.
  Qed.

  Instance modular_word_encoding : encoding of F m as word sz := {
    enc := Fm_enc;
    dec := Fm_dec;
    encoding_valid := Fm_encoding_valid
  }.

End ModularWordEncoding.

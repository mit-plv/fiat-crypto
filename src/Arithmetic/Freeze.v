Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import QArith.QArith_base QArith.Qround Crypto.Util.QUtil.
Require Import Crypto.Arithmetic.BaseConversion.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Opp.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.PeelLe.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.

(* TODO: rename this module? (Should it be, e.g., [Rows.freeze]?) *)
Module Freeze.
  Section Freeze.
    Context weight {wprops : @weight_properties weight}.

    Definition freeze n mask (m p:list Z) : list Z :=
      let '(p, carry) := Rows.sub weight n p m in
      let '(r, carry) := Rows.conditional_add weight n mask (-carry) p m in
      r.

    Lemma freezeZ m s c y :
      m = s - c ->
      0 < c < s ->
      s <> 0 ->
      0 <= y < 2*m ->
      ((y - m) + (if (dec (-((y - m) / s) = 0)) then 0 else m)) mod s
      = y mod m.
    Proof using Type.
      clear; intros.
      transitivity ((y - m) mod m);
        repeat first [ progress intros
                     | progress subst
                     | rewrite Z.opp_eq_0_iff in *
                     | break_innermost_match_step
                     | progress autorewrite with zsimplify_fast
                     | rewrite Z.div_small_iff in * by auto
                     | progress (Z.rewrite_mod_small; push_Zmod; Z.rewrite_mod_small)
                     | progress destruct_head'_or
                     | lia ].
    Qed.

    Lemma length_freeze n mask m p :
      length m = n -> length p = n -> length (freeze n mask m p) = n.
    Proof using wprops.
      cbv [freeze Rows.conditional_add Rows.add]; eta_expand; intros.
      distr_length; try assumption; cbn; intros; destruct_head'_or; destruct_head' False; subst;
        distr_length.
      erewrite Rows.length_sum_rows by (reflexivity || eassumption || distr_length); distr_length.
    Qed.
    Lemma eval_freeze_eq n mask m p
          (n_nonzero:n<>0%nat)
          (Hmask : List.map (Z.land mask) m = m)
          (Hplen : length p = n)
          (Hmlen : length m = n)
      : Positional.eval weight n (@freeze n mask m p)
        = (Positional.eval weight n p - Positional.eval weight n m +
           (if dec (-((Positional.eval weight n p - Positional.eval weight n m) / weight n) = 0) then 0 else Positional.eval weight n m))
            mod weight n.
            (*if dec ((Positional.eval weight n p - Positional.eval weight n m) / weight n = 0)
          then Positional.eval weight n p - Positional.eval weight n m
          else Positional.eval weight n p mod weight n.*)
    Proof using wprops.
      pose proof (@weight_positive weight wprops n).
      cbv [freeze Z.equiv_modulo]; eta_expand.
      repeat first [ solve [auto]
                   | rewrite Rows.conditional_add_partitions
                   | rewrite Rows.sub_partitions
                   | rewrite Rows.sub_div
                   | rewrite eval_partition
                   | progress distr_length
                   | progress pull_Zmod (*
                   | progress break_innermost_match_step
                   | progress destruct_head'_or
                   | lia
                   | f_equal; lia
                   | rewrite Z.div_small_iff in * by (auto using (@weight_positive weight ltac:(assumption)))
                   | progress Z.rewrite_mod_small *) ].
    Qed.

    Lemma eval_freeze n c mask m p
          (n_nonzero:n<>0%nat)
          (Hc : 0 < Associational.eval c < weight n)
          (Hmask : List.map (Z.land mask) m = m)
          (modulus:=weight n - Associational.eval c)
          (Hm : Positional.eval weight n m = modulus)
          (Hp : 0 <= Positional.eval weight n p < 2*modulus)
          (Hplen : length p = n)
          (Hmlen : length m = n)
      : Positional.eval weight n (@freeze n mask m p)
        = Positional.eval weight n p mod modulus.
    Proof using wprops.
      pose proof (@weight_positive weight wprops n).
      rewrite eval_freeze_eq by assumption.
      erewrite freezeZ; try eassumption; try lia.
      f_equal; lia.
    Qed.

    Lemma freeze_partitions n c mask m p
          (n_nonzero:n<>0%nat)
          (Hc : 0 < Associational.eval c < weight n)
          (Hmask : List.map (Z.land mask) m = m)
          (modulus:=weight n - Associational.eval c)
          (Hm : Positional.eval weight n m = modulus)
          (Hp : 0 <= Positional.eval weight n p < 2*modulus)
          (Hplen : length p = n)
          (Hmlen : length m = n)
      : @freeze n mask m p = Partition.partition weight n (Positional.eval weight n p mod modulus).
    Proof using wprops.
      pose proof (@weight_positive weight wprops n).
      pose proof (fun v => Z.mod_pos_bound v (weight n) ltac:(lia)).
      pose proof (Z.mod_pos_bound (Positional.eval weight n p) modulus ltac:(lia)).
      subst modulus.
      erewrite <- eval_freeze by eassumption.
      cbv [freeze]; eta_expand.
      rewrite Rows.conditional_add_partitions by (auto; rewrite Rows.sub_partitions; auto; distr_length).
      rewrite !eval_partition by assumption.
      apply Partition.partition_Proper; [ assumption .. | ].
      cbv [Z.equiv_modulo].
      pull_Zmod; reflexivity.
    Qed.
  End Freeze.
End Freeze.
Hint Rewrite Freeze.length_freeze : distr_length.

Section freeze_mod_ops.
  Import Positional.
  Import Freeze.
  Local Coercion Z.of_nat : nat >-> Z.
  Local Coercion QArith_base.inject_Z : Z >-> Q.
  (* Design constraints:
     - inputs must be [Z] (b/c reification does not support Q)
     - internal structure must not match on the arguments (b/c reification does not support [positive]) *)
  Context (limbwidth_num limbwidth_den : Z)
          (limbwidth_good : 0 < limbwidth_den <= limbwidth_num)
          (s : Z)
          (c : list (Z*Z))
          (n : nat)
          (bitwidth : Z)
          (m_enc : list Z)
          (m_nz:s - Associational.eval c <> 0) (s_nz:s <> 0)
          (Hn_nz : n <> 0%nat)
          (Hs_big : 1 < s).
  Local Notation bytes_weight := (@weight 8 1).
  Local Notation weight := (@weight limbwidth_num limbwidth_den).
  Let m := (s - Associational.eval c).

  Context (Hs : s = weight n).
  Context (c_small : 0 < Associational.eval c < weight n)
          (m_enc_bounded : List.map (BinInt.Z.land (Z.ones bitwidth)) m_enc = m_enc)
          (m_enc_correct : Positional.eval weight n m_enc = m)
          (Hm_enc_len : length m_enc = n).

  Definition wprops_bytes := (@wprops 8 1 ltac:(clear; lia)).
  Local Notation wprops := (@wprops limbwidth_num limbwidth_den limbwidth_good).

  Local Notation wunique := (@weight_unique limbwidth_num limbwidth_den limbwidth_good).
  Local Notation wunique_bytes := (@weight_unique 8 1 ltac:(clear; lia)) (only parsing).

  Local Hint Immediate (wprops) : core.
  Local Hint Immediate (wprops_bytes) : core.
  Local Hint Immediate (weight_0 wprops) : core.
  Local Hint Immediate (weight_positive wprops) : core.
  Local Hint Immediate (weight_multiples wprops) : core.
  Local Hint Immediate (weight_divides wprops) : core.
  Local Hint Immediate (weight_0 wprops_bytes) : core.
  Local Hint Immediate (weight_positive wprops_bytes) : core.
  Local Hint Immediate (weight_multiples wprops_bytes) : core.
  Local Hint Immediate (weight_divides wprops_bytes) : core.
  Local Hint Immediate (wunique) (wunique_bytes) : core.
  Local Hint Resolve (wunique) (wunique_bytes) : core.

  Definition bytes_n
    := Eval cbv [Qceiling Qdiv inject_Z Qfloor Qmult Qopp Qnum Qden Qinv Pos.mul]
      in Z.to_nat (Qceiling (Z.log2_up s / 8)).

  Lemma weight_bytes_weight_matches
    : weight n <= bytes_weight bytes_n.
  Proof using limbwidth_good Hs.
    clear -limbwidth_good Hs.
    cbv [weight bytes_n] in *; subst s.
    autorewrite with zsimplify_const.
    rewrite Z.log2_up_pow2, !Z2Nat.id, !Z.opp_involutive by (Z.div_mod_to_quot_rem; nia).
    Z.peel_le.
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Definition to_bytes (v : list Z)
    := BaseConversion.convert_bases weight bytes_weight n bytes_n v.

  Definition from_bytes (v : list Z)
    := BaseConversion.convert_bases bytes_weight weight bytes_n n v.

  Definition freeze_to_bytesmod (f : list Z) : list Z
    := to_bytes (freeze weight n (Z.ones bitwidth) m_enc f).

  Definition to_bytesmod (f : list Z) : list Z
    := to_bytes f.

  Definition from_bytesmod (f : list Z) : list Z
    := from_bytes f.

  Lemma bytes_pos : (0 < bytes_n)%nat.
  Proof using Hs_big.
    clear -Hs_big.
    cbv [bytes_n].
    pose proof (Z.log2_up_pos s Hs_big).
    zify; rewrite ?Z2Nat.id in *. (* This line only needed in < 8.11 *)
    all: Z.div_mod_to_quot_rem; try nia.
  Qed.

  Lemma bytes_nz : bytes_n <> 0%nat.
  Proof using Hs_big. generalize bytes_pos; clear; lia. Qed.

  Lemma bytes_n_big : weight n <= bytes_weight bytes_n.
  Proof using limbwidth_good Hn_nz Hs.
    clear -limbwidth_good Hn_nz Hs.
    cbv [bytes_n bytes_weight] in *; subst s.
    Z.peel_le.
    rewrite Z.log2_up_pow2 by (Z.div_mod_to_quot_rem; nia).
    autorewrite with zsimplify_fast.
    rewrite Z2Nat.id by (Z.div_mod_to_quot_rem; nia).
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma eval_to_bytes
    : forall (f : list Z)
        (Hf : length f = n),
      eval bytes_weight bytes_n (to_bytes f) = eval weight n f.
  Proof using limbwidth_good Hs_big.
    generalize wprops wprops_bytes; clear -limbwidth_good Hs_big.
    intros.
    cbv [to_bytes].
    rewrite BaseConversion.eval_convert_bases
      by (auto using bytes_nz; distr_length; auto using wprops).
    reflexivity.
  Qed.

  Lemma to_bytes_partitions
    : forall (f : list Z)
             (Hf : length f = n)
             (Hf_small : 0 <= eval weight n f < s),
      to_bytes f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f).
  Proof using Hs_big limbwidth_good.
    clear -Hs_big limbwidth_good.
    intros; cbv [to_bytes].
    pose proof bytes_nz.
    apply BaseConversion.convert_bases_partitions; eauto; try lia.
    split; [ | eapply Z.lt_le_trans ]; [ apply Hf_small.. | ].
    cbv [bytes_weight bytes_n].
    pose proof (Z.log2_up_pos s Hs_big).
    rewrite Z2Nat.id by (Z.div_mod_to_quot_rem; nia).
    autorewrite with zsimplify_fast.
    etransitivity; [ now apply Z.log2_up_spec | ].
    Z.peel_le.
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma eval_to_bytesmod
    : forall (f : list Z)
             (Hf : length f = n)
             (Hf_small : 0 <= eval weight n f < s),
      eval bytes_weight bytes_n (to_bytesmod f) = eval weight n f
      /\ to_bytesmod f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f).
  Proof using Hs_big limbwidth_good.
    split; apply eval_to_bytes || apply to_bytes_partitions; assumption.
  Qed.

  Lemma eval_freeze_to_bytesmod_and_partitions
    : forall (f : list Z)
        (Hf : length f = n)
        (Hf_bounded : 0 <= eval weight n f < 2 * m),
      (eval bytes_weight bytes_n (freeze_to_bytesmod f)) = (eval weight n f) mod m
      /\ freeze_to_bytesmod f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f mod m).
  Proof using m_enc_correct Hs_big limbwidth_good Hn_nz Hs c_small Hm_enc_len m_enc_bounded.
    clear -m_enc_correct Hs_big limbwidth_good Hn_nz Hs c_small Hm_enc_len m_enc_bounded.
    pose proof eval_to_bytes as eval_to_bytes.
    pose proof to_bytes_partitions as to_bytes_partitions.
    intros; subst m; rewrite Hs in *.
    cbv [freeze_to_bytesmod].
    rewrite eval_to_bytes, to_bytes_partitions;
      erewrite ?eval_freeze by eauto using wprops;
      autorewrite with distr_length; eauto.
    Z.div_mod_to_quot_rem; nia.
  Qed.

  Lemma eval_freeze_to_bytesmod
    : forall (f : list Z)
        (Hf : length f = n)
        (Hf_bounded : 0 <= eval weight n f < 2 * m),
      (eval bytes_weight bytes_n (freeze_to_bytesmod f)) = (eval weight n f) mod m.
  Proof using m_enc_correct Hs_big limbwidth_good Hn_nz Hs c_small Hm_enc_len m_enc_bounded.
    intros; now apply eval_freeze_to_bytesmod_and_partitions.
  Qed.

  Lemma freeze_to_bytesmod_partitions
    : forall (f : list Z)
        (Hf : length f = n)
        (Hf_bounded : 0 <= eval weight n f < 2 * m),
      freeze_to_bytesmod f = Partition.partition bytes_weight bytes_n (Positional.eval weight n f mod m).
  Proof using m_enc_correct Hs_big limbwidth_good Hn_nz Hs c_small Hm_enc_len m_enc_bounded.
    intros; now apply eval_freeze_to_bytesmod_and_partitions.
  Qed.

  Lemma eval_from_bytes
    : forall (f : list Z)
        (Hf : length f = bytes_n),
      eval weight n (from_bytes f) = eval bytes_weight bytes_n f.
  Proof using limbwidth_good Hs_big Hn_nz.
    generalize wprops wprops_bytes; clear -Hs_big limbwidth_good Hn_nz.
    intros.
    cbv [from_bytes].
    rewrite BaseConversion.eval_convert_bases
      by (auto using bytes_nz; distr_length; auto using wprops).
    reflexivity.
  Qed.

  Lemma from_bytes_partitions
    : forall (f : list Z)
             (Hf_small : 0 <= eval bytes_weight bytes_n f < weight n),
      from_bytes f = Partition.partition weight n (Positional.eval bytes_weight bytes_n f).
  Proof using limbwidth_good Hn_nz.
    clear -limbwidth_good Hn_nz.
    intros; cbv [from_bytes].
    apply BaseConversion.convert_bases_partitions; eauto; lia.
  Qed.

  Lemma eval_from_bytesmod
    : forall (f : list Z)
             (Hf : length f = bytes_n),
      eval weight n (from_bytesmod f) = eval bytes_weight bytes_n f.
  Proof using Hn_nz Hs_big limbwidth_good. apply eval_from_bytes. Qed.

  Lemma from_bytesmod_partitions
    : forall (f : list Z)
             (Hf_small : 0 <= eval bytes_weight bytes_n f < weight n),
      from_bytesmod f = Partition.partition weight n (Positional.eval bytes_weight bytes_n f).
  Proof using limbwidth_good Hn_nz. apply from_bytes_partitions. Qed.

  Lemma eval_from_bytesmod_and_partitions
    : forall (f : list Z)
             (Hf : length f = bytes_n)
             (Hf_small : 0 <= eval bytes_weight bytes_n f < weight n),
      eval weight n (from_bytesmod f) = eval bytes_weight bytes_n f
      /\ from_bytesmod f = Partition.partition weight n (Positional.eval bytes_weight bytes_n f).
  Proof using limbwidth_good Hn_nz Hs_big.
    now (split; [ apply eval_from_bytesmod | apply from_bytes_partitions ]).
  Qed.
End freeze_mod_ops.
Hint Rewrite eval_freeze_to_bytesmod eval_to_bytes eval_to_bytesmod eval_from_bytes eval_from_bytesmod : push_eval.

Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Util.Notations.
Local Open Scope Z_scope.
Import Weight.

Definition uweight (lgr : Z) : nat -> Z
  := weight lgr 1.
Definition uwprops lgr (Hr : 0 < lgr) : @weight_properties (uweight lgr).
Proof using Type. apply wprops; lia. Qed.
Lemma uweight_eq_alt' lgr n : uweight lgr n = 2^(lgr*Z.of_nat n).
Proof using Type. now cbv [uweight weight]; autorewrite with zsimplify_fast. Qed.
Lemma uweight_eq_alt lgr (Hr : 0 <= lgr) n : uweight lgr n = (2^lgr)^Z.of_nat n.
Proof using Type. now rewrite uweight_eq_alt', Z.pow_mul_r by lia. Qed.
Lemma uweight_eval_shift lgr (Hr : 0 <= lgr) xs :
  forall n,
    length xs = n ->
    Positional.eval (fun i => uweight lgr (S i)) n xs =
    (uweight lgr 1) * Positional.eval (uweight lgr) n xs.
Proof using Type.
  induction xs using rev_ind; destruct n; distr_length;
    intros; [cbn; ring | ].
  rewrite !Positional.eval_snoc with (n:=n) by distr_length.
  rewrite IHxs, !uweight_eq_alt by lia.
  autorewrite with push_Zof_nat push_Zpow.
  rewrite !Z.pow_succ_r by auto with zarith.
  ring.
Qed.
Lemma uweight_S lgr (Hr : 0 <= lgr) n : uweight lgr (S n) = 2 ^ lgr * uweight lgr n.
Proof using Type.
  rewrite !uweight_eq_alt by auto.
  autorewrite with push_Zof_nat.
  rewrite Z.pow_succ_r by auto with zarith.
  reflexivity.
Qed.
Lemma uweight_double_le lgr (Hr : 0 < lgr) n : uweight lgr n + uweight lgr n <= uweight lgr (S n).
Proof using Type.
  rewrite uweight_S, uweight_eq_alt by lia.
  rewrite Z.add_diag.
  apply Z.mul_le_mono_nonneg_r.
  { auto with zarith. }
  { transitivity (2 ^ 1); [ reflexivity | ].
    apply Z.pow_le_mono_r; lia. }
Qed.
Lemma uweight_sum_indices lgr (Hr : 0 <= lgr) i j : uweight lgr (i + j) = uweight lgr i * uweight lgr j.
Proof.
  rewrite !uweight_eq_alt by lia.
  rewrite Nat2Z.inj_add; auto using Z.pow_add_r with zarith.
Qed.
Lemma uweight_0 lgr : uweight lgr 0 = 1.
Proof.
  rewrite uweight_eq_alt', Z.mul_0_r; reflexivity.
Qed.
Lemma uweight_1 lgr : uweight lgr 1 = 2^lgr.
Proof using Type.
  cbv [uweight weight].
  f_equal; autorewrite with zsimplify_const; lia.
Qed.

(* Because the weight is uniform, we can start partitioning from
  any index and end up with the same result. *)
Lemma uweight_recursive_partition_change_start lgr (Hr : 0 <= lgr) n :
  forall i j x,
    recursive_partition (uweight lgr) n i x
    = recursive_partition (uweight lgr) n j x.
Proof using Type.
  induction n; intros; [reflexivity | ].
  cbn [recursive_partition].
  rewrite !uweight_eq_alt by lia.
  autorewrite with push_Zof_nat push_Zpow.
  rewrite <-!Z.pow_sub_r by auto using Z.pow_nonzero with lia.
  rewrite !Z.sub_succ_l.
  autorewrite with zsimplify_fast.
  erewrite IHn. reflexivity.
Qed.
Lemma uweight_recursive_partition_equiv lgr (Hr : 0 < lgr) n i x:
  Partition.partition (uweight lgr) n x =
  recursive_partition (uweight lgr) n i x.
Proof using Type.
  rewrite recursive_partition_equiv by auto using uwprops.
  auto using uweight_recursive_partition_change_start with lia.
Qed.

Lemma uweight_firstn_partition lgr (Hr : 0 < lgr) n x m (Hm : (m <= n)%nat) :
  firstn m (Partition.partition (uweight lgr) n x) = Partition.partition (uweight lgr) m x.
Proof.
  cbv [Partition.partition];
    repeat match goal with
           | _ => progress intros
           | _ => progress autorewrite with push_firstn natsimplify zsimplify_fast
           | _ => rewrite Nat.min_l by lia
           | _ => rewrite weight_0 by auto using uwprops
           | _ => reflexivity
           end.
Qed.

Lemma uweight_skipn_partition lgr (Hr : 0 < lgr) n x m :
  skipn m (Partition.partition (uweight lgr) n x) = Partition.partition (uweight lgr) (n - m) (x / uweight lgr m).
Proof.
  cbv [Partition.partition];
    repeat match goal with
           | _ => progress intros
           | _ => progress autorewrite with push_skipn natsimplify zsimplify_fast
           | _ => rewrite skipn_seq by auto
           | _ => rewrite weight_0 by auto using uwprops
           | _ => rewrite recursive_partition_equiv' by auto using uwprops
           | _ => auto using uweight_recursive_partition_change_start with zarith
           end.
Qed.

Lemma uweight_partition_unique lgr (Hr : 0 < lgr) n ls :
  length ls = n -> (forall x, List.In x ls -> 0 <= x <= 2^lgr - 1) ->
  ls = Partition.partition (uweight lgr) n (Positional.eval (uweight lgr) n ls).
Proof using Type.
  intro; subst n.
  rewrite uweight_recursive_partition_equiv with (i:=0%nat) by assumption.
  induction ls as [|x xs IHxs]; [ reflexivity | ].
  repeat first [ progress cbn [List.length recursive_partition List.In] in *
               | progress intros
               | assumption
               | rewrite Positional.eval_cons by reflexivity
               | rewrite weight_0 by now apply uwprops
               | rewrite uweight_1
               | progress specialize_by_assumption
               | progress split_contravariant_or
               | rewrite uweight_recursive_partition_change_start with (i:=1%nat) (j:=0%nat) by lia
               | rewrite uweight_eval_shift by lia
               | rewrite Z.div_1_r
               | progress Z.rewrite_mod_small
               | rewrite Z.div_add' by auto with arith lia
               | rewrite Z.div_small by lia
               | match goal with
                 | [ H : forall x, _ = x -> _ |- _ ] => specialize (H _ eq_refl)
                 | [ |- context[(_ + ?x * _) mod ?x] ]
                   => let k := fresh in
                      set (k := x); push_Zmod; pull_Zmod; subst k;
                      progress autorewrite with zsimplify_const
                 | [ |- ?x :: _ = ?x :: _ ] => apply f_equal
                 end ].
Qed.

Lemma uweight_eval_app' lgr (Hr : 0 <= lgr) n x y :
  n = length x ->
  Positional.eval (uweight lgr) (n + length y) (x ++ y) = Positional.eval (uweight lgr) n x + (uweight lgr n) * Positional.eval (uweight lgr) (length y) y.
Proof using Type.
  induction y using rev_ind;
    repeat match goal with
           | _ => progress intros
           | _ => progress distr_length
           | _ => progress autorewrite with push_eval zsimplify natsimplify
           | _ => rewrite Nat.add_succ_r
           | H : ?x = 0%nat |- _ => subst x
           | _ => progress rewrite ?app_nil_r, ?app_assoc
           | _ => reflexivity
           end.
  rewrite IHy by auto. rewrite uweight_sum_indices; lia.
Qed.

Lemma uweight_eval_app lgr (Hr : 0 <= lgr) n m x y :
  n = length x ->
  m = (n + length y)%nat ->
  Positional.eval (uweight lgr) m (x ++ y) = Positional.eval (uweight lgr) n x + (uweight lgr n) * Positional.eval (uweight lgr) (length y) y.
Proof using Type. intros. subst m. apply uweight_eval_app'; lia. Qed.

Lemma uweight_partition_app lgr (Hr : 0 < lgr) n m a b :
 Partition.partition (uweight lgr) n a ++ Partition.partition (uweight lgr) m b
  = Partition.partition (uweight lgr) (n+m) (a mod uweight lgr n + b * uweight lgr n).
Proof.
  assert (0 < uweight lgr n) by auto using uwprops.
  match goal with |- _ = ?rhs => rewrite <-(firstn_skipn n rhs) end.
  rewrite uweight_firstn_partition, uweight_skipn_partition by lia.
  rewrite Z.div_add by lia.
  rewrite (Z.div_small (_ mod _)) by auto with zarith.
  f_equal.
  { apply partition_eq_mod; [ auto using uwprops | ].
    push_Zmod. autorewrite with zsimplify. reflexivity. }
  { f_equal; lia. }
Qed.

Lemma mod_mod_uweight lgr (Hr : 0 < lgr) a i j :
  (i <= j)%nat -> (a mod (uweight lgr j)) mod (uweight lgr i) = a mod (uweight lgr i).
Proof.
  intros. rewrite <-Znumtheory.Zmod_div_mod; auto using uwprops; [ ].
  rewrite !uweight_eq_alt'. apply Divide.Z.divide_pow_le. nia.
Qed.

Lemma uweight_pull_mod lgr (Hr : 0 < lgr) x i j :
  (j <= i)%nat ->
  x mod (uweight lgr i) / uweight lgr j = (x / uweight lgr j) mod (uweight lgr (i - j)).
Proof.
  intros. rewrite Z.mod_pull_div by auto using Z.lt_le_incl, uwprops.
  rewrite <-uweight_sum_indices by lia.
  repeat (f_equal; try lia).
Qed.

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Classes.Morphisms.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.

Local Open Scope Z_scope.

Local Notation stabilizes_after x l := (exists b, forall n, l < n -> Z.testbit x n = b).

Lemma stabilizes_after_Proper x
  : Proper (Z.le ==> Basics.impl) (fun l => stabilizes_after x l).
Proof.
  intros ?? H [b H']; exists b.
  intros n H''; apply (H' n); omega.
Qed.

Lemma stabilization_time (x:Z) : stabilizes_after x (Z.max (Z.log2 (Z.pred (- x))) (Z.log2 x)).
Proof.
  destruct (Z_lt_le_dec x 0); eexists; intros;
    [ eapply Z.bits_above_log2_neg | eapply Z.bits_above_log2]; lia.
Qed.

Lemma stabilization_time_weaker (x:Z) : stabilizes_after x (Z.log2_up (Z.abs x)).
Proof.
  eapply stabilizes_after_Proper; try apply stabilization_time.
  repeat match goal with
         | [ |- context[Z.abs _ ] ] => apply Zabs_ind; intro
         | [ |- context[Z.log2 ?x] ]
           => rewrite (Z.log2_nonpos x) by omega
         | [ |- context[Z.log2_up ?x] ]
           => rewrite (Z.log2_up_nonpos x) by omega
         | _ => rewrite Z.max_r by auto with zarith
         | _ => rewrite Z.max_l by auto with zarith
         | _ => etransitivity; [ apply Z.le_log2_log2_up | omega ]
         | _ => progress Z.replace_all_neg_with_pos
         | [ H : 0 <= ?x |- _ ]
           => assert (x = 0 \/ x = 1 \/ 1 < x) by omega; clear H; destruct_head' or; subst
         | _ => omega
         | _ => simpl; omega
         | _ => rewrite Z.log2_up_eqn by assumption
         | _ => progress change (Z.log2_up 1) with 0
         end.
Qed.

Lemma land_stabilizes (a b la lb:Z) (Ha:stabilizes_after a la) (Hb:stabilizes_after b lb) : stabilizes_after (Z.land a b) (Z.max la lb).
Proof.
  destruct Ha as [ba Hba]. destruct Hb as [bb Hbb].
  exists (andb ba bb); intros n Hn.
  rewrite Z.land_spec, Hba, Hbb; trivial; lia.
Qed.

Lemma lor_stabilizes (a b la lb:Z) (Ha:stabilizes_after a la) (Hb:stabilizes_after b lb) : stabilizes_after (Z.lor a b) (Z.max la lb).
Proof.
  destruct Ha as [ba Hba]. destruct Hb as [bb Hbb].
  exists (orb ba bb); intros n Hn.
  rewrite Z.lor_spec, Hba, Hbb; trivial; lia.
Qed.

Local Arguments Z.pow !_ !_.
Local Arguments Z.log2_up !_.
Local Arguments Z.add !_ !_.
Lemma testbit_nonneg_iff x
  : (exists l, 0 <= l /\ forall n : Z, l < n -> Z.testbit x n = false) <-> 0 <= x.
Proof.
  split; intro H.
  { destruct H as [l [Hl H]].
    edestruct Z_lt_le_dec; [ | eassumption ].
    pose proof (fun pf n => Z.bits_above_log2_neg x n pf) as H'.
    specialize_by (omega || assumption).
    specialize (H (1 + Z.max l (Z.log2 (Z.pred (- x))))).
    specialize (H' (1 + Z.max l (Z.log2 (Z.pred (- x))))).
    specialize_by (apply Z.max_case_strong; omega).
    congruence. }
  { pose proof (fun n => Z.bits_above_log2 x n H) as Hf.
    eexists; split; [ | eapply Hf ]; auto with zarith. }
Qed.

Lemma stabilizes_bounded_pos (x l:Z) (H:stabilizes_after x l) (Hl : 0 <= l) (Hx : 0 < x)
  : x <= 2^(l + 1) - 1.
Proof.
  assert (Hlt : forall l n, l < n <-> l + 1 <= n) by (intros; omega).
  destruct H as [b H].
  destruct (proj2 (testbit_nonneg_iff x)) as [l' [H0' H1']]; [ omega | ].
  pose proof (Z.testbit_false_bound x (l' + 1)) as Hf.
  pose proof (Z.testbit_false_bound x (l + 1)) as Hf'.
  pose proof (fun pf n => Z.bits_above_log2 x n pf) as Hf''.
  pose proof (fun pf n => Z.log2_lt_pow2 x n pf) as Hlg.
  specialize_by omega.
  setoid_rewrite <- Z.le_ngt in Hf.
  setoid_rewrite <- Z.le_ngt in Hf'.
  setoid_rewrite <- Hlt in Hf; setoid_rewrite <- Hlt in Hf'; clear Hlt.
  setoid_rewrite <- Hlg in Hf''; clear Hlg.
  destruct b; specialize_by (omega || assumption); [ | omega ].
  specialize (H (1 + Z.max l l')).
  specialize (H1' (1 + Z.max l l')).
  specialize_by (apply Z.max_case_strong; omega).
  congruence.
Qed.

Lemma stabilizes_bounded (x l:Z) (H:stabilizes_after x l) (Hl : 0 <= l) : Z.abs x <= 2^(1 + l).
Proof.
  assert (Hlt : forall l n, l < n <-> l + 1 <= n) by (intros; omega).
  rewrite Z.add_comm.
  destruct (Z_zerop x); subst; simpl.
  { cut (0 < 2^(l + 1)); auto with zarith. }
  apply Zabs_ind; intro.
  { etransitivity; [ apply stabilizes_bounded_pos; eauto | ]; omega. }
  { Z.replace_all_neg_with_pos.
    destruct (Z.eq_dec x 1); subst.
    { assert (1 < 2^(l+1)) by auto with zarith.
      omega. }
    { assert (H' : stabilizes_after (Z.pred x) l).
      { destruct H as [b H]; exists (negb b).
        do 2 let x := fresh in intro x; specialize (H x).
        rewrite Z.bits_opp in H by omega.
        destruct b; rewrite ?Bool.negb_true_iff, ?Bool.negb_false_iff in H; assumption. }
      clear H.
      apply stabilizes_bounded_pos in H'; auto; omega. } }
Qed.

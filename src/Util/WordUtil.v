Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.
Require Import Bedrock.Word.
Require Import RelationClasses.

Local Open Scope nat_scope.

Lemma pow2_id : forall n, pow2 n = 2 ^ n.
Proof.
  induction n; intros; simpl; auto.
Qed.

Lemma Zpow_pow2 : forall n, pow2 n = Z.to_nat (2 ^ (Z.of_nat n)).
Proof.
  induction n; intros; auto.
  simpl pow2.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by apply Zle_0_nat.
  rewrite untimes2.
  rewrite Z2Nat.inj_mul by (try apply Z.pow_nonneg; omega).
  rewrite <- IHn.
  auto.
Qed.

Lemma wordToN_NToWord_idempotent : forall sz n, (n < Npow2 sz)%N ->
  wordToN (NToWord sz n) = n.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat.
  rewrite wordToNat_natToWord_idempotent; rewrite Nnat.N2Nat.id; auto.
Qed.

Lemma NToWord_wordToN : forall sz w, NToWord sz (wordToN w) = w.
Proof.
  intros.
  rewrite wordToN_nat, NToWord_nat, Nnat.Nat2N.id.
  apply natToWord_wordToNat.
Qed.

Lemma bound_check_nat_N : forall x n, (Z.to_nat x < 2 ^ n)%nat -> (Z.to_N x < Npow2 n)%N.
Proof.
  intros x n bound_nat.
  rewrite <- Nnat.N2Nat.id, Npow2_nat.
  replace (Z.to_N x) with (N.of_nat (Z.to_nat x)) by apply Z_nat_N.
  apply (Nat2N_inj_lt _ (pow2 n)).
  rewrite pow2_id; assumption.
Qed.

Lemma weqb_false_iff : forall sz (x y : word sz), weqb x y = false <-> x <> y.
Proof.
  split; intros.
  + intro eq_xy; apply weqb_true_iff in eq_xy; congruence.
  + case_eq (weqb x y); intros weqb_xy; auto.
    apply weqb_true_iff in weqb_xy.
    congruence.
Qed.

Definition wfirstn n {m} (w : Word.word m) {H : n <= m} : Word.word n.
  refine (Word.split1 n (m - n) (match _ in _ = N return Word.word N with
                            | eq_refl => w
                            end)); abstract omega. Defined.

Lemma combine_eq_iff {a b} (A:word a) (B:word b) C :
  combine A B = C <-> A = split1 a b C /\ B = split2 a b C.
Proof. intuition; subst; auto using split1_combine, split2_combine, combine_split. Qed.

Definition wordsize_eq_sig
  : {R : nat -> nat -> Prop | forall a b, R a b <-> a = b}.
  exact (exist _ eq (fun _ _ => reflexivity _ )). Qed.
Definition wordsize_eq : nat -> nat -> Prop := proj1_sig wordsize_eq_sig.
Lemma eq_wordsize_eq a b : a = b -> wordsize_eq a b.
Proof. exact (proj2 ((proj2_sig wordsize_eq_sig) a b)). Qed.
Lemma wordsize_eq_eq a b : wordsize_eq a b -> a = b.
Proof. exact (proj1 ((proj2_sig wordsize_eq_sig) a b)). Qed.

Ltac wordsize_eq_to_eq :=
  repeat match goal with
         | [H: wordsize_eq _ _ |- _] => apply wordsize_eq_eq in H
         | [H: wordsize_eq _ _ |- _] => unique pose proof (wordsize_eq_eq _ _ H)
         | |- wordsize_eq _ _ => apply eq_wordsize_eq
         end.

Section cast_word.
  Local Obligation Tactic := repeat (wordsize_eq_to_eq; Tactics.program_simpl).
  Program Fixpoint cast_word {n m} : forall {pf:wordsize_eq n m}, word n -> word m :=
    match n, m return wordsize_eq n m -> word n -> word m with
    | O, O => fun _ _ => WO
    | S n', S m' => fun _ w => WS (whd w) (@cast_word _ _ _ (wtl w))
    | _, _ => _ (* impossible *)
    end.
  Global Arguments cast_word {_ _ _} _. (* 8.4 does not pick up the forall braces *)
End cast_word.

Existing Class wordsize_eq.
Ltac wordsize_eq_tac := wordsize_eq_to_eq; omega.
Ltac gt84_abstract t := t. (* TODO: when we drop Coq 8.4, use [abstract] here *)
Hint Extern 100 (wordsize_eq _ _) => gt84_abstract wordsize_eq_tac : typeclass_instances.

Definition keeplow {n b:nat} {H:n <= b} (w:word b) : word b :=
  (wand (cast_word (zext (wones n) (b-n) )) w).

Local Infix "++" := combine.
Definition clearlow {n b:nat} {H:n <= b} (w:word b) : word b :=
  wand (cast_word( wones (b-n) ++ wzero n )) w.

Definition setbit {n b:nat} {H:n < b} (w:word b) : word b :=
  wor (cast_word( wzero (b-n-1)  ++ wones 1 ++ wzero n )) w.

Lemma wordToNat_cast_word : forall {n} (w:word n) m pf,
  wordToNat (@cast_word n m pf w) = wordToNat w.
Proof.
  induction w; destruct m eqn:Heqm;
    simpl; intros; wordsize_eq_to_eq;
      rewrite ?IHw; solve [trivial | discriminate].
Qed.

Lemma wordToN_cast_word {n} (w:word n) m pf :
  wordToN (@cast_word n m pf w) = wordToN w.
Proof. rewrite !wordToN_nat, wordToNat_cast_word; reflexivity. Qed.
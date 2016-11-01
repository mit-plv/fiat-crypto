Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.
Require Import Bedrock.Word.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Program.
Require Import Coq.Numbers.Natural.Peano.NPeano Util.NatUtil.
Require Import Coq.micromega.Psatz.

Local Open Scope nat_scope.

Create HintDb pull_wordToN discriminated.
Create HintDb push_wordToN discriminated.
Hint Extern 1 => autorewrite with pull_wordToN in * : pull_wordToN.
Hint Extern 1 => autorewrite with push_wordToN in * : push_wordToN.

Ltac word_util_arith := omega.

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

Hint Rewrite NToWord_wordToN : pull_wordToN.

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

Class wordsize_eq (x y : nat) := wordsize_eq_to_eq : x = y.
Ltac wordsize_eq_tac := cbv beta delta [wordsize_eq] in *; omega*.
Ltac gt84_abstract t := t. (* TODO: when we drop Coq 8.4, use [abstract] here *)
Hint Extern 100 (wordsize_eq _ _) => gt84_abstract wordsize_eq_tac : typeclass_instances.

Program Fixpoint cast_word {n m} : forall {pf:wordsize_eq n m}, word n -> word m :=
  match n, m return wordsize_eq n m -> word n -> word m with
  | O, O => fun _ _ => WO
  | S n', S m' => fun _ w => WS (whd w) (@cast_word _ _ _ (wtl w))
  | _, _ => fun _ _ => !
  end.
Global Arguments cast_word {_ _ _} _. (* 8.4 does not pick up the forall braces *)

Lemma cast_word_refl {n} pf (w:word n) : @cast_word n n pf w = w.
Proof. induction w; simpl; auto using f_equal. Qed.

Lemma wordToNat_cast_word {n} (w:word n) m pf :
  wordToNat (@cast_word n m pf w) = wordToNat w.
Proof. destruct pf; rewrite cast_word_refl; trivial. Qed.

Lemma wordToN_cast_word {n} (w:word n) m pf :
  wordToN (@cast_word n m pf w) = wordToN w.
Proof. destruct pf; rewrite cast_word_refl; trivial. Qed.
Hint Rewrite @wordToN_cast_word : push_wordToN.

Import NPeano Nat.
Local Infix "++" := combine.

Definition zext_ge n {m} {pf:m <= n} (w:word m) : word n :=
  cast_word (w ++ wzero (n - m)).

Definition keeplow {b} n (w:word b) : word b :=
  wand (cast_word( wones (min b n) ++ wzero (b-n) )) w.

Definition clearlow {b} n (w:word b) : word b :=
  wand (cast_word( wzero (min b n) ++ wones (b-n) )) w.

Definition setbit {b} n {H:n < b} (w:word b) : word b :=
  wor (cast_word( wzero n ++ wones 1 ++ wzero (b-n-1) )) w.

Definition clearbit {b} n {H:n < b} (w:word b) : word b :=
  wand (cast_word( wones n ++ wzero 1 ++ wones (b-n-1) )) w.

Lemma wordToNat_wzero {n} : wordToNat (wzero n) = 0.
Proof.
  unfold wzero; induction n; simpl; try rewrite_hyp!*; omega.
Qed.

Lemma wordToNat_combine : forall {a} (wa:word a) {b} (wb:word b),
  wordToNat (wa ++ wb) = wordToNat wa + 2^a * wordToNat wb.
Proof.
  induction wa; intros; simpl; rewrite ?IHwa; break_match; nia.
Qed.

Lemma wordToNat_zext_ge {n m pf} (w:word m) : wordToNat (@zext_ge n m pf w) = wordToNat w.
Proof.
  unfold zext_ge.
  rewrite wordToNat_cast_word, wordToNat_combine, wordToNat_wzero; nia.
Qed.

Lemma bitwp_combine {a b} f (x x' : word a) (y y' : word b)
  : bitwp f x x' ++ bitwp f y y' = bitwp f (x ++ y) (x' ++ y').
Proof.
  revert x' y y'.
  induction x as [|b' n x IHx]; simpl.
  { intro x'; intros.
    refine match x' with
           | WO => _
           | _ => I
           end.
    reflexivity. }
  { intros; rewrite IHx; clear IHx; revert x.
    refine match x' in word Sn return match Sn return word Sn -> _ with
                                      | 0 => fun _ => True
                                      | S _ => fun x' => forall x, WS (f b' (whd x')) (bitwp f (x ++ y) (wtl x' ++ y')) = WS (f b' (whd (x' ++ y'))) (bitwp f (x ++ y) (wtl (x' ++ y')))
                                      end x'
           with
           | WO => I
           | WS _ _ _ => fun _ => Logic.eq_refl
           end. }
Qed.

Lemma wand_combine {a b} (x : word a) (y : word b) (z : word (a + b))
  : (x ++ y) ^& z = ((x ^& split1 _ _ z) ++ (y ^& split2 _ _ z)).
Proof.
  rewrite <- (combine_split _ _ z) at 1.
  unfold wand.
  rewrite bitwp_combine.
  reflexivity.
Qed.

Lemma wordToNat_clearlow {b} (c : nat) (x : Word.word b) :
  wordToNat (clearlow c x) = wordToNat x - (wordToNat x) mod (2^c).
Proof.
  assert (2^c <> 0) by auto with arith.
  unfold clearlow.
  match goal with
  | [ |- context[@cast_word _ _ ?pf ?w] ]
    => generalize pf
  end.
  intro H'; revert x; destruct H'; intro x; rewrite cast_word_refl.
  rewrite <- (combine_split _ _ x) at 2 3.
  rewrite wand_combine, !wordToNat_combine, wand_kill, wand_unit, wordToNat_wzero.
  repeat match goal with H := _ |- _ => subst H end. (* only needed in 8.4 *)
  let min := match type of x with word (?min _ _ + _) => min end in
  repeat match goal with
         | [ |- context[?min' b c] ]
           => progress change min' with min
         end.
  generalize (split1 _ _ x); generalize (split2 _ _ x); clear x; simpl.
  apply Min.min_case_strong; intros Hbc x0 x1;
    pose proof (wordToNat_bound x0); pose proof (wordToNat_bound x1);
      rewrite pow2_id in *.
  { assert (b - c = 0) by omega.
    assert (2^b <= 2^c) by auto using pow_le_mono_r with arith.
    generalize dependent (b - c); intros; destruct x0; try omega; [].
    simpl; rewrite mul_0_r, add_0_r.
    rewrite mod_small by omega.
    omega. }
  { rewrite !(mul_comm (2^c)), mod_add, mod_small by omega.
    lia. }
Qed.

Lemma wordToNat_keeplow {b} (c : nat) (x : Word.word b) :
  wordToNat (keeplow c x) = (wordToNat x) mod (2^c).
Proof.
  assert (2^c <> 0) by auto with arith.
  unfold keeplow.
  match goal with
  | [ |- context[@cast_word _ _ ?pf ?w] ]
    => generalize pf
  end.
  intro H'; revert x; destruct H'; intro x; rewrite cast_word_refl.
  repeat match goal with H := _ |- _ => subst H end. (* only needed in 8.4 *)
  let min := match type of x with word (?min _ _ + _) => min end in
  repeat match goal with
         | [ |- context[?min' b c] ]
           => progress change min' with min
         end.
  rewrite <- (combine_split _ _ x) at 2 3.
  rewrite wand_combine, !wordToNat_combine, wand_kill, wand_unit, wordToNat_wzero.
  generalize (split1 _ _ x); generalize (split2 _ _ x); clear x; simpl.
  apply Min.min_case_strong; intros Hbc x0 x1;
    pose proof (wordToNat_bound x0); pose proof (wordToNat_bound x1);
      rewrite pow2_id in *.
  { assert (b - c = 0) by omega.
    assert (2^b <= 2^c) by auto using pow_le_mono_r with arith.
    generalize dependent (b - c); intros; destruct x0; try omega.
    simpl; rewrite mul_0_r, add_0_r.
    rewrite mod_small by omega.
    omega. }
  { rewrite !(mul_comm (2^c)), mod_add, mod_small by omega.
    lia. }
Qed.

Lemma wordToNat_split1 : forall a b w, wordToNat (split1 a b w) = (wordToNat w) mod (2^a).
Proof.
  intro a; induction a.
  { reflexivity. }
  { simpl; intros; rewrite IHa; clear IHa.
    rewrite (shatter_word w); simpl.
    change (2^a + (2^a + 0)) with (2 * 2^a).
    rewrite (mul_comm 2 (2^a)).
    assert (2^a <> 0) by auto with arith.
    destruct (whd w); try rewrite S_mod; try rewrite mul_mod_distr_r; omega. }
Qed.

Lemma wordToNat_wfirstn : forall a b w H, wordToNat (@wfirstn a b w H) = (wordToNat w) mod (2^a).
Proof.
  unfold wfirstn.
  intros; rewrite wordToNat_split1.
  match goal with |- appcontext[match ?x with _ => _ end] => generalize x end.
  intro H'; destruct H'.
  reflexivity.
Qed.

Lemma wordeqb_Zeqb {sz} (x y : word sz) : (Z.of_N (wordToN x) =? Z.of_N (wordToN y))%Z = weqb x y.
Proof.
  match goal with |- ?LHS = ?RHS => destruct LHS eqn:HL, RHS eqn:HR end;
    repeat match goal with
           | _ => reflexivity
           | _ => progress unfold not in *
           | [ H : Z.eqb _ _ = true |- _ ] => apply Z.eqb_eq in H
           | [ |- Z.eqb _ _ = true ] => apply Z.eqb_eq
           | [ H : context[Z.of_N _ = Z.of_N _] |- _ ] => rewrite N2Z.inj_iff in H
           | [ H : wordToN _ = wordToN _ |- _ ] => apply wordToN_inj in H
           | [ H : x = y :> word _ |- _ ] => apply weqb_true_iff in H
           | [ H : ?x = false |- _ ] => progress rewrite <- H; clear H
           | _ => congruence
           | [ H : weqb _ _ = true |- _ ] => apply weqb_true_iff in H; subst
           end.
Qed.

Local Notation bounds_2statement wop Zop := (forall {sz} (x y : word sz),
     (0 <= Zop (Z.of_N (wordToN x)) (Z.of_N (wordToN y))
  -> (Z.log2 (Zop (Z.of_N (wordToN x)) (Z.of_N (wordToN y))) < Z.of_nat sz)
  -> (Z.of_N (wordToN (wop x y)) = (Zop (Z.of_N (wordToN x)) (Z.of_N (wordToN y)))))%Z).

Require Import Crypto.Assembly.WordizeUtil.
Require Import Crypto.Assembly.Bounds.

Lemma wordToN_wplus : bounds_2statement (@wplus _) Z.add.
Proof.
  intros.
  rewrite <- wordize_plus; [rewrite N2Z.inj_add; reflexivity|].
  destruct (N.eq_dec (wordToN x + wordToN y) 0%N) as [e|e];
    [rewrite e; apply Npow2_gt0|].
  apply N.neq_0_lt_0 in e.
  apply N2Z.inj_lt in e.
  apply N2Z.inj_lt.
  rewrite N2Z.inj_add in *.
  rewrite Npow2_N.
  rewrite N2Z.inj_pow.
  replace (Z.of_N 2%N) with 2%Z by auto.
  apply Z.log2_lt_pow2; [auto|].
  rewrite nat_N_Z.
  assumption.
Qed.

Hint Rewrite @wordToN_wplus using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wplus using word_util_arith : pull_wordToN.

Lemma wordToN_wminus : bounds_2statement (@wminus _) Z.sub.
Proof.
  intros sz x y H ?.
  assert (wordToN y <= wordToN x)%N. {
    apply N2Z.inj_le.
    rewrite <- (Z.add_0_l (Z.of_N (wordToN y))).
    apply Z.le_add_le_sub_r; assumption.
  }

  rewrite <- N2Z.inj_sub; [|assumption].
  rewrite <- wordize_minus; [reflexivity|apply N.le_ge; assumption].
Qed.

Hint Rewrite @wordToN_wminus using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wminus using word_util_arith : pull_wordToN.

Lemma wordToN_wmult : bounds_2statement (@wmult _) Z.mul.
Proof.
  intros.
  rewrite <- wordize_mult; [rewrite N2Z.inj_mul; reflexivity|].
  destruct (N.eq_dec (wordToN x * wordToN y) 0%N) as [e|e];
    [rewrite e; apply Npow2_gt0|].
  apply N.neq_0_lt_0 in e.
  apply N2Z.inj_lt in e.
  apply N2Z.inj_lt.
  rewrite N2Z.inj_mul in *.
  rewrite Npow2_N.
  rewrite N2Z.inj_pow.
  replace (Z.of_N 2%N) with 2%Z by auto.
  apply Z.log2_lt_pow2; [auto|].
  rewrite nat_N_Z.
  assumption.
Qed.

Hint Rewrite @wordToN_wmult using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wmult using word_util_arith : pull_wordToN.

Lemma wordToN_wand : bounds_2statement (@wand _) Z.land.
Proof.
  intros.
  rewrite wordize_and.
  apply Z.bits_inj_iff'; intros k Hpos; apply Z.le_ge in Hpos.
  rewrite Z.land_spec.
  rewrite Z2N.inj_testbit; [|apply Z.ge_le; assumption].
  rewrite N.land_spec.
  repeat (rewrite <- Z2N.inj_testbit; [|apply Z.ge_le; assumption]).
  reflexivity.
Qed.
Hint Rewrite @wordToN_wand using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wand using word_util_arith : pull_wordToN.

Lemma wordToN_wor : bounds_2statement (@wor _) Z.lor.
Proof.
  intros.
  rewrite wordize_or.
  apply Z.bits_inj_iff'; intros k Hpos; apply Z.le_ge in Hpos.
  rewrite Z.lor_spec.
  rewrite Z2N.inj_testbit; [|apply Z.ge_le; assumption].
  rewrite N.lor_spec.
  repeat (rewrite <- Z2N.inj_testbit; [|apply Z.ge_le; assumption]).
  reflexivity.
Qed.
Hint Rewrite @wordToN_wor using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wor using word_util_arith : pull_wordToN.

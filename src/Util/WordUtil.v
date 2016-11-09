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

Lemma Z_land_le : forall x y, (0 <= x)%Z -> (Z.land x y <= x)%Z.
Proof.
  intros; apply Z.ldiff_le; [assumption|].
  rewrite Z.ldiff_land, Z.land_comm, Z.land_assoc.
  rewrite <- Z.land_0_l with (a := y); f_equal.
  rewrite Z.land_comm, Z.land_lnot_diag.
  reflexivity.
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

Local Notation bound n lower value upper := (
    (0 <= lower)%Z
  /\ (lower <= Z.of_N (@wordToN n value))%Z
  /\ (Z.of_N (@wordToN n value) <= upper)%Z).

Definition valid_update n lowerF valueF upperF : Prop :=
  forall lower0 value0 upper0
    lower1 value1 upper1,

    bound n lower0 value0 upper0
  -> bound n lower1 value1 upper1
  -> (0 <= lowerF lower0 upper0 lower1 upper1)%Z
  -> (Z.log2 (upperF lower0 upper0 lower1 upper1) < Z.of_nat n)%Z
  -> bound n (lowerF lower0 upper0 lower1 upper1)
            (valueF value0 value1)
            (upperF lower0 upper0 lower1 upper1).

Local Ltac add_mono := 
  etransitivity; [| apply Z.add_le_mono_r; eassumption]; omega.

Lemma add_valid_update: forall n,
    valid_update n
      (fun l0 u0 l1 u1 => l0 + l1)%Z
      (@wplus n)
      (fun l0 u0 l1 u1 => u0 + u1)%Z.
Proof.
  unfold valid_update; intros until upper1; intros B0 B1.
  destruct B0 as [? B0], B1 as [? B1], B0, B1.
  repeat split; [add_mono| |]; (
    rewrite wordToN_wplus; [add_mono|add_mono|];
    eapply Z.le_lt_trans; [| eassumption];
    apply Z.log2_le_mono; add_mono).
Qed.

Local Ltac sub_mono :=
  etransitivity;
  [| apply Z.sub_le_mono_r]; eauto;
  first [ reflexivity
        | apply Z.sub_le_mono_l; assumption
        | apply Z.le_add_le_sub_l; etransitivity; [|eassumption];
          repeat rewrite Z.add_0_r; assumption].

Lemma sub_valid_update: forall n,
    valid_update n
      (fun l0 u0 l1 u1 => l0 - u1)%Z
      (@wminus n)
      (fun l0 u0 l1 u1 => u0 - l1)%Z.
Proof.
  unfold valid_update; intros until upper1; intros B0 B1.
  destruct B0 as [? B0], B1 as [? B1], B0, B1.
  repeat split; [sub_mono| |]; (
   rewrite wordToN_wminus; [sub_mono|omega|];
   eapply Z.le_lt_trans; [apply Z.log2_le_mono|eassumption]; sub_mono).
Qed.

Local Ltac mul_mono := 
  etransitivity; [|apply Z.mul_le_mono_nonneg_r];
  repeat first
  [ eassumption
  | reflexivity
  | apply Z.mul_le_mono_nonneg_l
  | rewrite Z.mul_0_l
  | omega].

Lemma mul_valid_update: forall n,
    valid_update n
      (fun l0 u0 l1 u1 => l0 * l1)%Z
      (@wmult n)
      (fun l0 u0 l1 u1 => u0 * u1)%Z.
Proof.
  unfold valid_update; intros until upper1; intros B0 B1.
  destruct B0 as [? B0], B1 as [? B1], B0, B1.
  repeat split; [mul_mono| |]; (
    rewrite wordToN_wmult; [mul_mono|mul_mono|];
    eapply Z.le_lt_trans; [| eassumption];
    apply Z.log2_le_mono; mul_mono).
Qed.

Local Ltac solve_land_ge0 :=
  apply Z.land_nonneg; left; etransitivity; [|eassumption]; assumption.

Local Ltac land_mono :=
  first [assumption | etransitivity; [|eassumption]; assumption].

Lemma land_valid_update: forall n,
    valid_update n
      (fun l0 u0 l1 u1 => 0)%Z
      (@wand n)
      (fun l0 u0 l1 u1 => Z.min u0 u1)%Z.
Proof.
  unfold valid_update; intros until upper1; intros B0 B1.
  destruct B0 as [? B0], B1 as [? B1], B0, B1.
  repeat split; [reflexivity| |].

  - rewrite wordToN_wand; [solve_land_ge0|solve_land_ge0|].
    eapply Z.le_lt_trans; [apply Z.log2_land; land_mono|];
      eapply Z.le_lt_trans; [| eassumption];
      repeat match goal with
      | [|- context[Z.min ?a ?b]] =>
        destruct (Z.min_dec a b) as [g|g]; rewrite g; clear g
      end; apply Z.log2_le_mono; try assumption.

    admit. admit.

  - rewrite wordToN_wand; [|solve_land_ge0|].
    eapply Z.le_lt_trans; [apply Z.log2_land; land_mono|];
      match goal with
      | [|- (Z.min ?a ?b < _)%Z] =>
        destruct (Z.min_dec a b) as [g|g]; rewrite g; clear g
      end.

  .
  (*
[apply N2Z.is_nonneg|];
      unfold Word64.word64ToZ; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite wordize_and.

    destruct (Z_ge_dec upper1 upper0) as [g|g].

    - rewrite Z.min_r; [|abstract (apply Z.log2_le_mono; omega)].
      abstract (
        rewrite (land_intro_ones (wordToN value0));
        rewrite N.land_assoc;
        etransitivity; [apply N2Z.inj_le; apply N.lt_le_incl; apply land_lt_Npow2|];
        rewrite N2Z.inj_pow;
        apply Z.pow_le_mono; [abstract (split; cbn; [omega|reflexivity])|];
        unfold getBits; rewrite N2Z.inj_succ;
        apply -> Z.succ_le_mono;
        rewrite <- (N2Z.id (wordToN value0)), <- log2_conv;
        apply Z.log2_le_mono;
        etransitivity; [eassumption|reflexivity]).

    - rewrite Z.min_l; [|abstract (apply Z.log2_le_mono; omega)].
      abstract (
        rewrite (land_intro_ones (wordToN value1));
        rewrite <- N.land_comm, N.land_assoc;
        etransitivity; [apply N2Z.inj_le; apply N.lt_le_incl; apply land_lt_Npow2|];
        rewrite N2Z.inj_pow;
        apply Z.pow_le_mono; [abstract (split; cbn; [omega|reflexivity])|];
        unfold getBits; rewrite N2Z.inj_succ;
        apply -> Z.succ_le_mono;
        rewrite <- (N2Z.id (wordToN value1)), <- log2_conv;
        apply Z.log2_le_mono;
        etransitivity; [eassumption|reflexivity]).

*)
Admitted.

Lemma lor_valid_update: forall n,
    valid_update n
      (fun l0 u0 l1 u1 => Z.max l0 l1)%Z
      (@wor n)
      (fun l0 u0 l1 u1 => 2^(Z.max (Z.log2 (u0+1)) (Z.log2 (u1+1))) - 1)%Z.
Proof.
(*      unfold Word64.word64ToZ in *; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite wordize_or.

    - transitivity (Z.max (Z.of_N (wordToN value1)) (Z.of_N (wordToN value0)));
      [ abstract (destruct
          (Z_ge_dec lower1 lower0) as [l|l],
          (Z_ge_dec (Z.of_N (& value1)%w) (Z.of_N (& value0)%w)) as [v|v];
        [ rewrite Z.max_l, Z.max_l | rewrite Z.max_l, Z.max_r
        | rewrite Z.max_r, Z.max_l | rewrite Z.max_r, Z.max_r ];
        
        try (omega || assumption))
      | ].

      rewrite <- N2Z.inj_max.
      apply Z2N.inj_le; [apply N2Z.is_nonneg|apply N2Z.is_nonneg|].
      repeat rewrite N2Z.id.

      abstract (
        destruct (N.max_dec (wordToN value1) (wordToN value0)) as [v|v];
        rewrite v;
        apply N.ldiff_le, N.bits_inj_iff; intros k;
        rewrite N.ldiff_spec, N.lor_spec;
        induction (N.testbit (wordToN value1)), (N.testbit (wordToN value0)); simpl;
        reflexivity).

    - apply Z.lt_le_incl, Z.log2_lt_cancel.
      rewrite Z.log2_pow2; [| abstract (
        destruct (Z.max_dec (Z.log2 upper1) (Z.log2 upper0)) as [g|g];
        rewrite g; apply Z.le_le_succ_r, Z.log2_nonneg)].

      eapply (Z.le_lt_trans _ (Z.log2 (Z.lor _ _)) _).

      + apply Z.log2_le_mono, Z.eq_le_incl.
        apply Z.bits_inj_iff'; intros k Hpos.
        rewrite Z2N.inj_testbit, Z.lor_spec, N.lor_spec; [|assumption].
        repeat (rewrite <- Z2N.inj_testbit; [|assumption]).
        reflexivity.

      + abstract (
          rewrite Z.log2_lor; [|trans'|trans'];
          destruct
            (Z_ge_dec (Z.of_N (wordToN value1)) (Z.of_N (wordToN value0))) as [g0|g0],
            (Z_ge_dec upper1 upper0) as [g1|g1];
            [ rewrite Z.max_l, Z.max_l
            | rewrite Z.max_l, Z.max_r
            | rewrite Z.max_r, Z.max_l
            | rewrite Z.max_r, Z.max_r];
            try apply Z.log2_le_mono; try omega;
            apply Z.le_succ_l;
            apply -> Z.succ_le_mono;
            apply Z.log2_le_mono;
            assumption || (etransitivity; [eassumption|]; omega)).
*)
Admitted.

Lemma shr_valid_update: forall n,
    valid_update n
      (fun l0 u0 l1 u1 => Z.shiftr l0 u1)%Z
      (@wordBin N.shiftr n)
      (fun l0 u0 l1 u1 => Z.shiftr u0 l1)%Z.
Proof.
  (*
    Ltac shr_mono := etransitivity;
      [apply Z.div_le_compat_l | apply Z.div_le_mono].

    assert (forall x, (0 <= x)%Z -> (0 < 2^x)%Z) as gt0. {
      intros; rewrite <- (Z2Nat.id x); [|assumption].
      induction (Z.to_nat x) as [|n]; [cbv; auto|].
      eapply Z.lt_le_trans; [eassumption|rewrite Nat2Z.inj_succ].
      apply Z.pow_le_mono_r; [cbv; auto|omega].
    }

    build_binop Word64.w64shr ZBounds.shr; t_start; abstract (
      unfold Word64.word64ToZ; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite Z.shiftr_div_pow2 in *;
      repeat match goal with
      | [|- _ /\ _ ] => split
      | [|- (0 <= 2 ^ _)%Z ] => apply Z.pow_nonneg
      | [|- (0 < 2 ^ ?X)%Z ] => apply gt0
      | [|- (0 <= _ / _)%Z ] => apply Z.div_le_lower_bound; [|rewrite Z.mul_0_r]
      | [|- (2 ^ _ <= 2 ^ _)%Z ] => apply Z.pow_le_mono_r
      | [|- context[(?a >> ?b)%Z]] => rewrite Z.shiftr_div_pow2 in *
      | [|- (_ < Npow2 _)%N] => 
        apply N2Z.inj_lt, Z.log2_lt_cancel; simpl;
        eapply Z.le_lt_trans; [|eassumption]; apply Z.log2_le_mono; rewrite Z2N.id

      | _ => progress shr_mono
      | _ => progress trans'
      | _ => progress omega
      end).

*)
Admitted.

Lemma shl_valid_update: forall n,
    valid_update n
      (fun l0 u0 l1 u1 => Z.shiftl l0 l1)%Z
      (@wordBin N.shiftl n)
      (fun l0 u0 l1 u1 => Z.shiftl u0 u1)%Z.
Proof.
  (*
    Ltac shl_mono := etransitivity;
      [apply Z.mul_le_mono_nonneg_l | apply Z.mul_le_mono_nonneg_r].

    build_binop Word64.w64shl ZBounds.shl; t_start; abstract (
      unfold Word64.word64ToZ; repeat rewrite wordToN_NToWord; repeat rewrite Z2N.id;
      rewrite Z.shiftl_mul_pow2 in *;
      repeat match goal with
      | [|- (0 <= 2 ^ _)%Z ] => apply Z.pow_nonneg
      | [|- (0 <= _ * _)%Z ] => apply Z.mul_nonneg_nonneg
      | [|- (2 ^ _ <= 2 ^ _)%Z ] => apply Z.pow_le_mono_r
      | [|- context[(?a << ?b)%Z]] => rewrite Z.shiftl_mul_pow2
      | [|- (_ < Npow2 _)%N] => 
        apply N2Z.inj_lt, Z.log2_lt_cancel; simpl;
        eapply Z.le_lt_trans; [|eassumption]; apply Z.log2_le_mono; rewrite Z2N.id

      | _ => progress shl_mono
      | _ => progress trans'
      | _ => progress omega
      end).

*)
Admitted.


Axiom wlast : forall sz, word (sz+1) -> bool. Arguments wlast {_} _.
Axiom winit : forall sz, word (sz+1) -> word sz. Arguments winit {_} _.
Axiom combine_winit_wlast : forall {sz} a b (c:word (sz+1)),
    @combine sz a 1 b = c <-> a = winit c /\ b = (WS (wlast c) WO).
Axiom winit_combine : forall sz a b, @winit sz (combine a b) = a.
Axiom wlast_combine : forall sz a b, @wlast sz (combine a (WS b WO)) = b.
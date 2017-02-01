Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.ZArith.ZArith.
Require Import Coq.NArith.NArith.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Program.Program.
Require Import Coq.Numbers.Natural.Peano.NPeano Util.NatUtil.
Require Import Coq.micromega.Psatz.
Require Import Coq.Bool.Bool.

Require Import Crypto.Util.Bool.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Sigma.

Require Import Bedrock.Word.
Require Import Bedrock.Nomega.

Require Import Crypto.Util.FixCoqMistakes.

Local Open Scope nat_scope.

Create HintDb pull_wordToN discriminated.
Create HintDb push_wordToN discriminated.

Hint Extern 1 => autorewrite with pull_wordToN in * : pull_wordToN.
Hint Extern 1 => autorewrite with push_wordToN in * : push_wordToN.

Module Word.
  Fixpoint weqb_hetero sz1 sz2 (x : word sz1) (y : word sz2) : bool :=
    match x, y with
    | WO, WO => true
    | WO, _ => false
    | WS b _ x', WS b' _ y'
      => eqb b b' && @weqb_hetero _ _ x' y'
    | WS _ _ _, _
      => false
    end%bool.
  Global Arguments weqb_hetero {_ _} _ _.
  Theorem weqb_hetero_true_iff : forall sz1 x sz2 y,
      @weqb_hetero sz1 sz2 x y = true <-> exists pf : sz1 = sz2, eq_rect _ word x _ pf = y.
  Proof.
    induction x; intros sz2 y; (split; [ destruct y | ]);
      repeat first [ progress simpl
                   | intro
                   | congruence
                   | exists eq_refl
                   | progress destruct_head ex
                   | progress destruct_head bool
                   | progress subst
                   | progress split_andb
                   | match goal with
                     | [ IHx : forall sz2 y, weqb_hetero _ y = true <-> _, H : weqb_hetero _ _ = true |- _ ]
                       => apply IHx in H
                     | [ IHx : forall sz2 y, weqb_hetero _ y = true <-> _ |- weqb_hetero ?x ?x = true ]
                       => apply IHx
                     end ].
  Defined.
  (* oh, the hoops I jump through to make this transparent... *)
  Theorem weqb_hetero_homo_true_iff : forall sz x y,
      @weqb_hetero sz sz x y = true <-> x = y.
  Proof.
    etransitivity; [ apply weqb_hetero_true_iff | ].
    split; [ intros [pf H] | intro ]; try (subst y; exists eq_refl; reflexivity).
    revert y H; induction x as [|b n x IHx]; intros.
    { subst y;
        refine match pf in (_ = z)
                     return match z return 0 = z -> Prop with
                            | 0 => fun pf => WO = eq_rect 0 word WO 0 pf
                            | _ => fun pf => True
                            end pf
               with
               | eq_refl => eq_refl
               end. }
    { revert x y H IHx.
      refine (match pf in _ = Sn
                    return match Sn return S n = Sn -> Prop with
                           | 0 => fun _ => True
                           | S n' => fun pf =>
                                       forall (pfn : n = n')
                                              (x : word n)
                                              (y : word (S n'))
                                              (H : eq_rect (S n) word (WS b x) (S n') pf = y)
                                              (IHx : forall (pf : n = n') (y : word n'), eq_rect n word x n' pf = y -> eq_rect n word x n' pfn = y),
                                         WS b (eq_rect n word x n' pfn) = y
                           end pf
              with
              | eq_refl
                => fun pfn x y H IHx
                   => eq_trans
                        (f_equal2 (fun b => @WS b _)
                                  (f_equal (@whd _) H)
                                  (IHx eq_refl (wtl y) (f_equal (@wtl _) H)))
                        _
              end eq_refl).
      refine match y in word Sn return match Sn return word Sn -> Prop with
                                       | 0 => fun _ => True
                                       | S n => fun y => WS (whd y) (wtl y) = y
                                       end y
             with
             | WS _ _ _ => eq_refl
             | _ => I
             end. }
  Defined.
End Word.

(* Utility Tactics *)

Ltac word_util_arith := omega.

Ltac destruct_min :=
  match goal with
  | [|- context[Z.min ?a ?b]] =>
    let g := fresh in
    destruct (Z.min_dec a b) as [g|g]; rewrite g; clear g
  end.

Ltac destruct_max :=
  match goal with
  | [|- context[Z.max ?a ?b]] =>
    let g := fresh in
    destruct (Z.max_dec a b) as [g|g]; rewrite g; clear g
  end.

Ltac shatter a :=
  let H := fresh in
  pose proof (shatter_word a) as H; simpl in H;
    try rewrite H in *; clear H.

Section Natural.
  Definition Nge_dec (x y: N): {N.ge x y} + {N.lt x y}.
    refine (
      let c := (x ?= y)%N in
      match c as c' return c = c' -> _ with
      | Lt => fun _ => right _
      | _ => fun _ => left _
      end eq_refl); abstract (
        unfold c in *; unfold N.lt, N.ge;
        repeat match goal with
        | [ H: (_ ?= _)%N = _ |- _] =>
          rewrite H; intuition; try inversion H
        | [ H: Eq = _ |- _] => inversion H
        | [ H: Gt = _ |- _] => inversion H
        | [ H: Lt = _ |- _] => inversion H
        end).
  Defined.

  Lemma N_ge_0: forall x: N, (0 <= x)%N.
  Proof.
    intro x0; unfold N.le.
    pose proof (N.compare_0_r x0) as H.
    rewrite N.compare_antisym in H.
    induction x0; simpl in *;
      intro V; inversion V.
  Qed.

  Lemma of_nat_lt: forall x b, (x < b)%nat <-> (N.of_nat x < N.of_nat b)%N.
  Proof.
    intros x b; split; intro H.

    - unfold N.lt; rewrite N2Nat.inj_compare.
      repeat rewrite Nat2N.id.
      apply nat_compare_lt in H.
      intuition.

    - unfold N.lt in H; rewrite N2Nat.inj_compare in H.
      repeat rewrite Nat2N.id in H.
      apply nat_compare_lt in H.
      intuition.
  Qed.
End Natural.

Section Pow2.
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

  Lemma Npow2_gt0 : forall x, (0 < Npow2 x)%N.
  Proof.
    intros; induction x.

    - simpl; apply N.lt_1_r; intuition.

    - replace (Npow2 (S x)) with (2 * (Npow2 x))%N by intuition.
        apply (N.lt_0_mul 2 (Npow2 x)); left; split; apply N.neq_0_lt_0.

        + intuition; inversion H.

        + apply N.neq_0_lt_0 in IHx; intuition.
  Qed.

  Lemma Npow2_ge1 : forall x, (1 <= Npow2 x)%N.
  Proof.
    intro x.
    pose proof (Npow2_gt0 x) as Z.
    apply N.lt_pred_le; simpl.
    assumption.
  Qed.

  Lemma Npow2_N: forall n, Npow2 n = (2 ^ N.of_nat n)%N.
  Proof.
    induction n.

    - simpl; intuition.

    - rewrite Nat2N.inj_succ.
      rewrite N.pow_succ_r; [|apply N_ge_0].
      rewrite <- IHn.
      simpl; intuition.
  Qed.

  Lemma Npow2_Zlog2 : forall x n,
      (Z.log2 (Z.of_N x) < Z.of_nat n)%Z
   -> (x < Npow2 n)%N.
  Proof.
    intros.
    apply N2Z.inj_lt.
    rewrite Npow2_N, N2Z.inj_pow, nat_N_Z.
    destruct (N.eq_dec x 0%N) as [e|e].

    - rewrite e.
        apply Z.pow_pos_nonneg; [cbv; reflexivity|apply Nat2Z.is_nonneg].

    - apply Z.log2_lt_pow2; [|assumption].
        apply N.neq_0_lt_0, N2Z.inj_lt in e.
        assumption.
  Qed.

  Lemma Npow2_ordered: forall n m, (n <= m)%nat -> (Npow2 n <= Npow2 m)%N.
  Proof.
    induction n; intros m H; try rewrite Npow2_succ.

    - simpl; apply Npow2_ge1.

    - induction m; try rewrite Npow2_succ.

      + inversion H.

      + assert (n <= m)%nat as H0 by omega.
        apply IHn in H0.
        apply N.mul_le_mono_l.
        assumption.
  Qed.
End Pow2.

Section Z2N.
  Lemma Z_inj_shiftl: forall x y, Z.of_N (N.shiftl x y) = Z.shiftl (Z.of_N x) (Z.of_N y).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftl_spec; [|assumption].

    assert ((Z.to_N k) >= y \/ (Z.to_N k) < y)%N as g by (
        unfold N.ge, N.lt; induction (N.compare (Z.to_N k) y); [left|auto|left];
        intro H; inversion H).

    destruct g as [g|g];
    [ rewrite N.shiftl_spec_high; [|apply N2Z.inj_le; rewrite Z2N.id|apply N.ge_le]
    | rewrite N.shiftl_spec_low]; try assumption.

    - rewrite <- N2Z.inj_testbit; f_equal.
        rewrite N2Z.inj_sub, Z2N.id; [reflexivity|assumption|apply N.ge_le; assumption].

    - apply N2Z.inj_lt in g.
        rewrite Z2N.id in g; [symmetry|assumption].
        apply Z.testbit_neg_r; omega.
  Qed.

  Lemma Z_inj_shiftr: forall x y, Z.of_N (N.shiftr x y) = Z.shiftr (Z.of_N x) (Z.of_N y).
  Proof.
    intros.
    apply Z.bits_inj_iff'; intros k Hpos.
    rewrite Z2N.inj_testbit; [|assumption].
    rewrite Z.shiftr_spec, N.shiftr_spec; [|apply N2Z.inj_le; rewrite Z2N.id|]; try assumption.
    rewrite <- N2Z.inj_testbit; f_equal.
    rewrite N2Z.inj_add; f_equal.
    apply Z2N.id; assumption.
  Qed.
End Z2N.

Section ZInequalities.
  Lemma Z_land_le : forall x y, (0 <= x)%Z -> (Z.land x y <= x)%Z.
  Proof.
    intros; apply Z.ldiff_le; [assumption|].
    rewrite Z.ldiff_land, Z.land_comm, Z.land_assoc.
    rewrite <- Z.land_0_l with (a := y); f_equal.
    rewrite Z.land_comm, Z.land_lnot_diag.
    reflexivity.
  Qed.

  Lemma Z_lor_lower : forall x y, (0 <= x)%Z -> (0 <= y)%Z -> (x <= Z.lor x y)%Z.
  Proof.
    intros; apply Z.ldiff_le; [apply Z.lor_nonneg; auto|].
    rewrite Z.ldiff_land.
    apply Z.bits_inj_iff'; intros k Hpos; apply Z.le_ge in Hpos.
    rewrite Z.testbit_0_l, Z.land_spec, Z.lnot_spec, Z.lor_spec;
        [|apply Z.ge_le; assumption].
    induction (Z.testbit x k), (Z.testbit y k); cbv; reflexivity.
    Qed.

  Lemma Z_lor_le : forall x y z,
       (0 <= x)%Z
    -> (x <= y)%Z
    -> (y <= z)%Z
    -> (Z.lor x y <= (2 ^ Z.log2_up (z+1)) - 1)%Z.
  Proof.
    intros; apply Z.ldiff_le.

    - apply Z.le_add_le_sub_r.
        replace 1%Z with (2 ^ 0)%Z by (cbv; reflexivity).
        rewrite Z.add_0_l.
        apply Z.pow_le_mono_r; [cbv; reflexivity|].
        apply Z.log2_up_nonneg.

    - destruct (Z_lt_dec 0 z).

        + assert (forall a, a - 1 = Z.pred a)%Z as HP by (intro; omega);
            rewrite HP, <- Z.ones_equiv; clear HP.
        apply Z.ldiff_ones_r_low; [apply Z.lor_nonneg; split; omega|].
        rewrite Z.log2_up_eqn, Z.log2_lor; try omega.
        apply Z.lt_succ_r.
        destruct_max; apply Z.log2_le_mono; omega.

        + replace z with 0%Z by omega.
        replace y with 0%Z by omega.
        replace x with 0%Z by omega.
        cbv; reflexivity.
  Qed.

  Lemma Z_pow2_ge_0: forall a, (0 <= 2 ^ a)%Z.
  Proof.
    intros; apply Z.pow_nonneg; omega.
  Qed.

  Lemma Z_pow2_gt_0: forall a, (0 <= a)%Z -> (0 < 2 ^ a)%Z.
  Proof.
    intros; apply Z.pow_pos_nonneg; [|assumption]; omega.
  Qed.

  Local Ltac solve_pow2 :=
    repeat match goal with
    | [|- _ /\ _] => split
    | [|- (0 < 2 ^ _)%Z] => apply Z_pow2_gt_0
    | [|- (0 <= 2 ^ _)%Z] => apply Z_pow2_ge_0
    | [|- (2 ^ _ <= 2 ^ _)%Z] => apply Z.pow_le_mono_r
    | [|- (_ <= _)%Z] => omega
    | [|- (_ < _)%Z] => omega
    end.

  Lemma Z_shiftr_le_mono: forall a b c d,
       (0 <= a)%Z
    -> (0 <= d)%Z
    -> (a <= c)%Z
    -> (d <= b)%Z
    -> (Z.shiftr a b <= Z.shiftr c d)%Z.
  Proof.
    intros.
    repeat rewrite Z.shiftr_div_pow2; [|omega|omega].
    etransitivity; [apply Z.div_le_compat_l | apply Z.div_le_mono]; solve_pow2.
  Qed.

  Lemma Z_shiftl_le_mono: forall a b c d,
       (0 <= a)%Z
    -> (0 <= b)%Z
    -> (a <= c)%Z
    -> (b <= d)%Z
    -> (Z.shiftl a b <= Z.shiftl c d)%Z.
  Proof.
    intros.
    repeat rewrite Z.shiftl_mul_pow2; [|omega|omega].
    etransitivity; [apply Z.mul_le_mono_nonneg_l|apply Z.mul_le_mono_nonneg_r]; solve_pow2.
  Qed.
End ZInequalities.

Section WordToN.
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

  Lemma wordToN_zero: forall w, wordToN (wzero w) = 0%N.
  Proof.
    intros.
    unfold wzero; rewrite wordToN_nat.
    rewrite wordToNat_natToWord_idempotent; simpl; intuition.
    apply Npow2_gt0.
  Qed.

  Fixpoint wbit {n} (x: word n) (k: nat): bool :=
    match n as n' return word n' -> bool with
    | O => fun _ => false
    | S m => fun x' =>
      match k with
      | O => (whd x')
      | S k' => wbit (wtl x') k'
      end
    end x.

  Lemma wbit_inj_iff {n} (x y : word n)
    : (forall k, wbit x k = wbit y k) <-> x = y.
  Proof.
    split; intro H; subst; try reflexivity.
    induction x.
    { revert dependent y.
      let G := match goal with |- forall y, @?G y => G end in
      intro y;
        refine (match y in word n return match n with
                                         | 0 => G
                                         | _ => fun _ => True
                                         end y
                with
                | WO => fun _ => eq_refl
                | _ => I
                end). }
    { move y at top; revert dependent n.
      let G := match goal with |- forall n y, @?G n y => G end in
      intros n y;
        refine (match y in word n return match n with
                                         | 0 => fun _ => True
                                         | S n' => G n'
                                         end y
                with
                | WO => I
                | _ => _
                end).
      intros x H IH.
      pose proof (H 0) as H0; simpl in H0; subst; f_equal.
      apply IH; intro k; specialize (H (S k)); apply H. }
  Qed.

  Lemma wbit_inj_iff_lt {n} (x y : word n)
    : (forall k, k < n -> wbit x k = wbit y k) <-> x = y.
  Proof.
    rewrite <- wbit_inj_iff.
    induction n.
    { split; intros H k; specialize (H k); try intro H'; try omega.
      refine match x, y with
             | WO, WO => eq_refl
             | _, _ => I
             end. }
    { do 2 let n := match goal with n : nat |- _ => n end in
           revert dependent n;
             let G := match goal with |- forall n x, @?G n x => G end in
             intros n x;
               refine match x in word n return match n with
                                               | S n' => G n'
                                               | _ => fun _ => True
                                               end x
                      with
                      | WO => I
                      | _ => _
                      end; clear n x;
                 intro y; move y at top.
      intro IH.
      split; intros H k; pose proof (H k) as Hk; destruct k;
        simpl in Hk |- *;
        try solve [ intros; try (first [ apply H | apply Hk ]; omega) ].
      clear Hk; revert k.
      apply IH; intros k H'.
      specialize (H (S k)); apply H; omega. }
  Qed.

  Lemma wordToN_testbit: forall {n} (x: word n) k,
    N.testbit (wordToN x) k = wbit x (N.to_nat k).
  Proof.
    assert (forall x: N, match x with
            | 0%N => 0%N
            | N.pos q => N.pos (q~0)%positive
            end = N.double x) as kill_match by (
      induction x; simpl; intuition).

    induction n; intros.

    - shatter x; simpl; intuition.

    - revert IHn; rewrite <- (N2Nat.id k).
      generalize (N.to_nat k) as k'; intros; clear k.
      rewrite Nat2N.id in *.

      induction k'.

      + clear IHn; induction x; simpl; intuition.
        destruct (wordToN x), b; simpl; intuition.

      + clear IHk'.
        shatter x; simpl.

        rewrite N.succ_double_spec; simpl.

        rewrite kill_match.
        replace (N.pos (Pos.of_succ_nat k'))
           with (N.succ (N.of_nat k'))
             by (rewrite <- Nat2N.inj_succ;
                 simpl; intuition).

        rewrite N.double_spec.
        replace (N.succ (2 * wordToN (wtl x)))
           with (2 * wordToN (wtl x) + 1)%N
             by nomega.

        destruct (whd x);
          try rewrite N.testbit_odd_succ;
          try rewrite N.testbit_even_succ;
          try abstract (
            unfold N.le; simpl;
            induction (N.of_nat k'); intuition;
            try inversion H);
          rewrite IHn;
          rewrite Nat2N.id;
          reflexivity.
  Qed.

  Lemma wbit_NToWord {sz} k v
    : wbit (NToWord sz v) k = if Nat.ltb k sz
                              then N.testbit v (N.of_nat k)
                              else false.
  Proof.
    revert k v; induction sz, k; intros; try reflexivity.
    { destruct v as [|p]; simpl; try reflexivity.
      destruct p; simpl; reflexivity. }
    { pose proof (fun v k => IHsz k (Npos v)) as IHszp.
      pose proof (fun k => IHsz k 0%N) as IHsz0.
      destruct v as [|p]; simpl in *.
      { rewrite IHsz0; break_match; reflexivity. }
      { destruct p; simpl in *; try (rewrite IHsz0; break_match; reflexivity);
          rewrite IHszp, N.pos_pred_spec;
          change (N.pos (Pos.of_succ_nat k)) with (N.of_nat (S k));
          rewrite <- Nat2N.inj_pred; simpl;
            reflexivity. } }
  Qed.

  Lemma NToWord_wordToN_NToWord : forall sz1 sz2 w,
      sz2 <= sz1 -> NToWord sz2 (wordToN (NToWord sz1 w)) = NToWord sz2 w.
  Proof.
    intros.
    apply wbit_inj_iff_lt; intros k Hlt.
    rewrite !wbit_NToWord, wordToN_testbit, wbit_NToWord, Nat2N.id.
    break_match; try reflexivity;
      repeat match goal with
             | [ H : (_ <? _) = true |- _ ] => apply Nat.ltb_lt in H
             | [ H : (_ <? _) = false |- _ ] => apply Nat.ltb_ge in H
             | _ => omega
             end.
  Qed.

  Lemma wordToN_split1: forall {n m} x,
    wordToN (@split1 n m x) = N.land (wordToN x) (wordToN (wones n)).
  Proof.
    intros.

    pose proof (Word.combine_split _ _ x) as C; revert C.
    generalize (split1 n m x) as a, (split2 n m x) as b.
    intros a b C; rewrite <- C; clear C x.

    apply N.bits_inj_iff; unfold N.eqf; intro x.
    rewrite N.land_spec.
    repeat rewrite wordToN_testbit.
    revert x a b.

    induction n, m; intros;
      shatter a; shatter b;
      induction (N.to_nat x) as [|n0];
      try rewrite <- (Nat2N.id n0);
      try rewrite andb_false_r;
      try rewrite andb_true_r;
      simpl; intuition.
  Qed.

  Lemma wordToN_split2: forall {n m} x,
    wordToN (@split2 n m x) = N.shiftr (wordToN x) (N.of_nat n).
  Proof.
    intros.

    pose proof (Word.combine_split _ _ x) as C; revert C.
    generalize (split1 n m x) as a, (split2 n m x) as b.
    intros a b C.
    rewrite <- C; clear C x.

    apply N.bits_inj_iff; unfold N.eqf; intro x;
      rewrite N.shiftr_spec;
      repeat rewrite wordToN_testbit;
      try apply N_ge_0.

    revert x a b.
    induction n, m; intros;
      shatter a;
      try apply N_ge_0.

    - simpl; intuition.

    - replace (x + N.of_nat 0)%N with x by nomega.
      simpl; intuition.

    - rewrite (IHn x (wtl a) b).
      rewrite <- (N2Nat.id x).
      repeat rewrite <- Nat2N.inj_add.
      repeat rewrite Nat2N.id; simpl.
      replace (N.to_nat x + S n) with (S (N.to_nat x + n)) by omega.
      reflexivity.

    - rewrite (IHn x (wtl a) b).
      rewrite <- (N2Nat.id x).
      repeat rewrite <- Nat2N.inj_add.
      repeat rewrite Nat2N.id; simpl.
      replace (N.to_nat x + S n) with (S (N.to_nat x + n)) by omega.
      reflexivity.
  Qed.

  Lemma wordToN_wones: forall x, wordToN (wones x) = N.ones (N.of_nat x).
  Proof.
    induction x.

    - simpl; intuition.

    - rewrite Nat2N.inj_succ.
      replace (wordToN (wones (S x))) with (2 * wordToN (wones x) + N.b2n true)%N
        by (simpl; rewrite ?N.succ_double_spec; simpl; nomega).
      replace (N.ones (N.succ _))
         with (2 * N.ones (N.of_nat x) + N.b2n true)%N.

      + rewrite IHx; nomega.

      + replace (N.succ (N.of_nat x)) with (1 + (N.of_nat x))%N by (
          rewrite N.add_comm; nomega).
        rewrite N.ones_add.
        replace (N.ones 1) with 1%N by (
          unfold N.ones; simpl; intuition).
        simpl.
        reflexivity.
  Qed.

  Tactic Notation "replaceAt1" constr(x) "with" constr(y) "by" tactic(tac) :=
    let tmp := fresh in
    set (tmp := x) at 1;
    replace tmp with y by (unfold tmp; tac);
    clear tmp.

  Lemma wordToN_combine: forall {n m} a b,
    wordToN (@Word.combine n a m b)
      = N.lxor (N.shiftl (wordToN b) (N.of_nat n)) (wordToN a).
  Proof.
    intros; symmetry.

    replaceAt1 a with (Word.split1 _ _ (Word.combine a b))
      by (apply Word.split1_combine).

    replaceAt1 b with (Word.split2 _ _ (Word.combine a b))
      by (apply Word.split2_combine).

    generalize (Word.combine a b); intro x; clear a b.

    rewrite wordToN_split1, wordToN_split2, wordToN_wones.
    generalize (wordToN x); clear x; intro x.
    apply N.bits_inj_iff; unfold N.eqf; intro k.
    rewrite N.lxor_spec.

    destruct (Nge_dec k (N.of_nat n)).

    - rewrite N.shiftl_spec_high; try apply N_ge_0;
        [|apply N.ge_le; assumption].
      rewrite N.shiftr_spec; try apply N_ge_0.
      replace (k - N.of_nat n + N.of_nat n)%N with k by nomega.
      rewrite N.land_spec, N.ones_spec_high; [|apply N.ge_le; assumption].
      induction (N.testbit x k); cbv; reflexivity.

    - rewrite N.shiftl_spec_low; try assumption; try apply N_ge_0.
      rewrite N.land_spec, N.ones_spec_low; [|nomega].
      induction (N.testbit x k); cbv; reflexivity.
  Qed.

  Lemma NToWord_equal: forall n (x y: word n),
      wordToN x = wordToN y -> x = y.
  Proof.
    intros.
    rewrite <- (NToWord_wordToN _ x).
    rewrite <- (NToWord_wordToN _ y).
    rewrite H; reflexivity.
  Qed.

  Lemma Npow2_ignore: forall {n} (x: word n),
    x = NToWord _ (wordToN x + Npow2 n).
  Proof.
    intros.
    rewrite <- (NToWord_wordToN n x) at 1.
    repeat rewrite NToWord_nat.
    rewrite N2Nat.inj_add.
    rewrite Npow2_nat.
    replace (N.to_nat (wordToN x))
       with ((N.to_nat (wordToN x) + pow2 n) - 1 * pow2 n)
         by omega.
    rewrite drop_sub; f_equal; nomega.
  Qed.
End WordToN.

Section WordBounds.
  Lemma word_size_bound : forall {n} (w: word n), (wordToN w < Npow2 n)%N.
  Proof.
    intros; pose proof (wordToNat_bound w) as B;
      rewrite of_nat_lt in B;
      rewrite <- Npow2_nat in B;
      rewrite N2Nat.id in B;
      rewrite <- wordToN_nat in B;
      assumption.
  Qed.

  Lemma wordize_plus: forall {n} (x y: word n),
       (wordToN x + wordToN y < Npow2 n)%N
    -> (wordToN x + wordToN y)%N = wordToN (x ^+ y).
  Proof.
    intros n x y H.
    pose proof (word_size_bound x) as Hbx.
    pose proof (word_size_bound y) as Hby.

    unfold wplus, wordBin.
    rewrite wordToN_NToWord_idempotent; intuition.
  Qed.

  Lemma wordize_minus: forall {n} (x y: word n),
       (wordToN x >= wordToN y)%N
    -> (wordToN x - wordToN y)%N = wordToN (x ^- y).
  Proof.
    intros n x y H.

    destruct (Nge_dec 0%N (wordToN y)). {
      unfold wminus, wneg.
      replace (wordToN y) with 0%N in * by nomega.
      replace (Npow2 n - 0)%N with (wordToN (wzero n) + Npow2 n)%N
        by (rewrite wordToN_zero; nomega).
      rewrite <- Npow2_ignore.
      rewrite wplus_comm.
      rewrite wplus_unit.
      nomega.
    }

    assert (wordToN x - wordToN y < Npow2 n)%N. {
      transitivity (wordToN x);
        try apply word_size_bound;
        apply N.sub_lt;
        [apply N.ge_le|]; assumption.
    }

    assert (wordToN x - wordToN y + wordToN y < Npow2 n)%N. {
      replace (wordToN x - wordToN y + wordToN y)%N
        with (wordToN x) by nomega;
        apply word_size_bound.
    }

    assert (x = NToWord n (wordToN x - wordToN y) ^+ y) as Hv. {
      apply NToWord_equal.
      rewrite <- wordize_plus; rewrite wordToN_NToWord_idempotent; try assumption.
      nomega.
    }

    symmetry.
    rewrite Hv at 1.
    unfold wminus.
    repeat rewrite <- wplus_assoc.
    rewrite wminus_inv.
    rewrite wplus_comm.
    rewrite wplus_unit.
    rewrite wordToN_NToWord_idempotent; try assumption.
    reflexivity.
  Qed.

  Lemma wordize_mult: forall {n} (x y: word n),
      (wordToN x * wordToN y < Npow2 n)%N
    -> (wordToN x * wordToN y)%N = wordToN (x ^* y).
  Proof.
    intros n x y H.
    pose proof (word_size_bound x) as Hbx.
    pose proof (word_size_bound y) as Hby.

    unfold wmult, wordBin.
    rewrite wordToN_NToWord_idempotent; intuition.
  Qed.

  Lemma wordize_and: forall {n} (x y: word n),
    wordToN (wand x y) = N.land (wordToN x) (wordToN y).
  Proof.
    intros.
    apply N.bits_inj_iff; unfold N.eqf; intro k.
    rewrite N.land_spec.
    repeat rewrite wordToN_testbit.
    revert x y.
    generalize (N.to_nat k) as k'.
    induction n; intros; shatter x; shatter y; simpl; [reflexivity|].
    induction k'; [reflexivity|].
    fold wand.
    rewrite IHn.
    reflexivity.
  Qed.

  Lemma wordize_or: forall {n} (x y: word n),
    wordToN (wor x y) = N.lor (wordToN x) (wordToN y).
  Proof.
    intros.
    apply N.bits_inj_iff; unfold N.eqf; intro k.
    rewrite N.lor_spec.
    repeat rewrite wordToN_testbit.
    revert x y.
    generalize (N.to_nat k) as k'; clear k.
    induction n; intros; shatter x; shatter y; simpl; [reflexivity|].
    induction k'; [reflexivity|].
    rewrite IHn.
    reflexivity.
  Qed.
End WordBounds.

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

Fixpoint correct_wordsize_eq (x y : nat) : wordsize_eq x y -> x = y
  := match x, y with
     | O, O => fun _ => eq_refl
     | S x', S y' => fun pf => f_equal S (correct_wordsize_eq x' y' (f_equal pred pf))
     | _, _ => fun x => x
     end.

Lemma correct_wordsize_eq_refl n pf : correct_wordsize_eq n n pf = eq_refl.
Proof.
  induction n; [ reflexivity | simpl ].
  rewrite IHn; reflexivity.
Qed.

Definition cast_word {n m} {pf:wordsize_eq n m} : word n -> word m :=
  match correct_wordsize_eq n m pf in _ = y return word n -> word y with
  | eq_refl => fun w => w
  end.

Lemma cast_word_refl {n} pf (w:word n) : @cast_word n n pf w = w.
Proof. unfold cast_word; rewrite correct_wordsize_eq_refl; reflexivity. Qed.

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

Section Bounds.
  Local Notation bounds_2statement wop Zop := (forall {sz} (x y : word sz),
     (0 <= Zop (Z.of_N (wordToN x)) (Z.of_N (wordToN y))
  -> (Z.log2 (Zop (Z.of_N (wordToN x)) (Z.of_N (wordToN y))) < Z.of_nat sz)
  -> (Z.of_N (wordToN (wop x y)) = (Zop (Z.of_N (wordToN x)) (Z.of_N (wordToN y)))))%Z).

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
End Bounds.

Hint Rewrite @wordToN_wplus using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wplus using word_util_arith : pull_wordToN.

Hint Rewrite @wordToN_wminus using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wminus using word_util_arith : pull_wordToN.

Hint Rewrite @wordToN_wmult using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wmult using word_util_arith : pull_wordToN.

Hint Rewrite @wordToN_wand using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wand using word_util_arith : pull_wordToN.

Hint Rewrite @wordToN_wor using word_util_arith : push_wordToN.
Hint Rewrite <- @wordToN_wor using word_util_arith : pull_wordToN.

Section Updates.
  Local Notation bound n lower value upper := (
       (0 <= lower)%Z
    /\ (lower <= Z.of_N (@wordToN n value))%Z
    /\ (Z.of_N (@wordToN n value) <= upper)%Z
    /\ (Z.log2 upper < Z.of_nat n)%Z).

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
    unfold valid_update; intros until upper1; intros B0 B1 H0 H1.
    do 2 destruct B0 as [? B0], B1 as [? B1]; destruct B0, B1.
    repeat split; [add_mono| | |assumption]; (
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
    do 2 destruct B0 as [? B0], B1 as [? B1]; destruct B0, B1.
    repeat split; [sub_mono| | |assumption]; (
    rewrite wordToN_wminus; [sub_mono|omega|];
    eapply Z.le_lt_trans; [apply Z.log2_le_mono|eassumption]; sub_mono).
  Qed.

  Local Ltac mul_mono :=
    etransitivity; [|apply Z.mul_le_mono_nonneg_r];
    repeat (instantiate; first
    [ eassumption
    | reflexivity
    | apply Z.mul_le_mono_nonneg_l
    | rewrite Z.mul_0_l
    | omega]).

  Lemma mul_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => l0 * l1)%Z
        (@wmult n)
        (fun l0 u0 l1 u1 => u0 * u1)%Z.
  Proof.
    unfold valid_update; intros until upper1; intros B0 B1.
    do 2 destruct B0 as [? B0], B1 as [? B1]; destruct B0, B1.
    repeat split; [mul_mono| | |assumption]; (
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
    do 2 destruct B0 as [? B0], B1 as [? B1]; destruct B0, B1; intros.
    repeat split; [reflexivity|apply N2Z.is_nonneg| |assumption].
    rewrite wordToN_wand; [|solve_land_ge0|].

    - destruct_min;
        (etransitivity; [|eassumption]); [|rewrite Z.land_comm];
        (apply Z_land_le; land_mono).

    - eapply Z.le_lt_trans; [apply Z.log2_land; land_mono|destruct_min]; (
        eapply Z.le_lt_trans; [apply Z.log2_le_mono; eassumption|];
        assumption).
  Qed.

  Local Ltac lor_mono :=
    first [assumption | etransitivity; [|eassumption]; assumption].

  Local Ltac lor_trans :=
    destruct_max; (
        eapply Z.le_lt_trans; [apply Z.log2_le_mono; eassumption|];
        assumption).

  Lemma lor_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => Z.max l0 l1)%Z
        (@wor n)
        (fun l0 u0 l1 u1 => 2^(Z.max (Z.log2_up (u0+1)) (Z.log2_up (u1+1))) - 1)%Z.
  Proof.
    unfold valid_update; intros until upper1; intros B0 B1.
    do 2 destruct B0 as [? B0], B1 as [? B1]; destruct B0, B1; intros.
    repeat split; [destruct_max; assumption| | |assumption].

    - rewrite wordToN_wor;
        [ destruct_max; [|rewrite Z.lor_comm];
            (etransitivity; [|apply Z_lor_lower]; lor_mono)
        | apply Z.lor_nonneg; split; lor_mono|].

        rewrite Z.log2_lor; [lor_trans|lor_mono|lor_mono].

    - rewrite wordToN_wor; [
        | apply Z.lor_nonneg; split; lor_mono
        | rewrite Z.log2_lor; [lor_trans|lor_mono|lor_mono]].

        destruct (Z_ge_dec upper0 upper1) as [g|g].

        + apply Z.ge_le in g; pose proof g as g'.
        apply -> (Z.add_le_mono_r upper1 upper0 1) in g'.
        apply Z.log2_up_le_mono, Z.max_l in g'.
        rewrite g'; clear g'.

        destruct (Z.le_ge_cases (Z.of_N (wordToN value0)) (Z.of_N (wordToN value1)));
            [|rewrite Z.lor_comm];
            apply Z_lor_le; lor_mono.

        + assert (upper1 >= upper0)%Z as g'' by omega; clear g.
        pose proof g'' as g; pose proof g'' as g'; clear g''.
        apply Z.ge_le in g; apply Z.ge_le in g'.
        apply -> (Z.add_le_mono_r upper0 upper1 1) in g'.
        apply Z.log2_up_le_mono, Z.max_r in g'.
        rewrite g'; clear g'.

        destruct (Z.le_ge_cases (Z.of_N (wordToN value0)) (Z.of_N (wordToN value1)));
            [|rewrite Z.lor_comm];
            apply Z_lor_le; lor_mono.
  Qed.

  Local Ltac shift_mono := repeat progress first
    [ eassumption
    | etransitivity; [|eassumption]].

  Lemma shr_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => Z.shiftr l0 u1)%Z
        (@wordBin N.shiftr n)
        (fun l0 u0 l1 u1 => Z.shiftr u0 l1)%Z.
  Proof.
    unfold valid_update, wordBin; intros until upper1; intros B0 B1.
    do 2 destruct B0 as [? B0], B1 as [? B1]; destruct B0, B1; intros.

    repeat split; [assumption| | |assumption];
        (rewrite wordToN_NToWord_idempotent; [|apply Npow2_Zlog2]; rewrite Z_inj_shiftr);
        [ | eapply Z.le_lt_trans; [apply Z.log2_le_mono|eassumption]
        | | eapply Z.le_lt_trans; [apply Z.log2_le_mono|eassumption]];
        apply Z_shiftr_le_mono; shift_mono.
  Qed.

  Lemma shl_valid_update: forall n,
    valid_update n
        (fun l0 u0 l1 u1 => Z.shiftl l0 l1)%Z
        (@wordBin N.shiftl n)
        (fun l0 u0 l1 u1 => Z.shiftl u0 u1)%Z.
  Proof.
    unfold valid_update, wordBin; intros until upper1; intros B0 B1.
    do 2 destruct B0 as [? B0], B1 as [? B1]; destruct B0, B1; intros.

    repeat split; [assumption| | |assumption];
        (rewrite wordToN_NToWord_idempotent; [|apply Npow2_Zlog2]; rewrite Z_inj_shiftl);
        [ | eapply Z.le_lt_trans; [apply Z.log2_le_mono|eassumption]
        | | eapply Z.le_lt_trans; [apply Z.log2_le_mono|eassumption]];
        apply Z_shiftl_le_mono; shift_mono.
  Qed.
End Updates.

Definition winit {sz} (x: word (sz + 1)): word sz :=
  split1 sz 1 x.

Definition wlast {sz} (x: word (sz + 1)): bool :=
  whd (split2 sz 1 x).

Arguments winit {_} _.
Arguments wlast {_} _.

Lemma combine_winit_wlast : forall {sz} a b (c:word (sz+1)),
    @combine sz a 1 b = c <-> a = winit c /\ b = (WS (wlast c) WO).
Proof.
  intros; split; unfold winit, wlast; intro H.

  - rewrite <- H.
    rewrite split1_combine, split2_combine.
    split; [reflexivity|].
    shatter b; simpl; f_equal.
    generalize (wtl b) as b'; intro;
      shatter b'; reflexivity.

  - destruct H as [H0 H1]; rewrite H0.
    replace b with (split2 sz 1 c); [apply combine_split|].
    rewrite H1.
    generalize (split2 sz 1 c) as b'; intro.
    shatter b'.
    generalize (wtl b') as b''; intro;
      shatter b''; reflexivity.
Qed.

Lemma winit_combine : forall sz a b, @winit sz (combine a b) = a.
Proof.
  intros; unfold winit; rewrite split1_combine; reflexivity.
Qed.

Lemma wlast_combine : forall sz a b, @wlast sz (combine a (WS b WO)) = b.
Proof.
  intros; unfold wlast; rewrite split2_combine; cbv; reflexivity.
Qed.

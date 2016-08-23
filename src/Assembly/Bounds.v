Require Export Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Nnat NPow NPeano Ndec Ndigits.
Require Import Compare_dec Omega.
Require Import FunctionalExtensionality ProofIrrelevance.
Require Import Crypto.Assembly.QhasmUtil Crypto.Assembly.QhasmEvalCommon Crypto.Assembly.WordizeUtil.

Import EvalUtil.

Hint Rewrite wordToN_nat Nat2N.inj_add N2Nat.inj_add
             Nat2N.inj_mul N2Nat.inj_mul Npow2_nat : N.

Open Scope nword_scope.

Section Bounds.
  Lemma wordize_plus': forall {n} (x y: word n) (b: N),
      (&x < b)%N
    -> (&y < (Npow2 n - b))%N
    -> (b <= Npow2 n)%N
    -> (&x + &y)%N = & (x ^+ y).
  Proof.
    intros.
    unfold wplus, wordBin.
    rewrite wordToN_NToWord; intuition.
    apply (N.lt_le_trans _ (b + &y)%N _).

    - apply N.add_lt_le_mono; try assumption.
      apply N.eq_le_incl; reflexivity.

    - replace (Npow2 n) with (b + Npow2 n - b)%N by nomega;
        replace (b + Npow2 n - b)%N with (b + (Npow2 n - b))%N by (
        replace (b + (Npow2 n - b))%N with ((Npow2 n - b) + b)%N by nomega;
        rewrite (N.sub_add b (Npow2 n)) by assumption;
        nomega).

        apply N.add_le_mono_l; try nomega.
        apply N.lt_le_incl; assumption.
  Qed.

  Lemma wordize_mult': forall {n} (x y: word n) (b: N),
      (1 < n)%nat -> (0 < b)%N
    -> (&x < b)%N
    -> (&y < (Npow2 n) / b)%N
    -> (&x * &y)%N = & (x ^* y).
  Proof.
    intros; unfold wmult, wordBin.
    rewrite wordToN_NToWord; intuition.
    apply (N.lt_le_trans _ (b * ((Npow2 n) / b))%N _).

    - apply N.mul_lt_mono; assumption.

    - apply N.mul_div_le; nomega.
  Qed.

  Lemma constant_bound_N : forall {n} (k: word n),
    (& k < & k + 1)%N.
  Proof. intros; nomega. Qed.

  Lemma constant_bound_nat : forall (n k: nat),
      (N.of_nat k < Npow2 n)%N
    -> (& (@natToWord n k) < (N.of_nat k) + 1)%N.
  Proof.
    intros.
    rewrite wordToN_nat.
    rewrite wordToNat_natToWord_idempotent;
      try assumption; nomega.
  Qed.

  Lemma let_bound : forall {n} (x: word n) (f: word n -> word n) xb fb,
      (& x < xb)%N
    -> (forall x', & x' < xb -> & (f x') < fb)%N
    -> ((let k := x in &(f k)) < fb)%N.
  Proof. intros; eauto. Qed.

  Definition Nlt_dec (x y: N): {(x < y)%N} + {(x >= y)%N}.
    refine (
      let c := N.compare x y in
      match c as c' return c = c' -> _ with
      | Lt => fun _ => left _
      | _ => fun _ => right _
      end eq_refl);
    abstract (
      unfold c, N.ge, N.lt in *; intuition; subst;
      match goal with
      | [H0: ?x = _, H1: ?x = _ |- _] =>
        rewrite H0 in H1; inversion H1
      end).
  Defined.

  Lemma wplus_bound : forall {n} (w1 w2 : word n) b1 b2,
      (&w1 < b1)%N
    -> (&w2 < b2)%N
    -> (&(w1 ^+ w2) < b1 + b2)%N.
  Proof.
    intros.

    destruct (Nlt_dec (b1 + b2)%N (Npow2 n)) as [g|g].

    - rewrite <- wordize_plus' with (b := b1);
        try apply N.add_lt_mono;
        try assumption.

      + apply (N.lt_le_trans _ b2 _); try assumption.
        apply N.lt_le_incl.
        apply N.lt_add_lt_sub_l.
        assumption.

      + apply N.lt_le_incl; nomega.

    - apply (N.lt_le_trans _ (Npow2 n) _).

      + apply word_size_bound.

      + unfold N.le, N.ge in *.
        intro Hg.
        contradict g.
        rewrite N.compare_antisym.
        rewrite Hg.
        simpl; intuition.
  Qed.

  Theorem wmult_bound : forall {n} (w1 w2 : word n) b1 b2,
      (1 < n)%nat
    -> (&w1 < b1)%N
    -> (&w2 < b2)%N
    -> (&(w1 ^* w2) < b1 * b2)%N.
  Proof.
    intros.
    destruct (Nlt_dec (b1 * b2)%N (Npow2 n)) as [g|g].

    - rewrite <- wordize_mult' with (b := b1);
        try apply N.mul_lt_mono;
        try assumption;
        try nomega.

      apply (N.lt_le_trans _ b2 _); try assumption.
      apply N.div_le_lower_bound.

      + induction (& w1); nomega.

      + apply N.lt_le_incl.
        assumption.

    - apply (N.lt_le_trans _ (Npow2 n) _).

      + apply word_size_bound.

      + unfold N.le, N.ge in *.
        intro Hg.
        contradict g.
        rewrite N.compare_antisym.
        rewrite Hg.
        simpl; intuition.
  Qed.

  Lemma shiftr_bound : forall {n} (w : word n) b bits,
      (&w < b)%N
    -> (&(shiftr w bits) < N.succ (N.shiftr_nat b bits))%N.
  Proof.
    intros.
    apply (N.le_lt_trans _ (N.shiftr_nat b bits) _).

    - unfold shiftr, extend, high.
      destruct (le_dec bits n); try omega.

      + rewrite wordToN_convS.
        rewrite wordToN_zext.
        rewrite wordToN_split2.
        rewrite wordToN_convS.
        rewrite <- Nshiftr_equiv_nat.
        repeat rewrite N.shiftr_div_pow2.
        apply N.div_le_mono.

        * induction bits; try nomega.
          rewrite Nat2N.inj_succ.
          rewrite N.pow_succ_r'.
          assert (bits <= n)%nat as Hc by omega.
          apply IHbits in Hc.
          intro Hc'; contradict Hc.
          apply (N.mul_cancel_l _ _ 2);
            try rewrite Hc';
            try assumption;
            nomega.

        * apply N.lt_le_incl.
          assumption.

      + rewrite wordToN_nat.
        unfold wzero.
        rewrite wordToNat_natToWord_idempotent; simpl;
          try apply N_ge_0;
          try apply Npow2_gt0.

    - nomega.

  Qed.

  Lemma mask_bound : forall {n} (w : word n) m,
    (&(mask m w) < Npow2 m)%N.
  Proof.
    intros.
    unfold mask in *; destruct (le_dec m n); simpl;
      try apply extend_bound.

    pose proof (word_size_bound w) as H.
    apply (N.le_lt_trans _ (Npow2 n) _).

    - unfold N.le, N.lt in *; rewrite H; intro H0; inversion H0.

    - clear H.
      replace m with ((m - n) + n) by nomega.
      replace (Npow2 n) with (1 * (Npow2 n))%N
        by (rewrite N.mul_comm; nomega).
      rewrite Npow2_split.
      apply N.mul_lt_mono_pos_r; try apply Npow2_gt0.
      assert (0 < m - n)%nat by omega.
      induction (m - n); try inversion H; try abstract (
        simpl; replace 2 with (S 1) by omega;
        apply N.lt_1_2); subst.

      assert (0 < n1)%nat as Z by omega; apply IHn1 in Z.
      apply (N.le_lt_trans _ (Npow2 n1) _).

      + apply N.lt_le_incl; assumption.

      + rewrite Npow2_succ.
        replace' (Npow2 n1) with (1 * Npow2 n1)%N at 1 by (apply N.mul_1_l).
        apply N.mul_lt_mono_pos_r; try abstract (vm_compute; reflexivity).
        apply (N.lt_le_trans _ 1 _); try abstract (vm_compute; reflexivity).
        apply N.lt_le_incl; assumption.
  Qed.

  Lemma mask_update_bound : forall {n} (w : word n) b m,
      (1 < n)%nat
    -> (&w < b)%N
    -> (&(mask m w) < (N.min b (Npow2 m)))%N.
  Proof.
    intros.
    assert (& w mod Npow2 m < b)%N. {
      destruct (Nge_dec (&w) (Npow2 m)).

      - apply (N.lt_le_trans _ (Npow2 m) _).

        + pose proof (N.mod_bound_pos (&w) (Npow2 m)
                     (N_ge_0 _) (Npow2_gt0 _)) as H1.
          destruct H1.
          assumption.

        + transitivity (&w); try abstract (apply ge_to_le; assumption).
          apply N.lt_le_incl; assumption.

      - rewrite N.mod_small; assumption.
    }

    unfold mask, N.min, extend, low;
      destruct (le_dec m n),
               (N.compare b (Npow2 m)); simpl;
      repeat first [
        rewrite wordToN_convS  |
        rewrite wordToN_zext   |
        rewrite wordToN_wones  |
        rewrite wordToN_split1 |
        rewrite N.land_ones    |
        rewrite <- Npow2_N ];
      try assumption.

    - pose proof (N.mod_bound_pos (&w) (Npow2 m) (N_ge_0 _) (Npow2_gt0 _)) as Z.
      destruct Z.
      assumption.

    - apply (N.lt_le_trans _ (Npow2 n) _);
        try apply word_size_bound.
      apply Npow2_ordered.
      omega.
  Qed.

  Lemma plus_overflow_bound: forall x y a b,
      (x < a)%N
    -> (y < b - a)%N
    -> (x + y < b)%N.
  Proof. intros; nomega. Qed.

End Bounds.

(** Constant Tactics **)

Ltac assert_nat_constant t :=
  timeout 1 (match (eval vm_compute in t) with
  | O => idtac
  | S ?n => assert_nat_constant n
  | _ => fail
  end).

Ltac assert_pos_constant t :=
  timeout 1 (match (eval vm_compute in t) with
  | xH => idtac
  | xI ?p => assert_pos_constant p
  | xO ?p => assert_pos_constant p
  | _ => fail
  end).

Ltac assert_bin_constant t :=
  timeout 1 (match (eval vm_compute in t) with
  | N.pos ?p => assert_pos_constant p
  | N0 => idtac
  | _ => fail
  end).

Ltac assert_word_constant t :=
  timeout 1 (match (eval vm_compute in t) with
  | WO => idtac
  | WS _ ?w => assert_word_constant w
  | _ => fail
  end).

(** Bounding Tactics **)

Ltac multi_apply0 A L := pose proof (L A).

Ltac multi_apply1 A L :=
  match goal with
  | [ H: (wordToN A < ?b)%N |- _] => pose proof (L A b H)
  end.

Ltac multi_apply2 A B L :=
  match goal with
  | [ H1: (wordToN A < ?b1)%N, H2: (wordToN B < ?b2)%N |- _] => pose proof (L A B b1 b2 H1 H2)
  end.

Ltac multi_recurse n T :=
  match goal with
  | [ H: (wordToN T < _)%N |- _] => idtac
  | _ =>
    is_var T;
    let T' := (eval cbv delta [T] in T) in multi_recurse n T';
    match goal with
    | [ H : T' < ?x |- _ ] =>
      pose proof (H : T < x)
    end

  | _ =>
    match T with
    | ?W1 ^+ ?W2 =>
      multi_recurse n W1; multi_recurse n W2;
      multi_apply2 W1 W2 (@wplus_bound n)

    | ?W1 ^* ?W2 =>
      multi_recurse n W1; multi_recurse n W2;
      multi_apply2 W1 W2 (@wmult_bound n)

    | mask ?m ?w =>
      multi_recurse n w;
      multi_apply1 w (fun b => @mask_update_bound n w b)

    | mask ?m ?w =>
      multi_recurse n w;
      pose proof (@mask_bound n w m)

    | shiftr ?w ?bits =>
      multi_recurse n w;
      match goal with
      | [ H: (w < ?b)%N |- _] =>
        pose proof (@shiftr_bound n w b bits H)
      end

    | NToWord _ ?k => pose proof (@constant_bound_N n k)
    | natToWord _ ?k => pose proof (@constant_bound_nat n k)
    | _ => pose proof (@word_size_bound n T)
    end
  end.

Lemma unwrap_let: forall {n} (y: word n) (f: word n -> word n) (b: N),
    (&(let x := y in f x) < b)%N <-> let x := y in (&(f x) < b)%N.
Proof. intuition. Qed.

Ltac bound_compute :=
  repeat (try assumption; match goal with
  | [|- let A := ?B in _] =>
    match (type of B) with
    | word ?n => multi_recurse n B; intro
    end

  | [|- ((let A := _ in _) < _)%N] =>
    apply unwrap_let

  | [ H: (wordToN ?W < ?b0)%N |- (wordToN ?W < ?b1)%N ] =>
    try eassumption; eapply (N.lt_le_trans _ b0 _); try eassumption

  | [|- (@wordToN ?n ?W < ?b)%N ] =>
    multi_recurse n W

  | [|- (?x + ?y < ?b)%N ] =>
    eapply plus_overflow_bound

  | [|- (?a <= ?b)%N ] =>
    is_evar b; apply N.eq_le_incl; reflexivity

  | [|- (?a <= ?b)%N ] =>
    is_evar a; apply N.eq_le_incl; reflexivity

  | [|- (?a <= ?b)%N ] =>
    assert_bin_constant a;
    assert_bin_constant b;
    vm_compute;
      try reflexivity;
      try abstract (let H := fresh in intro H; inversion H)

  | [|- (?x < ?b)%N ] =>
    assert_bin_constant x;
    assert_bin_constant b;
    vm_compute; reflexivity

  (* cleanup generated nat goals *)
  | [|- (?a <= ?b)%nat ] => omega
  | [|- (?a < ?b)%nat ] => omega
  end).

(* for x : word n *)
Ltac find_bound_on x :=
  match (type of x) with
  | word ?n =>
    match x with
    | let A := ?b in ?c => find_bound_on b; set (A := b)
    | _ => multi_recurse n x
    end
  | _ => idtac
  end.

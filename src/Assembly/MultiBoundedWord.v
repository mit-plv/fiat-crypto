
Require Import Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Compare_dec Arith.
Require Import ProofIrrelevance Ring.
Require Import BoundedWord.

Import BoundedWord.

(* Parameters of boundedness calculations *)
Notation "A <= B" := (wordLeN A B) (at level 70).
Notation "$" := (natToWord _).

(* Hypothesis-based word-bound tactic *)
Ltac multi_apply0 A L := pose proof (L A).

Ltac multi_apply1 A L :=
  match goal with
  | [ H: A <= ?b |- _] => pose proof (L A b H)
  end.

Ltac multi_apply2 A B L :=
  match goal with
  | [ H1: A <= ?b1, H2: B <= ?b2 |- _] => pose proof (L A B b1 b2 H1 H2)
  end.

Ltac multi_recurse n T :=
  match goal with
  | [ H: T <= _ |- _] => idtac
  | _ =>
    is_var T;
    let T' := (eval cbv delta [T] in T) in multi_recurse n T';
    match goal with
    | [ H : T' <= ?x |- _ ] =>
    pose proof (H : T <= x)
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

    | ?x ^& (@NToWord _ (N.ones ?m)) =>
      multi_recurse n (mask (N.to_nat m) x);
      match goal with
      | [ H: (mask (N.to_nat m) x) <= ?b |- _] =>
        pose proof (@mask_wand n x m b H)
      end

    | shiftr ?w ?bits =>
      multi_recurse n w;
      match goal with
      | [ H: w <= ?b |- _] =>
        pose proof (@shiftr_bound n w b bits H)
      end

    | NToWord _ ?k => pose proof (@constant_bound_N n k)
    | natToWord _ ?k => pose proof (@constant_bound_nat n k)
    | ($ ?k) => pose proof (@constant_bound_nat n k)
    | _ => pose proof (@word_size_bound n T)
    end
  end.

Lemma unwrap_let: forall {n} (y: word n) (f: word n -> word n) (b: N),
    (let x := y in f x) <= b <-> let x := y in (f x <= b).
Proof. intuition. Qed.

Ltac multi_bound n :=
  match goal with
  | [|- let A := ?B in _] =>
    multi_recurse n B; intro; multi_bound n
  | [|- (let A := _ in _) <= _] =>
    apply unwrap_let; multi_bound n
  | [|- ?W <= _ ] =>
    multi_recurse n W
  end.

(* Examples *)
Lemma example1 : forall {n} (w1 w2 w3 w4 : word n) b1 b2 b3 b4,
    w1 <= b1
    -> w2 <= b2
    -> w3 <= b3
    -> w4 <= b4
    -> { b | let w5 := w2 ^* w3 in w1 ^+ w5 ^* w4 <= b }.    
Proof.
  eexists.
  multi_bound n.
  eassumption.
Defined.

Lemma example2 : forall {n} (w1 w2 w3 w4 : word n) b1 b2 b3 b4,
    w1 <= b1
    -> w2 <= b2
    -> w3 <= b3
    -> w4 <= b4
    -> { b | (let w5 := (w2 ^* $7 ^* w3) in w1 ^+ w5 ^* w4 ^+ $8 ^+ w2) <= b }.
Proof.
  eexists.
  multi_bound n.
  eassumption.
Defined.

Lemma example3 : forall {n} (w1 w2 w3 w4 : word n),
    w1 <= Npow2 3
    -> w2 <= Npow2 4
    -> w3 <= Npow2 8
    -> w4 <= Npow2 16
    -> { b | w1 ^+ (w2 ^* $7 ^* w3) ^* w4 ^+ $8 ^+ w2 <= b }.
Proof.
  eexists.
  multi_bound n.
  eassumption.
Defined.

Section MulmodExamples.

  Notation "A <= B" := (wordLeN A B) (at level 70).
  Notation "$" := (natToWord 32).

  Lemma example_and : forall x : word 32, wand x (NToWord 32 (N.ones 10)) <= 1023.
    intros.
    replace (wand x (NToWord 32 (N.ones 10))) with (mask 10 x) by admit.
    multi_bound 32; eassumption.
  Qed.

  Lemma example_shiftr : forall x : word 32, shiftr x 30 <= 3.
    intros.
    replace 3%N with (N.shiftr (Npow2 32 - 1) (N.of_nat 30)) by (simpl; intuition).
    multi_bound 32; eassumption.
  Qed.

  Lemma example_shiftr2 : forall x : word 32, x <= 1023 -> shiftr x 5 <= 31.
    intros.
    replace 31%N with (N.shiftr 1023%N 5%N) by (simpl; intuition).
    multi_bound 32; eassumption.
  Qed.

  Variable f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 : word 32.
  Variable g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : word 32.
  Hypothesis Hf0 : f0 <= 2^26.
  Hypothesis Hf1 : f1 <= 2^25.
  Hypothesis Hf2 : f2 <= 2^26.
  Hypothesis Hf3 : f3 <= 2^25.
  Hypothesis Hf4 : f4 <= 2^26.
  Hypothesis Hf5 : f5 <= 2^25.
  Hypothesis Hf6 : f6 <= 2^26.
  Hypothesis Hf7 : f7 <= 2^25.
  Hypothesis Hf8 : f8 <= 2^26.
  Hypothesis Hf9 : f9 <= 2^25.
  Hypothesis Hg0 : g0 <= 2^26.
  Hypothesis Hg1 : g1 <= 2^25.
  Hypothesis Hg2 : g2 <= 2^26.
  Hypothesis Hg3 : g3 <= 2^25.
  Hypothesis Hg4 : g4 <= 2^26.
  Hypothesis Hg5 : g5 <= 2^25.
  Hypothesis Hg6 : g6 <= 2^26.
  Hypothesis Hg7 : g7 <= 2^25.
  Hypothesis Hg8 : g8 <= 2^26.
  Hypothesis Hg9 : g9 <= 2^25.

  Lemma example_mulmod_s_ppt : { b | f0 ^* g0  <= b}.
    eexists.
    multi_bound 32; eassumption.
  Defined.

  Lemma example_mulmod_s_pp :  { b | f0 ^* g0 ^+ $19 ^* (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+ f2 ^* g8 ^+  f1 ^* g9 ^* $2) <= b}.
    eexists.
    multi_bound 32; eassumption.
  Defined.

  Lemma example_mulmod_s_pp_shiftr :
    { b | shiftr (f0 ^* g0 ^+  $19 ^* (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+ f2 ^* g8 ^+  f1 ^* g9 ^* $2)) 26 <= b}.
    eexists.
    multi_bound 32; eassumption.
  Defined.

  Lemma example_mulmod_u_fg1 :  { b |
      (let y : word 32 := 
        (f0 ^* g0 ^+
            $19 ^*
            (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+ f2 ^* g8 ^+
            f1 ^* g9 ^* $2)) in
        let y0 : word 32 :=
        (shiftr y 26 ^+
            (f1 ^* g0 ^+ f0 ^* g1 ^+
            $19 ^* (f9 ^* g2 ^+ f8 ^* g3 ^+ f7 ^* g4 ^+ f6 ^* g5 ^+ f5 ^* g6 ^+ f4 ^* g7 ^+ f3 ^* g8 ^+ f2 ^* g9))) in
        let y1 : word 32 :=
        (shiftr y0 25 ^+
            (f2 ^* g0 ^+ f1 ^* g1 ^* $2 ^+ f0 ^* g2 ^+
            $19 ^* (f9 ^* g3 ^* $2 ^+ f8 ^* g4 ^+ f7 ^* g5 ^* $2 ^+ f6 ^* g6 ^+ f5 ^* g7 ^* $2 ^+ f4 ^* g8 ^+ f3 ^* g9 ^* $2))) in
        let y2 : word 32 :=
        (shiftr y1 26 ^+
            (f3 ^* g0 ^+ f2 ^* g1 ^+ f1 ^* g2 ^+ f0 ^* g3 ^+
            $19 ^* (f9 ^* g4 ^+ f8 ^* g5 ^+ f7 ^* g6 ^+ f6 ^* g7 ^+ f5 ^* g8 ^+ f4 ^* g9))) in
        let y3 : word 32 :=
        (shiftr y2 25 ^+
            (f4 ^* g0 ^+ f3 ^* g1 ^* $2 ^+ f2 ^* g2 ^+ f1 ^* g3 ^* $2 ^+ f0 ^* g4 ^+
            $19 ^* (f9 ^* g5 ^* $2 ^+ f8 ^* g6 ^+ f7 ^* g7 ^* $2 ^+ f6 ^* g8 ^+ f5 ^* g9 ^* $2))) in
        let y4 : word 32 :=
        (shiftr y3 26 ^+
            (f5 ^* g0 ^+ f4 ^* g1 ^+ f3 ^* g2 ^+ f2 ^* g3 ^+ f1 ^* g4 ^+ f0 ^* g5 ^+
            $19 ^* (f9 ^* g6 ^+ f8 ^* g7 ^+ f7 ^* g8 ^+ f6 ^* g9))) in
        let y5 : word 32 :=
        (shiftr y4 25 ^+
            (f6 ^* g0 ^+ f5 ^* g1 ^* $2 ^+ f4 ^* g2 ^+ f3 ^* g3 ^* $2 ^+ f2 ^* g4 ^+ f1 ^* g5 ^* $2 ^+ f0 ^* g6 ^+
            $19 ^* (f9 ^* g7 ^* $2 ^+ f8 ^* g8 ^+ f7 ^* g9 ^* $2))) in
        let y6 : word 32 :=
        (shiftr y5 26 ^+
            (f7 ^* g0 ^+ f6 ^* g1 ^+ f5 ^* g2 ^+ f4 ^* g3 ^+ f3 ^* g4 ^+ f2 ^* g5 ^+ f1 ^* g6 ^+ f0 ^* g7 ^+
            $19 ^* (f9 ^* g8 ^+ f8 ^* g9))) in
        let y7 : word 32 :=
        (shiftr y6 25 ^+
            (f8 ^* g0 ^+ f7 ^* g1 ^* $2 ^+ f6 ^* g2 ^+ f5 ^* g3 ^* $2 ^+ f4 ^* g4 ^+ f3 ^* g5 ^* $2 ^+ f2 ^* g6 ^+ f1 ^* g7 ^* $2 ^+
            f0 ^* g8 ^+ $19 ^* f9 ^* g9 ^* $2)) in
        let y8 : word 32 :=
        (shiftr y7 26 ^+
            (f9 ^* g0 ^+ f8 ^* g1 ^+ f7 ^* g2 ^+ f6 ^* g3 ^+ f5 ^* g4 ^+ f4 ^* g5 ^+ f3 ^* g6 ^+ f2 ^* g7 ^+ f1 ^* g8 ^+
            f0 ^* g9)) in
        let y9 : word 32 :=
        ($19 ^* shiftr y8 25 ^+
            wand
            (f0 ^* g0 ^+
            $19 ^*
            (f9 ^* g1 ^* $2 ^+ f8 ^* g2 ^+ f7 ^* g3 ^* $2 ^+ f6 ^* g4 ^+ f5 ^* g5 ^* $2 ^+ f4 ^* g6 ^+ f3 ^* g7 ^* $2 ^+
                f2 ^* g8 ^+ f1 ^* g9 ^* $2)) (@NToWord 32 (N.ones 26%N))) in
        let fg1 : word 32 := (shiftr y9 26 ^+
        wand
            (shiftr y 26 ^+
            (f1 ^* g0 ^+ f0 ^* g1 ^+
            $19 ^* (f9 ^* g2 ^+ f8 ^* g3 ^+ f7 ^* g4 ^+ f6 ^* g5 ^+ f5 ^* g6 ^+ f4 ^* g7 ^+ f3 ^* g8 ^+ f2 ^* g9)))
            (@NToWord 32 (N.ones 26%N))) in
        fg1) <= b }.
  Proof.
    eexists; multi_bound 32; eassumption.

  Defined.

  Eval simpl in (proj1_sig example_mulmod_u_fg1).

End MulmodExamples.

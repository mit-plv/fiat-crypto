
Require Import Bedrock.Word Bedrock.Nomega.
Require Import NArith PArith Ndigits Compare_dec Arith.
Require Import ProofIrrelevance Ring.
Require Import BoundedWord.

Section MultiBoundedWord.
  Import BoundedWord.

  (* Parameters of boundedness calculations *)
  Delimit Scope Bounded_scope with bounded.
  Open Scope Bounded_scope.

  Context {n: nat}.

  Notation "A <= B" := (wordLeN A B) (at level 70) : Bounded_scope.
  Notation "$" := (natToWord n) : Bounded_scope.

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

  Ltac multi_recurse T :=
    match goal with
    | [ H: T <= _ |- _] => idtac
    | _ =>
      is_var T;
      let T' := (eval cbv delta [T] in T) in multi_recurse T';
      match goal with
      | [ H : T' <= ?x |- _ ] =>
        pose proof (H : T <= x)
      end

    | _ =>
      match T with
      | ?W1 ^+ ?W2 =>
        multi_recurse W1; multi_recurse W2;
        multi_apply2 W1 W2 (@wplus_bound n)

      | ?W1 ^* ?W2 =>
        multi_recurse W1; multi_recurse W2;
        multi_apply2 W1 W2 (@wmult_bound n)

      | mask ?m ?w <= (N.min _ (Npow2 _ - 1)) =>
        multi_recurse w;
        multi_apply1 w (@mask_update_bound n)

      | shiftr ?w ?bits <= N.shiftr ?b (N.of_nat _) =>
        multi_recurse w;
        match goal with
        | [ H: w <= ?b |- _] =>
          pose proof (@shiftr_bound n w b bits H)
        end

      | NToWord n ?k => pose proof (@constant_bound_N n k)
      | natToWord n ?k <= _ => pose proof (@constant_bound_nat n k)
      | ($ ?k) => pose proof (@constant_bound_nat n k)
      | _ => pose proof (@word_size_bound n T)
      end
    end.

  Lemma unwrap_let: forall (y: word n) (f: word n -> word n) (b: N),
      (let x := y in f x) <= b <-> let x := y in (f x <= b).
  Proof. intuition. Qed.

  Ltac multi_bound :=
    match goal with
    | [|- let A := ?B in _] =>
      multi_recurse B; intro; multi_bound
    | [|- (let A := _ in _) <= _] =>
      apply unwrap_let; multi_bound
    | [|- ?W <= _ ] =>
      multi_recurse W
    end.

  (* Examples *)
  Lemma example1 : forall (w1 w2 w3 w4 : word n) b1 b2 b3 b4,
    w1 <= b1
    -> w2 <= b2
    -> w3 <= b3
    -> w4 <= b4
    -> { b | let w5 := w2 ^* w3 in w1 ^+ w5 ^* w4 <= b }.    
  Proof.
    eexists.
    multi_bound.
    eassumption.
  Defined.

  Lemma example2 : forall (w1 w2 w3 w4 : word n) b1 b2 b3 b4,
    w1 <= b1
    -> w2 <= b2
    -> w3 <= b3
    -> w4 <= b4
    -> { b | (let w5 := (w2 ^* $7 ^* w3) in w1 ^+ w5 ^* w4 ^+ $8 ^+ w2) <= b }.
  Proof.
    eexists.
    multi_bound.
    eassumption.
  Defined.

  Lemma example3 : forall (w1 w2 w3 w4 : word n),
    w1 <= Npow2 3
    -> w2 <= Npow2 4
    -> w3 <= Npow2 8
    -> w4 <= Npow2 16
    -> { b | w1 ^+ (w2 ^* $7 ^* w3) ^* w4 ^+ $8 ^+ w2 <= b }.
  Proof.
    eexists.
    multi_bound.
    eassumption.
  Defined.

End MultiBoundedWord.

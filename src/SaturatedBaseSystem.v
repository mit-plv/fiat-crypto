Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.


Require Import Crypto.Tactics.Algebra_syntax.Nsatz.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.Tuple Crypto.Util.ListUtil Crypto.Util.Tactics.
Local Notation "A ^ n" := (tuple A n) : type_scope.

(***

Arithmetic on bignums that handles carry bits; this is useful for
saturated limbs. Compatible with mixed-radix bases.

***)
Section Saturated.
  Context {weight : nat->Z}
          {weight_0 : weight 0%nat = 1}
          {weight_nonzero : forall i, weight i <> 0}
          {weight_multiples : forall i, weight (S i) mod weight i = 0}
          {add_get_carry: nat->Z -> Z -> (Z * Z)}
          {add_get_carry_correct : forall i x y,
              fst (add_get_carry i x y)  = x + y - ((weight (S i) / weight i) * snd (add_get_carry i x y))}
  .

  Definition eval {n} (x : (list Z)^n) : Z :=
    B.Positional.eval weight (Tuple.map sum x).

  Definition eval_from {n} (offset:nat) (x : (list Z)^n) : Z :=
    B.Positional.eval (fun i => weight (i+offset)) (Tuple.map sum x).

  Lemma eval_from_0 {n} x : @eval_from n 0 x = eval x.
  Proof. cbv [eval_from eval]. auto using B.Positional.eval_wt_equiv. Qed.

  Lemma eval_from_S {n}: forall i (inp : (list Z)^(S n)),
    eval_from i inp = eval_from (S i) (tl inp) + weight i * sum (hd inp).
  Proof.
    intros; cbv [eval_from].
    replace inp with (append (hd inp) (tl inp))
      by (simpl in *; destruct n; destruct inp; reflexivity).
    rewrite map_append, B.Positional.eval_step, hd_append, tl_append.
    autorewrite with natsimplify; ring_simplify; rewrite Group.cancel_left.
    apply B.Positional.eval_wt_equiv; intros; f_equal; omega.
  Qed.

  (* Sums a list of integers using carry bits.
     Output : next index, carry, sum
   *)
  Fixpoint compact_digit n (digit : list Z) : nat * Z * Z :=
  match digit with
  | nil => (S n, 0, 0)
  | x :: nil => (S n, 0, x)
  | x :: tl =>
    let rec := compact_digit n tl in
    let sum_carry := add_get_carry n x (snd rec) in
    (S n, snd (fst rec) + snd sum_carry, fst sum_carry)
  end.

  Definition compact_step (idx_carry:nat*Z) (digit: list Z)
    : nat * Z * Z :=
    compact_digit (fst idx_carry) (snd idx_carry::digit).
  
  Definition compact {n} (xs : (list Z)^n) : Z * Z^n := 
    let idx_carry_result := map_with compact_step (0%nat,0) xs in
    (snd (fst idx_carry_result), snd idx_carry_result).

  Lemma compact_digit_correct i (xs : list Z) :
    snd (compact_digit i xs)  = sum xs - (weight (S i) / weight i) * snd (fst (compact_digit i xs)).
  Proof.
    induction xs; simpl compact_digit in *;
      repeat match goal with
             | _ => rewrite add_get_carry_correct
             | _ => progress (rewrite ?sum_cons, ?sum_nil in * )
             | _ => progress (autorewrite with cancel_pair in * )
             | _ => progress break_match; try discriminate
             | _ => progress ring_simplify
             | _ => reflexivity
             | _ => nsatz
             end.
  Qed.

  Lemma fst_fst_compact_step (ic : nat*Z) (digit : list Z) :
    fst (fst (compact_step ic digit)) = S (fst ic).
  Proof. destruct digit; reflexivity. Qed.

  Definition compact_invariant n (starter rem:nat*Z) (inp : tuple (list Z) n) (out : tuple Z n) :=
    B.Positional.eval_from weight (fst starter) out + weight (fst starter + n) * (snd rem)
    = eval_from (fst starter) inp + weight (fst starter)*(snd starter).

  Lemma compact_invariant_holds n starter rem inp out :
    compact_invariant n (fst (compact_step starter (hd inp))) rem (tl inp) out ->
    compact_invariant (S n) starter rem inp (append (snd (compact_step starter (hd inp))) out).
  Proof.
    cbv [compact_invariant B.Positional.eval_from]; intros.
    repeat match goal with
           | _ => rewrite B.Positional.eval_step
           | _ => rewrite eval_from_S
           | _ => rewrite sum_cons 
           | _ => rewrite weight_multiples
           | _ => rewrite Nat.add_succ_l in *
           | _ => rewrite Nat.add_succ_r in *
           | _ => (rewrite fst_fst_compact_step in * )
           | _ => progress ring_simplify
           | _ => rewrite ZUtil.Z.mul_div_eq_full by apply weight_nonzero
           | _ => cbv [compact_step] in *; rewrite compact_digit_correct
           | _ => progress (autorewrite with natsimplify in * )
           end.
    rewrite B.Positional.eval_wt_equiv with (wtb := fun i => weight (i + S (fst starter))) by (intros; f_equal; try omega).
    nsatz.
  Qed.

  Lemma compact_invariant_base rem : compact_invariant 0 rem rem tt tt.
  Proof. cbv [compact_invariant]. simpl. repeat (f_equal; try omega). Qed.

  Lemma compact_invariant_end {n} start (input : (list Z)^n):
    compact_invariant n start (fst (map_with compact_step start input)) input
                      (snd (map_with compact_step start input)).
  Proof.
    apply (map_with_invariant compact_step compact_invariant
                              compact_invariant_holds compact_invariant_base).
  Qed.

  Lemma eval_compact {n} (xs : tuple (list Z) n) :
    B.Positional.eval weight (snd (compact xs)) + (weight n * fst (compact xs)) = eval xs.
  Proof.
    cbv [compact].
    pose proof (compact_invariant_end (0%nat, 0) xs) as Hinv.
    cbv [compact_invariant] in Hinv.
    simpl in Hinv. autorewrite with zsimplify natsimplify in Hinv.
    rewrite eval_from_0, B.Positional.eval_from_0 in Hinv.  apply Hinv.
  Qed.

End Saturated.
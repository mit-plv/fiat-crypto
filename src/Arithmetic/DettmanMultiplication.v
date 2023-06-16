Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Util.LetIn.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Local Open Scope list_scope.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.

Module DettmanMultiplication.
  Section DettmanMultiplication.
    Context
      (s : Z)
      (c' : Z)
      (register_width : nat)
      (n : nat)
      (last_reduction : nat) (* should be between 1 and n - 3, inclusive.
                                This is the position that the final modular reduction lands in.
                                Larger values correspond to a faster algorithm but looser bounds on the output.
                              *)
      (weight: nat -> Z)
      (p_nz' : s - c' <> 0)
      (n_gteq_4 : (4 <= n)%nat) (* Technically we only need 2 <= n to get the proof to go through, but i0..0
0t doesn't make much sense to try to do this with less than four limbs.
                                   Note that having 4 limbs corresponds to zero iterations of the "loop" function defined below. *)
      (wprops : @weight_properties weight)
        
      (weight_0 := weight_0 wprops)
      (weight_positive := weight_positive wprops)
      (weight_multiples := weight_multiples wprops)
      (weight_divides := weight_divides wprops).

    Section WithoutADK.
      Context
        (s_small : forall i: nat, (weight (i + n)%nat / weight i) mod s = 0)
        (s_big : weight (n - 1)%nat <= s)
        (weight_lt_width : forall i: nat, (weight i * 2^register_width) mod weight (i + 1)%nat = 0).
      
      (* Proofs will go through regardless of which encoding we choose for c.
         We choose this encoding (with the weights given by the weight function)
         so that our reductions land in the weights given by the weight function.
         (Note that this won't necessarily work out nicely if we have a fractional
         limbwidth.)
       *)
      Definition c := Positional.to_associational weight n
                        (Positional.simple_encode weight n c').

      Lemma s_positive : s > 0.
      Proof. remember (weight_positive (n - 1)). lia. Qed.

      Lemma s_nz : s <> 0.
      Proof. remember s_positive. lia. Qed.

      Lemma weight_nz : forall i, weight i <> 0.
      Proof. intros i. remember (weight_positive i). lia. Qed.

      Lemma div_mul_le : forall x y, y > 0 -> x / y * y <= x.
      Proof. intros x y H. remember (Zmod_eq x y H). remember (Z_mod_lt x y H). lia. Qed.

      Lemma div_nz a b : b > 0 -> b <= a -> a / b <> 0.
      Proof. Z.div_mod_to_equations. lia. Qed.

      Lemma weight_div_nz : forall i j : nat, (i <= j)%nat -> weight j / weight i <> 0.
      Proof.
        intros i j H. assert (0 < weight j / weight i); try lia.
        apply Weight.weight_divides_full; assumption.
      Qed.

      Lemma s_small' (i j : nat) :
        (j = i + n)%nat ->
        weight j / weight i mod s = 0.
      Proof. intros H. subst. apply s_small. Qed.

      Lemma s_big' : s / weight (n - 1) <> 0.
      Proof. remember (weight_positive (n - 1)). apply div_nz; lia. Qed.

      Lemma weight_increasing : forall i j : nat, (i <= j)%nat -> weight i <= weight j.
      Proof.
        intros i j H.
        assert (0 < weight j / weight i). { apply Weight.weight_divides_full; try assumption. }
        assert (1 <= weight j / weight i) by lia.
        assert (1 * weight i <= weight j / weight i * weight i).
        { apply Zmult_le_compat_r; try lia. remember (weight_positive i). lia. }
        apply (Z.le_trans _ (weight j / weight i * weight i) _); try lia.
        apply div_mul_le. remember (weight_positive i). lia.
      Qed.

      Lemma mod_quotient_zero : forall x y, 0 < y -> x mod y = 0 -> x mod (x / y) = 0.
      Proof.
        intros x y H H1. rewrite Divide.Z.mod_divide_full in H1. destruct H1 as [z H1].
        subst. rewrite Z_div_mult by lia. rewrite Z.mul_comm. apply Z_mod_mult.
      Qed.

      Lemma weight_mod_quotient_zero : forall i j : nat,
          (i <= j)%nat ->
          (weight j) mod (weight j / weight i) = 0.
      Proof.
        intros i j H. apply mod_quotient_zero; try apply weight_positive.
        apply Weight.weight_multiples_full; assumption.
      Qed.

      Lemma divisible_implies_nonzero a b : 
        a mod b = 0 ->
        a <> 0 ->
        a / b <> 0.
      Proof. intros H1 H2. remember (Z_div_mod_eq_full a b). lia. Qed.

      Hint Resolve s_positive s_nz weight_nz div_nz s_big' : arith.
      Hint Resolve weight_0 weight_positive weight_multiples Weight.weight_multiples_full : arith.
      Hint Resolve weight_div_nz weight_mod_quotient_zero : arith.

      Lemma c_correct : Associational.eval c = c'.
      Proof.
        cbv [c]. rewrite eval_to_associational.
        replace (s - c') with (s - Associational.eval [(1, c')]).
        - apply eval_simple_encode; auto with arith. lia.
        - f_equal. cbv [Associational.eval]. simpl. destruct c'; lia.
      Qed.

      Lemma p_nz : s - Associational.eval c <> 0.
      Proof. rewrite c_correct. auto with arith. Qed.    
      Hint Resolve p_nz : arith.

      Local Open Scope nat_scope.

      Definition reduce' from to before := dedup_weights (reduce_one s from (from / to) c before).
      Definition carry' from to before := dedup_weights (Associational.carry from (to / from) before).
      Definition borrow' from to before := dedup_weights (borrow from (from / to) before).

      Hint Rewrite eval_reduce_one Associational.eval_carry eval_dedup_weights eval_borrow : push_eval.

      Definition carry_from_position i x :=
        carry' (weight i) (weight (i + 1)) x.

      Lemma eval_carry_from_position i x :
        Associational.eval (carry_from_position i x) = Associational.eval x.
      Proof.
        cbv [carry_from_position carry']. autorewrite with push_eval; auto with arith. Qed.
      Hint Rewrite eval_carry_from_position : push_eval.

      Definition carry_reduce i x :=
        let x := carry_from_position (i + n) x in
        let x := reduce' (weight (i + n)) (weight i) x in
        carry_from_position i x.

      Lemma eval_carry_reduce i x :
        (Associational.eval (carry_reduce i x) mod (s - Associational.eval c) =
           Associational.eval x mod (s - Associational.eval c))%Z.
      Proof. cbv [carry_reduce reduce']. autorewrite with push_eval; auto with arith. Qed.
      Hint Rewrite eval_carry_reduce : push_eval.

      (* rw stands for "register_width".
         The idea here is that, if x has value 0 at weight (i + n + 1), then
         carry_reduce_rw i x = carry_reduce (i + 1) (carry_reduce i x).

         The benefit of using carry_reduce_rw, then, instead of a couple of carry_reduces,
         is that (in C, or something similar), the LHS of the equation above takes less work
         to calculate than the RHS.  This is because carries by 2^register_width are very easy.
       *)
      Definition carry_reduce_rw i x :=
        let x := carry' (weight (i + n)) (weight (i + n) * 2^register_width) x in
        let x := reduce' (weight (i + n)) (weight i) x in
        let x := carry_from_position i x in
        let x := reduce' (weight (i + n) * 2^register_width) (weight (i + 1)) x in
        carry_from_position (i + 1) x.

      Local Open Scope Z_scope.

      Lemma reduction_divides i : weight (n + i - 1) * 2^register_width / weight i mod s = 0.
      Proof.
        rewrite Divide.Z.mod_divide_full. apply (Z.divide_trans _ (weight (n + i) / weight i)).
        - rewrite <- Divide.Z.mod_divide_full. rewrite (Nat.add_comm n i). apply s_small.
        - apply Z.divide_div.
          + remember (weight_positive i). lia.
          + rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption.
            lia.
          + rewrite <- Divide.Z.mod_divide_full.
            replace (weight (n + i)) with (weight (n + i - 1 + 1)).
            -- apply weight_lt_width.
            -- f_equal. lia.
      Qed.

      Lemma reduction_divides' (i j : nat) :
        (j = n + i - 1)%nat ->
        weight j * 2^register_width / weight i mod s = 0.
      Proof. intros H. subst. apply reduction_divides. Qed.

      Lemma weight_prod_mod_zero (i j : nat) :
        (i <= j)%nat ->
        (weight j * 2^register_width) mod (weight i) = 0.
      Proof.
        intros H. apply Divide.Z.mod_divide_full. apply Z.divide_mul_l.
        rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption.
      Qed.

      Lemma weight_prod_div_nz (i j : nat) :
        (i <= j)%nat ->
        weight j * 2^register_width / weight i <> 0.
      Proof.
        intros H. apply divisible_implies_nonzero. apply weight_prod_mod_zero; try lia.
        remember (weight_positive j). remember (Z.pow_nonneg 2 register_width). lia.
      Qed.

      Lemma s_small_particular : weight n mod s = 0.
      Proof.
        replace (weight n) with (weight n / weight 0).
        - apply s_small'; lia.
        - Z.div_mod_to_equations. lia.
      Qed.

      Lemma eval_carry_reduce_rw i x :
        (Associational.eval (carry_reduce_rw i x) mod (s - Associational.eval c) =
           Associational.eval x mod (s - Associational.eval c))%Z.
      Proof.
        cbv [carry_reduce_rw carry' reduce']. autorewrite with push_eval; auto with arith.
        - apply weight_prod_div_nz; lia.
        - apply weight_prod_div_nz; lia.
        - apply mod_quotient_zero; auto with arith. apply weight_prod_mod_zero; lia.
        - apply reduction_divides'; lia.
      Qed.
      Hint Rewrite eval_carry_reduce_rw : push_eval.

      Definition carry_chain idxs x :=
        fold_right carry_from_position x (rev idxs).

      Lemma eval_carry_chain idxs x :
        Associational.eval (carry_chain idxs x) = Associational.eval x.
      Proof.
        cbv [carry_chain]. induction (rev idxs).
        - reflexivity.
        - simpl. autorewrite with push_eval. assumption.
      Qed.
      Hint Rewrite eval_carry_chain : push_eval.

      Definition carry_reduce_chain idxs x :=
        fold_right carry_reduce x (rev idxs).

      Lemma eval_carry_reduce_chain idxs x :
        ((Associational.eval (carry_reduce_chain idxs x)) mod (s - Associational.eval c) = (Associational.eval x) mod (s - Associational.eval c))%Z.
      Proof.
        cbv [carry_reduce_chain]. induction (rev idxs).
        - reflexivity.
        - simpl. autorewrite with push_eval. assumption.
      Qed.
      Hint Rewrite eval_carry_reduce_chain : push_eval.

      Hint Resolve s_small_particular divisible_implies_nonzero Z_mod_same_full : arith.

      (* combine the values at position (n - 1) and n;
         then, split the combined value into
         pieces at position (n - 1) and weight s.
       *)
      Definition move_to_weight_s x :=
        let x := carry' (weight (n - 1)) s x in
        borrow' (weight n) s x.

      Lemma eval_move_to_weight_s x :
        Associational.eval (move_to_weight_s x) = Associational.eval x.
      Proof.
        cbv [move_to_weight_s borrow' carry']. autorewrite with push_eval; auto with arith.
        apply mod_quotient_zero; auto with arith. remember s_positive. lia.
      Qed.
      Hint Rewrite eval_move_to_weight_s : push_eval.

      (* This function is a reduction from position n to position 0---
         the main idea is to do something like 'let x := carry_reduce 0 x'.

         In fact, we move everything from position n to weight s, as well
         as taking the top few bits off position (n - 1) to put them in weight s,
         before doing the reduction from weight s to position 0.

         This gives us the opportunity to reduce from the top of position (n - 1),
         as well as from position n, while only having to do one reduction.
       *)
      Definition carry_reduce_s x :=
        let x := carry_from_position n x in
        let x := move_to_weight_s x in
        let x := reduce' s (weight 0) x in
        carry_from_position 0 x.

      Lemma eval_carry_reduce_s x :
        ((Associational.eval (carry_reduce_s x)) mod (s - Associational.eval c) =
           (Associational.eval x) mod (s - Associational.eval c))%Z.
      Proof.
        cbv [carry_reduce_s reduce']. autorewrite with push_eval; auto with arith.
        - rewrite weight_0. rewrite Z.div_1_r. apply s_nz.
        - rewrite weight_0. rewrite Z.div_1_r. auto with arith.
        - rewrite weight_0. rewrite Z.div_1_r. auto with arith.
      Qed.
      Hint Rewrite eval_carry_reduce_s : push_eval.

      Local Open Scope nat_scope.

      Definition seq_from_to a b := seq a (Z.to_nat (b - a + 1)).

      (* The main idea here is to have something like this:
             Definition overly_simple_reduce_carry_borrow x :=
                        carry_reduce_chain (seq_from_to 0 (n - 1)) x.
         Below, we have something like this, with a few extra things added in.
       *)
      Definition reduce_carry_borrow x :=
        let x := dedup_weights x in

        (* In the 'overly_simple_reduce_carry_borrow', the following code block
           would belong in the position marked with an 'A' down below.
           It turns out that doing that might make the output bounds too loose.

           In particular, we need last_reduction to be small enough so that the final
           carry chain (right below the 'A') does not overflow position (n - 1).
           We solve this issue by putting the code block here (instad of at 'A').

           This way, the reductions that land in positions
                  last_reduction + 1, last_reduction + 2, ..., n - 2, n - 1
           are carried up to position n (before the reduction from position n),
           so we don't have to worry about them overflowing position (n - 1).

           Note that, other than this constraint requiring last_reduction to be
           sufficiently small, we want to choose the last_reduction parameter to
           be as large as possible, since when it gets smaller, the final carry
           chain gets longer (and everything else takes the same amount of time).
         *)
        let x := carry_reduce_chain (seq_from_to (last_reduction + 1) (n - 3)) x in
        let x := carry_reduce_rw (n - 2) x in

        (* This next code block is similar to writing
                let x := carry_reduce 0 x,
           except it's a bit more clever.
           While reducing from position n to position 0, we simultaneously reduce
           the top few bits of position (n - 1) down to position 0.
         *)
        let x := carry_reduce_s x in

        (* This code block is what remains (after we've finished adding in all the
           extra stuff) of the 'overly_simple_reduce_carry_borrow' referred to above.

           The only clever part is that the last two carry_reduces have been replaced
           with a carry_reduce_rw.
         *)
        let x := carry_reduce_chain (seq_from_to 1 (last_reduction - 1)) x in
        let x := carry_reduce_rw last_reduction x in

        (* A *)

        let x := carry_chain (seq_from_to (last_reduction + 2) (n - 2)) x in

        Positional.from_associational weight n x.

      Definition mulmod a b :=
        let a_assoc := Positional.to_associational weight n a in
        let b_assoc := Positional.to_associational weight n b in
        let x := Associational.mul a_assoc b_assoc in
        reduce_carry_borrow x.

      Definition squaremod a :=
        let a_assoc := Positional.to_associational weight n a in
        let x := Associational.square a_assoc in
        reduce_carry_borrow x.

      Hint Rewrite Positional.eval_from_associational Positional.eval_to_associational : push_eval.

      Local Open Scope Z_scope.

      Lemma eval_reduce_carry_borrow r0 :
        (Positional.eval weight n (reduce_carry_borrow r0)) mod (s - Associational.eval c) =
          (Associational.eval r0) mod (s - Associational.eval c).
      Proof.
        cbv [reduce_carry_borrow carry' reduce' borrow'].
        autorewrite with push_eval; auto with arith; try lia.
      Qed.
      Hint Rewrite eval_reduce_carry_borrow : push_eval.

      Theorem eval_mulmod a b :
        (Positional.eval weight n (mulmod a b)) mod (s - c') =
          (Positional.eval weight n a * Positional.eval weight n b) mod (s - c').
      Proof.
        cbv [mulmod]. rewrite <- c_correct. autorewrite with push_eval. reflexivity.
      Qed.

      Theorem eval_squaremod a :
        (Positional.eval weight n (squaremod a)) mod (s - c') =
          (Positional.eval weight n a * Positional.eval weight n a) mod (s - c').
      Proof.
        cbv [squaremod]. rewrite <- c_correct. autorewrite with push_eval. reflexivity.
      Qed.
    End WithoutADK.

    Section WithADK.
      (* now we'll add the option to use the adk algorithm in place of associational.mul *)
      Context (weight_friendly : forall i j : nat, weight i * weight j = weight (i + j)).
      (* this Arbitrary-Degree Karatsuba multiplication uses fewer muls but more adds/subs compared to Associational.mul,
         as described here: https://eprint.iacr.org/2015/1247.pdf.
         As the number of limbs increases, the performance of this multiplication improves relative to Associational.mul.
         As described in the paper, the algorithm is this:
         xy = \sum_{i = 1}^{n - 1} \sum_{j = 0}^{i - 1} (x_i - x_j)(y_j - y_i) b^{i + j} +
              \sum_{i = 0}^{n - 1} \sum_{j = 0}^{n - 1} x_j y_j b^{i + j}.
         Then, as we see in this example
         (https://github.com/bitcoin-core/secp256k1/blob/9618abcc872a6e622715c4540164cc847b653efb/src/field_10x26_impl.h),
         the number of adds can be reduced by rewriting the second summation as follows:
         \sum_{i = 0}^{n - 1} \sum_{j = 0}^{n - 1} x_i y_i b^{i + j} = 
         \sum_{i = 0}^{2n - 2} b^i \sum_{j = \max(0, i - (n - 1))}^{i} x_j y_j = 
         \sum_{i = 0}^{2n - 2} b^i ([\sum_{j = 0}^i x_j y_j] - [\sum_{j = 0}^{i - n} x_j y_j]) = 
                 b^{2n - 2} x_{n - 1} y_{n - 1} + 
                 \sum_{i = 0}^{2n - 3} b^i ([\sum_{j = 0}^i x_j y_j] - [\sum_{j = 0}^{i - n} x_j y_j]).
         This last formula will be particularly nice if we precompute the values f_i = \sum_{j = 0}^i x_j y_j, as i ranges from 0 to n - 1.
       *) Print split. Search split. Print negate_snd.

      (* returns a0 * s_b1 + b0 * s_a1 *)
      Definition karatsuba_cross_terms (a0 s_a1 b0 s_b1 : (Z*Z)) : list (Z*Z) :=
        let sa := fst s_a1 / fst a0 in
        let sb := fst s_b1 / fst b0 in
        let s := if sa =? sb then sa else 1 in
        let a1 := (fst s_a1 / s, snd s_a1) in
        let b1 := (fst s_b1 / s, snd s_b1) in
        mul [(s, 1)]
          (mul [a0] [b0] ++
             mul [a1] [b1] ++
             mul (dedup_weights ([a1] ++ Associational.negate_snd [a0])) (dedup_weights ([b1] ++ Associational.negate_snd [b0]))).

      (* a and b should be ordered from least to greatest weight *)
      (* natural to think about this when length rest_of_a = length rest_of_b, but I don't think we need that *)
      (* returns a0 * rest_of_b + b0 * rest_of_a *)
      Fixpoint all_pairs (a0 b0 : Z*Z) (rest_of_a rest_of_b : list (Z*Z)) : list (Z*Z) :=
        match rest_of_a, rest_of_b with
        | s_a1 :: rest_of_a', s_b1 :: rest_of_b' => karatsuba_cross_terms a0 b0 s_a1 s_b1 ++ all_pairs a0 b0 rest_of_a' rest_of_b'
        | _, _ => []
        end.

      (* for this to work out nicely, a and b should have the same weights in the same (increasing) order.
         i.e., we want a = [(w_0, a_0), (w_1, a_1), ..., (w_n, a_n)], and
                       b = [(w_0, b_0), (w_1, b_1), ..., (w_n, b_n)], and
                       w_0 < w_1 < ... < w_n. *)
      Fixpoint adk_mul (a b : list (Z*Z)) :=
        match a, b with
        | a0 :: rest_of_a, b0 :: rest_of_b => mul [a0] [b0]                            (* a0 * b0 *)
                                                ++ all_pairs a0 b0 rest_of_a rest_of_b (* a0 * rest_of_b + b0 * rest_of_a *)
                                                ++ adk_mul rest_of_a rest_of_b         (* rest_of_a * rest_of_b *)
        | _, _ => []
        end.

      (* The algorithm above is very nice.  Now I apply some ugly transformations.
         AFAIK, the rewriter doesn't know how to rewrite things like a1 + b1 - a1 --> b1.
         This is a problem, since I would like to do term cancellation like that here.
         However, the rewriter does know how to rewrite things like a1 - a1 --> 0.
         So, I just need to manually group terms here, and then let the rewriter cancel them out. *)
      Print fold_right.

      Fixpoint append_to_nth {X} (n : nat) (x : list X) (l : list (list X)) : list (list X) :=
        match n with
        | O => match l with
               | l0 :: l' => (l0 ++ x) :: l'
               | [] => x :: []
               end
        | S n' => match l with
                  | l0 :: l' => l0 :: append_to_nth n' x l'
                  | [] => [] :: append_to_nth n' x []
                  end
        end.

      Fixpoint append_elementwise {X} (a b : list (list X)) : list (list X) :=
        match a, b with
        | a0 :: a', b0 :: b' => (a0 ++ b0) :: append_elementwise a' b'
        | [], _ => b
        | _, [] => a
        end.
      Print mul.

      Definition karatsuba_cross_terms_grouped_nicely (a0_marked s_a1_marked : Z*Z*nat)
        (b0 s_b1 : (Z*Z)) : list (list (Z*Z)) :=
        let (a0, a0_marker) := a0_marked in
        let (s_a1, s_a1_marker) := s_a1_marked in
        let sa := fst s_a1 / fst a0 in
        let sb := fst s_b1 / fst b0 in
        let s := if sa =? sb then sa else 1 in
        let a1 := (fst s_a1 / s, snd s_a1) in
        let b1 := (fst s_b1 / s, snd s_b1) in
        append_to_nth a0_marker (mul [(s, 1)] (mul [a0] [b0]))
          (append_to_nth s_a1_marker (mul [(s, 1)] (mul [a1] [b1]))
             (append_to_nth 0
                (mul [(s, 1)] 
                   (mul
                      (dedup_weights ([a1] ++ Associational.negate_snd [a0]))
                      (dedup_weights ([b1] ++ Associational.negate_snd [b0]))))
                [])).
                            
                      
      Fixpoint all_pairs_grouped_nicely (a0_marked : Z*Z*nat) (b0 : Z*Z) (rest_of_a : list (Z*Z*nat)) (rest_of_b : list (Z*Z)) :
        (list (list (Z*Z))) :=
        match rest_of_a, rest_of_b with
        | s_a1_marked :: rest_of_a', s_b1 :: rest_of_b' =>
            append_elementwise
              (karatsuba_cross_terms_grouped_nicely a0_marked s_a1_marked b0 s_b1)
              (all_pairs_grouped_nicely a0_marked b0 rest_of_a' rest_of_b')
        | _, _ => []
        end.

      Fixpoint adk_mul_grouped_nicely' (a_marked : list (Z*Z*nat)) (b : list (Z*Z)) : list (list (Z*Z)) :=
        match a_marked, b with
        | (a0, a0_marker) :: rest_of_a, b0 :: rest_of_b =>
            append_to_nth a0_marker (mul [a0] [b0])
              (append_elementwise
                 (all_pairs_grouped_nicely (a0, a0_marker) b0 rest_of_a rest_of_b)
                 (adk_mul_grouped_nicely' rest_of_a rest_of_b))
        | _, _ => []
        end.

      Definition adk_mul_grouped_nicely (a b : list (Z*Z)) : list (list (Z*Z)) :=
        let a_marked := fst (fold_right (fun p l_n => ((p, snd l_n) :: fst l_n, S n)) ([], S O) a) in
        (* if a = [a1; ...; an], then a_marked = [(1, a1); (2, a2); ...; (n, an)] *)
        adk_mul_grouped_nicely' a_marked b. Print fold_right.

      Definition nth_reifiable' {X} (i : Z) (l : list X) (default : X) : Z*X :=
        fold_right (fun next n_nth => (fst n_nth - 1, if (fst n_nth =? 0) then next else (snd n_nth))) (Z.of_nat (length l) - i - 1, default) l.    

      Lemma nth_reifiable'_spec {X} (i : Z) (l : list X) (default : X) :
        nth_reifiable' i l default = (-i - 1, if 0 <=? i then nth (Z.to_nat i) l default else default).
      Proof.
        cbv [nth_reifiable']. generalize dependent i. induction l as [| x l' IHl']; intros i.
        - simpl. f_equal. destruct (0 <=? i); destruct (Z.to_nat i); reflexivity.
        - replace (Z.of_nat (length (x :: l')) - i - 1) with
            (Z.of_nat (length l') - (i - 1) - 1).
          + simpl. rewrite IHl'. simpl. f_equal; try lia. destruct (_ =? 0) eqn:E1; destruct (0 <=? i - 1) eqn:E2; destruct (0 <=? i) eqn:E3; destruct (Z.to_nat i) eqn:E4; try lia; try reflexivity.
            f_equal. lia.
          + replace (length (x :: l')) with (1 + length l')%nat by reflexivity. lia.
      Qed.

      Definition nth_reifiable {X} (i : nat) (l : list X) (default : X) : X :=
        snd (nth_reifiable' (Z.of_nat i) l default).

      Lemma nth_reifiable_spec {X} (i : nat) (l : list X) (default : X) :
        nth_reifiable i l default = nth i l default.
      Proof.
        cbv [nth_reifiable]. rewrite nth_reifiable'_spec. simpl. destruct (_ <=? _) eqn:E; try lia.
        - rewrite Nat2Z.id. reflexivity.
        - apply Z.leb_gt in E. lia.
      Qed.

      Definition nthZ {X} (i : Z) (l : list X) (default : X) : X :=
        if (Z.of_nat (Z.to_nat i)) =? i then
          nth_reifiable (Z.to_nat i) l default
        else
          default.

      Lemma nthZ_lt_0 {X} (i : Z) (l : list X) (default : X) :
        i < 0 ->
        nthZ i l default = default.
      Proof.
        intros H. cbv [nthZ]. assert (H': Z.of_nat (Z.to_nat i) <> i) by lia.
        rewrite <- Z.eqb_neq in H'. rewrite H'. reflexivity.
      Qed.

      Lemma nthZ_ge_0 {X} (i : Z) (l : list X) (default : X) :
        0 <= i ->
        nthZ i l default = nth (Z.to_nat i) l default.
      Proof.
        intros H. cbv [nthZ]. assert (H': Z.of_nat (Z.to_nat i) = i) by lia.
        rewrite <- Z.eqb_eq in H'. rewrite H'. apply nth_reifiable_spec.
      Qed.
      
      Fixpoint half_that_cancels' (n : nat) (weight : nat -> Z) (a b : list Z) (current_n_plus_one : nat) : list (list (Z*Z)) :=
        (* we want
           a0 * b0 to appear at weights 0 ... (n - 1),
           a1 * b1 to appear at weights 1 ... n,
           ...
           a_(n - 1) * b_(n - 1) to appear at weights (n - 1) ... (2*n - 2)
         *)
        match current_n_plus_one with
        | O => []
        | S current_n => append_to_nth
                           current_n
                           (map (fun i => (weight i, (nthZ current_n a 0) * (nthZ current_n b 0))) (seq current_n n))
                           (half_that_cancels' n weight a b current_n)
        end.

      Definition half_that_cancels (n : nat) (weight : nat -> Z) (a b : list Z) : list (list (Z*Z)) :=
        half_that_cancels' n weight a b n.

      Definition seqZ a b :=
        map (fun x => Z.of_nat x + a) (seq 0 (Z.to_nat (1 + b - a))).

      Definition second_summation' (n : nat) (weight : nat -> Z) (products f : list Z) := 
        let high_part : Z*Z := (weight (n - 1)%nat * weight (n - 1)%nat, (nthZ (Z.of_nat (n - 1)) products 0)) in
        let low_part : list (Z*Z) := map (fun i => (weight (Z.to_nat i), (nthZ i f 0) - (nthZ (i - Z.of_nat n) f 0))) (seqZ 0 (2*Z.of_nat n - 3)) in
        low_part ++ [high_part].

      Definition second_summation (n : nat) (weight : nat -> Z) (x y : list Z) : list (Z*Z) :=
        dlet high_product : Z := (nthZ (Z.of_nat n - 1) x 0) * (nthZ (Z.of_nat n - 1) y 0) in
            let products : list Z :=
              map (fun i => (nthZ i x 0) * (nthZ i y 0))
                (seqZ 0 (Z.of_nat n - 2)) ++ [high_product] ++ (repeat 0 ((2*n - 3) - (n - 2 + 1))) in
            (list_rect
               (fun _ => list Z -> list (Z*Z))
               (fun f => second_summation' n weight products (rev f))
               (fun p _ g => fun f' => Let_In ((nthZ 0 f' 0) + p) (fun x => g (x :: f'))) 
               products) [].

      Definition half_that_doesnt_cancel (n : nat) (weight : nat -> Z) (a b : list Z) : list (Z*Z) :=
        second_summation n weight a b.

      (* We have two 'halves of zero'.  The 'half_that_cancels' should cancel out (be sure to use dedup_weights!) with stuff in adk_mul_grouped_nicely.
         Then, we just add on the 'half_that_doesnt_cancel'. Should be easy to prove that putting together the half that cancels with the half that doesn't cancel gives you zero.*)

      Definition first_summation (x y : list Z) : list (Z*Z) :=
        flat_map (fun i =>
                    map (fun j => (weight (Z.to_nat i) * weight (Z.to_nat j), (nthZ i x 0 - nthZ j x 0) * (nthZ j y 0 - nthZ i y 0)))
                      (seqZ 0 (i - 1)))
          (seqZ 1 (Z.of_nat n - 1)).

      Lemma friendly_list_rect products_remaining f_so_far base_case :
        (list_rect
           (fun _ => list Z -> list (Z*Z))
           base_case
           (fun p _ g => fun f' => Let_In ((nthZ 0 f' 0) + p) (fun x => g (x :: f'))) 
           products_remaining) f_so_far =
          base_case (fold_left (fun l p => (nthZ 0 l 0) + p :: l) products_remaining f_so_far).
      Proof.
        generalize dependent f_so_far. induction products_remaining as [| p products' IH].
        - reflexivity.
        - intros f_so_far. simpl. rewrite unfold_Let_In. rewrite IH. reflexivity.
      Qed.

      Lemma f_spec products :
        fold_left (fun l p => (nthZ 0 l 0) + p :: l) products [] =
          map
            (fun i => fold_right Z.add 0 (map (fun j => nthZ j products 0) (seqZ 0 i)))
            (seqZ 0 (length products)).
      Proof. Admitted.
        
      Definition friendly_second_summation (x y : list Z) : list (Z*Z) :=
        let products : list Z := map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (2*Z.of_nat n - 3)) in
        let f : list Z := fold_left (fun l p => (nthZ 0 l 0) + p :: l) products [] in
        second_summation' products (rev f).

      Lemma products_friendly x y :
        map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (Z.of_nat n - 2)) ++
          [(nthZ (Z.of_nat n - 1) x 0) * (nthZ (Z.of_nat n - 1) y 0)] ++
          (repeat 0 ((2*n - 3) - (n - 2 + 1))) =
        map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (2*Z.of_nat n - 3)).
      Proof. Admitted.
            
      Lemma second_summation_friendly x y :
        second_summation x y = friendly_second_summation x y.
      Proof.
        cbv [second_summation]. rewrite unfold_Let_In. rewrite products_friendly.
        cbv [friendly_second_summation]. rewrite friendly_list_rect. reflexivity.
      Qed.

      Definition adk_mul' (x y : list Z) : list (Z*Z) :=
        first_summation x y ++ second_summation x y.

      Definition friendly_second_summation' (products f : list Z) : list (Z*Z) :=
        map (fun i => (weight (Z.to_nat i), (nthZ i f 0) - (nthZ (i - Z.of_nat n) f 0))) (seqZ 0 (2*Z.of_nat n - 2)).

      Lemma expand_seqZ_le i j : i <= j -> seqZ i j = i :: seqZ (i + 1) j.
      Proof.
        clear n_gteq_4.
        intros H. cbv [seqZ].
        replace (Z.to_nat (1 + j - i)) with (S (Z.to_nat (j - i))) by lia.
        replace (Z.to_nat (1 + j - (i + 1))) with (Z.to_nat (j - i)) by lia.
        rewrite <- cons_seq. rewrite map_cons. f_equal; try lia.
        rewrite ListUtil.map_seq_succ. rewrite map_map. apply map_ext. lia.
      Qed.

      Lemma expand_seqZ_gt i j : i > j -> seqZ i j = [].
      Proof. intros H. cbv [seqZ]. replace (Z.to_nat (1 + j - i)) with 0%nat by lia. reflexivity. Qed.
      
      Definition f1 x y :=
        fun i j => (i + j, (nthZ i x 0 - nthZ j x 0) * (nthZ j y 0 - nthZ i y 0)).
      Definition first_summation_lifted (x y : list Z) : list (Z*Z) :=
        flat_map (fun i =>
                    map (f1 x y i)
                      (seqZ 0 (i - 1)))
          (seqZ 1 (Z.of_nat n - 1)).

      Definition value_at_position i lifted :=
        fold_right Z.add 0 (map snd (filter (fun p => fst p =? i) lifted)).

      Lemma filter_concat {X} (f : X -> bool) (l : list (list X)) :
        filter f (concat l) = concat (map (filter f) l).
      Proof. Admitted.

      Lemma filter_map {X Y} (f : Y -> bool) (g : X -> Y) (l : list X) :
        filter f (map g l) = map g (filter (fun x => f (g x)) l).
      Proof. Admitted.

      Lemma value_at_position_first_summation w x y :
        value_at_position w (first_summation_lifted x y) =
          sum (fun j => (nthZ j x 0 - nthZ (w - j) x 0) * (nthZ (w - j) y 0 - nthZ j y 0))
            1 (n - 1).
      Proof.
        cbv [first_summation_lifted]. set (xx := sum _ _ _). cbv [value_at_position].
        rewrite flat_map_concat_map. rewrite filter_concat. rewrite map_map. Admitted.
       set (filter' := filter _).
        Check map_ext.
        rewrite (map_ext (fun x0 => filter _ _)
                   (fun x0 => map (f1 x y x0)
                                (filter'
                                   (seqZ 0 (x0 - 1))))).
        - cbv [f1]. simpl.
          rewrite (map_ext_in (fun x0 => map _ _)
                     (fun x0 => map
                                  (fun j : Z => (x0 + j, (nthZ x0 x 0 - nthZ j x 0) * (nthZ j y 0 - nthZ x0 y 0)))
                                  (if x0 <=? i then [(i - x0)] else []))).

                                      Search map.
                                (fun j =>  (x0 + j, (nthZ x0 x 0 - nthZ j x 0) * (nthZ j y 0 - nthZ x0 y 0)))
                                (filter 

                   (map_funext).
        rewrite filter_map. Search filter.
        

      Lemma value_at_position_second_summation i x y :

      Definition project_to_associational (lifted : list (nat*Z)) : list (Z*Z) :=
        map (fun p => (weight (fst p), snd p)) lifted.

      Lemma proj_equal (lifted1 lifted2 : list (nat*Z)) :
        forall i, value_at_position i lifted1 = value_at_position i lifted2 ->
                  Permutation (dedup_weights lifted1) (dedup_weights lifted2).

      Print value_at_weight.

      Search filter. Print friendly_second_summation.

      Lemma value_at_weight_first_summation i x y :
        first_summation x y =
          sum (fun j => ((nthZ j x 0) - (nthZ (i - j) y 0)) * ((nthZ (i - j) y 0) - (nthZ i x 0))) 0 i.
      Proof.
        intros H. set (thesum := sum _ _ _). cbv [value_at_weight].

      Lemma value_at_weight_second_summation i x y :
        0 <= i <= 2*n - 2 ->
        value_at_weight (second_summation x y) (weight (Z.to_nat i)) =
          sum (fun j => (nthZ j x 0) * (nthZ (i - j) y 0)) 0 (n - 1).
      Proof. Admitted.

      Lemma 

      Lemma value_at_weight_correct x y :
        value_at_weight (adk_mul' x y) = value_at_weight ((Associational.mul
                                                        (Positional.to_associational weight n x)
                                                        (Positional.to_associational weight n y))).
      Proof.
        set (xx := value_at_weight (mul _ _)). cbv [adk_mul'].

      Lemma eval_adk_mul' x y :
        dedup_weights (adk_mul' x y) = dedup_weights (Associational.mul
                                                        (Positional.to_associational weight n x)
                                                        (Positional.to_associational weight n y)).
      Proof.
        cbv [adk_mul']. rewrite second_summation_friendly.
        induction n. Print dedup_weights. Print friendly_second_summation. Search Associational.mul.
        - simpl.

      Definition ZZ_is_bounded_by_bool (x : Z) (bounds : Z*Z) : bool :=
        (fst bounds <=? x) && (x <=? snd bounds).
    
      Definition is_bounded_by (l : list Z) (bounds : list (Z*Z)) : bool :=
        fold_right andb true
          (map (fun x_bound => ZZ_is_bounded_by_bool (fst x_bound) (snd x_bound))
             (combine l bounds)).

      Definition is_lower_bounded_by (bounds : list (Z*Z)) (xs : list Z) : bool :=
        fold_right andb true
          (map (fun bound_x => snd bound_x <=? fst (fst bound_x))
             (combine bounds xs)).

      (* if everything is nonnegative, then the output is nondecreasing in the inputs *)
      Definition output_bounds (x_bounds y_bounds : list (Z*Z)) : list (Z*Z) :=
        let lower_bounds := Positional.from_associational weight (2*n - 2 + 1)
                              (adk_mul' (map fst x_bounds) (map fst y_bounds)) in
        let upper_bounds := Positional.from_associational weight (2*n - 2 + 1)
                              (adk_mul' (map snd x_bounds) (map snd y_bounds)) in
        map (fun lower_upper => (fst lower_upper, snd lower_upper))
          (combine lower_bounds upper_bounds).

      Definition list_if_then_else {X} (cond : bool) (ifval elseval : list X) : list X :=
        map (fun if_else => if cond then fst if_else else snd if_else) (combine ifval elseval).

      Definition truncate (values : list Z) (upper_bounds : list Z) :=
        map (fun x_upper => Z.land (fst x_upper) (Z.ones (Z.log2_up (snd x_upper)))) (combine values upper_bounds).
    
      Definition adk_mul (x_bounds y_bounds : list (Z*Z)) (x y : list Z) : list Z :=
        list_if_then_else
          (is_lower_bounded_by x_bounds (repeat 0 n) &&
           is_lower_bounded_by y_bounds (repeat 0 n) &&
           ZZ_is_bounded_by_bool (nthZ 0 x 0) (nthZ 0 x_bounds (0, 0)) &&
           is_bounded_by y y_bounds)
          (truncate
             (Positional.from_associational weight (2*n - 2 + 1) (adk_mul' x y))
             (map snd (output_bounds x_bounds y_bounds)))
          (Positional.from_associational weight (2*n - 2 + 1) (adk_mul' x y)).

     

      Definition adk_mulmod (x_bounds y_bounds : list (Z*Z)) (x y : list Z) : list Z :=
        reduce_carry_borrow (Positional.to_associational weight n (adk_mul x_bounds y_bounds x y)).

      Theorem eval_adk_mulmod a_bounds b_bounds a b :
        (Positional.eval weight n (adk_mulmod a_bounds b_bounds a b)) mod (s - c') =
          (Positional.eval weight n a * Positional.eval weight n b) mod (s - c').
      Proof. Admitted.
    End WithADK.
  End DettmanMultiplication.  
End DettmanMultiplication.

(*Definition nn := 5%nat.
      Definition xx := [543; 654; 234; 123; 5698].
      Definition yy := [890423; 432; 321; 1; 232].
      Definition weightt i := 2^i.
      Compute (dedup_weights (DettmanMultiplication.adk_mul' nn weightt xx yy)).
      Compute (dedup_weights (Associational.mul (Positional.to_associational weightt nn xx)
                                                (Positional.to_associational weightt nn yy))).*)

Module dettman_multiplication_mod_ops.
  Section dettman_multiplication_mod_ops.
    Import DettmanMultiplication.
    Local Open Scope Z_scope.
    Local Coercion QArith_base.inject_Z : Z >-> Q.
    Local Coercion Z.pos : positive >-> Z.
    Context
        (s : Z)
        (c : Z)
        (register_width : nat)
        (n : nat)
        (last_limb_width : nat)
        (last_reduction : nat)
        (p_nz : s - c <> 0)
        (n_gteq_4 : (4 <= n)%nat)
        (last_limb_width_small : last_limb_width * n <= Z.log2 s)
        (last_limb_width_big : 1 <= last_limb_width)
        (s_power_of_2 : 2 ^ (Z.log2 s) = s).

    Local Notation limbwidth_num' := (Z.log2 s - last_limb_width).
    Local Notation limbwidth_den' := (n - 1). (* can't use Q here, or else reification doesn't work *)
    
    Context
        (registers_big : limbwidth_num' <= register_width * limbwidth_den') (* stated somewhat awkwardly in terms of Z; i think we might want to avoid Q here too *)
        (weight_big : Z.log2 s <= n * limbwidth_num' / limbwidth_den').

    (* I don't want these to be automatically unfolded in the proofs below. *)
    Definition limbwidth_num := limbwidth_num'.
    Definition limbwidth_den := limbwidth_den'.

    Definition weight := (weight limbwidth_num limbwidth_den).

    Definition mulmod := mulmod s c register_width n last_reduction weight.
    Definition squaremod := squaremod s c register_width n last_reduction weight.

    Lemma n_small : n - 1 <= Z.log2 s - last_limb_width.
    Proof.
      replace (Z.of_nat n) with (Z.of_nat n - 1 + 1) in last_limb_width_small by lia.
      remember (Z.of_nat n - 1) as n'.
      rewrite Z.mul_add_distr_l in last_limb_width_small.
      remember (Z.of_nat last_limb_width) as l.
      assert (H: n' <= l * n').
      { replace n' with (1 * n') by lia. replace (l * (1 * n')) with (l * n') by lia.
        apply Zmult_le_compat_r; lia. }
      lia.
    Qed.

    Lemma limbwidth_good : 0 < limbwidth_den <= limbwidth_num.
    Proof. remember n_small. cbv [limbwidth_den limbwidth_num]. lia. Qed.

    Local Notation wprops := (@wprops limbwidth_num limbwidth_den limbwidth_good).

    Lemma Qceiling_diff x y : Qfloor (x - y) <= Qceiling x - Qceiling y.
    Proof.
      assert (H: Qfloor (x - y) + Qceiling y <= Qceiling x).
      - replace (Qceiling x) with (Qceiling (x - y + y))%Q.
        + apply QUtil.add_floor_l_le_ceiling.
        + cbv [Qminus].
          rewrite <- Qplus_assoc. rewrite (Qplus_comm (-y) y).
          rewrite Qplus_opp_r. rewrite Qplus_0_r. reflexivity.
      - lia.
    Qed.

    Lemma Qopp_distr_mul_r x y : (- (x * y) == x * -y)%Q.
    Proof. cbv [Qmult Qopp Qeq]. simpl. lia. Qed.      
      
    Lemma s_small : forall i : nat, (weight (i + n) / weight i) mod s = 0.
    Proof.
      intros i. repeat rewrite (ModOps.weight_ZQ_correct _ _ limbwidth_good).
      rewrite <- Z.pow_sub_r; try lia.
      - rewrite <- s_power_of_2. apply Modulo.Z.mod_same_pow. split.
        + apply Z.log2_nonneg.
        + remember (_ * (i + n)%nat)%Q as x. remember (_ * i)%Q as y.
          apply (Z.le_trans _ (Qfloor (x - y))).
          -- subst. cbv [Qminus]. rewrite Qopp_distr_mul_r. rewrite <- Qmult_plus_distr_r.
             rewrite <- inject_Z_opp. rewrite <- inject_Z_plus.
             replace (Z.of_nat (i + n) + - Z.of_nat i) with (Z.of_nat n) by lia.
             replace (Z.log2 s) with (Qfloor (inject_Z (Z.log2 s))).
             ++ apply Qfloor_resp_le. rewrite Qmult_comm.
                apply (Qle_trans _ (inject_Z (n * limbwidth_num / limbwidth_den)))%Z.
                --- rewrite <- Zle_Qle. apply weight_big.
                --- cbv [Qdiv]. rewrite Zdiv_Qdiv.
                    apply (Qle_trans _ ((n * limbwidth_num)%Z / limbwidth_den)).
                    +++ apply Qfloor_le.
                    +++ rewrite inject_Z_mult. rewrite Qmult_assoc. apply Qle_refl.
             ++ apply Qfloor_Z.
          -- apply Qceiling_diff.
      - remember limbwidth_good as H eqn:clearMe; clear clearMe. split.
        + replace 0 with (Qceiling 0) by reflexivity. apply Qceiling_resp_le.
          apply Qmult_le_0_compat.
          -- cbv [Qdiv]. apply Qmult_le_0_compat.
             ++ replace 0%Q with (inject_Z 0) by reflexivity. rewrite <- Zle_Qle. lia.
             ++ apply Qinv_le_0_compat. replace 0%Q with (inject_Z 0) by reflexivity.
                rewrite <- Zle_Qle. lia.
          -- replace 0%Q with (inject_Z 0) by reflexivity. rewrite <- Zle_Qle. lia.
        + apply Qceiling_resp_le. rewrite Qmult_comm. rewrite (Qmult_comm (_ / _)).
          apply Qmult_le_compat_r.
          -- rewrite <- Zle_Qle. lia.
          -- cbv [Qdiv]. apply Qmult_le_0_compat.
             ++ replace 0%Q with (inject_Z 0) by reflexivity. rewrite <- Zle_Qle. lia.
             ++ apply Qinv_le_0_compat. replace 0%Q with (inject_Z 0) by reflexivity.
                rewrite <- Zle_Qle. lia.
    Qed.
      
    Lemma s_gt_0 : 0 < s.
      assert (H: s <= 0 \/ 0 < s) by lia. destruct H as [H|H].
      - apply Z.log2_nonpos in H. lia.
      - assumption.
    Qed.

    Lemma s_big : weight (n - 1) <= s.
    Proof.
      rewrite (ModOps.weight_ZQ_correct _ _ limbwidth_good).
      cbv [limbwidth_num limbwidth_den]. 
      remember (Z.log2_spec _ s_gt_0) as H eqn:clearMe. clear clearMe.
      destruct H as [H _].
      apply (Z.le_trans _ (2 ^ Z.log2 s)); try apply H.
      apply Z.pow_le_mono_r; try lia.
      rewrite Zle_Qle. cbv [Qdiv]. rewrite <- (Qmult_assoc _ (Qinv _)).
      rewrite (Qmult_comm (Qinv _)). rewrite Nat2Z.inj_sub; try lia. simpl. cbv [Z.sub].
      rewrite inject_Z_plus. simpl. cbv [Qminus]. rewrite Qmult_inv_r.
      - rewrite <- inject_Z_plus. rewrite Qmult_1_r. rewrite Qceiling_Z.
        rewrite <- Zle_Qle. remember (Z.le_log2_up_succ_log2 s). lia.
      - replace 0%Q with (inject_Z 0) by reflexivity. rewrite inject_Z_injective. lia.
    Qed.

    Lemma weight_lt_width : forall i: nat, (weight i * 2^register_width) mod weight (i + 1)%nat = 0.
    Proof.
      intros i. repeat rewrite (ModOps.weight_ZQ_correct _ _ limbwidth_good).
      remember limbwidth_good eqn:clearMe; clear clearMe.
      rewrite <- Z.pow_add_r; try lia.
      - apply Modulo.Z.mod_same_pow. split.
        + remember (_ / _ * _)%Q as x. replace 0 with (Qceiling 0%Z) by reflexivity.
          apply Qceiling_resp_le. subst. replace (inject_Z 0) with 0%Q by reflexivity.
          cbv [Qdiv]. apply Qmult_le_0_compat.
          -- apply Qmult_le_0_compat.
             ++ replace 0%Q with (inject_Z 0) by reflexivity. rewrite <- Zle_Qle. lia.
             ++ apply Qinv_le_0_compat. replace 0%Q with (inject_Z 0) by reflexivity.
                rewrite <- Zle_Qle. lia.
          -- replace 0%Q with (inject_Z 0) by reflexivity. rewrite <- Zle_Qle. lia.
        + rewrite Nat2Z.inj_add. rewrite inject_Z_plus. rewrite Qmult_plus_distr_r.
          remember (_ / _ * i)%Q as x. remember (_ / _ * 1%nat)%Q as y.
          apply (Z.le_trans _ (Qceiling x + Qceiling y)).
          -- apply QUtil.Qceiling_le_add.
          -- assert (Qceiling y <= register_width); try lia.
             replace (Z.of_nat register_width) with (Qceiling (inject_Z register_width)).
             ++ apply Qceiling_resp_le. subst.
                replace (inject_Z (Z.of_nat 1)) with 1%Q by reflexivity.
                rewrite Qmult_1_r. apply Qle_shift_div_r.
                --- remember limbwidth_good. replace 0%Q with (inject_Z 0) by reflexivity.
                    rewrite <- Zlt_Qlt. lia.
                --- rewrite <- inject_Z_mult. rewrite <- Zle_Qle.
                    cbv [limbwidth_num limbwidth_den]. lia.
             ++ apply Qceiling_Z.
      - replace 0 with (Qceiling 0) by reflexivity. apply Qceiling_resp_le.
        apply Qmult_le_0_compat.
        + cbv [Qdiv]. apply Qmult_le_0_compat.
          -- replace 0%Q with (inject_Z 0) by reflexivity. rewrite <- Zle_Qle. lia.
          -- apply Qinv_le_0_compat. replace 0%Q with (inject_Z 0) by reflexivity.
             rewrite <- Zle_Qle. lia.
        + replace 0%Q with (inject_Z 0) by reflexivity. rewrite <- Zle_Qle. lia.
    Qed.

    Definition eval_mulmod := eval_mulmod s c register_width n last_reduction weight p_nz n_gteq_4 wprops s_small s_big weight_lt_width.
    Definition eval_squaremod := eval_squaremod s c register_width n last_reduction weight p_nz n_gteq_4 wprops s_small s_big weight_lt_width.
  End dettman_multiplication_mod_ops.
End dettman_multiplication_mod_ops.

Module dettman_multiplication_with_adk_mod_ops.
  Section dettman_multiplication_with_adk_mod_ops.
    Import DettmanMultiplication.
    Local Open Scope Z_scope.
    Context
        (s : Z)
        (c : Z)
        (register_width : nat)
        (n : nat)
        (limbwidth : nat)
        (last_reduction : nat)
        (p_nz : s - c <> 0)
        (n_gteq_4 : (4 <= n)%nat)
        (limbwidth_nz : 0 <> limbwidth)
        (s_power_of_2 : 2 ^ (Z.log2 s) = s)
        (s_big' : (n - 1) * limbwidth <= Z.log2 s)
        (s_small' : Z.log2 s <= n * limbwidth)
        (registers_big : limbwidth <= register_width).

    Definition weight := weight limbwidth 1.

    Lemma limbwidth_good : 0 < 1 <= limbwidth.
    Proof. remember limbwidth_nz. lia. Qed.
    Local Notation wprops := (@wprops limbwidth 1 limbwidth_good).

    Lemma weight_simple : forall i, weight i = 2 ^ (i * limbwidth).
    Proof.
      intros i. rewrite (ModOps.weight_ZQ_correct _ _ limbwidth_good).
      cbv [Qdiv]. replace (Qinv (inject_Z 1)) with 1%Q by reflexivity.
      rewrite Qmult_1_r. rewrite <- inject_Z_mult. rewrite Qceiling_Z.
      f_equal. lia.
    Qed.

    Definition adk_mulmod := adk_mulmod s c register_width last_reduction n weight.

    Lemma weight_friendly : forall i j : nat, weight i * weight j = weight (i + j).
    Proof.
      intros i j. repeat rewrite weight_simple. rewrite <- Z.pow_add_r; try lia. f_equal. lia.
    Qed.
  
    Definition eval_adk_mulmod := eval_adk_mulmod s c register_width n last_reduction weight p_nz n_gteq_4 wprops weight_friendly.
  End dettman_multiplication_with_adk_mod_ops.
End dettman_multiplication_with_adk_mod_ops.
Module Export Hints.
  Import dettman_multiplication_mod_ops.
  Import dettman_multiplication_with_adk_mod_ops.
#[global]
  Hint Rewrite eval_mulmod using solve [ auto with zarith | congruence ] : push_eval.
#[global]
  Hint Rewrite eval_squaremod using solve [ auto with zarith | congruence ] : push_eval.
#[global]
  Hint Rewrite eval_adk_mulmod using solve [ auto with zarith | congruence ] : push_eval.
End Hints.

Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ADK.
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
      
      Definition adk_mulmod (x y : list Z) : list Z :=
       (*Positional.from_associational weight n (Positional.to_associational weight n ( *)ident_adk_mul n x y(* ) ) *)
          (*(Associational.mul
             (Positional.to_associational weight n x)
             (Positional.to_associational weight n y))*).

      Theorem eval_adk_mulmod (*a_bounds b_bounds*) a b :
        (Positional.eval weight n (adk_mulmod (*a_bounds b_bounds*) a b)) mod (s - c') =
          (Positional.eval weight n a * Positional.eval weight n b) mod (s - c').
      Proof.
        (*cbv [adk_mulmod]. rewrite <- c_correct. rewrite eval_reduce_carry_borrow.
        - Search to_associational. rewrite eval_to_associational. f_equal. 
          Check eval_reduce_carry_borrow. Search adk_mul.*)
      Admitted. Check adk_mulmod.
    End WithADK.
  End DettmanMultiplication.  
End DettmanMultiplication.
Require Import Crypto.Language.API.
Import
  Language.Compilers
  Language.API.Compilers.

Import Language.API.Compilers.API.
Import pmul.
Import DettmanMultiplication.
Locate "Reify".
Check adk_mulmod.
Print pmul.adk_mul'.
Print adk_mul_prod_at_i. Print nth_reifiable. Check adk_mulmod.
Print adk_mulmod. Check reduce_carry_borrow. Print reduce_carry_borrow.
Compute (ltac: (let r := Reify (adk_mulmod)
                            in
                  exact r)).

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
    Qed. Print adk_mulmod.

    Definition adk_mulmod (s c : Z) (register_width n limbwidth last_reduction : nat) := adk_mulmod n.

    Lemma weight_friendly : forall i j : nat, weight i * weight j = weight (i + j).
    Proof.
      intros i j. repeat rewrite weight_simple. rewrite <- Z.pow_add_r; try lia. f_equal. lia.
    Qed.
  
    Definition eval_adk_mulmod := eval_adk_mulmod s c register_width n last_reduction weight p_nz n_gteq_4 wprops weight_friendly.
  End dettman_multiplication_with_adk_mod_ops.
  Print eval_adk_mulmod.
  Print DettmanMultiplication.adk_mulmod. Print weight.
  (*Definition adk_mulmod (s c : Z) (register_width n limbwidth last_reduction : nat) :=
   DettmanMultiplication.adk_mulmod n weight.*)
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

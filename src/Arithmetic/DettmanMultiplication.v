Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.ModOps.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.Program.Wf.
Require Import Crypto.Util.LetIn.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZRange.


Definition value_in_range (x : Z) (r : zrange) (H : is_bounded_by_bool x r = true) : Z := x.

Local Open Scope list_scope.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.

Section adk_mul.
  Context (weight : nat -> Z).
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
       This last formula will be particularly nice if we precompute the values \sum_{j = 0}^i x_j y_j, as i ranges from 0 to n - 1.
     *)
      
    Definition nth_reifiable' {X} (n : Z) (l : list X) (default : X) : Z*X :=
      fold_right (fun next n_nth => (fst n_nth - 1, if (fst n_nth =? 0) then next else (snd n_nth))) (Z.of_nat (length l) - n - 1, default) l.

    Compute (nth_reifiable' 0 [7; 2; 3] (-1)).
    

    Lemma nth_reifiable'_spec {X} (n : Z) (l : list X) (default : X) :
      nth_reifiable' n l default = (-n - 1, if 0 <=? n then nth (Z.to_nat n) l default else default).
    Proof.
      cbv [nth_reifiable']. generalize dependent n. induction l as [| x l' IHl']; intros n.
      - simpl. f_equal. destruct (0 <=? n); destruct (Z.to_nat n); reflexivity.
      - replace (Z.of_nat (length (x :: l')) - n - 1) with
          (Z.of_nat (length l') - (n - 1) - 1).
        + simpl. rewrite IHl'. simpl. f_equal; try lia. destruct (_ =? 0) eqn:E1; destruct (0 <=? n - 1) eqn:E2; destruct (0 <=? n) eqn:E3; destruct (Z.to_nat n) eqn:E4; try lia; try reflexivity.
          f_equal. lia.
        + replace (length (x :: l')) with (1 + length l')%nat by reflexivity. lia.
    Qed.

    Definition nth_reifiable {X} (n : nat) (l : list X) (default : X) : X :=
      snd (nth_reifiable' (Z.of_nat n) l default).
    
   Lemma nth_reifiable_spec {X} (n : nat) (l : list X) (default : X) :
      nth_reifiable n l default = nth n l default.
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

    Search seq.
    Definition seqZ a b :=
      map (fun x => Z.of_nat x + a) (seq 0 (Z.to_nat (1 + b - a))).

    Definition first_summation (n : nat) (x y : list Z) : list (Z*Z) :=
      flat_map (fun i =>
                  map (fun j => (weight (Z.to_nat i) * weight (Z.to_nat j), (nthZ i x 0 - nthZ j x 0) * (nthZ j y 0 - nthZ i y 0)))
                    (seqZ 0 (i - 1)))
        (seqZ 1 (Z.of_nat n - 1)).

    Locate "dlet".

    Definition second_summation' (n : nat) (products f : list Z) := 
      let high_part : Z*Z := (weight (n - 1) * weight (n - 1), (nthZ (Z.of_nat (n - 1)) products 0)) in
      let low_part : list (Z*Z) := map (fun i => (weight (Z.to_nat i), (nthZ i f 0) - (nthZ (i - Z.of_nat n) f 0))) (seqZ 0 (2*Z.of_nat n - 3)) in
      low_part ++ [high_part].

    Print fold_right.
    Print list_rect.

    Fixpoint sums (x : list Z) (a : Z) : list Z :=
      match x with
      | [] => [a]
      | c :: x' => dlet y := a + c in
          y :: sums x' y
      end.

    Eval cbn [sums] in (sums [1; 2; 3] 7).
    Print list_rect.
    (*Goal (sums = list_rect (fun l => Z -> list Z) (fun a => [a]) (fun c x' rec a => dlet y := a + c in y :: rec y)).*)
    Definition sums' := list_rect (fun l => Z -> list Z) (fun a => [a]) (fun c x' rec a => dlet y := a + c in y :: rec y).
    Lemma sums_nil a : sums' [] a = [a].
    Proof. reflexivity. Qed.

    Print fold_right.
    Print list_rect.
    Check Let_In.

    (*Definition second_summation (n : nat) (x y : list Z) : list (Z*Z) :=
      dlet high_product : Z := (nthZ (Z.of_nat n - 1) x 0) * (nthZ (Z.of_nat n - 1) y 0) in
          let products : list Z := map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (Z.of_nat n - 2)) ++ [high_product] in
          (list_rect
             (fun _ => list Z -> list (Z*Z))
             (fun f => second_summation' n products (rev f))
             (fun i _ g => fun f' => Let_In (P:=fun _ => _) (((nthZ 0 f' 0) + (nthZ i products 0)) :: f') g) 
             (seqZ 0 (2*Z.of_nat n - 3))) [].*)
    
    Definition second_summation (n : nat) (x y : list Z) (*: list (Z*Z)*) :=
      dlet high_product : Z := (nthZ (Z.of_nat n - 1) x 0) * (nthZ (Z.of_nat n - 1) y 0) in
      let products : list Z := map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (Z.of_nat n - 2)) ++ [high_product] in
      let f_backwards : list Z := (fold_right (fun i f' => (*d*)let prev := (nthZ 0 f' 0) in prev + (nthZ i products 0) :: f') [] (rev (seqZ 0 (2*Z.of_nat n - 3)))) in
     (* let f_ := rev f_backwards in
      let f0 := nthZ 0 f_ 0 in
      let f := f0 :: map (fun i => nthZ i f_ 0) (seqZ 1 (Z.of_nat (length f_) - 1)) in*)
      let nthZf := fun i default => nthZ (Z.of_nat (length f_backwards) - i - 1) f_backwards default in
      let high_part : Z*Z := (weight (n - 1) * weight (n - 1), (nthZ (Z.of_nat (n - 1)) products 0)) in
      let low_part : list (Z*Z) := map (fun i => (weight (Z.to_nat i), (nthZf i 0) - (nthZf (i - Z.of_nat n) 0))) (seqZ 0 (2*Z.of_nat n - 3)) in
      low_part ++ [high_part].
    
    (*Definition second_summation (n : nat) (x y : list Z) : list (Z*Z) :=
      dlet high_product : Z := (nthZ (Z.of_nat n - 1) x 0) * (nthZ (Z.of_nat n - 1) y 0) in
      let products : list Z := map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (Z.of_nat n - 2)) ++ [high_product] in
      (list_rect
         (fun x => list Z -> list (Z*Z))
         (fun f => second_summation' n products (rev f))
         (fun i is g => fun f' => Let_In (P:=fun a => list (Z*Z)) (((nthZ 0 f' 0) + (nthZ i products 0)) :: f') g) 
         (seqZ 0 (2*Z.of_nat n - 3))) [].
    Check Let_In.
    Print fold_right.
    Definition fs (n : nat) (x y : list Z) : list Z :=
      dlet high_product : Z := (nthZ (Z.of_nat n - 1) x 0) * (nthZ (Z.of_nat n - 1) y 0) in
          let products : list Z := map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (Z.of_nat n - 2)) ++ [high_product] in
          dlet f : list Z := (fold_right (fun i f' => dlet prev := (nthZ 0 f' 0) in prev + (nthZ i products 0) :: f') [] (seqZ 0 (2*Z.of_nat n - 3))) in*)
    
    (*Check (list_rect (fun _ => list Z -> list (Z*Z)) ).

    Definition second_summation (n : nat) (x y : list Z) : list (Z*Z) :=
      dlet high_product : Z := (nthZ (Z.of_nat n - 1) x 0) * (nthZ (Z.of_nat n - 1) y 0) in
      let products : list Z := map (fun i => (nthZ i x 0) * (nthZ i y 0)) (seqZ 0 (Z.of_nat n - 2)) ++ [high_product] in
            (fold_right
              (fun i g => fun f' => Let_In (P:=fun _ => _) (((nthZ 0 f' 0) + (nthZ i products 0)) :: f') g) 
              (fun f => second_summation' n products (rev f))
              (seqZ 0 (2*Z.of_nat n - 3))) [].*)

    Definition adk_mul' (n : nat) (x y : list Z) : list (Z*Z) :=
      first_summation n x y ++ second_summation n x y.

    Compute (Z.lxor (-8) (-8)).
    Check Z.abs.
    Compute (Z.land (8) (-1)).
    
    Search Z.shiftr.

    (*Lemma Zleb_reifiable_spec (a b : Z) :
      Zleb_reifiable a b = Z.leb a b.
    Proof. cbv [Zleb_reifiable]. lia. Qed.*)

    (* condition should be either 1 or 0. *)
    Definition if_then_else' (condition : Z) (then_value : Z) (else_value : Z) : Z :=
      if condition =? 1 then then_value else else_value.

    Definition if_then_else (condition : Z) (then_value : Z) (else_value : Z) : Z :=
      condition * then_value + (1 - condition) * else_value.

    Definition ZZ_is_bounded_by_bool (x : Z) (bounds : Z*Z) : bool := true.
      (*((Z.ltz (fst bounds - 1) x) && (Z.ltz x (snd bounds + 1)))%bool.*)
    
    Definition is_bounded_by (l : list Z) (bounds : list (Z*Z)) : bool :=
      fold_right andb true
        (map (fun x_bound => ZZ_is_bounded_by_bool (fst x_bound) (snd x_bound))
           (combine l bounds)).

    Definition is_lower_bounded_by (bounds : list (Z*Z)) (xs : list Z) : bool :=
      fold_right andb true
        (map (fun bound_x => snd bound_x <=? fst (fst bound_x))
           (combine bounds xs)).

    (* if everything is nonnegative, then the output is nondecreasing in the inputs *)
    Definition output_bounds (n : nat) (x_bounds y_bounds : list (Z*Z)) : list (Z*Z) :=
      let lower_bounds := Positional.from_associational weight (2*n - 2 + 1)
                            (adk_mul' n (map fst x_bounds) (map fst y_bounds)) in
      let upper_bounds := Positional.from_associational weight (2*n - 2 + 1)
                            (adk_mul' n (map snd x_bounds) (map snd y_bounds)) in
      map (fun lower_upper => (fst lower_upper, snd lower_upper))
        (combine lower_bounds upper_bounds).

    Compute (true && true)%bool.
    Print value_in_range.
    Lemma nonsense x r : is_bounded_by_bool x (Build_zrange (fst r) (snd r)) = true. Proof. Admitted.
   
    Definition adk_mul'' (n : nat) (x_bounds y_bounds : list (Z*Z)) (x y : list Z) : list Z :=
      (*map (fun t_e => if_then_else (is_lower_bounded_by x_bounds (repeat 0 n) &&
           is_lower_bounded_by y_bounds (repeat 0 n) &&
           ZZ_is_bounded_by_bool (nthZ 0 x 0) (nthZ 0 x_bounds (0, 0)) &&
           is_bounded_by y y_bounds)%bool  Z.ltz (nthZ 0 x 0) (2^29)) (fst t_e) (snd t_e))

        (combine*) 
           (map (fun r_bounds => let r := fst r_bounds in
                                 let bounds := snd r_bounds in
                                 Z.land (value_in_range r (Build_zrange (fst bounds) (snd bounds)) (nonsense r bounds)) (Z.ones (Z.log2_up (snd bounds))))
              (combine
                  (Positional.from_associational weight (2*n - 2 + 1) (dedup_weights (adk_mul' n x y)))
                  (output_bounds n x_bounds y_bounds)
              )
           )
        (*Positional.from_associational weight n
          (Associational.mul (Positional.to_associational weight n x)
             (Positional.to_associational weight n y))
           (repeat 0 (2*n - 2 + 1))*)
        .

    Definition adk_mul (n : nat) (x y : list Z) : list Z :=
      adk_mul'' n (repeat (0, 2^29 - 1) 10) (repeat (0, 2^29 - 1) 10) x y.
End adk_mul.

Definition x := [3; 4; 123; 93].
  Definition y := [543; 123; 64; 1].
  Definition weight_ := (fun i => 2^Z.of_nat i).
  Definition n := 4%nat.
  Compute (adk_mul weight_ n x y).
  Compute (dedup_weights
          (Associational.mul (Positional.to_associational weight_ n x)
             (Positional.to_associational weight_ n y))).

Module DettmanMultiplication.
  Section DettmanMultiplication.
    Context
        (s : Z)
        (c_ : list (Z*Z))
        (register_width : nat)
        (limbs : nat)
        (weight: nat -> Z)
        (p_nz : s - Associational.eval c_ <> 0)
        (limbs_gteq_4 : (4 <= limbs)%nat) (* Technically we only need 2 <= limbs to get the proof to go through, but it doesn't make any sense to try to do this with less than three limbs.
                                           Note that having 4 limbs corresponds to zero iterations of the "loop" function defined below. *)
        (s_small : forall i: nat, (weight (i + limbs)%nat / weight i) mod s = 0)
        (s_big : weight (limbs - 1)%nat <= s)
        (weight_lt_width : forall i: nat, (weight i * 2^register_width) mod weight (i + 1)%nat = 0)
        (wprops : @weight_properties weight)
        
        (weight_0 := weight_0 wprops)
        (weight_positive := weight_positive wprops)
        (weight_multiples := weight_multiples wprops)
        (weight_divides := weight_divides wprops).

    Local Notation c' := (Associational.eval c_).

    Definition c := Positional.to_associational weight limbs
                      (Positional.simple_encode weight limbs c').        
      
    Lemma s_positive : s > 0.
    Proof. remember (weight_positive (limbs - 1)). lia. Qed.

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
      (j = i + limbs)%nat ->
      weight j / weight i mod s = 0.
    Proof. intros H. subst. apply s_small. Qed.

    Lemma s_big' : s / weight (limbs - 1) <> 0.
    Proof. remember (weight_positive (limbs - 1)). apply div_nz; lia. Qed.

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

    Lemma assoc_eval : Associational.eval [(1, c')] = c'.
    Proof. cbv [Associational.eval]. simpl. destruct (fold_right _); reflexivity. Qed.

    Lemma c_correct : Associational.eval c = c'.
    Proof.
      cbv [c]. rewrite eval_to_associational.
      replace (s - c') with (s - Associational.eval [(1, c')]).
      - apply eval_simple_encode; auto with arith. lia.
      - rewrite assoc_eval. lia.
    Qed.
    
    Lemma p_nz' : s - Associational.eval c <> 0.
    Proof. rewrite c_correct. auto with arith. Qed.    

    Hint Resolve p_nz' : arith.
    
    Local Open Scope nat_scope.

    Definition reduce' x1 x2 x3 x4 x5 := dedup_weights (reduce_one x1 x2 x3 x4 x5).
    Definition carry' x1 x2 x3 := dedup_weights (Associational.carry x1 x2 x3).

    Definition loop_body i before :=
      
      let from1 := weight (i + limbs) in
      let to1 := weight (i + limbs + 1) in
      let middle1 := carry' from1 (to1 / from1) before in

      let from2 := weight (i + limbs) in
      let to2 := weight i in
      let middle2 := reduce' s from2 (from2 / to2) c middle1 in

      let from := weight i in
      let to := weight (i + 1) in
      let after := carry' from (to / from) middle2 in
      after.

    Hint Rewrite eval_reduce_one Associational.eval_carry eval_dedup_weights: push_eval.

    Lemma eval_loop_body i before :
      (Associational.eval (loop_body i before) mod (s - Associational.eval c) =
         Associational.eval before mod (s - Associational.eval c))%Z.
    Proof. cbv [loop_body carry' reduce']. autorewrite with push_eval; auto with arith. Qed.

    Definition loop start :=
      fold_right loop_body start (rev (seq 1 (limbs - 2 - 1 - 1))).

    Definition loop32 start :=
      fold_right loop_body start (rev (seq 1 (limbs - 2 - 2 - 1))).
      
    Lemma eval_loop start :
      ((Associational.eval (loop start)) mod (s - Associational.eval c) = (Associational.eval start) mod (s - Associational.eval c))%Z.
    Proof.
      cbv [loop]. induction (rev (seq 1 (limbs - 2 - 1 - 1))) as [| i l' IHl'].
      - reflexivity.
      - simpl. rewrite eval_loop_body. apply IHl'.
    Qed.

     Lemma eval_loop32 start :
      ((Associational.eval (loop32 start)) mod (s - Associational.eval c) = (Associational.eval start) mod (s - Associational.eval c))%Z.
    Proof.
      cbv [loop32]. induction (rev (seq 1 (limbs - 2 - 2 - 1))) as [| i l' IHl'].
      - reflexivity.
      - simpl. rewrite eval_loop_body. apply IHl'.
    Qed.

    Definition reduce_carry_borrow r0 :=
      let l := limbs in
      let r0' := dedup_weights r0 in
      
      let r1 := carry' (weight (2 * l - 2)) (2^register_width) r0' in
      
      let from2 := weight (2 * l - 2) in
      let to2 := weight (l - 2) in
      let r2 := reduce' s from2 (from2 / to2) c r1 in

      let from3 := weight (l - 2) in
      let to3 := weight (l - 1) in
      let r3 := carry' from3 (to3 / from3) r2 in
      
      let from4 := Z.mul (weight (2 * l - 2)) (2^register_width) in
      let to4 := weight (l - 1) in
      let r4 := reduce' s from4 (from4 / to4) c r3 in

      let from5 := weight (l - 1) in
      let to5 := weight l in
      let r5 := carry' from5 (to5 / from5) r4 in

      let from6 := weight (l - 1) in
      let to6 := s in
      let r6 := carry' from6 (to6 / from6) r5 in

      let from7 := weight l in
      let to7 := weight (l + 1) in
      let r7 := carry' from7 (to7 / from7) r6 in

      let from8 := weight l in
      let to8 := s in
      let r8 := borrow from8 (from8 / to8) r7 in
      
      let r8' := dedup_weights r8 in
      
      let r9 := reduce' s s s c r8' in

      let from10 := weight 0 in
      let to10 := weight 1 in
      let r10 := carry' from10 (to10 / from10) r9 in
      
      let r11 := loop r10 in
      
      (* here I've pulled out the final iteration of the loop to do
         the special register_width carry. *)
      (* begin final loop iteration *)
      let i0 := l - 2 - 1 in
      
      let rloop1 := carry' (weight (i0 + limbs)) (2^register_width) r11 in

      let fromLoop2 := weight (i0 + limbs) in
      let toLoop2 := weight i0 in
      let rloop2 := reduce' s fromLoop2 (fromLoop2 / toLoop2) c rloop1 in

      let fromLoop3 := weight i0 in
      let toLoop3 := weight (i0 + 1) in
      let rloop3 := carry' fromLoop3 (toLoop3 / fromLoop3) rloop2 in
      (* end final loop iteration*)
      
      let from12 := Z.mul (weight (i0 + limbs)) (2^register_width) in
      let to12 := weight (i0 + 1) in
      let r12 := reduce' s from12 (from12 / to12) c rloop3 in

      let from13 := weight (l - 2) in
      let to13 := weight (l - 1) in
      let r13 := carry' from13 (to13 / from13) r12 in

      Positional.from_associational weight l r13.

    (* should write some comment here about what this is, and how it differs from the first one *)
    Definition reduce_carry_borrow32 r0 :=
      let l := limbs in
      
      let r0' := dedup_weights r0 in
      
      (* begin a loop iteration *)
      let from01 := weight (2 * l - 3) in
      let to01 := weight (2 * l - 2) in
      let r01 := carry' from01 (to01 / from01) r0' in

      let from02 := weight (2 * l - 3) in
      let to02 := weight (l - 3) in
      let r02 := reduce' s from02 (from02 / to02) c r01 in

      let from03 := weight (l - 3) in
      let to03 := weight (l - 2) in
      let r03 := carry' from03 (to03 / from03) r02 in
      
      (* end a loop iteration *)
      
      let r1 := carry' (weight (2 * l - 2)) (2^register_width) r03 in
      
      let from2 := weight (2 * l - 2) in
      let to2 := weight (l - 2) in
      let r2 := reduce' s from2 (from2 / to2) c r1 in

      let from3 := weight (l - 2) in
      let to3 := weight (l - 1) in
      let r3 := carry' from3 (to3 / from3) r2 in
      
      let from4 := Z.mul (weight (2 * l - 2)) (2^register_width) in
      let to4 := weight (l - 1) in
      let r4 := reduce' s from4 (from4 / to4) c r3 in

      let from5 := weight (l - 1) in
      let to5 := weight l in
      let r5 := carry' from5 (to5 / from5) r4 in

      let from6 := weight (l - 1) in
      let to6 := s in
      let r6 := carry' from6 (to6 / from6) r5 in

      let from7 := weight l in
      let to7 := weight (l + 1) in
      let r7 := carry' from7 (to7 / from7) r6 in

      let from8 := weight l in
      let to8 := s in
      let r8 := borrow from8 (from8 / to8) r7 in
      
      let r8' := dedup_weights r8 in
      
      let r9 := reduce' s s s c r8' in

      let from10 := weight 0 in
      let to10 := weight 1 in
      let r10 := carry' from10 (to10 / from10) r9 in
      
      let r11 := loop32 r10 in
      
      (* here I've pulled out the final iteration of the loop to do
         the special register_width carry. *)
      (* begin final loop iteration *)
      let i0 := l - 2 - 2 (* this changed from 64 *) in
      
      let rloop1 := carry' (weight (i0 + limbs)) (2^register_width) r11 in

      let fromLoop2 := weight (i0 + limbs) in
      let toLoop2 := weight i0 in
      let rloop2 := reduce' s fromLoop2 (fromLoop2 / toLoop2) c rloop1 in

      let fromLoop3 := weight i0 in
      let toLoop3 := weight (i0 + 1) in
      let rloop3 := carry' fromLoop3 (toLoop3 / fromLoop3) rloop2 in
      (* end final loop iteration*)

      let from12 := Z.mul (weight (i0 + limbs)) (2^register_width) in (*2l - 2 - 1 = i0 + limbs*)
      let to12 := weight (i0 + 1) in (* i0 + 1 = l - 2 *)
      let r12 := reduce' s from12 (from12 / to12) c rloop3 in (*from12 / to12 = 266.*)

      let from12A := weight (l - 3) in
      let to12A := weight (l - 2) in
      let r12A := carry' from12A (to12A / from12A) r12 in

      let from13 := weight (l - 2) in
      let to13 := weight (l - 1) in
      let r13 := carry' from13 (to13 / from13) r12A in

      Positional.from_associational weight l r13.

    Definition mulmod a b :=
      let a_assoc := Positional.to_associational weight limbs a in
      let b_assoc := Positional.to_associational weight limbs b in
      let r0 := Associational.mul a_assoc b_assoc in
      reduce_carry_borrow r0.

    Definition squaremod a :=
      let a_assoc := Positional.to_associational weight limbs a in
      let r0 := Associational.square a_assoc in
      reduce_carry_borrow r0.

    Definition mulmod32 a b :=
      let r0 := adk_mul weight limbs a b in
      reduce_carry_borrow32 (Positional.to_associational weight (2*limbs-2+1) r0).

    Definition squaremod32 a :=
      let a_assoc := Positional.to_associational weight limbs a in
      let r0 := Associational.square a_assoc in
      reduce_carry_borrow32 r0.

    Hint Rewrite Positional.eval_from_associational Positional.eval_to_associational eval_borrow eval_loop eval_loop32: push_eval.
    Hint Resolve Z_mod_same_full : arith.

    Local Open Scope Z_scope.

    Lemma reduction_divides i : weight (limbs + i - 1) * 2^register_width / weight i mod s = 0.
    Proof.
      rewrite Divide.Z.mod_divide_full. apply (Z.divide_trans _ (weight (limbs + i) / weight i)).
      - rewrite <- Divide.Z.mod_divide_full. rewrite (Nat.add_comm limbs i). apply s_small.
      - apply Z.divide_div.
        + remember (weight_positive i). lia.
        + rewrite <- Divide.Z.mod_divide_full. apply Weight.weight_multiples_full; try assumption.
          lia.
        + rewrite <- Divide.Z.mod_divide_full.
          replace (weight (limbs + i)) with (weight (limbs + i - 1 + 1)).
          -- apply weight_lt_width.
          -- f_equal. lia.
    Qed.

    Lemma reduction_divides' (i j : nat) :
      (j = limbs + i - 1)%nat ->
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

    Lemma s_small_particular : weight limbs mod s = 0.
    Proof.
      replace (weight limbs) with (weight limbs / weight 0).
      - apply s_small'; lia.
      - Z.div_mod_to_equations. lia.
    Qed.
      
    Lemma eval_reduce_carry_borrow r0 :
      (Positional.eval weight limbs (reduce_carry_borrow r0)) mod (s - Associational.eval c) =
      (Associational.eval r0) mod (s - Associational.eval c).
    Proof.
      cbv [reduce_carry_borrow carry' reduce']. autorewrite with push_eval; auto with arith.
      all: try apply weight_div_nz; try lia.
      all: try apply weight_mod_quotient_zero; try lia.
      all: try apply reduction_divides'; try lia.
      all: try apply weight_prod_div_nz; try lia.
      all: try apply s_small'; try lia.
      all: try apply mod_quotient_zero; try apply divisible_implies_nonzero; try apply s_small_particular; try apply weight_positive.
      all: try apply weight_prod_mod_zero; try lia.
      all: try (remember (weight_positive limbs); lia).
      all: try (remember s_positive; lia).
      all: try apply weight_nz.
    Qed.

    Lemma eval_reduce_carry_borrow32 r0 :
      (Positional.eval weight limbs (reduce_carry_borrow32 r0)) mod (s - Associational.eval c) =
      (Associational.eval r0) mod (s - Associational.eval c).
    Proof.
      cbv [reduce_carry_borrow32 carry' reduce']. autorewrite with push_eval; auto with arith.
      all: try apply weight_div_nz; try lia.
      all: try apply weight_mod_quotient_zero; try lia.
      all: try apply reduction_divides'; try lia.
      all: try apply weight_prod_div_nz; try lia.
      all: try apply s_small'; try lia.
      all: try apply mod_quotient_zero; try apply divisible_implies_nonzero; try apply s_small_particular; try apply weight_positive.
      all: try apply weight_prod_mod_zero; try lia.
      all: try (remember (weight_positive limbs); lia).
      all: try (remember s_positive; lia).
      all: try apply weight_nz.
    Qed.
        
    Hint Rewrite eval_reduce_carry_borrow eval_reduce_carry_borrow32 : push_eval.

    Theorem eval_mulmod a b :
      (Positional.eval weight limbs (mulmod a b)) mod (s - c') =
      (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - c').
    Proof.
      cbv [mulmod]. rewrite <- c_correct. autorewrite with push_eval. reflexivity.
    Qed.

    Theorem eval_squaremod a :
      (Positional.eval weight limbs (squaremod a)) mod (s - c') =
      (Positional.eval weight limbs a * Positional.eval weight limbs a) mod (s - c').
    Proof.
      cbv [squaremod]. rewrite <- c_correct. autorewrite with push_eval. reflexivity.
    Qed.

    Theorem eval_mulmod32 a b :
      (Positional.eval weight limbs (mulmod32 a b)) mod (s - c') =
      (Positional.eval weight limbs a * Positional.eval weight limbs b) mod (s - c').
    Proof.
      cbv [mulmod32]. rewrite <- c_correct. autorewrite with push_eval. Admitted. (*reflexivity.
    Qed.*)

    Theorem eval_squaremod32 a :
      (Positional.eval weight limbs (squaremod32 a)) mod (s - c') =
      (Positional.eval weight limbs a * Positional.eval weight limbs a) mod (s - c').
    Proof.
      cbv [squaremod32]. rewrite <- c_correct. autorewrite with push_eval. reflexivity.
    Qed.
  End DettmanMultiplication.
End DettmanMultiplication.

Module dettman_multiplication_mod_ops.
  Section dettman_multiplication_mod_ops.
    Import DettmanMultiplication.
    Local Open Scope Z_scope.
    Local Coercion QArith_base.inject_Z : Z >-> Q.
    Local Coercion Z.pos : positive >-> Z.
    Context
        (s : Z)
        (c : list (Z*Z))
        (register_width : nat)
        (n : nat)
        (last_limb_width : nat)
        (p_nz : s - Associational.eval c <> 0)
        (n_gteq_4 : (4 <= n)%nat)
        (last_limb_width_small : last_limb_width * n <= Z.log2 s)
        (last_limb_width_big : 1 <= last_limb_width)
        (s_power_of_2 : 2 ^ (Z.log2 s) = s).

    (* I do want to have Z.log2 s, not Z.log2_up (s - c) below.  We want to ensure that weight (n - 1) <= s <= weight limbs *)
    Local Notation limbwidth_num' := (Z.log2 s - last_limb_width).
    Local Notation limbwidth_den' := (n - 1). (* can't use Q here, or else reification doesn't work *)
    
    Context
        (registers_big : limbwidth_num' <= register_width * limbwidth_den') (* stated somewhat awkwardly in terms of Z; i think we might want to avoid Q here too *)
        (weight_big : Z.log2 s <= n * limbwidth_num' / limbwidth_den').

    (* I don't want these to be automatically unfolded in the proofs below. *)
    Definition limbwidth_num := limbwidth_num'.
    Definition limbwidth_den := limbwidth_den'.
    
    Definition weight := (weight limbwidth_num limbwidth_den).
    
    Definition mulmod := mulmod s c register_width n weight.
    Definition squaremod := squaremod s c register_width n weight.
    Definition mulmod32 := mulmod32 s c register_width n weight.
    Definition squaremod32 := squaremod32 s c register_width n weight.

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

    Definition eval_mulmod := eval_mulmod s c register_width n weight p_nz n_gteq_4 s_small s_big weight_lt_width wprops.
    Definition eval_squaremod := eval_squaremod s c register_width n weight p_nz n_gteq_4 s_small s_big weight_lt_width wprops.
    Definition eval_mulmod32 := eval_mulmod32 s c register_width n weight p_nz n_gteq_4 s_small s_big weight_lt_width wprops.
    Definition eval_squaremod32 := eval_squaremod32 s c register_width n weight p_nz n_gteq_4 s_small s_big weight_lt_width wprops.
  End dettman_multiplication_mod_ops.
End dettman_multiplication_mod_ops.

Module Export Hints.
  Import dettman_multiplication_mod_ops.
#[global]
  Hint Rewrite eval_mulmod using solve [ auto with zarith | congruence ] : push_eval.
#[global]
  Hint Rewrite eval_squaremod using solve [ auto with zarith | congruence ] : push_eval.
#[global]
  Hint Rewrite eval_mulmod32 using solve [ auto with zarith | congruence ] : push_eval.
#[global]
  Hint Rewrite eval_squaremod32 using solve [ auto with zarith | congruence ] : push_eval.
End Hints.

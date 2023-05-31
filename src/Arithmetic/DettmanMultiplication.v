Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import Crypto.Arithmetic.ModOps.
Require Import Coq.QArith.QArith_base Coq.QArith.Qround.
Require Import Coq.Program.Wf.
Local Open Scope list_scope.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.

Local Coercion Z.of_nat : nat >-> Z.

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

     (*(* maybe I should write a proof that this not only terminates, but actually works properly? *)
    Program Fixpoint num_digits' (x : N) (i : nat) { measure (N.to_nat x) } : nat :=
      match x with
      | N0 => 0
      | _ => 1 + num_digits' (x - Z.to_N (weight (i + 1) - weight i)) (i + 1)
      end.
    Next Obligation.
      remember (weight_positive wprops i). Remember (weight_dividesremember lia.
    Qed.
    
    Lemma num_digits'_equiv (x : N) (i : nat) :
      num_digits' x i =
        match x with
        | N0 => 0%nat
        | _ => (1 + num_digits' (x - Z.to_N (weight i)) (i + 1))%nat
        end.
    Proof.
      destruct x; trivial. cbv [num_digits'].
      remember (num_digits'_func (existT _ _ (i + 1)%nat)) as y eqn:Ey.
      cbv [num_digits'_func]. simpl. rewrite fix_sub_eq.
      - subst. reflexivity.
      - intros x f g H. destruct x. simpl. destruct x.
        + reflexivity.
        + f_equal. apply H.
    Qed.
    
    Definition num_digits (x : N) : nat := num_digits' x 0.

    (* currently, this is the only fact that I use about num_digits *)
    Lemma num_digits_0_0 (x : N) : num_digits x = 0%nat -> x = 0%N.
    Proof.
      cbv [num_digits]. rewrite num_digits'_equiv. destruct x; lia.
    Qed.

    Fixpoint Positional_from_N' (x : N) (num_digits : nat) : list Z :=
      match num_digits with
      | O => []
      | S num_digits' => Positional_from_N' (Z.to_N ((Z.of_N x) mod (weight num_digits'))) num_digits' ++
                           [(Z.of_N x) / (weight num_digits')]
      end.

    Definition Positional_from_N (x : N) : list Z :=
      Positional_from_N' x (num_digits x).
    
    Definition Positional_from_Z (x : Z) : list Z :=
      let abs := Positional_from_N (Z.to_N x) in
      if x <? 0 then
        map (fun a => -1 * a) abs
      else
        abs.

    Print Positional.eval.

    Lemma len_Positional_from_N (x : N) :
      length (Positional_from_N x) = num_digits x.
    Proof.
      cbv [Positional_from_N Positional_from_N'].
      remember (num_digits x) as len eqn:E. assert (len <= num_digits x) generalize dependent x.
      induction len as [| len' IHlen'].
      - reflexivity.
      - intros x. Search (length (_ ++ _)). rewrite app_length. simpl. rewrite IHlen'.
        + lia.
        + 
        
    Lemma eval_Positional_from_N (x : N) :
      Positional.eval weight (num_digits x) (Positional_from_N x) = Z.of_N x.
    Proof.
      cbv [Positional_from_N Positional_from_N']. remember (num_digits x) as len eqn:E.
      generalize dependent x. induction len as [ | len' IHlen'].
      - intros x H. symmetry in H. apply num_digits_0_0 in H. subst. reflexivity.
      - intros x H. Search Positional.eval. Check eval_snoc.
        rewrite (eval_snoc _ len'). rewrite eval_snoc. sC apply IHlen'.
      
    
    Fixpoint getC (c_ : Z) (log2_c : nat) : list (Z*Z) :=
      match log2_c with
      | 0 => [(1, c_)]
      | S log2_c' => Associational.mul [(2^ Context*)
        

                                         
      
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

      (* experiment with 32 bits *)
      (* last limb too big, so just add another carry on the end??? *)
      (*let from14 := weight (l - 1) in
      let to14 := s in
      let r14 := carry' from14 (to14 / from14) r13 in
      let r14' := dedup_weights r14 in

      let r15 := reduce' s s s c r14' in

      let from16 := weight 0 in
      let to16 := weight 1 in
      let r16 := carry' from16 (to16 / from16) r15 in*)

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
      let a_assoc := Positional.to_associational weight limbs a in
      let b_assoc := Positional.to_associational weight limbs b in
      let r0 := Associational.mul a_assoc b_assoc in
      reduce_carry_borrow32 r0.

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
      (*- replace 1 with (weight 0). Search (weight _ mod _). apply weight_multiples.
      - replace 1 with (weight 0). apply weight_multiples.*)
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
      (*- replace 1 with (weight 0). Search (weight _ mod _). apply weight_multiples.
      - replace 1 with (weight 0). apply weight_multiples.*)
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
      cbv [mulmod32]. rewrite <- c_correct. autorewrite with push_eval. reflexivity.
    Qed.

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

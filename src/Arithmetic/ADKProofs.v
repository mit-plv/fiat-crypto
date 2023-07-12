Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
Import Crypto.Util.ListUtil.Reifiable.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.Bool2Prop.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.EquivModulo.
Require Import Crypto.Util.ZUtil.Modulo Crypto.Util.ZUtil.Div.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.Hints.Core.
Require Import Crypto.Util.ZUtil.Modulo.PullPush.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Tactics.DivModToQuotRem.
Require Import Crypto.Util.ZUtil.Tactics.RewriteModSmall.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Util.Notations.
Require Import Coq.Sorting.Permutation.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ADK.
Import ListNotations. Local Open Scope Z_scope.
Import Core.SimpleWeight.
Import Core.Monotonicity.

Section SimpleWeight.
  Context (first_limb_weight : Z)
    (flw_gt_1 : first_limb_weight > 1).
  
  Definition weight (n : nat) : Z := first_limb_weight ^ Z.of_nat n.

  Definition seq_from_to a b := seq a (Z.to_nat (Z.of_nat b - Z.of_nat a + 1)).

  Local Notation nth' := (fun i l d => (nth_default d l i)).
  
  Definition friendly_adk_mul (n : nat) (x y : list Z) : list Z :=
    let products : list Z := map (fun i => (nth' i (firstn n x) 0) * (nth' i (firstn n y) 0)) (seq 0 (2*n - 1)) in
    let f_rev : list Z := fold_left (fun l p => (nth' 0%nat l 0) + p :: l) products [] in
    adk_mul' n x y (nth' (n - 1)%nat products 0) (rev f_rev).
  
  Lemma friendly_list_rect products_remaining f_so_far base_case :
    (list_rect
       (fun _ => list Z -> list Z)
       base_case
       (fun p _ g => fun f' => Let_In ((nth' 0%nat f' 0) + p) (fun x => g (x :: f'))) 
       products_remaining) f_so_far =
      base_case (fold_left (fun l p => (nth' 0%nat l 0) + p :: l) products_remaining f_so_far).
  Proof.
    generalize dependent f_so_far. induction products_remaining as [| p products' IH].
    - reflexivity.
    - intros f_so_far. simpl. rewrite unfold_Let_In. rewrite IH. reflexivity.
  Qed.
  
  Lemma adk_mul_friendly (n : nat) (x y : list Z) :
    adk_mul n x y = friendly_adk_mul n x y.
  Proof.
    cbv [adk_mul adk_mul_inner]. rewrite unfold_Let_In. rewrite friendly_list_rect.
    destruct (n =? 0)%nat eqn:E.
    - apply Nat.eqb_eq in E. subst. reflexivity.
    - apply Nat.eqb_neq in E.
      replace (_ ++ _ ++ _) with (map (fun i => (nth' i (firstn n x) 0) * (nth' i (firstn n y) 0)) (seq 0 (2*n - 1))).
      + cbv [friendly_adk_mul]. repeat rewrite nth_default_eq. Check map_nth'.
        rewrite (map_nth' _ _ _ 0%nat).
        -- repeat rewrite seq_nth.
           ++ repeat rewrite nth_default_eq. Search (nth _ (firstn _ _)). repeat rewrite nth_firstn. replace (_ <? _)%nat with true.
              --- f_equal.
              --- symmetry. apply Nat.ltb_lt. lia.
           ++ lia.
        -- rewrite seq_length. lia.
      + replace (2 * n - 1)%nat with ((n - 1) + 1 + (n - 1))%nat by lia. repeat rewrite seq_app. repeat rewrite map_app.
        rewrite <- app_assoc. f_equal.
        -- apply map_ext_in. intros a Ha. apply in_seq in Ha. repeat rewrite nth_default_eq. repeat rewrite SimpleWeight.nth_firstn. destruct (a <? n)%nat eqn:E'; try reflexivity. apply Nat.ltb_nlt in E'. lia.
        -- f_equal.
           ++ simpl. repeat rewrite nth_default_eq. repeat rewrite SimpleWeight.nth_firstn. replace (n - 1 <? n)%nat with true; try reflexivity. symmetry. apply Nat.ltb_lt. lia.
           ++ replace (0 + (n - 1 + 1))%nat with n by lia. replace (repeat 0 (n - 1)) with (repeat 0 (length (seq n (n - 1)))).
              --- rewrite <- map_const. apply map_ext_in. intros a Hin. repeat rewrite nth_default_eq. repeat rewrite SimpleWeight.nth_firstn. destruct (a <? n)%nat eqn:E'; try reflexivity. apply Nat.ltb_lt in E'.
                  apply in_seq in Hin. lia.
              --- f_equal. apply seq_length.
  Qed.
  
  Definition friendlier_adk_prod_at_i (n : nat) (x y : list Z) (i : nat) : Z :=
    fold_right Z.add 0 (map (fun j => (nth j x 0 - nth (i - j) x 0) * (nth (i - j) y 0 - nth j y 0))
                          (seq (i - (n - 1)) (Z.to_nat (1 + ((Z.of_nat i + 1)/2 - 1) - Z.of_nat (i - (n - 1))%nat)%Z))) +
      fold_right Z.add 0 (map (fun j => nth j x 0 * nth j y 0) (seq (i - (n - 1)) (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat n - 1) - Z.of_nat (i - (n - 1)))))).

  Definition reifiable_friendlier_adk_prod_at_i (n : nat) (x y : list Z) (i : nat) : Z :=
    fold_right Z.add 0 (map (fun j => (nth' j x 0 - nth' (i - j)%nat x 0) * (nth' (i - j)%nat y 0 - nth' j y 0))
                          (seq (i - (n - 1)) (Z.to_nat (1 + ((Z.of_nat i + 1)/2 - 1) - Z.of_nat (i - (n - 1))%nat)%Z))) +
      fold_right Z.add 0 (map (fun j => nth' j x 0 * nth' j y 0) (seq (i - (n - 1)) (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat n - 1) - Z.of_nat (i - (n - 1)))))).
  
  Definition friendlier_adk_mul (n : nat) (x y : list Z) :=
    map (friendlier_adk_prod_at_i n x y) (seq 0 (2*n - 1)).

  Definition reifiable_friendlier_adk_mul (n : nat) (x y : list Z) :=
    map (reifiable_friendlier_adk_prod_at_i n x y) (seq 0 (2*n - 1)).

  Lemma reifiable_ok n x y :
    reifiable_friendlier_adk_mul n x y = friendlier_adk_mul n x y.
  Proof.
    cbv [reifiable_friendlier_adk_mul friendlier_adk_mul]. apply map_ext. intros i.
    cbv [reifiable_friendlier_adk_prod_at_i friendlier_adk_prod_at_i]. f_equal.
    - f_equal. apply map_ext. intros j. repeat rewrite nth_default_eq. reflexivity.
    - f_equal. apply map_ext. intros j. repeat rewrite nth_default_eq. reflexivity.
  Qed.
  
  Lemma f_spec (n : nat) (xn yn : list Z) (i : nat) (d : Z) :
    let products : list Z := map (fun i => (nth' i xn 0) * (nth' i yn 0)) (seq 0 (2*n - 1)) in
    let f : list Z := rev (fold_left (fun l p => (nth' 0%nat l 0) + p :: l) products []) in
    nth i f d =
      if (i <? 2*n - 1)%nat then
        fold_right Z.add 0 (map (fun j => nth j xn 0 * nth j yn 0) (seq_from_to 0 i))
      else
        d.
  Proof.
    remember (2 * n - 1)%nat as m eqn:clearMe; clear clearMe.
    remember (map _ (seq _ m)) as p eqn:Ep. simpl. remember (rev (fold_left _ p _)) as f eqn:Ef. Search (_ /\ _ -> _).
    generalize dependent d. generalize dependent i. apply (@proj1 _ (length f = m)).
    subst. induction m as [|m' IHm'].
    - simpl. split; try reflexivity. intros i d. destruct i; reflexivity.
    - destruct IHm' as [IHnth IHlen].
      remember (map _ (seq _ (S m'))) as p eqn:Ep. remember (fold_left _ p _) as f_rev eqn:Ef.
      remember (map _ (seq 0 m')) as p' eqn:Ep'. remember (fold_left _ p' _) as f'_rev eqn:Ef'.
      rewrite seq_S in Ep. rewrite map_app in Ep. rewrite <- Ep' in Ep. clear Ep'. cbn [map] in Ep. rewrite Ep in *. clear Ep.
      Search (fold_left _ (_ ++ _) _). rewrite fold_left_app in Ef. cbn [fold_left] in Ef. rewrite <- Ef' in Ef. clear Ef'. rewrite Ef in *. clear Ef. cbn [rev].
      split.
      + repeat rewrite nth_default_eq. intros i d. destruct (i <? S m')%nat eqn:E1.
        -- apply Nat.ltb_lt in E1. remember (IHnth i) as IHnthi eqn:clearMe; clear clearMe. destruct (i <? m')%nat eqn:E2.
           ++ apply Nat.ltb_lt in E2. rewrite app_nth1 by lia. Search Nat.ltb. apply IHnthi.
           ++ apply Nat.ltb_nlt in E2. rewrite app_nth2 by lia. replace (i - length (rev f'_rev))%nat with 0%nat by lia. cbn [nth]. assert (i = m') by lia. rewrite H in *. clear E1 E2 H.
              Search (nth _ (rev _)). Check rev_involutive. rewrite <- (rev_involutive f'_rev). destruct (m' - 1 <? m')%nat eqn:E.
              --- apply Nat.ltb_lt in E. rewrite rev_nth by lia. rewrite IHlen. rewrite IHnth. rewrite <- Nat.ltb_lt in E. rewrite E. rewrite Nat.ltb_lt in E.
                  cbv [seq_from_to]. remember (Z.to_nat (Z.of_nat m' - _ + _)) as len. replace len with (S (len - 1)) by lia. rewrite seq_S.
                  rewrite map_app. cbn [map]. Search (fold_right Z.add). rewrite SimpleWeight.split_sum. cbn [fold_right]. f_equal.
                  +++ f_equal. f_equal. f_equal. lia.
                  +++ rewrite Z.add_0_r. f_equal.
                      ---- f_equal. lia.
                      ---- f_equal. lia.
              --- apply Nat.ltb_nlt in E. replace m' with 0%nat by lia. simpl. rewrite rev_involutive. destruct f'_rev as [|f0 f'_rev'].
                  +++ rewrite SimpleWeight.nth_nil. lia.
                  +++ simpl in IHlen. rewrite app_length in IHlen. cbn [length] in IHlen. lia.
        -- apply Nat.ltb_nlt in E1. rewrite nth_overflow.
           ++ reflexivity.
           ++ rewrite app_length. cbn [length]. lia.
      + rewrite app_length. cbn [length]. lia.
  Qed.
  
  Lemma adk_mul_friendlier (n : nat) (x y : list Z) :
    friendly_adk_mul n x y = friendlier_adk_mul n x y.
  Proof.
    cbv [friendly_adk_mul adk_mul_prod_at_i adk_mul' friendlier_adk_mul friendlier_adk_prod_at_i if_then_else].
    apply map_ext_in. repeat rewrite nth_default_eq. intros i Hi. apply in_seq in Hi. f_equal.
    1: { f_equal. apply map_ext. intros j. repeat rewrite nth_default_eq. reflexivity. }
    repeat rewrite nth_default_eq. repeat rewrite f_spec. replace (i - n <? 2 * n - 1)%nat with true.
    - replace (i <? 2 * n - 1)%nat with true.
      + repeat rewrite nth_default_eq. destruct (i =? 2 * n - 2)%nat eqn:E.
        -- apply Nat.eqb_eq in E. replace (Z.to_nat _) with 1%nat by lia. repeat rewrite (SimpleWeight.map_nth' _ _ _ 0%nat).
           ++ repeat rewrite nth_default_eq. rewrite seq_nth by lia. repeat rewrite SimpleWeight.nth_firstn. replace (_ <? _)%nat with true.
              --- cbn [seq map fold_right]. rewrite Z.add_0_r. f_equal.
                  +++ f_equal. lia.
                  +++ f_equal. lia.
              --- symmetry. apply Nat.ltb_lt. lia.
           ++ rewrite seq_length. lia.
        -- clear E. destruct (i <? n)%nat eqn:E.
           ++ apply Nat.ltb_lt in E. f_equal. replace (seq _ _) with (seq_from_to 0 i).
              --- repeat rewrite nth_default_eq. apply map_ext_in. intros j Hj. apply in_seq in Hj. repeat rewrite SimpleWeight.nth_firstn. replace (_ <? _)%nat with true.
                  +++ reflexivity.
                  +++ symmetry. apply Nat.ltb_lt. lia.
              --- cbv [seq_from_to]. f_equal; lia.
           ++ apply Nat.ltb_nlt in E. replace (seq_from_to 0 i) with (seq_from_to 0 (i - n) ++ seq_from_to (i - n + 1) i).
              --- rewrite map_app. rewrite SimpleWeight.split_sum. ring_simplify. Print friendly_adk_mul. remember (Z.to_nat _) as seqlen.
                  replace (seq_from_to (i - n + 1) i) with (seq (i - (n - 1)) seqlen ++ seq (i - (n - 1) + seqlen) (1 + i - (i - n + 1) - seqlen)).
                  2: { rewrite <- seq_app. cbv [seq_from_to]. f_equal; lia. }
                  rewrite map_app. rewrite SimpleWeight.split_sum. rewrite <- Z.add_0_r. f_equal.
                  +++ f_equal. apply map_ext_in. intros j Hj. apply in_seq in Hj.
                      repeat rewrite SimpleWeight.nth_firstn. replace (j <? n)%nat with true.
                      ---- reflexivity.
                      ---- symmetry. apply Nat.ltb_lt. lia.
                  +++ rewrite fold_right_map. apply fold_right_invariant; try reflexivity. intros j Hj s' Hs'. apply in_seq in Hj. repeat rewrite nth_overflow.
                      ---- lia.
                      ---- rewrite firstn_length. lia.
                      ---- rewrite firstn_length. lia.
              --- cbv [seq_from_to]. replace (i - n + 1)%nat with (0 + (i - n + 1))%nat by lia. replace (Z.to_nat (Z.of_nat (i - n) - Z.of_nat 0 + 1)) with (0 + (i - n + 1))%nat by lia.
                  rewrite <- seq_app. f_equal. lia.
      + symmetry. apply Nat.ltb_lt. lia.
    - symmetry. apply Nat.ltb_lt. lia.
  Qed.

    Lemma adk_mul_is_mul (n : nat) (x y : list Z) :
      adk_mul n x y = mul n x y.
    Proof.
      rewrite adk_mul_friendly. rewrite adk_mul_friendlier.
      cbv [friendlier_adk_mul mul]. cbv [prod_at_index friendlier_adk_prod_at_i].
      apply map_ext. intros i.
      remember (Zeven_odd_dec (Z.of_nat i + 1)) as H72 eqn:clearMe; clear clearMe.
      assert (H73: (Z.of_nat i + 1 = 2 * Z.div2 (Z.of_nat i + 1) \/ Z.of_nat i + 1 = 2 * Z.div2 (Z.of_nat i + 1) + 1)).
      { destruct H72 as [H'|H'].
        - left. apply Zeven_div2. apply H'.
        - right. apply Zodd_div2. apply H'. }
      induction n as [|n' IHn'].
      - replace (fold_right _ _ _) with 0.
        + replace (fold_right _ _ _) with 0.
          -- replace (fold_right _ _ _) with 0.
             ++ lia.
             ++ apply fold_right_invariant; try reflexivity. intros y0 Hin z IH.
                apply in_map_iff in Hin. destruct Hin as [x0 [H1 H2] ].
                apply in_seq in H2. lia.
          -- apply fold_right_invariant; try reflexivity. intros y0 Hin z IH.
                apply in_map_iff in Hin. destruct Hin as [x0 [H1 H2] ].
                repeat rewrite nth_nil in H1. apply in_seq in H2. lia.
        + apply fold_right_invariant; try reflexivity. intros y0 Hin z IH.
                apply in_map_iff in Hin. destruct Hin as [x0 [H1 H2] ].
                repeat rewrite nth_nil in H1. apply in_seq in H2. (* this is secretly a proof by contradiction. more contradiction above *) lia.
      -
        

        (* three cases.
           1. n = 1, or i = 2*n - 2.  In this case, the second summation on the LHS gets an extra term, as does the summation on the RHS.
              The summation on the RHS looks stupid.  I don't like the firstn garbage.  I should rewrite it so that the upper bound on the sum is Nat.min i (n - 1).
           2. (n - 1) <= i <= 2*n - 3.  In this case, all three summations get an extra term.
           3. True.  In this case, none of the summations gets an extra term.
         *)
        destruct (andb (negb (S n' =? 1)) (andb ((Z.of_nat (S n') - 1) <=? Z.of_nat i) (Z.of_nat i <=? 2*Z.of_nat (S n') - 3))%Z)%nat eqn:E1.
        + (* case 2 *) assert (E1': ((Z.of_nat i - (Z.of_nat (S n') - 1) <= Z.of_nat (S n') - 1) ->
                      ((Z.of_nat i - (Z.of_nat (S n') - 1) <= ((Z.of_nat i + 1) / 2 - 1)) <->
                         Z.of_nat i <= 2*Z.of_nat (S n') - 3))).
        { rewrite <- Z.div2_div. destruct (Zeven_odd_dec (Z.of_nat i + 1)) as [H'|H'].
          - apply Zeven_div2 in H'. cbv [Nat.double] in H'. split; try lia; try split; try lia; try split; try lia.
          - apply Zodd_div2 in H'. cbv [Nat.double] in H'. split; try lia.
        }
        apply andb_prop in E1. destruct E1 as [E1 E2]. Search (negb _ = true). rewrite Bool.negb_true_iff in E1.
        remember (Z.to_nat
       (1 + ((Z.of_nat i + 1) / 2 - 1) -
          Z.of_nat (i - (S n' - 1)))) as thing.
        apply andb_prop in E2. repeat rewrite Z.leb_le in E2.
               replace (seq (i - (S n' - 1)) thing) with                 
                 ((i - (S n' - 1))%nat ::
                                 (seq (i - (n' - 1)) (thing - 1))).
               2: { rewrite <- E1' in E2; try lia. replace thing with (S (thing - 1)) by lia. simpl. f_equal.
                    f_equal; try lia. (*apply Nat.eqb_neq in E1. lia.*) }
               replace (seq (i - (S n' - 1)) (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (S n') - 1) - Z.of_nat (i - (S n' - 1))))) with
                 ((i - (S n' - 1))%nat :: seq (i - (n' - 1)) (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (n') - 1) - Z.of_nat (i - (n' - 1)))) ++ [S n' - 1]%nat).
               2: { remember (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (n') - 1) - Z.of_nat (i - (n' - 1)))) as thing1.
                    remember (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (S n') - 1) - Z.of_nat (i - (S n' - 1)))) as thing2.
                    replace thing2 with (S (S (thing1))) by lia. rewrite seq_S. rewrite <- cons_seq. rewrite app_comm_cons. f_equal. Search (_ :: _ = _ ++ _).
                    - f_equal. f_equal. lia.
                    - f_equal. lia. }
               replace (seq (i - (S n' - 1)) (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat (i - (S n' - 1)))))
                 with ([i - (S n' - 1)]%nat ++ seq (i - (n' - 1)) (Z.to_nat (1 + Z.min (Z.of_nat (n') - 1) (Z.of_nat i) - Z.of_nat (i - (n' - 1)))) ++ [S n' - 1]%nat).
               
               2: { replace (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat (i - (S n' - 1)))) with
                 (S (S (Z.to_nat (1 + Z.min (Z.of_nat n' - 1) (Z.of_nat i) - Z.of_nat (i - (n' - 1)))))) by lia.
                    rewrite seq_S. rewrite <- cons_seq. cbn [app]. f_equal. f_equal.
                    - f_equal; lia.
                    - f_equal. lia. }
               Search (fold_right Z.add). repeat rewrite map_cons. repeat rewrite map_app. repeat rewrite map_cons. repeat rewrite split_sum. repeat rewrite map_nil. repeat rewrite fold_right_cons.
               repeat rewrite split_sum. repeat rewrite fold_right_cons.
               repeat rewrite fold_right_nil. repeat rewrite Z.add_0_r.
               repeat rewrite Z.add_assoc. rewrite (Z.add_comm _ (fold_right _ _ _)). rewrite (Z.add_comm _ (fold_right _ _ _)). rewrite (Z.add_comm _ (fold_right _ _ _)).
               repeat rewrite <- Z.add_assoc. rewrite Z.add_assoc. f_equal.
               -- rewrite <- IHn'. rewrite Z.add_comm. f_equal.
                  ++ f_equal. replace (Z.to_nat (1 + ((Z.of_nat i + 1) / 2 - 1) - Z.of_nat (i - (n' - 1)))) with (thing - 1)%nat by lia. apply map_ext_in. intros a Ha.
                     apply in_seq in Ha. Search firstn. apply Nat.eqb_neq in E1. clear IHn'.
                     assert (H1 : (a <= n' - 1)%nat). { rewrite <- Z.div2_div in *. destruct (Zeven_odd_dec (Z.of_nat i + 1)) as [H'|H'].
                                                       - apply Zeven_div2 in H'. lia.
                                                       - apply Zodd_div2 in H'. lia. }
                     assert (H2 : (i - a <= n' - 1)%nat) by lia. repeat rewrite nth_firstn.
                         replace (a <? S n')%nat with true. replace (i - a <? S n')%nat with true. replace (a <? n')%nat with true. replace (i - a <? n')%nat with true. reflexivity.
                         +++ symmetry. apply Nat.ltb_lt. lia.
                         +++ symmetry. apply Nat.ltb_lt. lia.
                         +++ symmetry. apply Nat.ltb_lt. lia.
                         +++ symmetry. apply Nat.ltb_lt. lia.
               -- repeat rewrite nth_default_eq.
                  remember (Zeven_odd_dec (Z.of_nat i + 1)) as H' eqn:clearMe; clear clearMe.
                 assert (H'': (Z.of_nat i + 1 = 2 * Z.div2 (Z.of_nat i + 1) \/ Z.of_nat i + 1 = 2 * Z.div2 (Z.of_nat i + 1) + 1)).
                 { destruct H' as [H'|H'].
                   - left. apply Zeven_div2. apply H'.
                   - right. apply Zodd_div2. apply H'. }
                 repeat rewrite nth_firstn. 
                 replace (i - (i - (S n' - 1)))%nat with (S n' - 1)%nat by lia. lia.
        + Search (andb _ _ = false). apply Bool.andb_false_iff in E1. rewrite Bool.negb_false_iff in E1. rewrite Nat.eqb_eq in E1. rewrite Bool.andb_false_iff in E1.
          repeat rewrite Z.leb_nle in E1.
          destruct (orb (andb (S n' =? 1) (i =? 0)) (i =? 2*(S n') - 2))%nat eqn:E2.
          -- (* case 1 *) clear E1. apply Bool.orb_prop in E2. rewrite Bool.andb_true_iff in E2. repeat rewrite Nat.eqb_eq in E2.
             replace (Z.to_nat (1 + ((Z.of_nat i + 1) / 2 - 1) - Z.of_nat (i - (S n' - 1)))) with 0%nat in * by lia.
             replace (Z.to_nat (1 + ((Z.of_nat i + 1) / 2 - 1) - Z.of_nat (i - (n' - 1)))) with 0%nat in * by lia.
             cbn [seq] in *. cbn [map] in *. cbn [fold_right] in *. rewrite Z.add_0_l in *.
             replace (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat n' - 1) - Z.of_nat (i - (n' - 1)))) with 0%nat in * by lia. cbn [seq map fold_right] in *.
             replace (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (S n') - 1) - Z.of_nat (i - (S n' - 1)))) with 1%nat by lia.
             cbn [seq map fold_right].
             replace (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat (i - (S n' - 1)))) with 1%nat by lia.
             cbn [seq map fold_right]. repeat rewrite nth_default_eq. f_equal.
             replace (i - (i - (S n' - 1)))%nat with (S n' - 1)%nat by lia.
             replace (i - (S n' - 1))%nat with (S n' - 1)%nat by lia.
             reflexivity.
          -- (* case 3 *) Search (orb _ _ = false). rewrite Bool.orb_false_iff in E2. rewrite Bool.andb_false_iff in E2. repeat rewrite Nat.eqb_neq in E2.
             assert (H: (i < (S n' - 1) \/ 2*(S n') - 2 < i)%nat) by lia.
             destruct H as [H|H].
             ++ replace (i - (S n' - 1))%nat with 0%nat in * by lia. replace (i - (n' - 1))%nat with 0%nat in * by lia.
                replace (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat 0)) with
                  (Z.to_nat (1 + Z.min (Z.of_nat n' - 1) (Z.of_nat i) - Z.of_nat 0))
                  in * by lia. rewrite <- IHn'. clear IHn'. f_equal.
                --- f_equal. replace ((Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (S n') - 1) - Z.of_nat 0))) with
                      (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat n' - 1) - Z.of_nat 0)) by lia. apply map_ext_in.
                    intros a Ha. apply in_seq in Ha. reflexivity.
             ++ replace (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat (i - (S n' - 1)))) with 0%nat by lia.
                replace ((Z.to_nat (1 + ((Z.of_nat i + 1) / 2 - 1) - Z.of_nat (i - (S n' - 1))))) with 0%nat by lia.
                replace (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (S n') - 1) - Z.of_nat (i - (S n' - 1)))) with 0%nat by lia.
                reflexivity.
    Qed.
    
    Lemma eval_mul n x y :
      Positional.eval weight n x * Positional.eval weight n y =
        Positional.eval weight (2*n - 1) (mul n x y).
    Proof.
      rewrite (mul_is_positional_mul first_limb_weight) by lia. cbv [Positional.mul].
      rewrite Positional.eval_from_associational.
      - rewrite Associational.eval_mul. repeat rewrite Positional.eval_to_associational. reflexivity.
      - apply weight_0.
      - apply weight_nz; lia.
      - destruct (dec (2 * n - 1 = 0)%nat).
        + right. cbv [Positional.to_associational]. replace n with 0%nat by lia. reflexivity.
        + lia.
    Qed.

    Lemma eval_adk_mul n x y :
      Positional.eval weight n x * Positional.eval weight n y =
        Positional.eval weight (2 * n - 1) (adk_mul n x y).
    Proof. rewrite adk_mul_is_mul. rewrite eval_mul. reflexivity. Qed.
End SimpleWeight.

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
Import ListNotations. Local Open Scope Z_scope.

Section Nice_weight.
  Context (first_limb_weight : Z)
    (flw_gt_1 : first_limb_weight > 1).
  
  Definition weight (n : nat) : Z := first_limb_weight ^ Z.of_nat n. Search nth_default.

  Local Notation nth' := (fun i l d => (nth_default d l i)).
  (* why does nth_default exist? why can i reify it, but not nth? why is the order of arguments
     switched around? *)
  Check nth_default.
  Search (nth_default _ _ _ = nth _ _ _). Check nth_default.
  
  Definition prod_at_index (n : nat) (x y : list Z) (i : nat) : Z :=
    fold_right Z.add 0
      (map
         (fun j : nat => nth' j x 0 * nth' (i - j)%nat y 0)
         (seq
            (i - (n - 1))
            (Z.to_nat (1 + (Z.min (Z.of_nat n - 1) (Z.of_nat i)) - Z.of_nat (i - (n - 1)))))).

  Definition pmul (n : nat) (x y : list Z) : list Z :=
    map (prod_at_index n x y) (seq 0 (2 * n - 1)).

  Definition amul (weight : nat -> Z) (n : nat) (x y : list Z) :=
    Positional.from_associational weight (2*n - 1)
      (Associational.mul
         (Positional.to_associational weight n x)
         (Positional.to_associational weight n y)).

  Lemma weight_0 : weight 0 = 1.
  Proof. cbv [weight]. rewrite Z.pow_0_r. reflexivity. Qed.
  
  Lemma weight_gt_0 : forall i, 0 < weight i.
  Proof. intros i. cbv [weight]. apply Z.pow_pos_nonneg; lia. Qed.

  Lemma weight_nz : forall i, weight i <> 0.
  Proof. intros i. remember (weight_gt_0 i). lia. Qed.
  
  Lemma weight_divides : forall i, weight (S i) mod weight i = 0.
  Proof. intros i. cbv [weight]. apply Z.mod_same_pow; lia. Qed.
    
  Lemma weight_injective : forall n i j, (i <= n)%nat -> (j <= n)%nat -> weight i = weight j -> i = j.
  Proof.
    intros n i j _ _ H. cbv [weight] in H. assert (Z.of_nat i = Z.of_nat j); try lia.
    apply (Z.pow_inj_r first_limb_weight); lia.
  Qed.
  
  Lemma place_weight' :
    forall n i x, Positional.place weight (weight i, x) n = (Nat.min i n, weight i / weight (Nat.min i n) * x).
  Proof.
    intros n i x. apply Positional.place_weight.
    - apply weight_0.
    - apply weight_nz.
    - apply weight_gt_0.
    - apply weight_divides.
    - apply (weight_injective n).
  Qed.

  Lemma weight_prod_sum i j :
    weight i * weight j = weight (i + j).
  Proof.
    cbv [weight]. replace (Z.of_nat (i + j)) with (Z.of_nat i + Z.of_nat j) by lia.
    rewrite Z.pow_add_r; lia.
  Qed.

  Lemma destruct_list_backwards {X} (l : list X) :
    (0 < length l)%nat ->
    exists l' ln, l = l' ++ [ln].
  Proof.
    intros H. destruct (rev l) as [|x ll] eqn:E. 
    - rewrite <- (rev_involutive l) in H. rewrite E in H. simpl in H. lia.
    - exists (rev ll). exists x. rewrite <- (rev_involutive l). rewrite E. reflexivity.
  Qed.

  Lemma destruct_list_backwards' {X} (l : list X) :
    l = [] \/ exists l' ln, l = l' ++ [ln].
  Proof.
    destruct (rev l) as [|x ll] eqn:E. 
    - left. rewrite <- (rev_involutive l). rewrite E. reflexivity.
    - right. exists (rev ll). exists x. rewrite <- (rev_involutive l). rewrite E. reflexivity.
  Qed.

  Lemma list_induction_backwards {X} (P : list X -> Prop) :
    P [] ->
    (forall x l, P l -> P (l ++ [x])) ->
    forall l, P l.
  Proof.
    intros H1 H2 l. assert (H : forall ll, P (rev ll)).
    - intros ll. induction ll as [|x ll'].
      + apply H1.
      + simpl. apply H2. apply IHll'.
    - rewrite <- rev_involutive. apply H.
  Qed.

  Lemma combine_app_one {X} (l1 l2 : list X) (x : X) :
    combine l1 (l2 ++ [x]) = if (length l1 <=? length l2)%nat then combine l1 l2 else combine l1 l2 ++ [(nth (length l2) l1 x, x)].
  Proof.
    generalize dependent l1. induction l2 as [|x2 l2' IHl2'].
    - intros l1. simpl. destruct l1 as [|x1 l1']; try reflexivity. replace (_ <=? _)%nat with false.
      + simpl. rewrite combine_nil_r. reflexivity.
      + symmetry. rewrite Nat.leb_nle. simpl. lia.
    - intros l1. simpl. destruct l1 as [|x1 l1']; try reflexivity. Search (combine _ []). simpl.
      destruct (_ <=? _)%nat eqn:E.
      + f_equal. rewrite IHl2'. rewrite E. reflexivity.
      + f_equal. rewrite IHl2'. rewrite E. reflexivity.
  Qed.

  Lemma nth_equal {X}  (a b : X) (l1 l2 : list X) :
    a <> b ->
    (forall i x, nth i l1 x = nth i l2 x) ->
    l1 = l2.
  Proof.
    intros H1. generalize dependent l2. generalize dependent l1. induction l1 as [|l1_0 l1' IHl1'].
    - intros l2 H2. destruct l2; try reflexivity. remember (H2 0%nat a) as H2_1 eqn:E; clear E.
      remember (H2 0%nat b) as H2_2 eqn:E; clear E. simpl in H2_1. simpl in H2_2. congruence.
    - intros l2 H2. destruct l2 as [|l20 l2'].
      + remember (H2 0%nat a) as H2_a eqn:E; clear E. remember (H2 0%nat b) as H2_b eqn:E; clear E.
        simpl in H2_a. simpl in H2_b. congruence.
      + f_equal.
        -- remember (H2 0%nat a) as H2_a eqn:E; clear E. remember (H2 0%nat b) as H2_b eqn:E; clear E. simpl in H2_a. simpl in H2_b. apply H2_a.
        -- apply IHl1'. intros i x. remember (H2 (S i)%nat x) as H eqn:E; clear E. simpl in H.
           apply H.
  Qed.
  Import Permutation.
  Print Permutation.

  Lemma fold_right_comm_permutation {X Y : Type} (f : X -> Y -> Y) (a0 : Y) (l1 l2 : list X) :
    (forall x1 x2 y, f x1 (f x2 y) = f x2 (f x1 y)) ->
    Permutation l1 l2 ->
    fold_right f a0 l1 = fold_right f a0 l2.
  Proof.
    intros H1 H2. induction H2 as [| | |l1 l2 l3 P12 IHP12 P23 IHP23].
    - reflexivity.
    - simpl. f_equal. assumption.
    - simpl. apply H1.
    - rewrite IHP12. apply IHP23.
  Qed.
  
  Lemma nth_error_nth_full {X} (n : nat) (l : list X) (d : X) :
    nth n l d = match (nth_error l n) with Some x => x | None => d end.
  Proof.
    destruct (nth_error l n) eqn:E.
    - apply nth_error_nth. apply E.
    - Search (nth_error _ _ = None). apply nth_overflow. apply nth_error_None. apply E.
  Qed.
  
  Lemma mth_add_to_nth m n x l d :
    m <> n ->
    nth m (Positional.add_to_nth n x l) d = nth m l d.
  Proof.
    intros H. rewrite nth_error_nth_full. cbv [Positional.add_to_nth]. rewrite nth_update_nth.
    rewrite <- beq_nat_eq_nat_dec. apply Nat.eqb_neq in H. rewrite H.
    rewrite <- nth_error_nth_full. reflexivity.
  Qed.
  
  Lemma nth_add_to_nth n x l d :
    nth n (Positional.add_to_nth n x l) d = if (n <? length l)%nat then (nth n l d + x) else (nth n l d).
  Proof.
    rewrite nth_error_nth_full. cbv [Positional.add_to_nth]. rewrite nth_update_nth.
    rewrite <- beq_nat_eq_nat_dec. rewrite Nat.eqb_refl. destruct (n <? length l)%nat eqn:E.
    - apply Nat.ltb_lt in E. rewrite nth_error_nth_full. destruct (nth_error l n) eqn:E'.
      + simpl. lia.
      + simpl. apply nth_error_None in E'. lia.
    - apply Nat.ltb_nlt in E. rewrite nth_error_nth_full. destruct (nth_error l n) eqn:E'.
      + simpl. Check nth_error_None. assert (H: (length l <= n)%nat) by lia.
        rewrite <- nth_error_None in H. congruence.
      + reflexivity.
  Qed.

  Lemma unstupid_nth_add_to_nth n x l d :
    (n < length l)%nat ->
    nth n (Positional.add_to_nth n x l) d = nth n l d + x.
  Proof.
    intros H. rewrite nth_add_to_nth. destruct (_ <? _)%nat eqn:E; try reflexivity.
    apply Nat.ltb_nlt in E. lia.
  Qed.
        
  Lemma mth_add_to_nth_full m n x l d :
    nth m (Positional.add_to_nth n x l) d = if (andb (m =? n) (m <? length l))%nat then (nth m l d + x) else (nth m l d).
  Proof.
    destruct (m =? n)%nat eqn:E1. simpl.
    - apply Nat.eqb_eq in E1. subst. apply nth_add_to_nth.
    - simpl. apply Nat.eqb_neq in E1. apply mth_add_to_nth. apply E1.
  Qed.
      
  Lemma add_to_nth_comm i1 i2 x1 x2 l :
    Positional.add_to_nth i1 x1 (Positional.add_to_nth i2 x2 l) =
      Positional.add_to_nth i2 x2 (Positional.add_to_nth i1 x1 l).
  Proof.
    apply (nth_equal 0 1); try lia. intros i x. repeat rewrite mth_add_to_nth_full.
    repeat rewrite Positional.length_add_to_nth.
    destruct (i =? i1)%nat eqn:E1;
      destruct (i =? i2)%nat eqn:E2;
      destruct (i <? length l)%nat eqn:E3;
      try rewrite Nat.eqb_eq in *; try rewrite Nat.eqb_neq in *;
      try rewrite Nat.ltb_lt in *; try rewrite Nat.ltb_nlt in *;
      simpl; lia.
  Qed.

  Lemma p_to_a_app weight n l1 l2 :
    Positional.from_associational weight n (l1 ++ l2) = Positional.from_associational weight n (l2 ++ l1).
  Proof.
    cbv [Positional.from_associational]. Search (Permutation (_ ++ _) (_ ++ _)).
    Check Permutation_app_comm. Search Permutation. Check fold_right_comm_permutation.
    apply fold_right_comm_permutation.
    - intros x1 x2 y. repeat rewrite unfold_Let_In. apply add_to_nth_comm.
    - apply Permutation_app_comm.
  Qed.

  Lemma map_nth' {X Y} (f : X -> Y) l d1 d2 n :
    (n < length l)%nat ->
    nth n (map f l) d1 = f (nth n l d2).
  Proof.
    intros H. rewrite (nth_indep _ d1 (f d2)).
    - apply map_nth.
    - rewrite map_length. apply H.
  Qed.

  Lemma expand_singleton_l a b y :
    Associational.mul [(a, b)] y =  map (fun t' : Z * Z => (a * fst t', b * snd t')) y.
  Proof. simpl. rewrite app_nil_r. reflexivity. Qed.

  Lemma split_sum (l1 l2 : list Z) :
    fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
  Proof.
    induction l1 as [|x l1' IHl1'].
    - reflexivity.
    - simpl. rewrite IHl1'. lia.
  Qed.

  Lemma length_pmul : forall n x y,
      length (pmul n x y) = (2*n - 1)%nat.
  Proof.
    intros n x y. cbv [pmul]. rewrite map_length. rewrite seq_length. reflexivity.
  Qed.

  Lemma nth_nil {X} n d :
    nth n (@nil X) d = d.
  Proof. destruct n; reflexivity. Qed.
        
  Lemma amul_is_pmul' : forall n x y,
      length y = n ->
      pmul n x y = amul weight n x y.
  Proof.
    intros n x y H0. generalize dependent x. apply list_induction_backwards. (* forall x : list Z, length x = n -> pmul n y x = amul n y x *)
    - cbv [pmul amul]. replace (Positional.to_associational weight n []) with (@nil (Z*Z)).
      2: { cbv [Positional.to_associational combine]. destruct (map _ _); reflexivity. }
      replace (Associational.mul [] _) with (@nil (Z*Z)) by reflexivity.
      cbv [Positional.from_associational fold_right]. cbv [Positional.zeros]. cbv [prod_at_index].
      replace (map _ (seq 0 (2 * n - 1))) with (@map nat Z (fun j => 0) (seq 0 (2*n - 1))).
      + remember (2*n - 1)%nat as m eqn:E. clear E. remember (seq 0 m) as l eqn:E. assert (H : length l = m).
        -- rewrite E. apply seq_length.
        -- clear E. generalize dependent l. induction m as [|m' IHm'].
           ++ destruct l as [| l0 l']; try reflexivity. intros H. simpl in H. congruence.
           ++ intros l H. destruct l as [| l0 l'].
              --- simpl in H. congruence.
              --- simpl in H. injection H as H. apply IHm' in H. simpl. f_equal. apply H.
      + apply map_ext. intros a. remember (a + 1)%nat as b eqn:E; clear E.
        remember (seq 0 b) as l eqn:E. assert (H : length l = b).
        -- rewrite E. apply seq_length.
        -- clear E. apply fold_right_invariant; try reflexivity. intros y0 Hin sum IH.
           apply in_map_iff in Hin. destruct Hin as [i [Hin_1 Hin_2] ].
           rewrite nth_default_eq in Hin_1. rewrite nth_nil in Hin_1. lia.
    - intros x l H. cbv [pmul amul]. cbv [Positional.to_associational]. destruct n as [| n']; try reflexivity. rewrite combine_app_one.
      Search (length (map _ _)). rewrite map_length. Search (length (seq _ _)). rewrite seq_length. destruct (S n' <=? length l)%nat eqn:E.
      + cbv [pmul amul] in H. cbv [prod_at_index]. apply Nat.leb_le in E. cbv [Positional.to_associational] in H. rewrite <- H. apply map_ext_in.
        intros a Ha. apply in_seq in Ha. cbv [prod_at_index]. f_equal. apply map_ext_in. intros b Hb. Search (nth _ (_ ++ _)). apply in_seq in Hb.
        repeat rewrite nth_default_eq. rewrite app_nth1 by lia. reflexivity.
      + rewrite Associational.mul_app_l. replace (nth (length l) (map weight (seq 0 (S n'))) x) with (weight (length l)).
        -- rewrite expand_singleton_l. rewrite p_to_a_app. cbv [Positional.from_associational]. rewrite fold_right_app. cbv [amul Positional.from_associational Positional.to_associational] in H.
           rewrite <- H. clear H.

           replace (map _ (combine (map weight (seq 0 (S n'))) y)) with ((*firstn (length y) don't need this, since length y = n*) (map (fun i => (weight (i + length l), x * nth i y 0)) (seq 0 (S n')))).
           2: {
             clear E. generalize dependent y. induction (S n') as [|n'' IHr'].
             - reflexivity.
             - intros y H. assert (H'': (0 < length y)%nat) by lia.
               remember (destruct_list_backwards _ H'') as H' eqn:E; clear E.
               destruct H' as [y0 [y' H'] ]. rewrite H'. rewrite seq_snoc. repeat rewrite map_app.
               rewrite combine_app_samelength.
               + rewrite map_app. repeat rewrite map_cons. repeat rewrite map_nil.
                 rewrite combine_cons. rewrite combine_nil. rewrite map_cons. rewrite map_nil.
                 rewrite H' in H. rewrite app_length in H. simpl in H.
                 replace (0 + n'')%nat with n'' by lia. rewrite <- IHr'.
                 -- replace (combine (map weight (seq 0 n'')) (y0 ++ [y'])) with (combine (map weight (seq 0 n'')) y0).
                    ++ f_equal.
                       --- apply map_ext_in. intros a Ha. f_equal. f_equal. rewrite in_seq in Ha. rewrite app_nth1; try lia.
                       --- f_equal. simpl. rewrite weight_prod_sum. f_equal.
                           +++ f_equal. lia.
                           +++ f_equal. rewrite app_nth2; try lia. replace (n'' - length y0)%nat with 0%nat by lia. reflexivity.
                    ++ rewrite combine_app_one. replace (length (map weight (seq 0 n'')) <=? length y0)%nat with true; try reflexivity. symmetry. apply Nat.leb_le.
                    rewrite map_length. rewrite seq_length. lia.
                 -- lia.
               + rewrite map_length. rewrite seq_length. rewrite H' in H. rewrite app_length in H. simpl in H. lia.
           }
           
           ++ rewrite fold_right_map.
              replace (fold_right _ _ _) with (fold_right (fun x0 y0 => Positional.add_to_nth (x0 + length l) (x * nth x0 y 0) y0) (pmul (S n') l y) (seq 0 (S n'))).
              2: { apply fold_right_ext_in. intros x0 y0 H. rewrite unfold_Let_In. simpl. rewrite place_weight'. simpl.
                   replace (Nat.min (x0 + length l) _) with (x0 + length l)%nat.
                   - rewrite Z.div_same.
                     + f_equal. lia.
                     + apply weight_nz.
                   - apply in_seq in H. apply Nat.leb_nle in E. lia.
              }
              cbv [prod_at_index]. apply (nth_equal 0 1); try lia. intros i x0.
              destruct (i <? 2 * S n' - 1)%nat eqn:E'.
              --- apply Nat.ltb_lt in E'. rewrite (map_nth' _ _ _ 0%nat _).
                  +++ rewrite seq_nth; try apply E'.
                      remember (Z.to_nat _) as thing.                           
                      replace (nth i _ _) with (nth i (pmul (S n') l y) 0 + (if (andb (i - (S n' - 1) <=? length l) (length l <? (i - (S n' - 1)) + thing))%nat then (x * (nth (i - length l) y 0)) else 0)).
                      ---- Search (nth _ (_ ++ _)). Check firstn_app. (*rewrite firstn_app.*) apply Nat.leb_nle in E.
                           replace (S n' - length l)%nat with (S (n' - length l))%nat by lia.
                           replace (0 + i)%nat with i in * by lia.
                           destruct (andb (i - (S n' - 1) <=? length l) (length l <? (i - (S n' - 1)) + thing))%nat eqn:E''.
                           * apply Bool.andb_true_iff in E''. rewrite Nat.leb_le in E''. rewrite Nat.ltb_lt in E''. remember (seq _ _) as theseq.
                           replace (fold_right Z.add 0 (map (fun j : nat => nth' j (l ++ [x]) 0 * nth' (i - j)%nat y 0) theseq)) with
                             (fold_right Z.add 0 (map (fun j : nat => nth' j l 0 * nth' (i - j)%nat y 0) theseq) + x * nth' (i - length l)%nat y 0).
                             ++++ repeat rewrite nth_default_eq. f_equal. symmetry. cbv [pmul]. rewrite (map_nth' _ _ _ 0%nat _).
                                  ----- subst. cbv [prod_at_index]. replace (nth i (seq 0 (2 * S n' - 1)) 0%nat) with i; try reflexivity. rewrite seq_nth; try lia.
                                  ----- rewrite seq_length. lia.
                             ++++ subst. remember (Z.to_nat _) as thing.
                                  ----- replace (seq (i - (S n' - 1)) thing) with
                                          ((seq (i - (S n' - 1)) (length l - (i - (S n' - 1)))) ++ [length l] ++ (seq (length l + 1) (thing - 1 - (length l - (i - (S n' - 1)))))).
                                +++++ repeat rewrite map_app. repeat rewrite split_sum. rewrite <- Z.add_assoc. f_equal.
                                ------ f_equal. apply map_ext_in. intros a Ha. f_equal. repeat rewrite nth_default_eq. rewrite app_nth1; try reflexivity. apply in_seq in Ha. lia.
                                ------ rewrite <- Z.add_comm. rewrite Z.add_assoc. f_equal. repeat rewrite nth_reifiable_spec.
                                ++++++ repeat rewrite map_cons. repeat rewrite map_nil. repeat rewrite fold_right_cons. repeat rewrite fold_right_nil. repeat rewrite nth_default_eq.
                                rewrite (nth_overflow l) by lia. rewrite app_nth2 by lia. replace (length l - length l)%nat with 0%nat by lia. simpl. lia.
                                ++++++ f_equal. apply map_ext_in. intros a Ha. repeat rewrite nth_default_eq. f_equal. apply in_seq in Ha. rewrite nth_overflow; try rewrite firstn_length; try lia.
                                rewrite nth_overflow; try reflexivity. rewrite app_length. replace (length [x]) with 1%nat by reflexivity. lia.
                                +++++ replace ([length l]) with (seq (length l) 1) by reflexivity.
                                rewrite <- seq_add. replace (seq (length l)) with (seq ((i - (S n' - 1)) + (length l - (i - (S n' - 1)))))%nat. 2: { f_equal. lia. } rewrite <- seq_add. f_equal. lia.
                           * apply Bool.andb_false_iff in E''. rewrite Nat.leb_nle in E''. rewrite Nat.ltb_nlt in E''. cbv [pmul]. rewrite (map_nth' _ _ _ 0%nat _).
                             ++++ cbv [prod_at_index]. replace (nth i (seq 0 (2 * S n' - 1)) 0%nat) with i. 
                                  ----- rewrite Z.add_0_r. f_equal. subst. apply map_ext_in. intros a Ha. apply in_seq in Ha. repeat rewrite nth_default_eq. f_equal. destruct E'' as [E''|E''].
                                  +++++ repeat rewrite nth_overflow. reflexivity.
                                  ------ lia.
                                  ------ rewrite app_length. cbn [length]. lia.
                                  +++++ apply app_nth1. lia.
                                  ----- rewrite seq_nth; try lia.
                             ++++ rewrite seq_length. lia.
                             ---- destruct ((i - (S n' - 1) <=? length l)%nat && (length l <? i - (S n' - 1) + thing)%nat)%bool eqn:E''.
                                  ++++ remember (pmul _ _ _) as p eqn:Ep. assert (H: (length p = 2 * (S n') - 1)%nat).
                                       { subst. apply length_pmul. }
                                       rewrite <- H in E'. destruct (i - length l <? length y)%nat eqn:E7.
                                       ** replace (seq 0 (S n')) with (seq 0 (i - length l) ++ [i - length l] ++ seq (i - length l + 1) (S n' - (i - length l) - 1))%nat.
                                       ----- repeat rewrite fold_right_app. remember (fold_right _ (fold_right _ p _) _) as the_list eqn:E3.
                                       remember (fun _ _ => _) as the_fun eqn:E4.
                                       replace (nth i (fold_right the_fun the_list (seq 0 (i - length l))) x0) with (nth i the_list x0).
                                       +++++ rewrite E3. clear E3 the_list. remember (fold_right the_fun p _) as the_list eqn:E3.
                                       replace (nth i (fold_right the_fun the_list [(i - length l)%nat]) x0) with ((nth i the_list x0) + x * nth (i - length l) y 0).
                                       ------ rewrite E3. clear E3. replace (nth i (fold_right the_fun p _) x0) with (nth i p x0).
                                       ++++++ f_equal. apply nth_indep. lia.
                                       ++++++ apply fold_right_invariant.
                                       ------- reflexivity.
                                       ------- intros y0 Hin l' IH. rewrite E4; clear E4. rewrite mth_add_to_nth.
                                       +++++++ apply IH.
                                       +++++++ apply in_seq in Hin. lia.
                                       ------ simpl. rewrite E4. apply Bool.andb_true_iff in E''. rewrite Nat.leb_le in E''. rewrite Nat.ltb_lt in E''.
                                       replace (i - length l + length l)%nat with i by lia. rewrite nth_add_to_nth.
                                       replace (i <? length the_list)%nat with true.
                                       ++++++ reflexivity.
                                       ++++++ symmetry. rewrite Nat.ltb_lt. replace (length the_list) with (length p); try lia. rewrite E3; clear E3. apply fold_right_invariant.
                                       ------- reflexivity.
                                       ------- intros y0 H' l' IH. rewrite E4; clear E4. rewrite Positional.length_add_to_nth. apply IH.
                                       +++++ apply fold_right_invariant; try reflexivity. intros y0 H' l' IH. rewrite E4. rewrite mth_add_to_nth.
                                       ------ apply IH.
                                       ------ apply in_seq in H'. lia.
                                       ----- replace [(i - length l)%nat] with (seq (i - length l)%nat 1) by reflexivity. rewrite <- seq_app. rewrite <- seq_app. f_equal.
                                       rewrite Bool.andb_true_iff in E''. rewrite Nat.leb_le in E''. rewrite Nat.ltb_lt in E''. rewrite H in E'. apply Nat.ltb_lt in E7. lia.
                                       ** rewrite (nth_overflow y).
                                          ----- rewrite Z.mul_0_r. rewrite Z.add_0_r. remember (fold_right _ _ _) as pp eqn:E11. apply (@proj2 (length pp = length p)).
                                          rewrite E11; clear E11. apply fold_right_invariant.
                                          +++++ split; try reflexivity. apply nth_indep. lia.
                                          +++++ intros y0 H' l' [IH1 IH2]. rewrite Positional.length_add_to_nth. split; try apply IH1.
                                          destruct (y0 + length l =? i)%nat eqn:E8.
                                          ------ apply Nat.eqb_eq in E8. rewrite E8. rewrite nth_add_to_nth. destruct (i <? length l')%nat eqn:E10.
                                          ++++++ rewrite (nth_overflow y).
                                          ------- rewrite IH2. lia.
                                          ------- apply in_seq in H'. apply Nat.ltb_nlt in E7. rewrite Bool.andb_true_iff in E''. rewrite Nat.leb_le in E''. rewrite Nat.ltb_lt in E''.
                                          apply Nat.leb_nle in E. apply Nat.ltb_lt in E10. lia.
                                          ++++++ apply IH2.
                                          ------ apply Nat.eqb_neq in E8. rewrite mth_add_to_nth.
                                          ++++++ apply IH2.
                                          ++++++ lia.
                                          ----- apply Nat.ltb_nlt in E7. lia.
                                          ++++ rewrite Z.add_0_r. apply fold_right_invariant.
                                               ----- apply nth_indep. rewrite length_pmul. lia.
                                               ----- intros y0 H l' IH. rewrite mth_add_to_nth; try apply IH. rewrite Bool.andb_false_iff in E''.
                                               rewrite Nat.leb_nle in E''. rewrite Nat.ltb_nlt in E''. rewrite Nat.leb_nle in E. apply in_seq in H. lia.
                                          +++ rewrite seq_length. lia.
                                          --- repeat rewrite nth_overflow; try reflexivity.
                                              +++ replace (length _) with (2 * S n' - 1)%nat.
                                                  ---- apply Nat.ltb_nlt in E'. lia.
                                                  ---- apply fold_right_invariant.
                                                       ++++ rewrite length_pmul. lia.
                                                       ++++ intros y0 Hin l' IH. rewrite Positional.length_add_to_nth. apply IH.
                                              +++ rewrite map_length. rewrite seq_length. apply Nat.ltb_nlt in E'. lia.
                             -- clear H H0. rewrite (map_nth' _ _ _ 0%nat).
                                ++ rewrite seq_nth.
                                   --- f_equal; lia.
                                   --- apply Nat.leb_nle in E. lia.
                                ++ apply Nat.leb_nle in E. rewrite seq_length. lia.
  Qed.

  Definition pad_or_truncate (len : nat) (l : list Z) : list Z :=
    (firstn len l) ++ (repeat 0 (len - length l)%nat).

  Lemma pad_or_truncate_length (len : nat) (l : list Z) :
    length (pad_or_truncate len l) = len.
  Proof. cbv [pad_or_truncate]. rewrite app_length. rewrite firstn_length. rewrite repeat_length. lia. Qed.

  Lemma nth_pad_default {X} (i : nat) (l : list X) (d : X) (n : nat) :
    nth i l d = nth i (l ++ repeat d n) d.
  Proof.
    Search (nth _ (_ ++ _)). destruct (i <? length l)%nat eqn:E.
    - apply Nat.ltb_lt in E. rewrite app_nth1; try apply E. reflexivity.
    - apply Nat.ltb_nlt in E. rewrite app_nth2; try lia. Search (nth _ (repeat _ _) _). rewrite nth_repeat. rewrite nth_overflow; try lia. reflexivity.
  Qed.

  Lemma nth_firstn {X} (l : list X) (n i : nat) (d : X) :
    nth i (firstn n l) d = if (i <? n)%nat then nth i l d else d.
  Proof.
    repeat rewrite nth_error_nth_full. rewrite nth_error_firstn.
    destruct (i <? n)%nat eqn:E.
    - apply Nat.ltb_lt in E. destruct (lt_dec i n); try lia. reflexivity.
    - apply Nat.ltb_nlt in E. destruct (lt_dec i n); try lia. reflexivity.
  Qed.
  
  Lemma pmul'_doesnt_care_about_zeros n x y :
    pmul n x y = pmul n x (pad_or_truncate n y).
  Proof.
    cbv [pad_or_truncate pmul]. cbv [prod_at_index]. apply map_ext_in. intros a1 Ha1. f_equal. apply map_ext_in. intros a2 Ha2. repeat rewrite nth_default_eq. f_equal. rewrite <- nth_pad_default.
    rewrite nth_firstn. apply in_seq in Ha1. apply in_seq in Ha2. replace (_ <? _)%nat with true; try reflexivity. symmetry. apply Nat.ltb_lt. lia.
  Qed.

  Lemma amul_doesnt_care_about_zeros n x y :
    amul weight n x y = amul weight n x (pad_or_truncate n y).
  Proof.
    generalize dependent x. apply list_induction_backwards. (* we have to use induction because we want the left factor (x) to be a singleton, so we can apply mul_singleton_l_app_r *)
    - cbv [amul]. cbv [Positional.to_associational]. Search (combine _ []). rewrite combine_nil_r. simpl. reflexivity.
    - intros xn x' IHx'. cbv [amul]. cbv [Positional.to_associational]. Search (combine _ (_ ++ _)). rewrite combine_app_one. destruct (_ <=? _)%nat eqn:E0; try apply IHx'.
      repeat rewrite Associational.mul_app_l. Search Positional.add_to_nth. rewrite p_to_a_app. Check p_to_a_app. rewrite (p_to_a_app _ _ (Associational.mul (combine _ _) _)).
      cbv [Positional.from_associational]. repeat rewrite fold_right_app. cbv [amul Positional.from_associational Positional.to_associational] in IHx'. rewrite IHx'. clear IHx'.
      remember (fold_right _ (Positional.zeros _) _) as some_list eqn:clearMe; clear clearMe.
      remember (fold_right _ _ _) as thegoal eqn:E1. remember (fun _ _ => _) as the_fun eqn:E2.
      cbv [pad_or_truncate]. Search Positional.to_associational. cbv [Positional.to_associational].
    assert (E: seq 0 n = seq 0 (Nat.min (length y) n) ++ seq (length y) (n - length y)).
    { destruct (length y <=? n)%nat eqn:E'.
      - apply Nat.leb_le in E'. replace (Nat.min (length y) n) with (length y) by lia. rewrite <- seq_app. f_equal. lia.
      - apply Nat.leb_nle in E'. replace (Nat.min (length y) n) with n by lia. replace (n - length y)%nat with 0%nat by lia. simpl. rewrite app_nil_r. reflexivity.
    }
    rewrite E. rewrite map_app. rewrite combine_app_samelength.
      + rewrite Associational.mul_singleton_l_app_r. (*rewrite (combine_add_garbage_l _ (firstn _ _) (map weight (seq (length y) (n - length y)))).*)
        -- rewrite <- map_app. rewrite <- E.
           cbv [Positional.from_associational]. rewrite fold_right_app. rewrite E1. f_equal.
           2: { f_equal. remember (map weight (seq 0 n)) as x eqn:Ex. destruct (length y <=? n)%nat eqn:E3.
                - apply Nat.leb_le in E3. Search (firstn _ _ = _). rewrite firstn_all2 by lia. replace (map weight (seq 0 (Nat.min _ _))) with (firstn (length y) x).
                  + apply combine_truncate_l.
                  + replace (Nat.min (length y) n) with (length y) by lia. subst. Check firstn_map. rewrite firstn_map. f_equal. Check firstn_seq. rewrite firstn_seq. f_equal. lia.
                - apply Nat.leb_nle in E3. replace (Nat.min (length y) n) with n by lia. rewrite <- Ex. replace n with (length x). apply combine_truncate_r. subst. rewrite map_length.
                  rewrite seq_length. lia. }
           apply fold_right_invariant; try reflexivity. intros y0 Hin l' IHl'. rewrite E2; clear E2. rewrite unfold_Let_In. cbv [Associational.mul] in Hin. apply in_flat_map in Hin.
           destruct Hin as [x0 [Hin_1 Hin_2] ]. destruct y0 as [y0_1 y0_2]. Search (In _ (combine _ _)). apply in_map_iff in Hin_2. destruct Hin_2 as [y0' [Hin_2_1 Hin_2_2] ].
           destruct y0' as [y0'_1 y0'_2].
           remember (in_combine_l _ _ _ _ Hin_2_2) as Hin_2_2_l eqn:clearMe; clear clearMe. remember (in_combine_r _ _ _ _ Hin_2_2) as Hin_2_2_r eqn:clearMe; clear clearMe. Search (In _ (repeat _ _)).
           apply repeat_spec in Hin_2_2_r.
           rewrite Hin_2_2_r in *; clear Hin_2_2 Hin_2_2_r. simpl in Hin_2_1. Search (In _ (map _ _)). apply in_map_iff in Hin_2_2_l.
           destruct Hin_2_2_l as [i [defi rangei] ].
           injection Hin_2_1 as E1' E2'. rewrite <- E2'. rewrite <- E1' in *. clear E1' E2'. apply in_inv in Hin_1. simpl in Hin_1. destruct Hin_1 as [Hin_1 | Hin_1].  2: { exfalso. apply Hin_1. }
                                                                                                                                                                     Search (nth _ (seq _ _)). apply Nat.leb_nle in E0. rewrite map_length in E0. rewrite seq_length in E0. Search map_nth'. Check map_nth'. rewrite (map_nth' _ _ _ 0%nat) in Hin_1.
           ++ rewrite seq_nth in Hin_1 by lia. rewrite <- Hin_1 in *; clear Hin_1 x0. simpl. rewrite <- defi; clear defi y0'_1. rewrite weight_prod_sum. rewrite place_weight'. simpl.
              repeat rewrite Z.mul_0_r. rewrite Positional.add_to_nth_zero. apply IHl'.
           ++ rewrite seq_length. lia.
      + rewrite firstn_length. rewrite map_length. rewrite seq_length. lia.
  Qed.

  Lemma amul_is_pmul : forall n x y,
      pmul n x y = amul weight n x y.
  Proof.
    intros n x y. rewrite amul_doesnt_care_about_zeros. rewrite pmul'_doesnt_care_about_zeros. apply amul_is_pmul'. Search (length (pad_or_truncate _ _)). apply pad_or_truncate_length.
  Qed.

  Definition seq_from_to a b := seq a (Z.to_nat (Z.of_nat b - Z.of_nat a + 1)).
  
  Definition adk_mul_prod_at_i (n : nat) (x y products f : list Z) (i : nat) : Z :=
    fold_right Z.add 0 (map (fun j => (nth' j x 0 - nth' (i - j)%nat x 0) * (nth' (i - j)%nat y 0 - nth' j y 0))
                          (seq (i - (n - 1)) (Z.to_nat (1 + ((Z.of_nat i + 1)/2 - 1) - Z.of_nat (i - (n - 1))%nat)%Z))) +
      (if (i =? 2 * n - 2)%nat then
         nth' (n - 1)%nat products 0
       else
         nth' i f 0 - if (i <? n)%nat then 0 else nth' (i - n)%nat f 0).
  
  Definition adk_mul' (n : nat) (x y products f : list Z) : list Z :=
    map (adk_mul_prod_at_i n x y products f) (seq 0 (2*n - 1)).
  
  Definition adk_mul (n : nat) (x y : list Z) : list Z :=
    dlet high_product : Z := (nth' (n - 1)%nat x 0) * (nth' (n - 1)%nat y 0) in
        let products : list Z := map (fun i => (nth' i x 0) * (nth' i y 0)) (seq 0 (n - 1)) ++ [high_product] ++ (repeat 0 (n - 1)) (*the total length of products should be (2*n - 1), since this is
                                                                                                                                    what we want the length of f to be.*) in
        (list_rect
           (fun _ => list Z -> list Z)
           (fun f => adk_mul' n x y products (rev f))
           (fun p _ g => fun f' => Let_In ((nth' 0%nat f' 0) + p) (fun x => g (x :: f'))) 
           products) [].

  (*Lemma adk_mul'_ext nth1 nth2 n x y p f :
    (forall i l d, nth1 i l d = nth2 i l d) ->
    adk_mul' nth1 n x y p f = adk_mul' nth2 n x y p f.
  Proof.
    intros H. cbv [adk_mul']. apply map_ext. intros i. cbv [adk_mul_prod_at_i]. f_equal.
    - f_equal. apply map_ext. intros j. repeat rewrite H. reflexivity.
    - repeat rewrite H. reflexivity.
  Qed.
    
  Definition adk_mul_ext nth1 nth2 n x y :
    (forall i l d, nth1 i l d = nth2 i l d) ->
    adk_mul nth1 n x y = adk_mul nth2 n x y.
  Proof.
    intros H. cbv [adk_mul]. repeat rewrite unfold_Let_In.
    repeat rewrite <- eq_fold_right_list_rect. Check fold_right_ext.
    remember [] as z eqn:clearMe; clear clearMe.
    remember
      (map (fun i : nat => nth2 i x 0 * nth2 i y 0) (seq 0 (n - 1)) ++
         (nth2 (n - 1)%nat x 0 * nth2 (n - 1)%nat y 0 :: z) ++ repeat 0 (n - 1))
      as l1 eqn:El1.
    remember
      (map (fun i : nat => nth1 i x 0 * nth1 i y 0) (seq 0 (n - 1)) ++
         (nth1 (n - 1)%nat x 0 * nth1 (n - 1)%nat y 0 :: z) ++ repeat 0 (n - 1))
      as l2 eqn:El2.
    replace l1 with l2.
    - clear El1 El2. generalize dependent z. rename l2 into l. remember l as ll eqn:El.
      replace (adk_mul' nth1 n x y ll) with (adk_mul' nth1 n x y l).
      + replace (adk_mul' nth2 n x y ll) with (adk_mul' nth2 n x y l).
        -- clear El. induction ll as [|ll0 ll' IHll'].
           ++ intros z. simpl. apply adk_mul'_ext. apply H.
           ++ intros z. simpl. repeat rewrite unfold_Let_In. repeat rewrite H. apply IHll'.
        -- f_equal. symmetry. apply El.
      + f_equal. symmetry. apply El.
    - subst. repeat rewrite H. f_equal. apply map_ext. intros a. repeat rewrite H. reflexivity.
  Qed.*)

  Local Notation nth_ := 5.
  
  Definition friendly_adk_mul (n : nat) (x y : list Z) : list Z :=
    let products : list Z := map (fun i => (nth' i (firstn n x) 0) * (nth' i (firstn n y) 0)) (seq 0 (2*n - 1)) in
    let f_rev : list Z := fold_left (fun l p => (nth' 0%nat l 0) + p :: l) products [] in
    adk_mul' n x y products (rev f_rev).
  
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
    cbv [adk_mul]. rewrite unfold_Let_In. rewrite friendly_list_rect.
    destruct (n =? 0)%nat eqn:E.
    - apply Nat.eqb_eq in E. subst. reflexivity.
    - apply Nat.eqb_neq in E.
      replace (_ ++ _ ++ _) with (map (fun i => (nth' i (firstn n x) 0) * (nth' i (firstn n y) 0)) (seq 0 (2*n - 1))).
      + cbv [friendly_adk_mul]. reflexivity.
      + replace (2 * n - 1)%nat with ((n - 1) + 1 + (n - 1))%nat by lia. repeat rewrite seq_app. repeat rewrite map_app.
        rewrite <- app_assoc. f_equal.
        -- apply map_ext_in. intros a Ha. apply in_seq in Ha. repeat rewrite nth_default_eq. repeat rewrite nth_firstn. destruct (a <? n)%nat eqn:E'; try reflexivity. apply Nat.ltb_nlt in E'. lia.
        -- f_equal.
           ++ simpl. repeat rewrite nth_default_eq. repeat rewrite nth_firstn. replace (n - 1 <? n)%nat with true; try reflexivity. symmetry. apply Nat.ltb_lt. lia.
           ++ replace (0 + (n - 1 + 1))%nat with n by lia. replace (repeat 0 (n - 1)) with (repeat 0 (length (seq n (n - 1)))).
              --- rewrite <- map_const. apply map_ext_in. intros a Hin. repeat rewrite nth_default_eq. repeat rewrite nth_firstn. destruct (a <? n)%nat eqn:E'; try reflexivity. apply Nat.ltb_lt in E'.
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
                  rewrite map_app. cbn [map]. Search (fold_right Z.add). rewrite split_sum. cbn [fold_right]. f_equal.
                  +++ f_equal. f_equal. f_equal. lia.
                  +++ rewrite Z.add_0_r. f_equal.
                      ---- f_equal. lia.
                      ---- f_equal. lia.
              --- apply Nat.ltb_nlt in E. replace m' with 0%nat by lia. simpl. rewrite rev_involutive. destruct f'_rev as [|f0 f'_rev'].
                  +++ rewrite nth_nil. lia.
                  +++ simpl in IHlen. rewrite app_length in IHlen. cbn [length] in IHlen. lia.
        -- apply Nat.ltb_nlt in E1. rewrite nth_overflow.
           ++ reflexivity.
           ++ rewrite app_length. cbn [length]. lia.
      + rewrite app_length. cbn [length]. lia.
  Qed.
  
  Lemma adk_mul_friendlier (n : nat) (x y : list Z) :
    friendly_adk_mul n x y = friendlier_adk_mul n x y.
  Proof.
    cbv [friendly_adk_mul adk_mul_prod_at_i adk_mul' friendlier_adk_mul friendlier_adk_prod_at_i].
    apply map_ext_in. repeat rewrite nth_default_eq. intros i Hi. apply in_seq in Hi. f_equal.
    1: { f_equal. apply map_ext. intros j. repeat rewrite nth_default_eq. reflexivity. }
    repeat rewrite nth_default_eq. repeat rewrite f_spec. replace (i - n <? 2 * n - 1)%nat with true.
    - replace (i <? 2 * n - 1)%nat with true.
      + repeat rewrite nth_default_eq. destruct (i =? 2 * n - 2)%nat eqn:E.
        -- apply Nat.eqb_eq in E. replace (Z.to_nat _) with 1%nat by lia. repeat rewrite (map_nth' _ _ _ 0%nat).
           ++ repeat rewrite nth_default_eq. rewrite seq_nth by lia. repeat rewrite nth_firstn. replace (_ <? _)%nat with true.
              --- cbn [seq map fold_right]. rewrite Z.add_0_r. f_equal.
                  +++ f_equal. lia.
                  +++ f_equal. lia.
              --- symmetry. apply Nat.ltb_lt. lia.
           ++ rewrite seq_length. lia.
        -- clear E. destruct (i <? n)%nat eqn:E.
           ++ apply Nat.ltb_lt in E. rewrite Z.sub_0_r. f_equal. replace (seq _ _) with (seq_from_to 0 i).
              --- repeat rewrite nth_default_eq. apply map_ext_in. intros j Hj. apply in_seq in Hj. repeat rewrite nth_firstn. replace (_ <? _)%nat with true.
                  +++ reflexivity.
                  +++ symmetry. apply Nat.ltb_lt. lia.
              --- cbv [seq_from_to]. f_equal; lia.
           ++ apply Nat.ltb_nlt in E. replace (seq_from_to 0 i) with (seq_from_to 0 (i - n) ++ seq_from_to (i - n + 1) i).
              --- rewrite map_app. rewrite split_sum. ring_simplify. Print friendly_adk_mul. remember (Z.to_nat _) as seqlen.
                  replace (seq_from_to (i - n + 1) i) with (seq (i - (n - 1)) seqlen ++ seq (i - (n - 1) + seqlen) (1 + i - (i - n + 1) - seqlen)).
                  2: { rewrite <- seq_app. cbv [seq_from_to]. f_equal; lia. }
                  rewrite map_app. rewrite split_sum. rewrite <- Z.add_0_r. f_equal.
                  +++ f_equal. apply map_ext_in. intros j Hj. apply in_seq in Hj. repeat rewrite nth_firstn. replace (j <? n)%nat with true.
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

    Lemma adk_mul_is_pmul (n : nat) (x y : list Z) :
      adk_mul n x y = pmul n x y.
    Proof.
      rewrite adk_mul_friendly. rewrite adk_mul_friendlier.
      cbv [friendlier_adk_mul pmul]. cbv [prod_at_index friendlier_adk_prod_at_i].
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
        (*assert (H: (i - (S n' - 1) <= (i + 1) / 2 - 1 <-> i - (S n' - 1) <= S n' <= i)%nat).
        { assert (H: (S n' <= (i + 1) / 2 - 1 <-> S n' + 1 <= (i + 1) / 2)%nat) by lia.
          Search Nat.div2. Search Nat.div2. Search Nat.Even.
          destruct (Nat.Even_or_Odd (i + 1)) as [H'|H'].
          - Search Nat.div2. apply Nat.Even_double in H'. cbv [Nat.double] in H'.
            Search Nat.div2. rewrite <- Nat.div2_div. split.
            + intros H1. split; try lia.
            + intros H1. .lolollooooollia. 
            nia. lia.*)
        (*assert (H: (i - (S n' - 1) <= (i + 1) / 2 - 1 <-> 2 * (i - S n' - 1) + 1 <= i)%nat).
        { rewrite <- Nat.div2_div. destruct (Nat.Even_or_Odd (i + 1)) as [H'|H'].
          - apply Nat.Even_double in H'. cbv [Nat.double] in H'. split; try lia.
          - apply Nat.Odd_double in H'. cbv [Nat.double] in H'. lia. }*)
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
             (*assert (E1 : S n' = 1%nat \/ ~ Z.of_nat (S n') - 1 <= Z.of_nat i \/ ~ Z.of_nat i <= 2 * Z.of_nat (S n') - 3) by lia.*)
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
             (*assert (H: (((i - (S n' - 1)) = (i - (n' - 1)) /\ (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat (i - (S n' - 1)))) =
                                                                 (Z.to_nat (1 + Z.min (Z.of_nat (n') - 1) (Z.of_nat i) - Z.of_nat (i - (n' - 1))))) \/ (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat (i - (S n' - 1)))) = 0)%nat) by lia.*)
             destruct H as [H|H].
             ++ replace (i - (S n' - 1))%nat with 0%nat in * by lia. replace (i - (n' - 1))%nat with 0%nat in * by lia.
                replace (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat 0)) with
                  (Z.to_nat (1 + Z.min (Z.of_nat n' - 1) (Z.of_nat i) - Z.of_nat 0))
                  in * by lia. rewrite <- IHn'. clear IHn'. f_equal.
                (*--- f_equal. apply map_ext_in. intros a Ha. apply in_seq in Ha. Search firstn.
                    repeat rewrite nth_firstn. replace (_ <? _)%nat with true. replace (_ <? _)%nat with true. replace (_ <? _)%nat with true. replace (_ <? _)%nat with true. reflexivity.
                    +++ symmetry. apply Nat.ltb_lt. lia.
                    +++ symmetry. apply Nat.ltb_lt. lia.
                    +++ symmetry. apply Nat.ltb_lt. lia.
                    +++ symmetry. apply Nat.ltb_lt. lia.*)
                --- f_equal. replace ((Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (S n') - 1) - Z.of_nat 0))) with
                      (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat n' - 1) - Z.of_nat 0)) by lia. apply map_ext_in.
                    intros a Ha. apply in_seq in Ha. reflexivity.
             ++ replace (Z.to_nat (1 + Z.min (Z.of_nat (S n') - 1) (Z.of_nat i) - Z.of_nat (i - (S n' - 1)))) with 0%nat by lia.
                (*replace (Z.to_nat (1 + Z.min (Z.of_nat n' - 1) (Z.of_nat i) - Z.of_nat (i - (n' - 1)))) with 0%nat in * by lia.*)
                replace ((Z.to_nat (1 + ((Z.of_nat i + 1) / 2 - 1) - Z.of_nat (i - (S n' - 1))))) with 0%nat by lia.
                replace (Z.to_nat (1 + Z.min (Z.of_nat i) (Z.of_nat (S n') - 1) - Z.of_nat (i - (S n' - 1)))) with 0%nat by lia.
                reflexivity.
    Qed.
    
    Lemma eval_pmul n x y :
      Positional.eval weight n x * Positional.eval weight n y =
        Positional.eval weight (2*n - 1) (pmul n x y).
    Proof.
      Search amul. rewrite amul_is_pmul. cbv [amul]. Search Positional.from_associational.
      rewrite Positional.eval_from_associational.
      - Search Associational.mul. rewrite Associational.eval_mul. Search Positional.to_associational. repeat rewrite Positional.eval_to_associational. reflexivity.
      - apply weight_0.
      - apply weight_nz.
      - destruct (dec (2 * n - 1 = 0)%nat).
        + right. cbv [Positional.to_associational]. replace n with 0%nat by lia. reflexivity.
        + lia.
    Qed.

    Lemma eval_adk_mul n x y :
      Positional.eval weight n x * Positional.eval weight n y =
        Positional.eval weight (2 * n - 1) (adk_mul n x y).
    Proof. rewrite adk_mul_is_pmul. rewrite eval_pmul. reflexivity. Qed.      
End Nice_weight.

Definition everything_nonneg_assoc : list (Z*Z) -> Prop :=
  Forall (fun wv => 0 <= fst wv /\ 0 <= snd wv).

Definition everything_nonneg_pos : list Z -> Prop :=
  Forall (fun v => 0 <= v).

Definition values_le_assoc : list (Z*Z) -> list (Z*Z) -> Prop :=
  Forall2 (fun wv1 wv2 => fst wv1 = fst wv2 /\ snd wv1 <= snd wv2).

Definition values_le_pos : list Z -> list Z -> Prop :=
  Forall2 (fun v1 v2 => v1 <= v2).

Lemma le_nonneg_pos p p' :
  everything_nonneg_pos p ->
  values_le_pos p p' ->
  everything_nonneg_pos p'.
Proof.
  cbv [everything_nonneg_pos values_le_pos]. generalize dependent p.
  induction p' as [|p'0 p'' IHp''].
  - intros p H1 H2. apply Forall_nil.
  - intros p H1 H2. inversion H2. subst. inversion H1. subst. apply Forall_cons.
    + lia.
    + eapply IHp''.
      -- eassumption.
      -- assumption.
Qed.

Lemma Forall2_same (A : Type) (l : list A) (P : A -> A -> Prop) :
  Forall2 P l l <-> Forall (fun x => P x x) l.
Proof.
  split.
  - induction l as [|x l' IHl'].
    + intros H. apply Forall_nil.
    + intros H. inversion H. subst. constructor; auto.
  - induction l as [|x l' IHl'].
    + constructor.
    + intros H. inversion H. subst. constructor; auto.
Qed.

(*Lemma le_nonneg_assoc p p' :
  everything_nonneg_assoc p ->
  values_le_assoc p p' ->
  everything_nonneg_assoc p'.
Proof.
  cbv [everything_nonneg_pos values_le_pos]. generalize dependent p.
  induction p' as [|p'0 p'' IHp''].
  - intros p H1 H2. apply Forall_nil.
  - intros p H1 H2. inversion H2. subst. inversion H1. subst. apply Forall_cons.
    + lia.
    + eapply IHp''.
      -- eassumption.
      -- assumption. (* same proof script as previous proof *)
Qed.*)

Lemma mul_nonneg p q :
  everything_nonneg_assoc p ->
  everything_nonneg_assoc q ->
  everything_nonneg_assoc (Associational.mul p q).
Proof.
  cbv [everything_nonneg_assoc]. intros Hp Hq. induction p as [|p0 p' IHp'].
  - simpl. apply Forall_nil.
  - replace (p0 :: p') with ([p0] ++ p') by reflexivity. rewrite Associational.mul_app_l.
    apply Forall_app. inversion Hp. subst. split.
    + clear Hp IHp'. cbv [Associational.mul]. cbn [flat_map].
      rewrite app_nil_r. apply Forall_map. simpl. try rewrite Forall_forall in *.
      intros x Hx. apply Hq in Hx. lia.
    + apply IHp'. assumption.
Qed.

Check Forall_map. Search Forall2.

Lemma Forall2_map :
  forall (A1 A2 B1 B2 : Type) (f1 : A1 -> B1) (f2 : A2 -> B2) (P : B1 -> B2 -> Prop)
         (l1 : list A1) (l2 : list A2),
    Forall2 P (map f1 l1) (map f2 l2) <->
      Forall2 (fun (x1 : A1) (x2 : A2) => P (f1 x1) (f2 x2)) l1 l2.
Proof.
  intros. split.
  - generalize dependent l2. induction l1 as [|l10 l1' IHl1'].
    + intros l2 H. simpl in H. inversion H. destruct l2; try (cbn [map] in *; congruence).
      apply Forall2_nil.
    + intros l2 H. destruct l2; simpl in H; inversion H. subst. apply Forall2_cons.
      -- Search Forall2. assumption.
      -- apply IHl1'. assumption.
  - generalize dependent l2. induction l1 as [|l10 l1' IHl1'].
    + intros l2 H. inversion H. subst. simpl. apply Forall2_nil.
    + intros l2 H. inversion H. subst. simpl. apply Forall2_cons.
      -- assumption.
      -- apply IHl1'. assumption.
Qed.

Check Forall2_app.

Lemma Forall2_app_one {A B : Type} (R : A -> B -> Prop) l1 l2 x1 x2 :
  Forall2 R (l1 ++ [x1]) (l2 ++ [x2]) ->
  Forall2 R l1 l2 /\ Forall2 R [x1] [x2].
Proof.
  induction l1 as [|l0 l' IHl'].
  - intros H. simpl in H. inversion H as [H1|]. inversion H1. subst. Search (_ = _ ++ _).
    destruct l2; try (split; assumption). simpl in H4. Admitted. (*discriminate H4. congruence. inversion H4.*)
  

Lemma or_to_and (P1 P2 Q : Prop) : (P1 \/ P2 -> Q) <-> ((P1 -> Q) /\ (P2 -> Q)).
Proof. split; auto. intros H1 H2. destruct H1. destruct H2; auto. Qed.

Check Zmult_le_compat_r.

Lemma mul_monotone_l p p' q :
  everything_nonneg_assoc p ->
  everything_nonneg_assoc q ->
  values_le_assoc p p' ->
  values_le_assoc (Associational.mul p q) (Associational.mul p' q).
Proof.
  intros Hp Hq Hle.
  generalize dependent p'. induction p as [|p0 p_rest IHp_rest].
  - intros p' Hle. inversion Hle. subst. rewrite Associational.mul_nil_l. constructor.
  - intros p' Hle. cbv [everything_nonneg_assoc values_le_assoc] in *. inversion Hle. subst.
    inversion Hp. subst. rewrite Forall_forall in Hq.
    (*Search (_ \/ _ -> _).
    assert (Hp1: forall x : Z*Z, p0 = x -> 0 <= fst x /\ 0 <= snd x) by auto.
    assert (Hp2: forall x : Z*Z, In x p_rest -> 0 <= fst x /\ 0 <= snd x) by auto.*)
    repeat rewrite Associational.mul_cons_l. inversion Hle. subst. apply Forall2_app.
    + Search Forall2. Search (Forall2 _ (map _ _)). apply Forall2_map. simpl. apply Forall2_same.
      apply Forall_forall. intros x Hx. assert (H1' : 0 <= fst x /\ 0 <= snd x) by auto.
      assert (H2' : 0 <= fst p0 /\ 0 <= snd p0) by auto. split; try lia. (* lia doesn't work:( *)
      apply Zmult_le_compat_r; try lia.
    + apply IHp_rest.
      -- assumption.
      -- assumption.
Qed.
      
Lemma mul_monotone_r p q q' :
  everything_nonneg_assoc p ->
  everything_nonneg_assoc q ->
  values_le_assoc q q' ->
  values_le_assoc (Associational.mul p q) (Associational.mul p q').
Proof.
  cbv [everything_nonneg_assoc values_le_assoc] in *. intros Hp Hq Hle.
  induction p as [|p0 p_rest IHp_rest].
  - simpl. apply Forall2_nil.
  - inversion Hp. subst. rewrite Forall_forall in Hq.
    (*Search (_ \/ _ -> _).
    assert (Hp1: forall x : Z*Z, p0 = x -> 0 <= fst x /\ 0 <= snd x) by auto.
    assert (Hp2: forall x : Z*Z, In x p_rest -> 0 <= fst x /\ 0 <= snd x) by auto.*)
    repeat rewrite Associational.mul_cons_l. apply Forall2_app.
    + apply Forall2_map. simpl. Print Forall2_impl.
      apply (@Forall2_impl _ _ (fun wv1 wv2 : Z * Z => fst wv1 = fst wv2 /\ snd wv1 <= snd wv2)).
      -- intros. split; try lia. inversion Hp. subst. apply Zmult_le_compat_l; lia.
      -- assumption.
    + apply IHp_rest. assumption.
Qed.

Check list_induction_backwards. Check (0 = 0 -> 0 = 0).

Lemma to_associational_nonneg weight n p :
  (forall i, 0 <= weight i) ->
  everything_nonneg_pos p ->
  everything_nonneg_assoc (Positional.to_associational weight n p).
Proof.
  intros Hweight. cbv [everything_nonneg_assoc everything_nonneg_pos Positional.to_associational].
  intros H. rewrite Forall_forall. rewrite Forall_forall in H. intros x Hx1.
  assert (Hx2 := Hx1). destruct x as [x1 x2]. apply in_combine_l in Hx1. apply in_combine_r in Hx2.
  rewrite in_map_iff in Hx1. destruct Hx1 as [x1' [Hx1' _] ].
  apply H in Hx2. assert (Hweightx1' := Hweight x1'). simpl. lia.
Qed. Check combine_nth.

Lemma combine_nth' {A B : Type} (l : list A) (l' : list B) (n : nat) (d : A*B) :
  (n < length (combine l l'))%nat -> nth n (combine l l') d = (nth n l (fst d), nth n l' (snd d)).
Proof.
  intros H. Search (length (combine _ _)). rewrite combine_length in H. rewrite combine_truncate_r.
  rewrite combine_truncate_l. destruct d as [d1 d2]. rewrite combine_nth.
  - Search (nth _ (firstn _ _)). repeat rewrite nth_firstn. replace (_ <? _)%nat with true.
    replace (_ <? _)%nat with true.
    + reflexivity.
    + symmetry. apply Nat.ltb_lt. lia.
    + symmetry. apply Nat.ltb_lt. rewrite firstn_length. lia.
  - repeat rewrite firstn_length. lia.
Qed.
  

Lemma to_associational_monotone weight n p p' :
  values_le_pos p p' ->
  values_le_assoc (Positional.to_associational weight n p) (Positional.to_associational weight n p').
Proof.
  cbv [values_le_pos values_le_assoc Positional.to_associational]. intros H.
  Search Forall2. assert (Hlen := Forall2_length H).
  rewrite Forall2_forall_iff in H; try apply Hlen.
  - Check Forall2_forall_iff. rewrite (Forall2_forall_iff _ _ _ (0,0) (0,0)).
    + intros i Hi. repeat rewrite nth_default_eq. Search (nth _ (combine _ _)).
      repeat rewrite combine_nth'.
      -- simpl. split; try reflexivity. rewrite combine_length in Hi.
         assert (Hi': (i < length p)%nat) by lia. apply H in Hi'. repeat rewrite nth_default_eq in Hi'. apply Hi'.
      -- rewrite combine_length in *. rewrite <- Hlen. apply Hi.
      -- apply Hi.
    + repeat rewrite combine_length. rewrite Hlen. reflexivity. 
Qed.

Print Positional.place.

(*
Search (?f (if _ then _ else _) = (if _ then ?f _ else ?f _)).
The lemmas 'Z.mod_r_distr_if' and 'Associational.eval_if' seem a bit silly.
 *)

Lemma distr_if {A B : Type} (f : A -> B) (cond : bool) (a1 a2 : A) :
  f (if cond then a1 else a2) = if cond then f a1 else f a2.
Proof. destruct cond; reflexivity. Qed.

Lemma place_indep weight t1 t2 t2' n :
  fst (Positional.place weight (t1, t2) n) = fst (Positional.place weight (t1, t2') n).
Proof.
  cbv [Positional.place]. simpl. Search nat_rect. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. Search (?f (if _ then _ else _) = (if _ then ?f _ else ?f _)). 
    repeat rewrite (distr_if fst). rewrite IHn'. reflexivity.
Qed.

Lemma place_monotone weight t1 t2 t2' n :
  (forall i, 0 <= weight i) ->
  0 <= t1 ->
  t2 <= t2' ->
  snd (Positional.place weight (t1, t2) n) <= snd (Positional.place weight (t1, t2') n).
Proof.
  intros Hweight Hnonneg Hle. cbv [Positional.place]. simpl. induction n as [|n' IHn'].
  - intros. simpl. apply Zmult_le_compat_l; lia.
  - simpl. Search (?f (if _ then _ else _) = (if _ then ?f _ else ?f _)).
    destruct (_ =? _)%Z; try lia. simpl. apply Zmult_le_compat_l; try lia. Search (0 <= _ / _).
    apply Z.div_nonneg; try lia. apply Hweight.
Qed.

Lemma from_associational_monotone weight n p p' :
  (forall i, 0 <= weight i) ->
  everything_nonneg_assoc p ->
  values_le_assoc p p' ->
  values_le_pos (Positional.from_associational weight n p) (Positional.from_associational weight n p').
Proof.
  cbv [everything_nonneg_assoc values_le_assoc values_le_pos].
  intros Hweight. generalize dependent p'. induction p as [|p0 p_ IHp_].
  - intros p' Hp Hle. inversion Hle. subst. simpl. induction n as [|n' IHn'].
    + cbv [Positional.zeros]. simpl. constructor.
    + cbv [Positional.zeros]. simpl. constructor; try lia. apply IHn'.
  - intros p' Hp Hle. inversion Hp as [|p0' p_' H1 H2]. subst.
    inversion Hle as [|x1 x2 p'0 p'_ H4]. subst. simpl.
    repeat rewrite unfold_Let_In. Search Positional.add_to_nth.
    assert (IHp_' := IHp_ p'_ H2 H). clear IHp_. clear H Hle H2 Hp.
    rewrite (Forall2_forall_iff _ _ _ 0 0) in IHp_'.
    + rewrite (Forall2_forall_iff _ _ _ 0 0). intros i Hi. repeat rewrite nth_default_eq.
      rewrite Positional.length_add_to_nth in Hi. assert (IHp_'' := IHp_' _ Hi). clear IHp_'.
      repeat rewrite nth_default_eq in IHp_''.
      destruct p0 as [p0_1 p0_2]. destruct x2 as [x2_1 x2_2]. simpl in *. destruct H4 as [HHH H4].
      subst.
      rewrite (place_indep _ _ p0_2 x2_2) in *. remember (fst _) as i' eqn:clearMe; clear clearMe.
      destruct (dec (i = i')) as [E|E].
      -- subst. Check nth_add_to_nth. repeat rewrite unstupid_nth_add_to_nth.
         ++ destruct H1 as [H1_1 H1_2].
            assert (plmono := place_monotone weight x2_1 p0_2 x2_2 (Init.Nat.pred n) Hweight H1_1 H4). lia.
         ++ rewrite Positional.length_from_associational in *.  lia.
         ++ rewrite Positional.length_from_associational in *. lia.
      -- repeat rewrite mth_add_to_nth by lia. apply IHp_''.
      -- repeat rewrite Positional.length_add_to_nth. repeat rewrite Positional.length_from_associational. lia.
    + repeat rewrite Positional.length_from_associational. lia.
Qed.

Lemma amul_monotone_l weight n p p' q :
  (forall i, 0 <= weight i) ->
  everything_nonneg_pos p ->
  everything_nonneg_pos q ->
  values_le_pos p p' ->
  values_le_pos (amul weight n p q) (amul weight n p' q).
Proof.
  intros Hweight Hp Hq Hle.
  cbv [amul]. apply from_associational_monotone.
  - apply Hweight.
  - apply mul_nonneg.
    + apply to_associational_nonneg.
      -- apply Hweight.
      -- apply Hp.
    + apply to_associational_nonneg.
      -- apply Hweight.
      -- apply Hq.
  - apply mul_monotone_l.
    + apply to_associational_nonneg.
      -- apply Hweight.
      -- apply Hp.
    + apply to_associational_nonneg.
      -- apply Hweight.
      -- apply Hq.
    + apply to_associational_monotone. apply Hle.
Qed.

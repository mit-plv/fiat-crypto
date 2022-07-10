Require Import Crypto.Arithmetic.Core.
Require Import Coq.ZArith.ZArith Coq.micromega.Lia.
Require Import Coq.Structures.Orders.
Require Import Coq.Lists.List.
Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ListUtil.
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
Require Import Coq.Numbers.NatInt.NZDiv.
(** * Push-Button Synthesis Examples *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Rewriter.Language.Language.
Require Import Crypto.Language.API.
Require Import Crypto.Stringification.C.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Arithmetic.Primitives.
Require Import Crypto.BoundsPipeline.
Import ListNotations.
Local Open Scope Z_scope. Local Open Scope list_scope.

Import
  Language.Compilers
  Stringification.C.Compilers.
Import Compilers.API.

Import Associational Positional.
Import ListNotations. Local Open Scope Z_scope.



Definition is_in (x : Z) (l : list Z) :=
  fold_right (fun x' found => orb (x' =? x) found) false l.

Lemma is_in_true_iff : forall x l, is_in x l = true <-> In x l.
  intros. induction l as [ | x' l'].
  - split; intros H.
    + discriminate H.
    + destruct H.
  - split; intros H.
    + simpl in *. destruct (x' =? x) eqn:E.
      -- apply Z.eqb_eq in E. left. apply E.
      -- simpl in H. right. rewrite <- IHl'. apply H.
    + destruct H as [H | H].
      -- simpl. apply Z.eqb_eq in H. rewrite H. reflexivity.
      -- simpl. rewrite <- IHl' in H. rewrite H. destruct (x' =? x); reflexivity.
Qed.

Lemma is_in_false_iff : forall x l, is_in x l = false <-> ~ In x l.
Proof.
  intros. rewrite <- is_in_true_iff. split.
  - intros H. rewrite H. auto.
  - intros H. destruct (is_in x l).
    + exfalso. apply H. reflexivity.
    + reflexivity.
Qed.

Definition just_once (l : list Z) :=
  fold_right (fun x l' => if (is_in x l') then l' else (x :: l')) [] l.

Lemma just_once_in_iff (x : Z) (l : list Z) : In x l <-> In x (just_once l).
Proof.
  induction l as [|x' l' IHl'].
  - reflexivity.
  - simpl. destruct (is_in x' (just_once l')) eqn:E.
    + rewrite is_in_true_iff in E. split.
      -- intros [H|H].
        ++ rewrite <- H. apply E.
        ++ rewrite <- IHl'. apply H.
      -- intros H. right. rewrite IHl'. apply H.
    + rewrite is_in_false_iff in E. split.
      -- intros [H|H].
        ++ rewrite H. simpl. left. reflexivity.
        ++ simpl. right. rewrite <- IHl'. apply H.
      -- simpl. intros [H|H].
        ++ left. apply H.
        ++ right. rewrite IHl'. apply H.
Qed.

Lemma just_once_works (x : Z) (l : list Z) : In x l ->
  exists l1 l2, just_once l = l1 ++ [x] ++ l2 /\ ~ In x l1 /\ ~ In x l2.
Proof.
  intros H. induction l as [| x' l'].
  - simpl in H. destruct H.
  - simpl in H. destruct H as [H|H].
    + rewrite H. clear H. simpl. destruct (is_in x (just_once l')) eqn:E. 
      -- rewrite is_in_true_iff in E. rewrite <- just_once_in_iff in E.
         apply IHl' in E. apply E.
      -- exists []. exists (just_once l'). split.
        ++ rewrite app_nil_l. reflexivity.
        ++ split.
          --- auto.
          --- rewrite <- is_in_false_iff. apply E.
    + apply IHl' in H. clear IHl'. simpl. destruct (is_in x' (just_once l')) eqn:E.
      -- apply H.
      -- destruct H as [l1 [l2 [H1 [H2 H3] ] ] ]. exists (x' :: l1). exists l2. split.
        ++ rewrite H1. reflexivity.
        ++ split.
          --- simpl. intros [H|H].
            +++ rewrite H in *. rewrite H1 in E. apply is_in_false_iff in E. apply E.
                repeat rewrite in_app_iff. right. left. simpl. left. reflexivity.
            +++ apply H2. apply H.
          --- apply H3.
Qed.

Definition total (a : list (Z * Z)) (d : Z) :=
  fold_right (fun p sum => if (d =? fst p) then (sum + snd p) else sum) 0 a.

Lemma total_works a d : d * (total a d) = Associational.eval (filter (fun p => d =? fst p) a).
Proof.
  induction a as [| a0 a' IHa'].
  - cbv [Associational.eval]. simpl. ring.
  - simpl. destruct (d =? fst a0) eqn:E.
    + rewrite Associational.eval_cons. rewrite <- IHa'. apply Z.eqb_eq in E. rewrite E. ring.
    + apply IHa'.
Qed.

Definition firsts (a : list (Z*Z)) :=
  map (fun p => fst p) a.

Lemma total_not_in a d : ~ In d (firsts a) -> total a d = 0.
Proof.
  intros H. induction a as [| x a' IHa'].
  - reflexivity.
  - simpl. destruct (d =? fst x) eqn:E.
    + exfalso. apply H. simpl. left. apply Z.eqb_eq in E. symmetry. apply E.
    + apply IHa'. intros H'. apply H. simpl. right. apply H'.
Qed.

Definition collect_terms a :=
  map (fun d => (d, total a d)) (just_once (firsts a)).

Search (_ * (_ + _)).

Lemma map_eq (x y : Z) l a : ~ In x l ->
  map (fun d : Z => (d, total a d)) l = map (fun d : Z => (d, if d =? x then (total a d + y) else total a d)) l.
Proof.
  intros H. induction l as [|x' l' IHl'].
  - reflexivity.
  - simpl. destruct (x' =? x) eqn:E.
    + exfalso. apply H. apply Z.eqb_eq in E. rewrite E. simpl. left. reflexivity.
    + rewrite IHl'.
      -- reflexivity.
      -- intros H'. apply H. simpl. right. apply H'.
Qed.

Theorem eval_collect_terms a : Associational.eval (collect_terms a) = Associational.eval a.
Proof.
  induction a as [| a0 a'].
  - reflexivity.
  - cbv [collect_terms]. simpl. destruct (is_in (fst a0) (just_once (firsts a'))) eqn:E.
    + apply is_in_true_iff in E. rewrite <- just_once_in_iff in E. apply just_once_works in E.
      destruct E as [l1 [l2 [H1 [H2 H3] ] ] ]. rewrite H1. repeat rewrite map_app. rewrite <- (map_eq _ _ _ _ H2).
      rewrite <- (map_eq _ _ _ _ H3). repeat rewrite Associational.eval_app. simpl. rewrite Z.eqb_refl. repeat rewrite Associational.eval_cons.
      rewrite <- IHa'. simpl. rewrite Associational.eval_nil. cbv [collect_terms]. rewrite H1.
      repeat rewrite map_app. repeat rewrite Associational.eval_app. cbv [Associational.eval]. simpl. ring.
    + simpl. rewrite Z.eqb_refl. apply is_in_false_iff in E. rewrite <- (map_eq _ _ _ _ E). repeat rewrite Associational.eval_cons.
      simpl. rewrite <- IHa'. cbv [collect_terms]. f_equal. f_equal. rewrite <- just_once_in_iff in E. rewrite (total_not_in _ _ E). ring.
Qed.

Definition split_one (s:Z) (w fw : Z) (p:list (Z*Z)) :=
  let hi_lo := partition (fun t => (fst t =? w)) p in
    (snd hi_lo, map (fun t => (fst t / fw, snd t)) (fst hi_lo)).

Compute Positional.to_associational (fun x => 2) 3 [1; 1; 1].

Lemma mod_thing : forall a b, b <> 0 -> a mod b = 0 -> (forall c, b * (c * a / b) = c * a).
Proof.
  intros. symmetry. apply Z_div_exact_full_2.
  - apply H.
  - rewrite Z.mul_mod_full. rewrite H0. rewrite Z.mul_comm. simpl. apply Z.mod_0_l. apply H.
Qed.

Check Z_div_exact_full_2.

Lemma eval_split_one s w fw p (s_nz:s<>0) (fw_nz:fw<>0) (w_fw : w mod fw = 0) (fw_s : fw mod s = 0):
  Associational.eval (fst (split_one s w fw p)) + fw * Associational.eval (snd (split_one s w fw p)) = Associational.eval p.
Proof.
  remember (Z_div_exact_full_2 _ _ fw_nz w_fw) as H2.
  clear HeqH2 fw_nz w_fw.
  induction p as [|t p'].
  - simpl. cbv [Associational.eval]. simpl. lia.
  - cbv [split_one]. simpl. destruct (fst t =? w) eqn:E.
    + simpl in IHp'. remember (partition (fun t0 : Z * Z => fst t0 =? w) p') as thing. 
      destruct thing as [thing1 thing2]. simpl. simpl in IHp'. repeat rewrite Associational.eval_cons.
      ring_simplify. simpl.
      apply Z.eqb_eq in E. rewrite E. rewrite <- H2. rewrite <- IHp'. ring.
    + simpl in IHp'. remember (partition (fun t0 : Z * Z => fst t0 =? w) p') as thing.
      destruct thing as [thing1 thing2]. simpl. simpl in IHp'. repeat rewrite Associational.eval_cons.
      rewrite <- IHp'. ring.
Qed.

Lemma reduction_rule' b s c (modulus_nz:s-c<>0) :
  (s * b) mod (s - c) = (c * b) mod (s - c).
Proof using Type. replace (s * b) with ((c*b) + b*(s-c)) by nsatz.
  rewrite Z.add_mod,Z_mod_mult,Z.add_0_r,Z.mod_mod;trivial. Qed.

Lemma reduction_rule a b s c (modulus_nz:s-c<>0) :
  (a + s * b) mod (s - c) = (a + c * b) mod (s - c).
Proof using Type. apply Z.add_mod_Proper; [ reflexivity | apply reduction_rule', modulus_nz ]. Qed.

(*assumes that (H1 : w mod fw = 0) (H2 : fw mod s = 0) *)
Definition reduce_one (s:Z) (w fw : Z) (c: Z) (p:list _) : list (Z*Z) :=
  let lo_hi := split_one s w fw p in
  fst lo_hi ++ map (fun thing => (fst thing, snd thing * (c * (fw / s)))) (snd lo_hi).

Local Ltac push := autorewrite with
      push_eval push_map push_partition push_flat_map
      push_fold_right push_nth_default cancel_pair.

Lemma eval_map_mul_snd (x:Z) (p:list (Z*Z))
  : Associational.eval (List.map (fun t => (fst t, snd t * x)) p) = x * Associational.eval p.
Proof. induction p; push; nsatz. Qed.

Lemma eval_reduce_one s w fw c p (s_nz:s<>0) (fw_nz:fw<>0) (w_fw : w mod fw = 0) (fw_s : fw mod s = 0) 
                             (modulus_nz: s - c<>0) :
            Associational.eval (reduce_one s w fw c p) mod (s - c) = 
            Associational.eval p mod (s - c).
Proof using Type.
  cbv [reduce_one]; push.
  rewrite eval_map_mul_snd. rewrite <- Z.mul_assoc.
  rewrite <- (reduction_rule _ _ _ _ modulus_nz).
  rewrite Z.mul_assoc. rewrite <- (Z_div_exact_full_2 fw s s_nz fw_s). rewrite eval_split_one; trivial.
Qed.

(* 'carrying down', aka borrowing *)
Definition carryterm_down (w fw:Z) (t:Z * Z) :=
    let quot := w / fw in
    if (Z.eqb (fst t) w)
      then [(quot, snd t * fw)]
      else [t].

Lemma eval_carryterm_down w fw (t:Z * Z) (fw_nz:fw<>0) (w_fw:w mod fw = 0) :
      Associational.eval (carryterm_down w fw t) = Associational.eval [t].
Proof using Type*.
  cbv [carryterm_down Let_In]; break_match; push; [|trivial].
  pose proof (Z.div_mod (snd t) fw fw_nz).
  rewrite Z.eqb_eq in *.
  remember (mod_thing _ _ fw_nz w_fw) as H'.
  ring_simplify. rewrite Z.mul_comm. rewrite Z.mul_assoc. rewrite <- (Z.mul_1_l w). rewrite H'. rewrite Heqb.
  destruct w; ring.
Qed.

Definition carry_down (w fw:Z) (p:list (Z*Z)) :=
  flat_map (carryterm_down w fw) p.

Lemma eval_carry_down w fw p (fw_nz:fw<>0) (w_fw:w mod fw = 0):
      Associational.eval (carry_down w fw p) = Associational.eval p.
Proof using Type*.
  cbv [carry_down carryterm_down]. induction p.
  - trivial.
  - push. destruct (fst a =? w) eqn:E.
    + rewrite IHp. remember (mod_thing _ _ fw_nz w_fw) as H. rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
      rewrite <- (Z.mul_1_l w). rewrite H. ring_simplify. apply Z.eqb_eq in E. rewrite E. ring.
    + rewrite IHp. ring.
Qed.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.LetIn Crypto.Util.CPSUtil.
Require Import Crypto.Util.Tuple Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Decidable Crypto.Util.ZUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Tactics.SpecializeBy.
Local Notation "A ^ n" := (tuple A n) : type_scope.

(***

Arithmetic on bignums that handles carry bits; this is useful for
saturated limbs. Compatible with mixed-radix bases.

Uses "columns" representation: a bignum has type [tuple (list Z) n].
Associated with a weight function w, the bignum B represents:

    \sum_{i=0}^{n}{w[i] * sum{B[i]}}

Example: ([a21, a20],[],[a0]) with weight function (fun i => 10^i)
represents

    a0 + 10*0 + 100 * (a20 + a21)

If you picture this representation with the weights on the bottom and
the terms in each list stacked above the corresponding weight,

                a20
    a0          a21
    ---------------
     1    10    100

it's easy to see how the lists can be called "columns".

This is a particularly useful representation for adding partial
products after multiplication, particularly when we want to do this
using a carrying add. We want to add together the terms from each
column, accumulating the carries together along the way. Then we want
to add the carry accumulator to the next column, and repeat, producing
a [tuple Z n] as output. This operation is called "compact".

As an example, let's compact the product of 571 and 645 in base 10.
At first, the partial products look like this:


                   1*6
            1*4    7*4     7*6
     1*5    7*5    5*5     5*4      5*6
    ------------------------------------
       1     10    100    1000    10000

                     6
              4     28      42
       5     35     25      20       30
    ------------------------------------
       1     10    100    1000    10000

Now, we process the first column:

     {carry_acc = 0; output =()}
     STEP [5]
     {carry_acc = 0; output=(5,)}

Since we have only one term, there's no addition to do, and no carry
bit. We add a 0 to the next column and continue.

     STEP [0,4,35] (0 + 4 = 4)
     {carry_acc = 0; output=(5,)}
     STEP [4,35] (4 + 35 = 39)
     {carry_acc = 3; output=(9,5)}

This time, we have a carry. We add it to the third column and process
that:

     STEP [9,6,28,25] (9 + 6  = 15)
     {carry_acc = 1; output=(9,5)}
     STEP [5,28,25] (5 + 28 = 33)
     {carry_acc = 4; output=(9,5)}
     STEP [3,25] (3 + 25 = 28)
     {carry_acc = 2; output=(8,9,5)}

You're probably getting the idea, but here are the fourth and fifth
columns:

     STEP [2,42,20] (2 + 42 = 44)
     {carry_acc = 4; output=(8,9,5)}
     STEP [4,20] (4 + 20 = 24)
     {carry_acc = 6; output=(4,8,9,5)}

     STEP [6,30] (6 + 30 = 36)
     {carry_acc = 3; output=(6,4,8,9,5)}

The final result is the output plus the final carry, so we produce
(6,4,8,9,5) and 3, representing the number 364895. A quick calculator
check confirms our result.

 ***)

Module Columns.
  Section Columns.
    Context (weight : nat->Z)
            {weight_0 : weight 0%nat = 1}
            {weight_nonzero : forall i, weight i <> 0}
            {weight_positive : forall i, weight i > 0}
            {weight_multiples : forall i, weight (S i) mod weight i = 0}
            {weight_divides : forall i : nat, weight (S i) / weight i > 0}
            (* add_get_carry takes in a number at which to split output *)
            {add_get_carry: Z ->Z -> Z -> (Z * Z)}
            {add_get_carry_mod : forall s x y,
                fst (add_get_carry s x y)  = (x + y) mod s}
            {add_get_carry_div : forall s x y,
                snd (add_get_carry s x y)  = (x + y) / s}
            {div modulo : Z -> Z -> Z}
            {div_correct : forall a b, div a b = a / b}
            {modulo_correct : forall a b, modulo a b = a mod b}
    .
    Hint Rewrite div_correct modulo_correct add_get_carry_mod add_get_carry_div : div_mod.

    Definition eval {n} (x : (list Z)^n) : Z :=
      B.Positional.eval weight (Tuple.map sum x).

    Lemma eval_unit (x:unit) : eval (n:=0) x = 0.
    Proof. reflexivity. Qed.
    Hint Rewrite eval_unit : push_basesystem_eval.

    Lemma eval_single (x:list Z) : eval (n:=1) x = sum x.
    Proof.
      cbv [eval]. simpl map. cbv - [Z.mul Z.add sum].
      rewrite weight_0; ring.
    Qed. Hint Rewrite eval_single : push_basesystem_eval.

    Definition eval_from {n} (offset:nat) (x : (list Z)^n) : Z :=
      B.Positional.eval (fun i => weight (i+offset)) (Tuple.map sum x).

    Lemma eval_from_0 {n} x : @eval_from n 0 x = eval x.
    Proof using Type. cbv [eval_from eval]. auto using B.Positional.eval_wt_equiv. Qed.

    Lemma eval_from_S {n}: forall i (inp : (list Z)^(S n)),
        eval_from i inp = eval_from (S i) (tl inp) + weight i * sum (hd inp).
    Proof using Type.
      intros i inp; cbv [eval_from].
      replace inp with (append (hd inp) (tl inp))
        by (simpl in *; destruct n; destruct inp; reflexivity).
      rewrite map_append, B.Positional.eval_step, hd_append, tl_append.
      autorewrite with natsimplify; ring_simplify; rewrite Group.cancel_left.
      apply B.Positional.eval_wt_equiv; intros; f_equal; omega.
    Qed.

    (* Sums a list of integers using carry bits.
     Output : carry, sum
     *)
    Fixpoint compact_digit_cps n (digit : list Z) {T} (f:Z * Z->T) :=
      match digit with
      | nil => f (0, 0)
      | x :: nil => f (div x (weight (S n) / weight n), modulo x (weight (S n) / weight n))
      | x :: y :: nil =>
          dlet sum_carry := add_get_carry (weight (S n) / weight n) x y in
          dlet carry := snd sum_carry in
          f (carry, fst sum_carry)
      | x :: tl =>
        compact_digit_cps n tl
          (fun rec =>
            dlet sum_carry := add_get_carry (weight (S n) / weight n) x (snd rec) in
            dlet carry' := (fst rec + snd sum_carry)%RT in
            f (carry', fst sum_carry))
      end.

    Definition compact_digit n digit := compact_digit_cps n digit id.
    Lemma compact_digit_id n digit: forall {T} f,
        @compact_digit_cps n digit T f = f (compact_digit n digit).
    Proof using Type.
      induction digit; intros; cbv [compact_digit]; [reflexivity|];
        simpl compact_digit_cps; break_match; rewrite ?IHdigit;
          reflexivity.
    Qed.
    Hint Opaque compact_digit : uncps.
    Hint Rewrite compact_digit_id : uncps.

    Definition compact_step_cps (index:nat) (carry:Z) (digit: list Z)
               {T} (f:Z * Z->T) :=
      compact_digit_cps index (carry::digit) f.

    Definition compact_step i c d := compact_step_cps i c d id.
    Lemma compact_step_id i c d T f :
      @compact_step_cps i c d T f = f (compact_step i c d).
    Proof using Type. cbv [compact_step_cps compact_step]; autorewrite with uncps; reflexivity. Qed.
    Hint Opaque compact_step : uncps.
    Hint Rewrite compact_step_id : uncps.

    Definition compact_cps {n} (xs : (list Z)^n) {T} (f:Z * Z^n->T) :=
      Tuple.mapi_with_cps compact_step_cps 0 xs f.

    Definition compact {n} xs := @compact_cps n xs _ id.
    Lemma compact_id {n} xs {T} f : @compact_cps n xs T f = f (compact xs).
    Proof using Type. cbv [compact_cps compact]; autorewrite with uncps; reflexivity. Qed.

    Lemma compact_digit_mod i (xs : list Z) :
      snd (compact_digit i xs)  = sum xs mod (weight (S i) / weight i).
    Proof using add_get_carry_div add_get_carry_mod div_correct modulo_correct.
      induction xs; cbv [compact_digit]; simpl compact_digit_cps;
        cbv [Let_In];
        repeat match goal with
               | _ => progress autorewrite with div_mod
               | _ => rewrite IHxs, <-Z.add_mod_r
               | _ => progress (rewrite ?sum_cons, ?sum_nil in * )
               | _ => progress (autorewrite with uncps push_id cancel_pair in * )
               | _ => progress break_match; try discriminate
               | _ => reflexivity
               | _ => f_equal; ring
               end.
    Qed. Hint Rewrite compact_digit_mod : div_mod.

    Lemma compact_digit_div i (xs : list Z) :
      fst (compact_digit i xs)  = sum xs / (weight (S i) / weight i).
    Proof using add_get_carry_div add_get_carry_mod div_correct modulo_correct weight_0 weight_divides.
      induction xs; cbv [compact_digit]; simpl compact_digit_cps;
        cbv [Let_In];
        repeat match goal with
               | _ => progress autorewrite with div_mod
               | _ => rewrite IHxs
               | _ => progress (rewrite ?sum_cons, ?sum_nil in * )
               | _ => progress (autorewrite with uncps push_id cancel_pair in * )
               | _ => progress break_match; try discriminate
               | _ => reflexivity
               | _ => f_equal; ring
               end.
      assert (weight (S i) / weight i <> 0) by auto using Z.positive_is_nonzero.
      match goal with |- _ = (?a + ?X) / ?D =>
                      transitivity  ((a + X mod D + D * (X / D)) / D);
                        [| rewrite (Z.div_mod'' X D) at 3; f_equal; auto; ring]
      end.
      rewrite Z.div_add' by auto; nsatz.
    Qed.

    Lemma small_mod_eq a b n: a mod n = b mod n -> 0 <= a < n -> a = b mod n.
    Proof. intros; rewrite <-(Z.mod_small a n); auto. Qed.

    (* helper for some of the modular logic in compact *)
    Lemma compact_mod_step a b c d: 0 < a -> 0 < b ->
      a * ((c / a + d) mod b) + c mod a = (a * d + c) mod (a * b).
    Proof.
      clear.
      intros Ha Hb. assert (a <= a * b) by (apply Z.le_mul_diag_r; omega).
      pose proof (Z.mod_pos_bound c a Ha).
      pose proof (Z.mod_pos_bound (c/a+d) b Hb).
      apply small_mod_eq.
      { rewrite <-(Z.mod_small (c mod a) (a * b)) by omega.
        rewrite <-Z.mul_mod_distr_l with (c:=a) by omega.
        rewrite Z.mul_add_distr_l, Z.mul_div_eq, <-Z.add_mod_full by omega.
        f_equal; ring. }
      { split; [zero_bounds|].
        apply Z.lt_le_trans with (m:=a*(b-1)+a); [|ring_simplify; omega].
        apply Z.add_le_lt_mono; try apply Z.mul_le_mono_nonneg_l; omega. }
    Qed.

    Lemma compact_div_step a b c d : 0 < a -> 0 < b ->
      (c / a + d) / b = (a * d + c) / (a * b).
    Proof.
      clear. intros Ha Hb.
      rewrite <-Z.div_div by omega.
      rewrite Z.div_add_l' by omega.
      f_equal; ring.
    Qed.

    Lemma compact_div_mod {n} inp :
      (B.Positional.eval weight (snd (compact inp))
       = (eval inp) mod (weight n))
        /\ (fst (compact inp) = eval (n:=n) inp / weight n).
    Proof.
      cbv [compact compact_cps compact_step compact_step_cps];
        autorewrite with uncps push_id.
      change (fun i s a => compact_digit_cps i (s :: a) id)
        with (fun i s a => compact_digit i (s :: a)).

      apply mapi_with'_linvariant; [|tauto].

      clear n inp. intros n st x0 xs ys Hst Hys [Hmod Hdiv].
      pose proof (weight_positive n). pose proof (weight_divides n).
      autorewrite with push_basesystem_eval.
      destruct n; cbv [mapi_with] in *; simpl tuple in *;
        [destruct xs, ys; subst; simpl| cbv [eval] in *];
        repeat match goal with
               | _ => rewrite mapi_with'_left_step
               | _ => rewrite compact_digit_div, sum_cons
               | _ => rewrite compact_digit_mod, sum_cons
               | _ => rewrite map_left_append
               | _ => rewrite B.Positional.eval_left_append
               | _ => rewrite weight_0, ?Z.div_1_r, ?Z.mod_1_r
               | _ => rewrite Hdiv
               | _ => rewrite Hmod
               | _ => progress subst
               | _ => progress autorewrite with natsimplify cancel_pair push_basesystem_eval
               | _ => solve [split; ring_simplify; f_equal; ring]
               end.
        remember (weight (S (S n)) / weight (S n)) as bound.
        replace (weight (S (S n))) with (weight (S n) * bound)
          by (subst bound; rewrite Z.mul_div_eq by omega;
              rewrite weight_multiples; ring).
        split; [apply compact_mod_step | apply compact_div_step]; omega.
    Qed.

    Lemma compact_mod {n} inp :
      (B.Positional.eval weight (snd (compact inp))
       = (eval (n:=n) inp) mod (weight n)).
    Proof. apply (proj1 (compact_div_mod inp)). Qed.
    Hint Rewrite @compact_mod : push_basesystem_eval.

    Lemma compact_div {n} inp :
      fst (compact inp) = eval (n:=n) inp / weight n.
    Proof. apply (proj2 (compact_div_mod inp)). Qed.
    Hint Rewrite @compact_div : push_basesystem_eval.

    (* TODO : move to tuple *)
    Lemma hd_to_list {A n} a (t : A^(S n)) : List.hd a (to_list (S n) t) = hd t.
    Proof.
      rewrite (subst_append t), to_list_append, hd_append. reflexivity.
    Qed.

    Definition cons_to_nth_cps {n} i (x:Z) (t:(list Z)^n)
               {T} (f:(list Z)^n->T) :=
      @on_tuple_cps _ _ nil (update_nth_cps i (cons x)) n n t _ f.

    Definition cons_to_nth {n} i x t := @cons_to_nth_cps n i x t _ id.
    Lemma cons_to_nth_id {n} i x t T f :
      @cons_to_nth_cps n i x t T f = f (cons_to_nth i x t).
    Proof using Type.
      cbv [cons_to_nth_cps cons_to_nth].
      assert (forall xs : list (list Z), length xs = n ->
                 length (update_nth_cps i (cons x) xs id) = n) as Hlen.
      { intros. autorewrite with uncps push_id distr_length. assumption. }
      rewrite !on_tuple_cps_correct with (H:=Hlen)
        by (intros; autorewrite with uncps push_id; reflexivity). reflexivity.
    Qed.
    Hint Opaque cons_to_nth : uncps.
    Hint Rewrite @cons_to_nth_id : uncps.

    Lemma map_sum_update_nth l : forall i x,
      List.map sum (update_nth i (cons x) l) =
      update_nth i (Z.add x) (List.map sum l).
    Proof using Type.
      induction l as [|a l IHl]; intros i x; destruct i; simpl; rewrite ?IHl; reflexivity.
    Qed.

    Lemma cons_to_nth_add_to_nth n i x t :
      map sum (@cons_to_nth n i x t) = B.Positional.add_to_nth i x (map sum t).
    Proof using weight.
      cbv [B.Positional.add_to_nth B.Positional.add_to_nth_cps cons_to_nth cons_to_nth_cps on_tuple_cps].
      induction n; [simpl; rewrite !update_nth_cps_correct; reflexivity|].
      specialize (IHn (tl t)). autorewrite with uncps push_id in *.
      apply to_list_ext. rewrite <-!map_to_list.
      erewrite !from_list_default_eq, !to_list_from_list.
      rewrite map_sum_update_nth. reflexivity.
      Unshelve.
      distr_length.
      distr_length.
    Qed.

    Lemma eval_cons_to_nth n i x t : (i < n)%nat ->
      eval (@cons_to_nth n i x t) = weight i * x + eval t.
    Proof using Type.
      cbv [eval]; intros. rewrite cons_to_nth_add_to_nth.
      auto using B.Positional.eval_add_to_nth.
    Qed.
    Hint Rewrite eval_cons_to_nth using omega : push_basesystem_eval.

    Definition nils n : (list Z)^n := Tuple.repeat nil n.

    Lemma map_sum_nils n : map sum (nils n) = B.Positional.zeros n.
    Proof using Type.
      cbv [nils B.Positional.zeros]; induction n as [|n]; [reflexivity|].
      change (repeat nil (S n)) with (@nil Z :: repeat nil n).
      rewrite map_repeat, sum_nil. reflexivity.
    Qed.

    Lemma eval_nils n : eval (nils n) = 0.
    Proof using Type. cbv [eval]. rewrite map_sum_nils, B.Positional.eval_zeros. reflexivity. Qed. Hint Rewrite eval_nils : push_basesystem_eval.

    Definition from_associational_cps n (p:list B.limb)
               {T} (f:(list Z)^n -> T) :=
      fold_right_cps
        (fun t st =>
           B.Positional.place_cps weight t (pred n)
             (fun p=> cons_to_nth_cps (fst p) (snd p) st id))
        (nils n) p f.

    Definition from_associational n p := from_associational_cps n p id.
    Lemma from_associational_id n p T f :
      @from_associational_cps n p T f = f (from_associational n p).
    Proof using Type.
      cbv [from_associational_cps from_associational].
      autorewrite with uncps push_id; reflexivity.
    Qed.
    Hint Opaque from_associational : uncps.
    Hint Rewrite from_associational_id : uncps.

    Lemma eval_from_associational n p (n_nonzero:n<>0%nat):
      eval (from_associational n p) = B.Associational.eval p.
    Proof using weight_0 weight_nonzero.
      cbv [from_associational_cps from_associational]; induction p;
        autorewrite with uncps push_id push_basesystem_eval; [reflexivity|].
        pose proof (B.Positional.weight_place_cps weight weight_0 weight_nonzero a (pred n)).
        pose proof (B.Positional.place_cps_in_range weight a (pred n)).
        rewrite Nat.succ_pred in * by assumption. simpl.
        autorewrite with uncps push_id push_basesystem_eval in *.
        rewrite eval_cons_to_nth by omega. nsatz.
    Qed.
  End Columns.
End Columns.
Hint Rewrite
     @Columns.compact_digit_id
     @Columns.compact_step_id
     @Columns.compact_id
     @Columns.cons_to_nth_id
     @Columns.from_associational_id
  : uncps.
Hint Rewrite
     @Columns.compact_mod
     @Columns.compact_div
     @Columns.eval_cons_to_nth
     @Columns.eval_from_associational
     @Columns.eval_nils
  using (assumption || omega): push_basesystem_eval.

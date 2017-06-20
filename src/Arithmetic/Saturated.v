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
Require Import Crypto.Util.ZUtil.Definitions.
Require Import Crypto.Util.ZUtil.AddGetCarry.
Require Import Crypto.Util.ZUtil.Zselect.
Require Import Crypto.Util.ZUtil.MulSplit.
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

Module Associational.
  Section Associational.
    Context {mul_split : Z -> Z -> Z -> Z * Z} (* first argument is where to split output; [mul_split s x y] gives ((x * y) mod s, (x * y) / s) *)
            {mul_split_mod : forall s x y,
                fst (mul_split s x y)  = (x * y) mod s}
            {mul_split_div : forall s x y,
                snd (mul_split s x y)  = (x * y) / s}
            .

    Definition multerm_cps s (t t' : B.limb) {T} (f:list B.limb ->T) :=
      dlet xy := mul_split s (snd t) (snd t') in
      f ((fst t * fst t', fst xy) :: (fst t * fst t' * s, snd xy) :: nil).

    Definition multerm s t t' := multerm_cps s t t' id.
    Lemma multerm_id s t t' T f :
      @multerm_cps s t t' T f = f (multerm s t t').
    Proof. reflexivity. Qed.
    Hint Opaque multerm : uncps.
    Hint Rewrite multerm_id : uncps.

    Definition mul_cps s (p q : list B.limb) {T} (f : list B.limb -> T) :=
      flat_map_cps (fun t => @flat_map_cps _ _ (multerm_cps s t) q) p f.

    Definition mul s p q := mul_cps s p q id.
    Lemma mul_id s p q T f : @mul_cps s p q T f = f (mul s p q).
    Proof. cbv [mul mul_cps]. autorewrite with uncps. reflexivity. Qed.
    Hint Opaque mul : uncps.
    Hint Rewrite mul_id : uncps.

    Lemma eval_map_multerm s a q (s_nonzero:s<>0):
      B.Associational.eval (flat_map (multerm s a) q) = fst a * snd a * B.Associational.eval q.
    Proof.
      cbv [multerm multerm_cps Let_In]; induction q;
      repeat match goal with
             | _ => progress (autorewrite with uncps push_id cancel_pair push_basesystem_eval in * )
             | _ => progress simpl flat_map
             | _ => progress rewrite ?IHq, ?mul_split_mod, ?mul_split_div
             | _ => rewrite Z.mod_eq by assumption
             | _ => ring_simplify; omega
             end.
    Qed.
    Hint Rewrite eval_map_multerm using (omega || assumption)
      : push_basesystem_eval.

    Lemma eval_mul s p q (s_nonzero:s<>0):
      B.Associational.eval (mul s p q) = B.Associational.eval p * B.Associational.eval q.
    Proof.
      cbv [mul mul_cps]; induction p; [reflexivity|].
      repeat match goal with
             | _ => progress (autorewrite with uncps push_id push_basesystem_eval in * )
             | _ => progress simpl flat_map
             | _ => rewrite IHp
             | _ => progress change (fun x => multerm_cps s a x id)  with (multerm s a)
             | _ => ring_simplify; omega
             end.
    Qed.
    Hint Rewrite eval_mul : push_basesystem_eval.

  End Associational.
End Associational.
Hint Opaque Associational.mul Associational.multerm : uncps.
Hint Rewrite @Associational.mul_id @Associational.multerm_id : uncps.
Hint Rewrite @Associational.eval_mul @Associational.eval_map_multerm using (omega || assumption) : push_basesystem_eval.

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
      intros Ha Hb.
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

  Section Wrappers.
    Context (weight : nat->Z).

    Definition add_cps {n1 n2 n3} (p : Z^n1) (q : Z^n2)
               {T} (f : (Z*Z^n3)->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.to_associational_cps weight q
        (fun Q => from_associational_cps weight n3 (P++Q)
        (fun R => compact_cps (div:=div) (modulo:=modulo) (add_get_carry:=Z.add_get_carry_full) weight R f))).

    Definition unbalanced_sub_cps {n1 n2 n3} (p : Z^n1) (q:Z^n2)
               {T} (f : (Z*Z^n3)->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.negate_snd_cps weight q
        (fun nq => B.Positional.to_associational_cps weight nq
        (fun Q => from_associational_cps weight n3 (P++Q)
        (fun R => compact_cps (div:=div) (modulo:=modulo) (add_get_carry:=Z.add_get_carry_full) weight R f)))).

    Definition mul_cps {n1 n2 n3} s (p : Z^n1) (q : Z^n2)
               {T} (f : (Z*Z^n3)->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.to_associational_cps weight q
        (fun Q => Associational.mul_cps (mul_split := Z.mul_split) s P Q
        (fun PQ => from_associational_cps weight n3 PQ
        (fun R => compact_cps (div:=div) (modulo:=modulo) (add_get_carry:=Z.add_get_carry_full) weight R f)))).

    End Wrappers.
End Columns.
Hint Unfold
     Columns.add_cps
     Columns.unbalanced_sub_cps
     Columns.mul_cps.
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

Section Freeze.
    Context (weight : nat->Z)
            {weight_0 : weight 0%nat = 1}
            {weight_nonzero : forall i, weight i <> 0}
            {weight_positive : forall i, weight i > 0}
            {weight_multiples : forall i, weight (S i) mod weight i = 0}
            {weight_divides : forall i : nat, weight (S i) / weight i > 0}
    .

    Definition conditional_add_cps {n} mask cond (p q : Z^n)
               {T} (f:_->T) :=
      B.Positional.select_cps mask cond q
                 (fun qq => Columns.add_cps (n3:=n) weight p qq f).
    Definition conditional_add {n} mask cond p q :=
      @conditional_add_cps n mask cond p q _ id.
    Lemma conditional_add_id {n} mask cond p q T f:
      @conditional_add_cps n mask cond p q T f
      = f (conditional_add mask cond p q).
    Proof.
      cbv [conditional_add_cps conditional_add]; autounfold.
      autorewrite with uncps push_id; reflexivity.
    Qed.
    Hint Opaque conditional_add : uncps.
    Hint Rewrite @conditional_add_id : uncps.

    Lemma eval_conditional_add {n} mask cond p q (n_nonzero:n<>0%nat)
      (H:Tuple.map (Z.land mask) q = q) :
    B.Positional.eval weight (snd (@conditional_add n mask cond p q))
    = B.Positional.eval weight p + (if (dec (cond = 0)) then 0 else B.Positional.eval weight q) - weight n * (fst (conditional_add mask cond p q)).
  Proof.
    cbv [conditional_add_cps conditional_add];
      repeat progress autounfold in *.
    pose proof Z.add_get_carry_full_mod.
    pose proof Z.add_get_carry_full_div.
    pose proof div_correct. pose proof modulo_correct.
    autorewrite with uncps push_id push_basesystem_eval.
    break_match;
      match goal with
        |- context [weight ?n * (?x / weight ?n)] =>
        pose proof (Z.div_mod x (weight n) (weight_nonzero n))
      end; omega.
  Qed.
  Hint Rewrite @eval_conditional_add using (omega || assumption)
    : push_basesystem_eval.


  (*
    The input to [freeze] should be less than 2*m (this can probably
    be accomplished by a single carry_reduce step, for most moduli).

    [freeze] has the following steps:
    (1) subtract modulus in a carrying loop (in our framework, this
    consists of two steps; [Columns.unbalanced_sub_cps] combines the
    input p and the modulus m such that the ith limb in the output is
    the list [p[i];-m[i]]. We can then call [Columns.compact].)
    (2) look at the final carry, which should be either 0 or -1. If
    it's -1, then we add the modulus back in. Otherwise we add 0 for
    constant-timeness.
    (3) discard the carry after this last addition; it should be 1 if
    the carry in step 3 was -1, so they cancel out.
   *)
  Definition freeze_cps {n} mask (m:Z^n) (p:Z^n) {T} (f : Z^n->T) :=
    Columns.unbalanced_sub_cps weight p m
      (fun carry_p => conditional_add_cps mask (fst carry_p) (snd carry_p) m
      (fun carry_r => f (snd carry_r)))
  .

  Definition freeze {n} mask m p :=
    @freeze_cps n mask m p _ id.
  Lemma freeze_id {n} mask m p T f:
    @freeze_cps n mask m p T f = f (freeze mask m p).
  Proof.
    cbv [freeze_cps freeze]; repeat progress autounfold;
      autorewrite with uncps push_id; reflexivity.
  Qed.
  Hint Opaque freeze : uncps.
  Hint Rewrite @freeze_id : uncps.

  Lemma freezeZ m s c y y0 z z0 c0 a :
    m = s - c ->
    0 < c < s ->
    s <> 0 ->
    0 <= y < 2*m ->
    y0 = y - m ->
    z = y0 mod s ->
    c0 = y0 / s ->
    z0 = z + (if (dec (c0 = 0)) then 0 else m) ->
    a = z0 mod s ->
    a mod m = y0 mod m.
  Proof.
    clear. intros. subst. break_match.
    { rewrite Z.add_0_r, Z.mod_mod by omega.
      assert (-(s-c) <= y - (s-c) < s-c) by omega.
      match goal with H : s <> 0 |- _ =>
                      rewrite (proj2 (Z.mod_small_iff _ s H))
                              by (apply Z.div_small_iff; assumption)
      end.
      reflexivity. }
    { rewrite <-Z.add_mod_l, Z.sub_mod_full.
      rewrite Z.mod_same, Z.sub_0_r, Z.mod_mod by omega.
      rewrite Z.mod_small with (b := s)
      by (pose proof (Z.div_small (y - (s-c)) s); omega).
      f_equal. ring. }
  Qed.

  Lemma eval_freeze {n} c mask m p
        (n_nonzero:n<>0%nat)
        (Hc : 0 < B.Associational.eval c < weight n)
        (Hmask : Tuple.map (Z.land mask) m = m)
        modulus (Hm : B.Positional.eval weight m = Z.pos modulus)
        (Hp : 0 <= B.Positional.eval weight p < 2*(Z.pos modulus))
        (Hsc : Z.pos modulus = weight n - B.Associational.eval c)
    :
      mod_eq modulus
             (B.Positional.eval weight (@freeze n mask m p))
             (B.Positional.eval weight p).
  Proof.
    cbv [freeze_cps freeze conditional_add_cps].
    repeat progress autounfold.
    pose proof Z.add_get_carry_full_mod.
    pose proof Z.add_get_carry_full_div.
    pose proof div_correct. pose proof modulo_correct.
    autorewrite with uncps push_id push_basesystem_eval.

    pose proof (weight_nonzero n).

    remember (B.Positional.eval weight p) as y.
    remember (y + -B.Positional.eval weight m) as y0.
    rewrite Hm in *.

    transitivity y0; cbv [mod_eq].
    { eapply (freezeZ (Z.pos modulus) (weight n) (B.Associational.eval c) y y0);
        try assumption; reflexivity. }
    { subst y0.
      assert (Z.pos modulus <> 0) by auto using Z.positive_is_nonzero, Zgt_pos_0.
      rewrite Z.add_mod by assumption.
      rewrite Z.mod_opp_l_z by auto using Z.mod_same.
      rewrite Z.add_0_r, Z.mod_mod by assumption.
      reflexivity. }
  Qed.
End Freeze.

Section UniformWeight.
  Context (bound : Z) {bound_pos : bound > 0}.

  Definition uweight : nat -> Z := fun i => bound ^ Z.of_nat i.
  Lemma uweight_0 : uweight 0%nat = 1. Proof. reflexivity. Qed.
  Lemma uweight_positive i : uweight i > 0.
  Proof. apply Z.lt_gt, Z.pow_pos_nonneg; omega. Qed.
  Lemma uweight_nonzero i : uweight i <> 0.
  Proof. auto using Z.positive_is_nonzero, uweight_positive. Qed.
  Lemma uweight_multiples i : uweight (S i) mod uweight i = 0.
  Proof. apply Z.mod_same_pow; rewrite Nat2Z.inj_succ; omega. Qed.
  Lemma uweight_divides i : uweight (S i) / uweight i > 0.
  Proof.
    cbv [uweight]. rewrite <-Z.pow_sub_r by (rewrite ?Nat2Z.inj_succ; omega).
    apply Z.lt_gt, Z.pow_pos_nonneg; rewrite ?Nat2Z.inj_succ; omega.
  Qed.

End UniformWeight.

Section API.
  Context (bound : Z) {bound_pos : bound > 0}.
  Definition T : nat -> Type := tuple Z.

  (* lowest limb is less than its bound; this is required for [divmod]
  to simply separate the lowest limb from the rest and be equivalent
  to normal div/mod with [bound]. *)
  Definition small {n} (p : T n) : Prop :=
    forall x, In x (to_list _ p) -> 0 <= x < bound.

  Definition zero {n:nat} : T n := B.Positional.zeros n.

  Definition join0_cps {n:nat} (p : T n) {R} (f:T (S n) -> R)
    := Tuple.left_append_cps 0 p f.
  Definition join0 {n} p : T (S n) := @join0_cps n p _ id.

  Definition divmod_cps {n} (p : T (S n)) {R} (f:T n * Z->R) : R
    := Tuple.tl_cps p (fun d => Tuple.hd_cps p (fun m =>  f (d, m))).
  Definition divmod {n} p : T n * Z := @divmod_cps n p _ id.

  Definition drop_high_cps {n : nat} (p : T (S n)) {R} (f:T n->R)
    := Tuple.left_tl_cps p f.
  Definition drop_high {n} p : T n := @drop_high_cps n p _ id.

  Definition scmul_cps {n} (c : Z) (p : T n) {R} (f:T (S n)->R) :=
    Columns.mul_cps (n1:=1) (n3:=S n) (uweight bound) bound c p
      (* The carry that comes out of Columns.mul_cps will be 0, since
      (S n) limbs is enough to hold the result of the
      multiplication, so we can safely discard it. *)
      (fun carry_result =>f (snd carry_result)).
  Definition scmul {n} c p : T (S n) := @scmul_cps n c p _ id.

  Definition add_cps {n m pred_nm} (p : T n) (q : T m) {R} (f:T (S pred_nm)->R) :=
    Columns.add_cps (uweight bound) p q
      (fun carry_result => Tuple.left_append_cps (fst carry_result) (snd carry_result)
      f).
  Definition add {n m pred_nm} p q : T (S pred_nm) := @add_cps n m pred_nm p q _ id.

  (* Subtract q if and only if p < bound^n. The correctness of this
  lemma depends on the precondition that p < q + bound^n.  *)
  Definition conditional_sub_cps {n} mask (p : Z^S n) (q : Z ^ n)
             {T} (f:Z^n->T) :=
      (* we pass the highest digit of p into select_cps as the
      conditional argument; if it is 0, the subtraction will not
      happen, otherwise it will.*)
      B.Positional.select_cps mask (left_hd p) q
        (fun qq => Columns.unbalanced_sub_cps (n3:=n) (uweight bound) p qq
        (* We can safely discard the carry, since our preconditions tell us
           that, whether or not the subtraction happened, n limbs is
           sufficient to store the result. *)
        (fun carry_result => f (snd carry_result))).

  Definition conditional_sub {n} mask p q := @conditional_sub_cps n mask p q _ id.

  Hint Opaque join0 divmod drop_high scmul add conditional_sub : uncps.

  Section CPSProofs.

    Local Ltac prove_id :=
      repeat autounfold; autorewrite with uncps; reflexivity.

    Lemma join0_id n p R f :
      @join0_cps n p R f = f (join0 p).
    Proof. cbv [join0_cps join0]. prove_id. Qed.

    Lemma divmod_id n p R f :
      @divmod_cps n p R f = f (divmod p).
    Proof. cbv [divmod_cps divmod]; prove_id. Qed.

    Lemma drop_high_id n p R f :
      @drop_high_cps n p R f = f (drop_high p).
    Proof. cbv [drop_high_cps drop_high]; prove_id. Qed.
    Hint Rewrite drop_high_id : uncps.

    Lemma scmul_id n c p R f :
      @scmul_cps n c p R f = f (scmul c p).
    Proof. cbv [scmul_cps scmul]. prove_id. Qed.

    Lemma add_id n m pred_nm p q R f :
      @add_cps n m pred_nm p q R f = f (add p q).
    Proof. cbv [add_cps add Let_In]. prove_id. Qed.

    Lemma conditional_sub_id n mask p q R f :
      @conditional_sub_cps n mask p q R f = f (conditional_sub mask p q).
    Proof. cbv [conditional_sub_cps conditional_sub Let_In]. prove_id. Qed.

  End CPSProofs.
  Hint Rewrite join0_id divmod_id drop_high_id scmul_id add_id conditional_sub_id : uncps.

  Section Proofs.

    Definition eval {n} (p : T n) : Z :=
      B.Positional.eval (uweight bound) p.

    Lemma In_to_list_left_tl n (p : Z^S n) x:
      In x (to_list n (left_tl p)) -> In x (to_list (S n) p).
    Admitted.

    Lemma In_left_hd n (p : Z^S n):
      In (left_hd p) (to_list _ p).
    Admitted.

    Lemma eval_small n (p : T n) (Hsmall : small p) :
      0 <= eval p < uweight bound n.
    Proof.
      cbv [small eval] in *; intros.
      induction n; cbv [T uweight] in *; [destruct p|rewrite (subst_left_append p)];
      repeat match goal with
             | _ => progress autorewrite with push_basesystem_eval
             | _ => rewrite Z.pow_0_r
             | _ => specialize (IHn (left_tl p))
             | _ =>
               let H := fresh "H" in
               match type of IHn with
                 ?P -> _ => assert P as H by auto using In_to_list_left_tl;
                              specialize (IHn H)
               end
             | |- context [?b ^ Z.of_nat (S ?n)] =>
               replace (b ^ Z.of_nat (S n)) with (b ^ Z.of_nat n * b) by
                   (rewrite Nat2Z.inj_succ, <-Z.add_1_r, Z.pow_add_r,
                    Z.pow_1_r by (omega || auto using Nat2Z.is_nonneg);
                    reflexivity)
             | _ => omega
             end.

        specialize (Hsmall _ (In_left_hd _ p)).
        split; [Z.zero_bounds; omega |].
        apply Z.lt_le_trans with (m:=bound^Z.of_nat n * (left_hd p+1)).
        { rewrite Z.mul_add_distr_l.
          apply Z.add_le_lt_mono; omega. }
        { apply Z.mul_le_mono_nonneg; omega. }
    Qed.

    Lemma eval_zero n : eval (@zero n) = 0.
    Proof.
      cbv [eval zero].
      autorewrite with push_basesystem_eval.
      reflexivity.
    Qed.

    Lemma small_zero n : small (@zero n).
    Proof.
      cbv [zero small B.Positional.zeros]. destruct n; [simpl;tauto|].
      rewrite to_list_repeat.
      intros x H; apply repeat_spec in H; subst x; omega.
   Qed.

    Lemma eval_join0 n p
      : eval (@join0 n p) = eval p.
    Proof.
    Admitted.

    Local Ltac pose_uweight bound :=
      match goal with H : bound > 0 |- _ =>
                      pose proof (uweight_0 bound);
                      pose proof (@uweight_positive bound H);
                      pose proof (@uweight_nonzero bound H);
                      pose proof (@uweight_multiples bound);
                      pose proof (@uweight_divides bound H)
      end.

    Local Ltac pose_all :=
      pose_uweight bound;
      pose proof Z.add_get_carry_full_div;
      pose proof Z.add_get_carry_full_mod;
      pose proof Z.mul_split_div; pose proof Z.mul_split_mod;
      pose proof div_correct; pose proof modulo_correct.

    Lemma eval_add_nz n m pred_nm p q :
      pred_nm <> 0%nat ->
      eval (@add n m pred_nm p q) = eval p + eval q.
    Proof.
      intros. pose_all.
      repeat match goal with
             | _ => progress (cbv [add_cps add eval Let_In]; repeat autounfold)
             | _ => progress autorewrite with uncps push_id cancel_pair push_basesystem_eval
             | _ => rewrite B.Positional.eval_left_append

             | _ => progress
                      (rewrite <-!from_list_default_eq with (d:=0);
                       erewrite !length_to_list, !from_list_default_eq,
                       from_list_to_list)
             | _ => rewrite Z.mul_div_eq by auto;
                      omega
             end.
    Qed.

    Lemma eval_add_z n m pred_nm p q :
      pred_nm = 0%nat ->
      n = 0%nat ->
      m = 0%nat ->
      eval (@add n m pred_nm p q) = eval p + eval q.
    Proof. intros; subst; reflexivity. Qed.

    Lemma eval_add n m pred_nm p q (Hpred_nm : pred_nm = 0%nat -> n = 0%nat /\ m = 0%nat)
      :  eval (@add n m pred_nm p q) = eval p + eval q.
    Proof.
      destruct (Nat.eq_dec pred_nm 0%nat); intuition auto using eval_add_z, eval_add_nz.
    Qed.
    Lemma eval_add_same n p q
      :  eval (@add n n n p q) = eval p + eval q.
    Proof. apply eval_add; omega. Qed.
    Lemma eval_add_S1 n p q
      :  eval (@add (S n) n (S n) p q) = eval p + eval q.
    Proof. apply eval_add; omega. Qed.
    Lemma eval_add_S2 n p q
      :  eval (@add n (S n) (S n) p q) = eval p + eval q.
    Proof. apply eval_add; omega. Qed.
    Hint Rewrite eval_add_same eval_add_S1 eval_add_S2 : push_basesystem_eval.

    Lemma to_list_left_append {n} (p:T n) x:
      (to_list _ (left_append x p)) = to_list n p ++ x :: nil.
    Admitted.

    Lemma uweight_le_mono n m : (n <= m)%nat ->
      uweight bound n <= uweight bound m.
    Admitted.

    Lemma uweight_lt_mono n m : (n < m)%nat ->
      uweight bound n < uweight bound m.
    Admitted.

    Lemma uweight_succ n : uweight bound (S n) = bound * uweight bound n.
    Admitted.

    Local Definition compact {n} := Columns.compact (n:=n) (add_get_carry:=Z.add_get_carry_full) (div:=div) (modulo:=modulo) (uweight bound).
    Local Definition compact_digit := Columns.compact_digit (add_get_carry:=Z.add_get_carry_full) (div:=div) (modulo:=modulo) (uweight bound).
    Lemma small_compact {n} (p:(list Z)^n) : small (snd (compact p)).
    Proof.
      pose_all.
      match goal with
        |- ?G => assert (G /\ fst (compact p) = fst (compact p)); [|tauto]
      end. (* assert a dummy second statement so that fst (compact x) is in context *)
      cbv [compact Columns.compact Columns.compact_cps small
                   Columns.compact_step Columns.compact_step_cps];
        autorewrite with uncps push_id.
      change (fun i s a => Columns.compact_digit_cps (uweight bound) i (s :: a) id)
      with (fun i s a => compact_digit i (s :: a)).
      remember (fun i s a => compact_digit i (s :: a)) as f.

      apply @mapi_with'_linvariant with (n:=n) (f:=f) (inp:=p);
        intros; [|simpl; tauto]. split; [|reflexivity].
      let P := fresh "H" in
      match goal with H : _ /\ _ |- _ => destruct H end.
      destruct n0; subst f.
      { cbv [compact_digit uweight to_list to_list' In].
        rewrite Columns.compact_digit_mod by assumption.
        rewrite Z.pow_0_r, Z.pow_1_r, Z.div_1_r. intros x ?.
        match goal with
          H : _ \/ False |- _ => destruct H; [|exfalso; assumption] end.
        subst x. apply Z.mod_pos_bound, Z.gt_lt, bound_pos. }
      { rewrite to_list_left_append.
        let H := fresh "H" in
        intros x H; apply in_app_or in H; destruct H;
          [solve[auto]| cbv [In] in H; destruct H;
                        [|exfalso; assumption] ].
        subst x. cbv [compact_digit].
        rewrite Columns.compact_digit_mod by assumption.
        rewrite !uweight_succ, Z.div_mul by
            (apply Z.neq_mul_0; split; auto; omega).
        apply Z.mod_pos_bound, Z.gt_lt, bound_pos. }
    Qed.

    Lemma small_add n m pred_nm a b :
      (2 <= bound) -> (max n m <= pred_nm)%nat ->
      small a -> small b -> small (@add n m pred_nm a b).
    Proof.
      intros. pose_all.
      cbv [small add_cps add Let_In]. repeat autounfold.
      autorewrite with uncps push_id.
      rewrite to_list_left_append.
      let H := fresh "H" in intros x H; apply in_app_or in H;
                              destruct H as [H | H];
                              [apply (small_compact _ _ H)
                              |destruct H; [|exfalso; assumption] ].
      subst x.
      rewrite Columns.compact_div by assumption.
      repeat match goal with
               H : small ?x |- _ => apply eval_small in H; cbv [eval] in H
             end.
      destruct pred_nm as [|pred_pred_nm]; autorewrite with push_basesystem_eval;
        repeat match goal with
               | [ H : (max ?x ?y <= 0)%nat |- _ ]
                 => assert (x = 0%nat) by omega *;
                      assert (y = 0%nat) by omega *;
                      clear H
               | _ => progress subst
               end.
      { destruct bound; cbv -[Z.le Z.lt]; lia. }
      split; [ solve [ unfold uweight in *; Z.zero_bounds ] | ].
      apply Zdiv_lt_upper_bound; [ solve [ unfold uweight in *; Z.zero_bounds ] | ].
      apply Z.lt_le_trans with (m:=uweight bound n + uweight bound m);
          [omega|].
      apply Z.le_trans with (m:=uweight bound (max n m) + uweight bound (max n m)); auto using Z.add_le_mono, uweight_le_mono, Max.le_max_l, Max.le_max_r.
      rewrite Z.add_diag.
      pose proof (uweight_le_mono (max n m) (S pred_pred_nm)).
      specialize_by_assumption.
      apply Z.mul_le_mono_nonneg; try omega.
      apply Max.max_case_strong; omega.
    Qed.

    Lemma small_left_tl n (v:T (S n)) : small v -> small (left_tl v).
    Proof. cbv [small]. auto using In_to_list_left_tl. Qed.

    Lemma small_divmod n (p: T (S n)) (Hsmall : small p) :
      left_hd p = eval p / uweight bound n /\ eval (left_tl p) = eval p mod (uweight bound n).
    Admitted.

    Lemma small_highest_zero_iff {n} (p: T (S n)) (Hsmall : small p) :
      (left_hd p = 0 <-> eval p < uweight bound n).
    Proof.
      destruct (small_divmod _ p Hsmall) as [Hdiv Hmod].
      pose proof Hsmall as Hsmalltl. apply eval_small in Hsmall.
      apply small_left_tl, eval_small in Hsmalltl. rewrite Hdiv.
      rewrite (Z.div_small_iff (eval p) (uweight bound n))
        by auto using uweight_nonzero.
      split; [|intros; left; omega].
      let H := fresh "H" in intro H; destruct H; [|omega].
      pose proof (uweight_lt_mono n (S n) (Nat.lt_succ_diag_r _)).
      omega.
    Qed.

    Lemma eval_conditional_sub_nz n mask (p:T (S n)) (q:T n)
          (n_nonzero: (n <> 0)%nat) (psmall : small p) (qsmall : small q)
          (Hmask : Tuple.map (Z.land mask) q = q):
      0 <= eval p < eval q + (uweight bound n) ->
      eval (conditional_sub mask p q) = eval p + (if uweight bound n <=? eval p then - eval q else 0).
    Proof.
      cbv [conditional_sub conditional_sub_cps eval].
      intros. pose_all. repeat autounfold. apply eval_small in qsmall.
      autorewrite with uncps push_id push_basesystem_eval.
      pose proof (small_highest_zero_iff p psmall).
      break_match; cbv [eval] in *;
        repeat  match goal with
                | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
                | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
                | H : 0 = 0 <-> ?P |- _ =>
                  assert P by (apply H; reflexivity);  clear H
                | _ => rewrite Z.mod_small; omega
                end.
    Qed.

    Lemma eval_conditional_sub n mask (p:T (S n)) (q:T n)
           (psmall : small p) (qsmall : small q)
          (Hmask : Tuple.map (Z.land mask) q = q):
      0 <= eval p < eval q + (uweight bound n) ->
      eval (conditional_sub mask p q) = eval p + (if uweight bound n <=? eval p then - eval q else 0).
    Proof.
      destruct n; [|solve[auto using eval_conditional_sub_nz]].
      repeat match goal with
             | _ => progress (intros; cbv [T tuple tuple'] in p, q)
             | q : unit |- _ => destruct q
             | _ => progress (cbv [conditional_sub conditional_sub_cps eval] in * )
             | _ => progress autounfold
             | _ => progress (autorewrite with uncps push_id push_basesystem_eval in * )
             | _ => (rewrite uweight_0 in * )
             | _ => assert (p = 0) by omega; subst p; break_match; ring
             end.
    Qed.

    Lemma small_conditional_sub n mask (p:T (S n)) (q:T n)
           (psmall : small p) (qsmall : small q)
          (Hmask : Tuple.map (Z.land mask) q = q):
      0 <= eval p < eval q + (uweight bound n) ->
      small (conditional_sub mask p q).
    Admitted.

    Lemma eval_drop_high n v :
      small v -> eval (@drop_high n v) = eval v mod (uweight bound n).
    Proof.
      cbv [drop_high drop_high_cps eval].
      rewrite Tuple.left_tl_cps_correct, push_id. (* TODO : for some reason autorewrite with uncps doesn't work here *)
      intro H. apply small_left_tl in H.
      rewrite (subst_left_append v) at 2.
      autorewrite with push_basesystem_eval.
      apply eval_small in H.
      rewrite Z.mod_add_l' by (pose_uweight bound; auto).
      rewrite Z.mod_small; auto.
    Qed.

    Lemma small_drop_high n v : small v -> small (@drop_high n v).
    Proof.
      cbv [drop_high drop_high_cps].
      rewrite Tuple.left_tl_cps_correct, push_id.
      apply small_left_tl.
    Qed.

    Lemma eval_scmul n a v : small v -> 0 <= a < bound ->
      eval (@scmul n a v) = a * eval v.
    Proof.
      intro Hsmall. pose_all. apply eval_small in Hsmall.
      intros. cbv [scmul scmul_cps eval] in *. repeat autounfold.
      autorewrite with uncps push_id push_basesystem_eval.
      rewrite uweight_0, Z.mul_1_l. apply Z.mod_small.
      split; [solve[Z.zero_bounds]|]. cbv [uweight] in *.
      rewrite !Nat2Z.inj_succ, Z.pow_succ_r by auto using Nat2Z.is_nonneg.
      apply Z.mul_lt_mono_nonneg; omega.
    Qed.

    Lemma small_scmul n a v : small (@scmul n a v).
    Proof.
      cbv [scmul scmul_cps eval] in *. repeat autounfold.
      autorewrite with uncps push_id push_basesystem_eval.
      apply small_compact.
    Qed.

    (* TODO : move to tuple *)
    Lemma from_list_tl {A n} (ls : list A) H H':
      from_list n (List.tl ls) H = tl (from_list (S n) ls H').
    Proof.
      induction ls; distr_length. simpl List.tl.
      rewrite from_list_cons, tl_append, <-!(from_list_default_eq a ls).
      reflexivity.
    Qed.

    Lemma eval_div n p : small p -> eval (fst (@divmod n p)) = eval p / bound.
    Proof.
      repeat match goal with
             | _ => progress (intros; cbv [divmod_cps divmod eval]; repeat autounfold)
             | _ => progress autorewrite with uncps push_id cancel_pair push_basesystem_eval
             end.
      rewrite (subst_append p) at 2.
      rewrite B.Positional.eval_step.
      rewrite uweight_0.
    Admitted.

    Lemma eval_mod n p : small p -> snd (@divmod n p) = eval p mod bound.
    Proof.
    Admitted.

    Lemma small_div n v : small v -> small (fst (@divmod n v)).
    Admitted.

  End Proofs.
End API.
Hint Rewrite join0_id divmod_id drop_high_id scmul_id add_id conditional_sub_id : uncps.

(*
(* Just some pretty-printing *)
Local Notation "fst~ a" := (let (x,_) := a in x) (at level 40, only printing).
Local Notation "snd~ a" := (let (_,y) := a in y) (at level 40, only printing).

(* Simple example : base 10, multiply two bignums and compact them *)
Definition base10 i := Eval compute in 10^(Z.of_nat i).
Eval cbv -[runtime_add runtime_mul Let_In] in
    (fun adc a0 a1 a2 b0 b1 b2 =>
       Columns.mul_cps (weight := base10) (n:=3) (a2,a1,a0) (b2,b1,b0) (fun ab => Columns.compact (n:=5) (add_get_carry:=adc) (weight:=base10) ab)).

(* More complex example : base 2^56, 8 limbs *)
Definition base2pow56 i := Eval compute in 2^(56*Z.of_nat i).
Time Eval cbv -[runtime_add runtime_mul Let_In] in
    (fun adc a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 =>
       Columns.mul_cps (weight := base2pow56) (n:=8) (a7,a6,a5,a4,a3,a2,a1,a0) (b7,b6,b5,b4,b3,b2,b1,b0) (fun ab => Columns.compact (n:=15) (add_get_carry:=adc) (weight:=base2pow56) ab)). (* Finished transaction in 151.392 secs *)

(* Mixed-radix example : base 2^25.5, 10 limbs *)
Definition base2pow25p5 i := Eval compute in 2^(25*Z.of_nat i + ((Z.of_nat i + 1) / 2)).
Time Eval cbv -[runtime_add runtime_mul Let_In] in
    (fun adc a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 =>
       Columns.mul_cps (weight := base2pow25p5) (n:=10) (a9,a8,a7,a6,a5,a4,a3,a2,a1,a0) (b9,b8,b7,b6,b5,b4,b3,b2,b1,b0) (fun ab => Columns.compact (n:=19) (add_get_carry:=adc) (weight:=base2pow25p5) ab)). (* Finished transaction in 97.341 secs *)
*)

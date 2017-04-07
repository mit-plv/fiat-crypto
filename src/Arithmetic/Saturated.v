Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Algebra.Nsatz.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Util.LetIn Crypto.Util.CPSUtil.
Require Import Crypto.Util.Tuple Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
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
    Context {weight : nat->Z}
            {weight_0 : weight 0%nat = 1}
            {weight_nonzero : forall i, weight i <> 0}
            {weight_multiples : forall i, weight (S i) mod weight i = 0}
            (* add_get_carry takes in a number at which to split output *)
            {add_get_carry: Z ->Z -> Z -> (Z * Z)}
            {add_get_carry_correct : forall s x y,
                fst (add_get_carry s x y)  = x + y - s * snd (add_get_carry s x y)}
    .

    Definition eval {n} (x : (list Z)^n) : Z :=
      B.Positional.eval weight (Tuple.map sum x).

    Definition eval_from {n} (offset:nat) (x : (list Z)^n) : Z :=
      B.Positional.eval (fun i => weight (i+offset)) (Tuple.map sum x).

    Lemma eval_from_0 {n} x : @eval_from n 0 x = eval x.
    Proof using Type. cbv [eval_from eval]. auto using B.Positional.eval_wt_equiv. Qed.

    Lemma eval_from_S {n}: forall i (inp : (list Z)^(S n)),
        eval_from i inp = eval_from (S i) (tl inp) + weight i * sum (hd inp).
    Proof using Type.
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
    Fixpoint compact_digit_cps n (digit : list Z) {T} (f:Z * Z->T) :=
      match digit with
      | nil => f (0, 0)
      | x :: nil => f (0, x)
      | x :: tl =>
        compact_digit_cps n tl (fun rec =>
                                  dlet sum_carry := add_get_carry (weight (S n) / weight n) x (snd rec) in
                                    dlet carry' := (fst rec + snd sum_carry)%RT in
                                    f (carry', fst sum_carry))
      end.

    Definition compact_digit n digit := compact_digit_cps n digit id.
    Lemma compact_digit_id n digit: forall {T} f,
        @compact_digit_cps n digit T f = f (compact_digit n digit).
    Proof using Type.
      induction digit; intros; cbv [compact_digit]; [reflexivity|];
        simpl compact_digit_cps; break_match; [reflexivity|].
      rewrite !IHdigit; reflexivity.
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
      mapi_with_cps compact_step_cps 0 xs f.

    Definition compact {n} xs := @compact_cps n xs _ id.
    Lemma compact_id {n} xs {T} f : @compact_cps n xs T f = f (compact xs).
    Proof using Type. cbv [compact_cps compact]; autorewrite with uncps; reflexivity. Qed.

    Lemma compact_digit_correct i (xs : list Z) :
      snd (compact_digit i xs)  = sum xs - (weight (S i) / weight i) * (fst (compact_digit i xs)).
    Proof using add_get_carry_correct weight_0.
      induction xs; cbv [compact_digit]; simpl compact_digit_cps;
        cbv [Let_In];
        repeat match goal with
               | _ => rewrite add_get_carry_correct
               | _ => progress (rewrite ?sum_cons, ?sum_nil in * )
               | _ => progress (autorewrite with uncps push_id in * )
               | _ => progress (autorewrite with cancel_pair in * )
               | _ => progress break_match; try discriminate
               | _ => progress ring_simplify
               | _ => reflexivity
               | _ => nsatz
               end.
    Qed.

    Definition compact_invariant n i (starter rem:Z) (inp : tuple (list Z) n) (out : tuple Z n) :=
      B.Positional.eval_from weight i out + weight (i + n) * (rem)
      = eval_from i inp + weight i*starter.

    Lemma compact_invariant_holds n i starter rem inp out :
      compact_invariant n (S i) (fst (compact_step_cps i starter (hd inp) id)) rem (tl inp) out ->
      compact_invariant (S n) i starter rem inp (append (snd (compact_step_cps i starter (hd inp) id)) out).
    Proof using Type*.
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
             | _ => cbv [compact_step_cps] in *;
                      autorewrite with uncps push_id;
                      rewrite compact_digit_correct
             | _ => progress (autorewrite with natsimplify in * )
             end.
      rewrite B.Positional.eval_wt_equiv with (wtb := fun i0 => weight (i0 + S i)) by (intros; f_equal; try omega).
      nsatz.
    Qed.

    Lemma compact_invariant_base i rem : compact_invariant 0 i rem rem tt tt.
    Proof using Type. cbv [compact_invariant]. simpl. repeat (f_equal; try omega). Qed.

    Lemma compact_invariant_end {n} start (input : (list Z)^n):
      compact_invariant n 0%nat start (fst (mapi_with_cps compact_step_cps start input id)) input (snd (mapi_with_cps compact_step_cps start input id)).
    Proof using Type*.
      autorewrite with uncps push_id.
      apply (mapi_with_invariant _ compact_invariant
                                 compact_invariant_holds compact_invariant_base).
    Qed.

    Lemma eval_compact {n} (xs : tuple (list Z) n) :
      B.Positional.eval weight (snd (compact xs)) + (weight n * fst (compact xs)) = eval xs.
    Proof using Type*.
      pose proof (compact_invariant_end 0 xs) as Hinv.
      cbv [compact_invariant] in Hinv.
      simpl in Hinv. autorewrite with zsimplify natsimplify in Hinv.
      rewrite eval_from_0, B.Positional.eval_from_0 in Hinv; apply Hinv.
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
      induction l; intros; destruct i; simpl; rewrite ?IHl; reflexivity.
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
      cbv [nils B.Positional.zeros]; induction n; [reflexivity|].
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

    Definition mul_cps {n m} (p q : Z^n) {T} (f : (list Z)^m->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.to_associational_cps weight q
        (fun Q => B.Associational.mul_cps P Q
        (fun PQ => from_associational_cps m PQ f))).

    Definition add_cps {n} (p q : Z^n) {T} (f : (list Z)^n->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.to_associational_cps weight q
        (fun Q => from_associational_cps n (P++Q) f)).

  End Columns.
End Columns.

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

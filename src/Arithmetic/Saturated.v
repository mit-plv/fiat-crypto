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
      B.Positional.eval weight (snd (compact xs)) = eval xs - (weight n * fst (compact xs)).
    Proof using Type*.
      pose proof (compact_invariant_end 0 xs) as Hinv.
      cbv [compact_invariant] in Hinv.
      simpl in Hinv. autorewrite with zsimplify natsimplify in Hinv.
      rewrite eval_from_0, B.Positional.eval_from_0 in Hinv. nsatz.
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

    Definition sub_cps {n} (p q : Z^n) {T} (f : (list Z)^n->T) :=
      B.Positional.to_associational_cps weight p
        (fun P => B.Positional.to_associational_cps weight q
        (fun Q => from_associational_cps n (P++Q) f)).

  End Columns.
End Columns.
Hint Unfold
     Columns.add_cps
     Columns.mul_cps
     Columns.sub_cps.
Hint Rewrite
     @Columns.compact_digit_id
     @Columns.compact_step_id
     @Columns.compact_id
     @Columns.cons_to_nth_id
     @Columns.from_associational_id
  : uncps.
Hint Rewrite
     @Columns.eval_compact
     @Columns.eval_cons_to_nth
     @Columns.eval_from_associational
     @Columns.eval_nils
  using (assumption || omega): push_basesystem_eval.

Section Freeze.
  Context (weight : nat->Z)
          {weight_0 : weight 0%nat = 1}
          {weight_nonzero : forall i, weight i <> 0}
          {weight_multiples : forall i, weight (S i) mod weight i = 0}
          (* add_get_carry takes in a number at which to split output *)
          {add_get_carry: Z ->Z -> Z -> (Z * Z)}
          {add_get_carry_correct : forall s x y,
              fst (add_get_carry s x y)  = x + y - s * snd (add_get_carry s x y)}
  .

  (* adds p and q if cond is 0, else adds 0 to p*)
  Definition conditional_mask_cps {n} (mask:Z) (cond:Z) (p:Z^n)
             {T} (f:_->T) :=
    dlet and_term := if (dec (cond = 0)) then 0 else mask in
    f (Tuple.map (Z.land and_term) p).

  Definition conditional_mask {n} mask cond p :=
    @conditional_mask_cps n mask cond p _ id.
  Lemma conditional_mask_id {n} mask cond p T f:
    @conditional_mask_cps n mask cond p T f
    = f (conditional_mask mask cond p).
  Proof.
    cbv [conditional_mask_cps conditional_mask Let_In]; break_match;
      autounfold; autorewrite with uncps push_id; reflexivity.
  Qed.
  Hint Opaque conditional_mask : uncps.
  Hint Rewrite @conditional_mask_id : uncps.

  Definition conditional_add_cps {n} mask cond (p q : Z^n) {T} (f:_->T) :=
    conditional_mask_cps mask cond q
    (fun qq => Columns.add_cps weight p qq
    (fun R => Columns.compact_cps (add_get_carry:=add_get_carry) weight R f)).
  Definition conditional_add {n} mask cond p q :=
    @conditional_add_cps n mask cond p q _ id.
  Lemma conditional_add_id {n} mask cond p q T f:
    @conditional_add_cps n mask cond p q T f
    = f (conditional_add mask cond p q).
  Proof.
    cbv [conditional_add_cps conditional_add]; autounfold;
      autorewrite with uncps push_id; reflexivity.
  Qed.
  Hint Opaque conditional_add : uncps.
  Hint Rewrite @conditional_add_id : uncps.
  
  
  (*
    [freeze] has the following steps:
    (1) pseudomersenne reduction using [carry_reduce]
    (2) subtract modulus in a carrying loop (in our framework, this
    consists of two steps; [Columns.sub_cps] combines the input p and
    the modulus m such that the ith limb in the output is the list
    [p[i];-m[i]]. We can then call [Columns.compact].)
    (3) look at the final carry, which should be either 0 or -1. If
    it's -1, then we add the modulus back in. Otherwise we add 0 for
    constant-timeness.
    (4) discard the carry after this last addition; it should be 1 if
    the carry in step 3 was -1, so they cancel out.
   *)
  Definition freeze_cps
             {n} (mask:Z) (s:Z) (c:list B.limb) (m:Z^n) (p:Z^n)
             {T} (f : Z^n->T) :=
    B.Positional.carry_reduce_cps
      (div:=div) (modulo:=modulo) weight s c p
      (fun P => Columns.sub_cps weight P m
      (fun Q => Columns.compact_cps (add_get_carry:=add_get_carry) weight Q
      (fun carry_q => conditional_add_cps mask (fst carry_q) (snd carry_q) m
      (fun carry_r => f (snd carry_r)))))
  .

  SearchAbout (((_ mod _) mod _)).

  Definition freeze {n} mask s c m p :=
    @freeze_cps n mask s c m p _ id.
  Lemma freeze_id {n} mask s c m p T f:
    @freeze_cps n mask s c m p T f = f (freeze mask s c m p).
  Proof.
    cbv [freeze_cps freeze]; repeat progress autounfold;
      autorewrite with uncps push_id; reflexivity.
  Qed.
  Hint Opaque freeze : uncps.
  Hint Rewrite @freeze_id : uncps.

  Lemma map_land_zero {n} (p:Z^n):
    Tuple.map (Z.land 0) p = B.Positional.zeros n.
  Proof.
    induction n; [ destruct p; reflexivity | ].
    replace p with (append (hd p) (tl p)) by
        (simpl in p; destruct n; destruct p; reflexivity).
    rewrite map_append, IHn, Z.land_0_l; reflexivity.
  Qed.

  Lemma eval_conditional_mask {n} mask cond p (n_nonzero:n<>0%nat)
    (Hmask : Tuple.map (Z.land mask) p = p):
    B.Positional.eval weight (@conditional_mask n mask cond p)
    = if (dec (cond = 0)) then 0 else B.Positional.eval weight p.
  Proof.
    cbv [conditional_mask_cps conditional_mask Let_In];
      repeat progress autounfold; break_match;
        rewrite ?Hmask, ?map_land_zero;
        autorewrite with uncps push_id push_basesystem_eval; ring.
  Qed.
  Hint Rewrite @eval_conditional_mask using (omega || assumption)
    : push_basesystem_eval.

  Lemma eval_conditional_add {n} mask cond p q (n_nonzero:n<>0%nat)
    (Hmask : Tuple.map (Z.land mask) q = q):
    B.Positional.eval weight (snd (@conditional_add n mask cond p q))
    = B.Positional.eval weight p + (if (dec (cond = 0)) then 0 else B.Positional.eval weight q) - weight n * (fst (conditional_add mask cond p q)).
  Proof.
    cbv [conditional_add_cps conditional_add];
      repeat progress autounfold; rewrite ?Hmask, ?map_land_zero; 
        autorewrite with uncps push_id push_basesystem_eval;
        break_match; ring.
  Qed.
  Hint Rewrite @eval_conditional_add using (omega || assumption)
    : push_basesystem_eval.

  Lemma freezeZ m s c y0 z z0 c0 a :
    m = s - c ->
    0 < c < s ->
    s <> 0 ->
    -m <= y0 < m ->
    z = y0 mod s ->
    c0 = y0 / s ->
    c0 <> 0 ->
    z0 = z + m ->
    a = z0 mod s ->
    a mod m = y0 mod m.
  Proof.
    clear. intros. subst.
    rewrite Z.add_mod by assumption.
    rewrite Z.mod_mod by assumption.
    rewrite <-Z.add_mod by assumption.
    assert (~ (0 <= y0 < s)) by (pose proof (Z.div_small y0 s); tauto).
    assert (-(s-c) <= y0 < 0) by omega.
    rewrite Z.mod_small with (b := s) by omega.
    rewrite Z.add_mod, Z.mod_same, Z.add_0_r, Z.mod_mod by omega.
    reflexivity.
  Qed.

  Lemma eval_freeze {n} mask s c m p
        (n_nonzero:n<>0%nat) (s_nonzero:s<>0)
        (Hweight : weight (S (pred n)) / weight (pred n) <> 0)
        (Hmask : Tuple.map (Z.land mask) m = m)
        modulus (Hm : B.Positional.eval weight m = Z.pos modulus)
        (Hsc : Z.pos modulus = s - B.Associational.eval c)
    :
      mod_eq modulus
             (B.Positional.eval weight (@freeze n mask s c m p))
             (B.Positional.eval weight p).
  Proof.
    cbv [freeze_cps freeze mod_eq]; repeat progress autounfold;
      autorewrite with uncps push_id.
    
    assert (Z.pos modulus <> 0) by (pose proof Pos2Z.is_pos modulus; omega).
    pose proof div_mod.
    break_match; subst.
    
    rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r.
    (* TODO : how to prove second carry is 0? *)
    rewrite Z.add_mod, B.Associational.eval_reduce by assumption.
    autorewrite with uncps push_id push_basesystem_eval.
    rewrite Hm. autorewrite with zsimplify.
    reflexivity.

    
    ring_simplify.
    let p := fresh "P" in
    let carry := fresh "carry" in
    let result := fresh "result" in
    match goal with H:fst ?x <> 0 |- _ =>
                         remember x as p; destruct p as [carry result];
                           autorewrite with cancel_pair in *
    end.
    rewrite Columns.eval_from_associational by assumption.
    autorewrite with uncps push_id push_basesystem_eval.
    rewrite Hm.
    Check Z.add_mod_full.
    match goal with |- context [(?a + ?b - ?c + ?d) mod ?m] =>
                    replace (a + b - c + d) with (b + (a-c) + d) by ring;
                    rewrite (Z.add_mod_full _ d), (Z.add_mod_full _ (a-c))
    end.
    rewrite !Z.mod_same by assumption.
    rewrite !Z.add_0_r, !Z.add_0_l.
    rewrite !Z.mod_mod by assumption.
    rewrite Z.sub_mod_full.
    rewrite B.Associational.eval_reduce by assumption.
    autorewrite with uncps push_id push_basesystem_eval.
    

  
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

Require Import Coq.Init.Nat.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Local Open Scope Z_scope.

Require Import Crypto.Tactics.Algebra_syntax.Nsatz.
Require Import Crypto.NewBaseSystem.
Require Import Crypto.Util.LetIn Crypto.Util.CPSUtil.
Require Import Crypto.Util.Tuple Crypto.Util.ListUtil Crypto.Util.Tactics.
Local Notation "A ^ n" := (tuple A n) : type_scope.

(***

Arithmetic on bignums that handles carry bits; this is useful for
saturated limbs. Compatible with mixed-radix bases.

 ***)

Section Saturated.
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
  Proof. cbv [eval_from eval]. auto using B.Positional.eval_wt_equiv. Qed.

  Lemma eval_from_S {n}: forall i (inp : (list Z)^(S n)),
    eval_from i inp = eval_from (S i) (tl inp) + weight i * sum (hd inp).
  Proof.
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
  Proof.
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
  Proof. cbv [compact_step_cps compact_step]; autorewrite with uncps; reflexivity. Qed.
  Hint Opaque compact_step : uncps.
  Hint Rewrite compact_step_id : uncps.
  
  Definition compact_cps {n} (xs : (list Z)^n) {T} (f:Z * Z^n->T) := 
    mapi_with_cps compact_step_cps 0 xs f.

  Definition compact {n} xs := @compact_cps n xs _ id.
  Lemma compact_id {n} xs {T} f : @compact_cps n xs T f = f (compact xs).
  Proof. cbv [compact_cps compact]; autorewrite with uncps; reflexivity. Qed.

  Lemma compact_digit_correct i (xs : list Z) :
    snd (compact_digit i xs)  = sum xs - (weight (S i) / weight i) * (fst (compact_digit i xs)).
  Proof.
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
  Proof.
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
  Proof. cbv [compact_invariant]. simpl. repeat (f_equal; try omega). Qed.

  Lemma compact_invariant_end {n} start (input : (list Z)^n):
    compact_invariant n 0%nat start (fst (mapi_with_cps compact_step_cps start input id)) input (snd (mapi_with_cps compact_step_cps start input id)).
  Proof.
    autorewrite with uncps push_id.
    apply (mapi_with_invariant _ compact_invariant
                               compact_invariant_holds compact_invariant_base).
  Qed.

  Lemma eval_compact {n} (xs : tuple (list Z) n) :
    B.Positional.eval weight (snd (compact xs)) + (weight n * fst (compact xs)) = eval xs.
  Proof.
    pose proof (compact_invariant_end 0 xs) as Hinv.
    cbv [compact_invariant] in Hinv.
    simpl in Hinv. autorewrite with zsimplify natsimplify in Hinv.
    rewrite eval_from_0, B.Positional.eval_from_0 in Hinv; apply Hinv.
  Qed.

End Saturated.

(*
Definition base10 i := Eval compute in 10^(Z.of_nat i).
Import ListNotations.
Eval cbv -[runtime_add runtime_mul Let_In] in
    (fun adc a0 a1 b0 b1 =>
       compact (n:=2) (add_get_carry:=adc) (weight:=base10) ([a1;b1],[a0;b0])).
*)
Require Import Coq.ZArith.ZArith Coq.micromega.Lia. Local Open Scope Z_scope.

(*
Goal forall W s c a b, 0 <= c -> W < s ->
  0 <= a < s ->
  0 <= c*b <= W-c ->
  s <= (a + c*b) ->
  (((a + c*b) mod s) / W = ((a + c*b) mod s + c * ((a + c*b) / s)) / W).
Proof.
  intros; assert ((a + c * b) / s = 1) by (Z.div_mod_to_equations; nia).
  transitivity 0; Z.div_mod_to_equations; nia.
Qed.

Goal forall W s (HH: s / W * W = s) c a b, 0 <= c < W -> W < s ->
  0 <= a < s ->
  0 <= -c*b < W-c ->
  (a + c*b) < 0 ->
  (((a + c*b) mod s) / W = ((a + c*b) mod s + c * ((a + c*b) / s)) / W).
Proof.
  intros; assert ((a + c * b) / s = -1) by (Z.div_mod_to_equations; nia).
  assert ((a + c * b) mod s = s + a + c*b) by (Z.div_mod_to_equations; nia).
  rewrite H4 in *; rewrite H5 in *.
  enough ((s + a + c * b) / W - (s/W-1) = (s + a + c * b + c * -1) / W - (s/W-1)) by lia.
  rewrite <-2Z.div_sub with (b:=s/W-1) by lia; rewrite 2Z.div_small; trivial.
  all : rewrite ?HH; try split; ring_simplify; try nia.
Qed.
 *)

Lemma saturated_pseudomersenne_reduction_converges :
  forall W s c a b (HH: b < 0 -> s / W * W = s), 0 <= c < W -> W <= s ->
  0 <= a < s ->
  0 <= c*Z.abs b <= W-c ->
  (((a + c*b) mod s) / W = ((a + c*b) mod s + c * ((a + c*b) / s)) / W).
Proof.
  intros; assert ((a+c*b)/s = -1 \/ (a+c*b)/s = 0 \/ (a+c*b)/s = 1)
    by (Z.div_mod_to_equations; nia); intuition idtac.
  { clear -HH H H0 H2 H4 H7. transitivity (s/W-1); Z.div_mod_to_equations; nia. }
  { f_equal. rewrite Z.mod_small; Z.div_mod_to_equations; lia. }
  { clear -H0 H3 H4 H6 H7. transitivity 0; Z.div_mod_to_equations; nia. }
Qed.

Require Import Coq.Classes.Morphisms.

Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.LetIn.
Require Import Crypto.Util.ZUtil.Modulo .
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Require Import Crypto.Arithmetic.WeightStream.
Import WeightStream.stream WeightStream.Saturated.
Import List ListNotations Coq.Init.Datatypes Coq.Lists.List List.

Implicit Types (weight bound : stream positive).
Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.

(* See lemma saturated_pseudomersenne_reduction_converges *)
Definition reduce' bound k (c : Z) (a : list Z) (b : list Z) : list Z :=
  let (sum, carry) := add_mul_small bound a c b in
  let (sum', _) := add bound 0 sum [c * carry] in
  firstn k sum' ++ skipn k sum.

Lemma eval_reduce' bound k c a b m
  (s : Z := weight bound (Nat.max (length a) (length b))) (Hc : s mod m = c)
  (Hc' : 0 <= c < weight bound k) (Hla : (k <= length a)%nat)
  (Ha : 0 <= eval bound a < weight bound (length a))
  (Hb : c * Z.abs (eval bound b) <= weight bound k - c) :
  eval bound (reduce' bound k c a b) mod m = (eval bound a + s * eval bound b) mod m.
Proof.
  cbv [reduce'] in *.
  repeat (rewrite ?add_mul_small_correct, ?add_correct, ?firstn_encode, ?eval_app,
    ?eval_encode, ?length_encode, ?eval_skipn_encode, ?eval_cons, ?eval_nil,
    ?Z.add_0_l, ?Z.mul_0_r, ?Z.add_0_r by lia; cbn [fst snd length]); fold s.
  rewrite saturated_pseudomersenne_reduction_converges, <-Z.div_mod''; try split; try lia.
  { rewrite (Zmod_eq _ s) by lia. push_Zmod. rewrite ?Hc. pull_Zmod. f_equal. ring. }
  { intros. rewrite Z.mul_comm. symmetry; apply Z.div_exact; try apply mod_weight_le; lia. }
  { apply weight_mono_le; lia. }
  { enough (weight bound (length a) <= s) by lia. apply weight_mono_le. lia. }
Qed.

Definition reduce bound k (c : Z) (a : list Z) (b : list Z) : list Z :=
  (* NOTE: it would be nice if we had an "if" that threw error messages during specialization *)
  if ((Z.of_nat k <=? Z.of_nat (length a))
  && (Z.of_nat (length b) <=? Z.of_nat (length a))
  && (0 <=? c)
  && (c <? weight bound k)
  && (0 <=? eval bound a)
  && (eval bound a <? weight bound (length a))
  && (c*Z.abs (eval bound b) <=? weight bound k - c))%bool
  then reduce' bound k c a b
  else a ++ b.

Lemma eval_reduce bound k c a b m
  (s : Z := weight bound (length a)) (Hc : s mod m = c)
  (Hbound : pointwise_relation nat eq (stream.skipn (length a) bound) bound) :
  eval bound (reduce bound k c a b) mod m = (eval bound a + s * eval bound b) mod m.
Proof.
  cbv [reduce]; break_match.
  { repeat match goal with H : _ |- _ => apply Bool.andb_prop in H; case H as [H ?] end.
    Require Import Crypto.Util.Decidable.Bool2Prop.
    rewrite eval_reduce'; rewrite ?Nat.max_l; repeat split; auto; try apply Nat2Z.inj_le; auto. }
  { rewrite eval_app; subst s. f_equiv. f_equiv. f_equiv. eapply Proper_eval; trivial. }
Qed.

(*
Definition mul_short_mod bound c n (a b : list Z) :=
  let p := mul bound a b in
  let (lo, hi) := (firstn n p, skipn n p) in
  if (* true by range analysis *) c*Z.abs (eval bound hi) <=? weight bound (length hi) - c
  then reduce' bound (length hi) c  lo hi
  else p.
*)

Definition mulmod bound n c a b :=
  dlet p := mul bound a b in
  let (lo, hi) := add_mul_limb bound (firstn n p) c (skipn n p) in
  if (* true by range analysis *) c*Z.abs hi <=? weight bound 1 - c
  then reduce' bound 1 c lo [hi]
  else lo ++ [hi].

Lemma eval_mulmod B (bound := fun _ => B) n a b m
  (s : Z := weight bound n) (c := s mod m) (Hc' : 0 <= c < stream.hd bound)
  (Hn : (n <= length a + length b <= n + n)%nat) (Hb : b <> nil)
  : eval bound (mulmod bound n c a b) mod m = (eval bound a * eval bound b) mod m.
Proof.
  cbv [Let_In mulmod].
  assert (1 <= length b)%nat by (destruct b; cbn [length] in *; congruence || lia).
  pose proof (eq_refl : weight bound n mod m = c) as Hc.
  pose proof eval_mul B a b as Hmul; fold bound in Hmul.
  epose proof eq_sym (eval_app _ (firstn n _) (skipn n _)) as Hsplit.
  erewrite firstn_skipn, Hmul in Hsplit.
  replace (length (firstn n (mul bound a b))) with n in *
    by (rewrite firstn_length, length_mul; trivial; lia).
  apply (f_equal (fun x => x mod m)) in Hsplit.
  revert Hsplit; push_Zmod; rewrite ?Hc; pull_Zmod; intro.
  change (stream.skipn n bound) with bound in *.
  rewrite add_mul_limb_correct.
  set (t := eval bound (firstn n (mul bound a b)) +
    c * eval bound (skipn n (mul bound a b))) in *.
  progress replace (Nat.max (length (firstn n (mul bound a b))) (length (skipn n (mul bound a b))))
    with n in * by (rewrite firstn_length, skipn_length, !length_mul; trivial; lia).
  break_match; [rewrite eval_reduce', eval_encode, Z.add_comm | rewrite eval_app];
  repeat rewrite ?length_encode, ?firstn_length, ?skipn_length, ?length_mul, ?eval_cons,
                 ?eval_encode, ?eval_nil, ?Z.mul_0_r, ?Z.add_0_r, ?weight_1 in *;
  cbn [length]; replace (Nat.max n 1) with n by lia; trivial; try lia.
  { rewrite <-Z.div_mod by lia. rewrite Hsplit; trivial. }
  { apply Z.mod_pos_bound. lia. }
  rewrite Z.add_comm. rewrite <-Z.div_mod; lia.
Qed.

Definition addmod bound c a b :=
  let (sum, carry) := add bound 0 a b in
  reduce' bound 1 c sum [carry].

Lemma eval_addmod bound c a b m
  (s : Z := weight bound (length a)) (Hc : s mod m = c)
  (Hc' : 0 <= 2*c <= bound O)
  (Hla : (1 < length a)%nat) (Hlb : (length b <= length a)%nat)
  (Ha : 0 <= eval bound a < weight bound (length a))
  (Hb : - weight bound (length a) <= eval bound b <= weight bound (length a)) :
  eval bound (addmod bound c a b) mod m = (eval bound a + eval bound b) mod m.
Proof.
  cbv [addmod]; rewrite add_correct by trivial; rewrite ?Z.add_0_l.
  rewrite eval_reduce'; rewrite ?eval_encode, ?length_encode, ?weight_1,
  ?eval_cons, ?eval_nil; cbn [length]; rewrite ?Nat.max_l, ?Z.mul_0_r, ?Z.add_0_r by lia; 
    try solve [trivial | cbn; lia | apply Z.mod_pos_bound; lia ].
  { rewrite (Z.add_comm (_ mod _) (_ * (_ / _))), <-Z.div_mod; lia. }
  assert (Z.abs ((eval bound a + eval bound b) / Z.pos (weight bound (length a))) <= 1) by (Z.div_mod_to_equations; nia); nia.
Qed.

Definition submod bound c a b := addmod bound c a (map Z.opp b).

Lemma eval_submod bound c a b m
  (s : Z := weight bound (length a)) (Hc : s mod m = c)
  (Hc' : 0 <= 2*c <= bound O)
  (Hla : (1 < length a)%nat) (Hlb : (length b <= length a)%nat)
  (Ha : 0 <= eval bound a < weight bound (length a))
  (Hb : - weight bound (length a) <= eval bound b <= weight bound (length a)) :
  eval bound (submod bound c a b) mod m = (eval bound a - eval bound b) mod m.
Proof. cbv [submod]; rewrite eval_addmod; rewrite ?map_length, ?eval_map_opp; auto; lia. Qed.

Section Examples.
  Local Notation "!" := ltac:(Decidable.vm_decide) (only parsing).
  Goal forall a0 a1 a2 a3 b : Z, False. intros.
  Proof.
    pose proof (eval_reduce' (fun _ => 2^64)%positive 1 38 [a0;a1;a2;a3] [b] (2^256-38) ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 4%nat)) with (2^256)%positive in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)) with (2^64)%positive in *.
    change (weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)%positive with (2^64)%positive in *.
    set (eval (fun _ : nat => (2 ^ 64)%positive)) as eval in *.
    set (reduce' (fun _ : nat => (2 ^ 64)%positive) _ _ _) as reduce' in *.
  Abort.

  Goal forall a0 a1 a2 a3 b0 b1 b2 b3 : Z, False. intros.
  Proof.
    pose proof (eval_addmod (fun _ => 2^64)%positive 38 [a0;a1;a2;a3] [b0;b1;b2;b3] (2^256-38) ! ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 4%nat)) with (2^256)%positive in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)) with (2^64)%positive in *.
    change (weight (fun _ : nat => (2 ^ 64)%positive) 1%nat)%positive with (2^64)%positive in *.
    set (eval (fun _ : nat => (2 ^ 64)%positive)) as eval in *.
    set (addmod _ _) as addmod in *.
  Abort.

  Goal forall a0 a1 a2 a3 b0 b1 b2 b3 : Z, False. intros.
  Proof.
    pose proof (eval_mulmod (2^64)%positive 4 [a0;a1;a2;a3] [b0;b1;b2;b3] (2^256-38) ! ! !).
    cbn [length] in *.
    change ((weight (fun _ : nat => (2 ^ 64)%positive) 4%nat)) with (2^256)%positive in *.
    set (eval (fun _ : nat => (2 ^ 64)%positive)) as eval in *.
    change (2 ^ 256 mod (2 ^ 256 - 38)) with 38 in *.
    set (mulmod _ _) as mulmod in *.
  Abort.
End Examples.

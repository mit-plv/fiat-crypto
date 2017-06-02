
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(***********************************************************************
      Cyclic.v

      Proof that an abelien ring is cyclic
 ************************************************************************)
Require Import ZCAux.
Require Import List.
Require Import Root.
Require Import UList.
Require Import IGroup.
Require Import EGroup.
Require Import FGroup.

Open Scope Z_scope.

Section Cyclic.

Variable A: Set.
Variable plus mult: A -> A -> A.
Variable op: A -> A.
Variable zero one: A.
Variable support: list A.
Variable e: A.

Hypothesis A_dec: forall a b: A, {a = b} + {a <> b}.
Hypothesis e_not_zero: zero <> e.
Hypothesis support_ulist: ulist support.
Hypothesis e_in_support: In e support.
Hypothesis zero_in_support: In zero support.
Hypothesis mult_internal: forall a b, In a support -> In b support -> In (mult a b) support.
Hypothesis mult_assoc: forall a b c, In a support -> In b support -> In c support -> mult a (mult b c) = mult (mult a b) c.
Hypothesis e_is_zero_l:  forall a, In a support ->  mult e a = a.
Hypothesis e_is_zero_r:  forall a, In a support ->  mult a e = a.
Hypothesis plus_internal: forall a b, In a support -> In b support -> In (plus a b) support.
Hypothesis plus_zero: forall a, In a support -> plus zero a = a.
Hypothesis plus_comm: forall a b, In a support -> In b support -> plus a b = plus b a.
Hypothesis plus_assoc: forall a b c, In a support -> In b support -> In c support -> plus a (plus b c) = plus (plus a b) c.
Hypothesis mult_zero: forall a, In a support -> mult zero a = zero.
Hypothesis mult_comm: forall a b, In a support -> In b support ->mult a b = mult b a.
Hypothesis mult_plus_distr: forall a b c, In a support -> In b support -> In c support -> mult a (plus b c) = plus (mult a b) (mult a c).
Hypothesis op_internal: forall a, In a support -> In (op a) support.
Hypothesis plus_op_zero: forall a, In a support -> plus a (op a) = zero.
Hypothesis mult_integral: forall a b, In a support -> In b support -> mult a b = zero -> a = zero \/ b = zero.

Definition IA := (IGroup A mult support e A_dec support_ulist e_in_support mult_internal
                             mult_assoc
                             e_is_zero_l e_is_zero_r).

Hint Resolve (fun x => isupport_incl _ mult support e A_dec x).

Theorem gpow_evaln: forall n, 0 < n ->
  exists p, (length p <=  Zabs_nat n)%nat /\  (forall i, In i p -> In i support) /\
  forall x, In x IA.(s) -> eval A plus mult zero (zero::p) x = gpow x IA n.
intros n Hn; generalize Hn; pattern n; apply natlike_ind; auto with zarith.
intros H1; contradict H1; auto with zarith.
intros x Hx Rec _.
case Zle_lt_or_eq with (1 := Hx); clear Hx; intros Hx; subst; simpl.
case Rec; auto; simpl; intros p (Hp1, (Hp2, Hp3)); clear Rec.
exists (zero::p); split; simpl.
rewrite Zabs_nat_Zsucc; auto with arith zarith.
split.
intros i [Hi | Hi]; try rewrite <- Hi; auto.
intros x1 Hx1; simpl.
rewrite Hp3; repeat rewrite plus_zero; unfold Zsucc; try rewrite gpow_add; auto with zarith.
rewrite gpow_1; try apply mult_comm; auto.
apply  (fun x => isupport_incl _ mult support e A_dec x); auto.
change (In (gpow x1 IA x) IA.(s)).
apply gpow_in; auto.
apply mult_internal; auto.
apply  (fun x => isupport_incl _ mult support e A_dec x); auto.
change (In (gpow x1 IA x) IA.(s)).
apply gpow_in; auto.
exists (e:: nil); split; simpl.
compute; auto with arith.
split.
intros i [Hi | Hi]; try rewrite <- Hi; auto; case Hi.
intros x Hx; simpl.
rewrite plus_zero; rewrite (fun x => mult_comm x zero); try rewrite mult_zero; auto.
rewrite plus_comm; try rewrite plus_zero; auto.
Qed.

Definition check_list_gpow: forall l n, (incl l IA.(s)) -> {forall a, In a l -> gpow a IA n = e} + {exists a, In a l /\  gpow a IA n <> e}.
intros l n; elim l; simpl; auto.
intros H; left; intros a H1; case H1.
intros a l1 Rec H.
case (A_dec (gpow a IA n) e); intros H2.
case Rec; try intros H3.
apply incl_tran with (2 := H); auto with datatypes.
left; intros a1 H4; case H4; auto.
intros H5; rewrite <- H5; auto.
right; case H3; clear H3; intros a1 (H3, H4).
exists a1; auto.
right; exists a; auto.
Defined.


Theorem prime_power_div: forall p q i, prime p -> 0 <= q -> 0 <= i -> (q | p ^ i)  -> exists j, 0 <= j <= i /\ q = p ^ j.
intros p q i Hp Hq Hi H.
assert (Hp1: 0 < p).
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
pattern q; apply prime_div_induction with (p ^ i); auto with zarith.
exists 0; rewrite Zpower_0_r; auto with zarith.
intros p1 i1 Hp2 Hi1 H1.
case Zle_lt_or_eq with (1 := Hi1); clear Hi1; intros Hi1; subst.
assert (Heq: p1 = p).
apply prime_div_Zpower_prime with i; auto.
apply Zdivide_trans with (2 := H1).
apply Zpower_divide; auto with zarith.
exists i1; split; auto; try split; auto with zarith.
case (Zle_or_lt i1 i); auto; intros H2.
absurd (p1 ^ i1 <= p  ^ i).
apply Zlt_not_le; rewrite Heq; apply Zpower_lt_monotone; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
apply Zdivide_le; auto with zarith.
rewrite Heq; auto.
exists 0; repeat rewrite Zpower_exp_0; auto with zarith.
intros p1 q1 Hpq (j1,((Hj1, Hj2), Hj3)) (j2, ((Hj4, Hj5), Hj6)).
case Zle_lt_or_eq with (1 := Hj1); clear Hj1; intros Hj1; subst.
case Zle_lt_or_eq with (1 := Hj4); clear Hj4; intros Hj4; subst.
inversion Hpq as [ H0 H1 H2].
absurd (p | 1).
intros H3; absurd (1 < p).
apply Zle_not_lt; apply Zdivide_le; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
apply H2; apply Zpower_divide; auto with zarith.
exists j1; rewrite Zpower_0_r; auto with zarith.
exists j2; rewrite Zpower_0_r; auto with zarith.
Qed.

Theorem inj_lt_inv: forall n m : nat, Z_of_nat n < Z_of_nat m -> (n < m)%nat.
intros n m H; case (le_or_lt m n); auto; intros H1; contradict H.
apply Zle_not_lt; apply inj_le; auto.
Qed.

Theorem not_all_solutions: forall i, 0 < i < g_order IA -> exists a, In a IA.(s) /\ gpow a IA i <> e.
intros i (Hi, Hi2).
case (check_list_gpow IA.(s) i); try intros H; auto with datatypes.
case (gpow_evaln i); auto; intros p (Hp1, (Hp2, Hp3)).
absurd ((op e) = zero).
intros H1; case e_not_zero.
rewrite <- (plus_op_zero e); try rewrite H1; auto.
rewrite plus_comm; auto.
apply (root_max_is_zero _ (fun x => In x support) plus mult op zero) with (l := IA.(s)) (p := op e :: p); auto with datatypes.
simpl; intros x [Hx | Hx]; try rewrite <- Hx; auto.
intros x Hx.
generalize (Hp3 _ Hx); simpl; rewrite plus_zero; auto.
intros tmp; rewrite tmp; clear tmp.
rewrite H; auto; rewrite plus_comm; auto with datatypes.
apply mult_internal; auto.
apply eval_P; auto.
simpl; apply lt_le_S; apply le_lt_trans with (1 := Hp1).
apply inj_lt_inv.
rewrite inj_Zabs_nat; auto with zarith.
rewrite Zabs_eq; auto with zarith.
Qed.

Theorem divide_g_order_e_order: forall n, 0 <= n -> (n | g_order IA) -> exists a, In a IA.(s) /\ e_order A_dec  a IA = n.
intros n Hn H.
assert (Hg: 0 < g_order IA).
apply g_order_pos.
assert (He: forall a, 0 <= e_order A_dec a IA).
intros a; apply Zlt_le_weak; apply e_order_pos.
pattern n; apply prime_div_induction with (n := g_order IA); auto.
exists e; split; auto.
apply IA.(e_in_s).
apply Zle_antisym.
apply Zdivide_le; auto with zarith.
apply e_order_divide_gpow; auto with zarith.
apply IA.(e_in_s).
rewrite gpow_1; auto.
apply IA.(e_in_s).
match goal with |- (_ <= ?X) => assert (0 < X) end; try apply e_order_pos; auto with zarith.
intros p i Hp Hi K.
assert (Hp1: 0 < p).
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
assert (Hi1: 0 < p ^ i).
apply Zpower_gt_0; auto.
case Zle_lt_or_eq with (1 := Hi); clear Hi; intros Hi; subst.
case (not_all_solutions (g_order IA / p)).
apply Zdivide_Zdiv_lt_pos; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
apply Zdivide_trans with (2 := K).
apply Zpower_divide; auto.
intros a (Ha1, Ha2).
exists (gpow a IA (g_order IA  / p ^ i)); split.
apply gpow_in; auto.
match goal with |- ?X = ?Y => assert (H1: (X | Y) ) end; auto.
apply e_order_divide_gpow; auto with zarith.
apply gpow_in; auto.
rewrite <- gpow_gpow; auto with zarith.
rewrite Zmult_comm; rewrite <- Zdivide_Zdiv_eq; auto with zarith.
apply fermat_gen; auto.
apply Z_div_pos; auto with zarith.
case prime_power_div with (4 := H1); auto with zarith.
intros j ((Hj1, Hj2), Hj3).
case Zle_lt_or_eq with (1 := Hj2); intros Hj4; subst; auto.
case Ha2.
replace (g_order IA) with (((g_order IA / p ^i) * p ^ j) * p ^ (i - j - 1) * p).
rewrite Z_div_mult; auto with zarith.
repeat rewrite gpow_gpow; auto with zarith.
rewrite <- Hj3.
rewrite gpow_e_order_is_e; auto with zarith.
rewrite gpow_e; auto.
apply Zlt_le_weak; apply Zpower_gt_0; auto with zarith.
apply gpow_in; auto.
apply Z_div_pos; auto with zarith.
apply Zmult_le_0_compat; try apply Z_div_pos; auto with zarith.
pattern p at 4; rewrite <- Zpower_1_r.
repeat rewrite <- Zmult_assoc; repeat rewrite <- Zpower_exp; auto with zarith.
replace (j + (i - j - 1 + 1)) with i; auto with zarith.
apply sym_equal; rewrite Zmult_comm; apply Zdivide_Zdiv_eq; auto with zarith.
rewrite Zpower_0_r; exists e; split.
apply IA.(e_in_s).
match goal with |- ?X = 1 => assert (tmp: 0 < X); try apply e_order_pos;
case Zle_lt_or_eq with 1 X; auto with zarith; clear tmp; intros H1 end.
absurd (gpow IA.(FGroup.e) IA 1 = IA.(FGroup.e)).
apply gpow_e_order_lt_is_not_e with A_dec; auto with zarith.
apply gpow_e; auto with zarith.
intros p q H1 (a, (Ha1, Ha2)) (b, (Hb1, Hb2)).
exists (mult a b); split.
apply IA.(internal); auto.
rewrite <- Ha2; rewrite <- Hb2; apply order_mult; auto.
rewrite Ha2; rewrite Hb2; auto.
Qed.

Set Implicit Arguments.
Definition cyclic (A: Set) A_dec (op: A -> A -> A) (G: FGroup op):= exists a, In a G.(s) /\ e_order A_dec a G = g_order G.
Unset Implicit Arguments.

Theorem cyclic_field: cyclic A_dec IA.
red; apply divide_g_order_e_order; auto.
apply Zlt_le_weak; apply g_order_pos.
exists 1; ring.
Qed.

End Cyclic.

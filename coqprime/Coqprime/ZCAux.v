
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

(**********************************************************************
     ZCAux.v

     Auxillary functions & Theorems
 **********************************************************************)

Require Import ArithRing.
Require Export ZArith Zpow_facts.
Require Export Znumtheory.
Require Export Tactic.

Theorem Zdivide_div_prime_le_square:  forall x, 1 < x -> ~prime x -> exists p, prime p /\ (p | x) /\ p * p <= x.
intros x Hx; generalize Hx; pattern x; apply Z_lt_induction; auto with zarith.
clear x Hx; intros x Rec H H1.
case (not_prime_divide x); auto.
intros x1 ((H2, H3), H4); case (prime_dec x1); intros H5.
case (Zle_or_lt (x1 * x1) x); intros H6.
exists x1; auto.
case H4; clear H4; intros x2 H4; subst.
assert (Hx2: x2 <= x1).
case (Zle_or_lt x2 x1); auto; intros H8; contradict H6; apply Zle_not_lt.
apply Zmult_le_compat_r; auto with zarith.
case (prime_dec x2); intros H7.
exists x2; repeat (split; auto with zarith).
apply Zmult_le_compat_l; auto with zarith.
apply Zle_trans with 2%Z; try apply prime_ge_2; auto with zarith.
case (Zle_or_lt 0 x2); intros H8.
case Zle_lt_or_eq with (1 := H8); auto with zarith; clear H8; intros H8; subst; auto with zarith.
case (Zle_lt_or_eq 1 x2); auto with zarith; clear H8; intros H8; subst; auto with zarith.
case (Rec x2); try split; auto with zarith.
intros x3 (H9, (H10, H11)).
exists x3; repeat (split; auto with zarith).
contradict H; apply Zle_not_lt; auto with zarith.
apply Zle_trans with (0 * x1);  auto with zarith.
case (Rec x1); try split; auto with zarith.
intros x3 (H9, (H10, H11)).
exists x3; repeat (split; auto with zarith).
apply Zdivide_trans with x1; auto with zarith.
Qed.


Theorem Zmult_interval: forall p q, 0 < p * q  -> 1 < p -> 0 < q < p * q.
intros p q H1 H2; assert (0 < q).
case (Zle_or_lt q 0); auto; intros H3; contradict H1; apply Zle_not_lt.
rewrite <- (Zmult_0_r p).
apply Zmult_le_compat_l; auto with zarith.
split; auto.
pattern q at 1; rewrite <- (Zmult_1_l q).
apply Zmult_lt_compat_r; auto with zarith.
Qed.

Theorem prime_induction: forall (P: Z -> Prop), P 0 -> P 1 -> (forall p q, prime p -> P q -> P (p * q)) -> forall p, 0 <= p -> P p.
intros P H H1 H2 p Hp.
generalize Hp; pattern p; apply Z_lt_induction; auto; clear p Hp.
intros p Rec Hp.
case Zle_lt_or_eq with (1 := Hp); clear Hp; intros Hp; subst; auto.
case (Zle_lt_or_eq  1 p); auto with zarith; clear Hp; intros Hp; subst; auto.
case (prime_dec p); intros H3.
rewrite <- (Zmult_1_r p); apply H2; auto.
 case (Zdivide_div_prime_le_square p); auto.
intros q (Hq1, ((q2, Hq2), Hq3)); subst.
case (Zmult_interval q q2).
rewrite Zmult_comm; apply Zlt_trans with 1; auto with zarith.
apply Zlt_le_trans with 2; auto with zarith; apply prime_ge_2; auto.
intros H4 H5; rewrite Zmult_comm; apply H2; auto.
apply Rec; try split; auto with zarith.
rewrite Zmult_comm; auto.
Qed.

Theorem div_power_max: forall p q, 1 < p -> 0 < q -> exists n, 0 <= n /\ (p ^n | q)  /\ ~(p ^(1 + n) | q).
intros p q H1 H2; generalize H2; pattern q; apply Z_lt_induction; auto with zarith; clear q H2.
intros q Rec H2.
case (Zdivide_dec p q); intros H3.
case (Zdivide_Zdiv_lt_pos p q); auto with zarith; intros H4 H5.
case (Rec (Zdiv q p)); auto with zarith.
intros n (Ha1, (Ha2, Ha3)); exists (n + 1); split; auto with zarith; split.
case Ha2; intros q1 Hq; exists q1.
rewrite Zpower_exp; try rewrite Zpower_1_r; auto with zarith.
rewrite  Zmult_assoc; rewrite <- Hq.
rewrite Zmult_comm; apply Zdivide_Zdiv_eq; auto with zarith.
intros (q1, Hu); case Ha3; exists q1.
apply Zmult_reg_r with p; auto with zarith.
rewrite (Zmult_comm (q / p)); rewrite <- Zdivide_Zdiv_eq; auto with zarith.
apply trans_equal with (1 := Hu); repeat rewrite Zpower_exp; try rewrite Zpower_exp_1; auto with zarith.
ring.
exists 0; repeat split; try rewrite Zpower_1_r; try rewrite Zpower_exp_0; auto with zarith.
Qed.

Theorem prime_div_induction:
  forall (P: Z -> Prop) n,
    0 < n ->
    (P 1) ->
    (forall p i, prime p -> 0 <= i -> (p^i | n) -> P (p^i)) ->
    (forall p q, rel_prime p q -> P p -> P q -> P (p * q)) ->
   forall m, 0 <= m -> (m | n) -> P m.
intros P n P1 Hn H H1 m Hm.
generalize Hm; pattern m; apply Z_lt_induction; auto; clear m Hm.
intros m Rec Hm H2.
case (prime_dec m); intros Hm1.
rewrite <- Zpower_1_r; apply H; auto with zarith.
rewrite Zpower_1_r; auto.
case Zle_lt_or_eq with (1 := Hm); clear Hm; intros Hm; subst.
2: contradict P1; case H2; intros; subst; auto with zarith.
case (Zle_lt_or_eq 1 m); auto with zarith; clear Hm; intros Hm; subst; auto.
case Zdivide_div_prime_le_square with m; auto.
intros p (Hp1, (Hp2, Hp3)).
case (div_power_max p m); auto with zarith.
generalize (prime_ge_2 p Hp1); auto with zarith.
intros i (Hi, (Hi1, Hi2)).
case Zle_lt_or_eq with (1 := Hi); clear Hi; intros Hi.
assert (Hpi: 0 < p ^ i).
apply Zpower_gt_0; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
rewrite (Z_div_exact_2 m (p ^ i)); auto with zarith.
apply H1; auto with zarith.
apply rel_prime_sym; apply rel_prime_Zpower_r; auto with zarith.
apply rel_prime_sym.
apply prime_rel_prime; auto.
contradict Hi2.
case Hi1; intros; subst.
rewrite Z_div_mult in Hi2; auto with zarith.
case Hi2; intros q0 Hq0; subst.
exists q0; rewrite Zpower_exp; try rewrite Zpower_1_r; auto with zarith.
apply H; auto with zarith.
apply Zdivide_trans with (1 := Hi1); auto.
apply Rec; auto with zarith.
split; auto with zarith.
apply Z_div_pos; auto with zarith.
apply Z_div_lt; auto with zarith.
apply Zle_ge; apply Zle_trans with p.
apply prime_ge_2; auto.
pattern p at 1; rewrite <- Zpower_1_r; apply Zpower_le_monotone; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
apply Z_div_pos; auto with zarith.
apply Zdivide_trans with (2 := H2); auto.
exists (p ^ i); apply Z_div_exact_2; auto with zarith.
apply Zdivide_mod; auto with zarith.
apply Zdivide_mod; auto with zarith.
case Hi2; rewrite <- Hi; rewrite Zplus_0_r; rewrite Zpower_1_r; auto.
Qed.

Theorem prime_div_Zpower_prime: forall n p q, 0 <= n -> prime p -> prime q -> (p | q ^ n) -> p = q.
intros n p q Hp Hq; generalize p q Hq; pattern n; apply natlike_ind; auto; clear n p q Hp Hq.
intros  p q Hp Hq; rewrite Zpower_0_r.
intros (r, H); subst.
case (Zmult_interval p r); auto; try rewrite Zmult_comm.
rewrite <- H; auto with zarith.
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
rewrite <- H; intros H1 H2; contradict H2; auto with zarith.
intros n1 H Rec p q Hp Hq; try rewrite Zpower_Zsucc; auto with zarith; intros H1.
case prime_mult with (2 := H1); auto.
intros H2; apply prime_div_prime; auto.
Qed.

Definition Zmodd  a b :=
match a with
| Z0 => 0
| Zpos a' =>
    match b with
    | Z0 => 0
    | Zpos _ => Zmod_POS a' b
    | Zneg b' =>
        let r := Zmod_POS a' (Zpos b') in
        match r  with Z0 =>  0 |  _  =>   b + r end
    end
| Zneg a' =>
    match b with
    | Z0 => 0
    | Zpos _ =>
        let r := Zmod_POS a' b in
        match r with Z0 =>  0 | _  =>  b - r end
    | Zneg b' => - (Zmod_POS a' (Zpos b'))
    end
end.

Theorem Zmodd_correct: forall a b, Zmodd a b = Zmod a b.
intros a b; unfold Zmod; case a; simpl; auto.
intros p; case b; simpl; auto.
intros p1; refine (Zmod_POS_correct _ _); auto.
intros p1; rewrite Zmod_POS_correct; auto.
case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
intros p; case b; simpl; auto.
intros p1; rewrite Zmod_POS_correct; auto.
case (Zdiv_eucl_POS p (Zpos p1)); simpl; intros z1 z2; case z2; auto.
intros p1; rewrite Zmod_POS_correct; simpl; auto.
case (Zdiv_eucl_POS p (Zpos p1)); auto.
Qed.

Theorem prime_divide_prime_eq:
 forall p1 p2, prime p1 -> prime p2 -> Zdivide p1 p2 ->  p1 = p2.
intros p1 p2 Hp1 Hp2 Hp3.
assert (Ha: 1 < p1).
inversion Hp1; auto.
assert (Ha1: 1 < p2).
inversion Hp2; auto.
case (Zle_lt_or_eq p1 p2); auto with zarith.
apply Zdivide_le; auto with zarith.
intros Hp4.
case (prime_div_prime p1 p2); auto with zarith.
Qed.

Theorem Zdivide_Zpower: forall n m, 0 < n -> (forall p i, prime p -> 0 < i -> (p^i | n) -> (p^i | m)) -> (n | m).
intros n m Hn; generalize m Hn; pattern n; apply prime_induction; auto with zarith; clear n m Hn.
intros m H1; contradict H1; auto with zarith.
intros p q H Rec m H1 H2.
assert (H3: (p | m)).
rewrite <- (Zpower_1_r p); apply H2; auto with zarith; rewrite Zpower_1_r; apply Zdivide_factor_r.
case (Zmult_interval p q); auto.
apply Zlt_le_trans with 2; auto with zarith; apply prime_ge_2; auto.
case H3; intros k Hk; subst.
intros Hq Hq1.
rewrite (Zmult_comm k); apply Zmult_divide_compat_l.
apply Rec; auto.
intros p1 i Hp1 Hp2 Hp3.
case (Z_eq_dec p p1); intros Hpp1; subst.
case (H2 p1 (Zsucc i)); auto with zarith.
rewrite Zpower_Zsucc; try apply Zmult_divide_compat_l; auto with zarith.
intros q2 Hq2; exists q2.
apply Zmult_reg_r with p1.
contradict H; subst; apply not_prime_0.
rewrite Hq2; rewrite Zpower_Zsucc; try ring; auto with zarith.
apply Gauss with p.
rewrite Zmult_comm; apply H2; auto.
apply Zdivide_trans with (1:= Hp3).
apply Zdivide_factor_l.
apply rel_prime_sym; apply rel_prime_Zpower_r; auto with zarith.
apply prime_rel_prime; auto.
contradict Hpp1; apply prime_divide_prime_eq; auto.
Qed.

Theorem prime_divide_Zpower_Zdiv: forall m a p i, 0 <= i -> prime p -> (m | a) -> ~(m | (a/p)) -> (p^i | a) -> (p^i | m).
intros m a p i Hi Hp (k, Hk) H (l, Hl); subst.
case (Zle_lt_or_eq 0 i); auto with arith; intros Hi1; subst.
assert (Hp0: 0 < p).
apply Zlt_le_trans with 2; auto with zarith; apply prime_ge_2; auto.
case (Zdivide_dec p k); intros H1.
case H1; intros k' H2; subst.
case H; replace (k' * p * m) with ((k' * m) * p); try ring; rewrite Z_div_mult; auto with zarith.
apply Gauss with k.
exists l; rewrite Hl; ring.
apply rel_prime_sym; apply rel_prime_Zpower_r; auto.
apply rel_prime_sym; apply prime_rel_prime; auto.
rewrite Zpower_0_r; apply Zone_divide.
Qed.

Theorem Zle_square_mult: forall a b, 0 <= a <= b -> a * a <= b * b.
intros a b (H1, H2); apply Zle_trans with (a * b); auto with zarith.
Qed.

Theorem Zlt_square_mult_inv: forall a b, 0 <= a -> 0 <= b -> a * a < b * b -> a < b.
intros a b H1 H2 H3; case (Zle_or_lt b a); auto; intros H4; apply Zmult_lt_reg_r with a;
   contradict H3; apply Zle_not_lt; apply Zle_square_mult; auto.
Qed.


Theorem Zmod_closeby_eq: forall a b n,  0 <= a -> 0 <= b < n -> a - b < n -> a mod n = b -> a = b.
intros a b n H H1 H2 H3.
case (Zle_or_lt 0 (a - b)); intros H4.
case Zle_lt_or_eq with (1 := H4); clear H4; intros H4; auto with zarith.
contradict H2; apply Zle_not_lt; apply Zdivide_le; auto with zarith.
apply Zmod_divide_minus; auto with zarith.
rewrite <- (Zmod_small a n); try split; auto with zarith.
Qed.


Theorem Zpow_mod_pos_Zpower_pos_correct: forall a m n, 0 < n -> Zpow_mod_pos a m n = (Zpower_pos a m) mod n.
intros a m; elim m; simpl; auto.
intros p Rec n H1; rewrite xI_succ_xO; rewrite Pplus_one_succ_r; rewrite <- Pplus_diag; auto.
repeat rewrite Zpower_pos_is_exp; auto.
repeat rewrite Rec; auto.
replace (Zpower_pos a 1) with a; auto.
2: unfold Zpower_pos; simpl; auto with zarith.
repeat rewrite (fun x => (Zmult_mod x a)); auto.
rewrite  (Zmult_mod  (Zpower_pos a p)); auto.
case (Zpower_pos a p mod n); auto.
intros p Rec n H1; rewrite <- Pplus_diag; auto.
repeat rewrite Zpower_pos_is_exp; auto.
repeat rewrite Rec; auto.
rewrite  (Zmult_mod  (Zpower_pos a p)); auto.
case (Zpower_pos a p mod n); auto.
unfold Zpower_pos; simpl; rewrite Zmult_1_r; auto with zarith.
Qed.

Theorem Zpow_mod_Zpower_correct: forall a m n, 1 < n -> 0 <= m -> Zpow_mod a m n = (a ^ m) mod n.
intros a m n; case m; simpl; auto.
intros; apply Zpow_mod_pos_Zpower_pos_correct; auto with zarith.
Qed.

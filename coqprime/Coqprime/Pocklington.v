
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Require Import ZArith.
Require Export Znumtheory.
Require Import Tactic.
Require Import ZCAux.
Require Import Zp.
Require Import FGroup.
Require Import EGroup.
Require Import Euler.

Open Scope Z_scope.

Theorem Pocklington:
forall N F1 R1, 1 < F1 -> 0 < R1 -> N - 1 = F1 * R1 ->
   (forall p, prime p -> (p | F1) -> exists a,  1 < a /\ a^(N - 1) mod N = 1 /\ Zgcd (a ^ ((N - 1)/ p) - 1) N = 1) ->
  forall n, prime n -> (n | N) -> n mod F1 = 1.
intros N F1 R1 HF1 HR1 Neq Rec n Hn H.
assert (HN: 1 < N).
assert (0 < N - 1); auto with zarith.
rewrite Neq; auto with zarith.
apply Zlt_le_trans with (1* R1); auto with zarith.
assert (Hn1: 1 < n); auto with zarith.
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
assert (H1: (F1 | n - 1)).
2: rewrite <- (Zmod_small 1 F1); auto with zarith.
2: case H1; intros k H1'.
2: replace n with (1 + (n - 1)); auto with zarith.
2: rewrite H1'; apply Z_mod_plus; auto with zarith.
apply Zdivide_Zpower; auto with zarith.
intros p i Hp Hi HiF1.
case (Rec p); auto.
apply Zdivide_trans with (2 := HiF1).
apply Zpower_divide; auto with zarith.
intros a (Ha1, (Ha2, Ha3)).
assert (HNn: a ^ (N - 1) mod n = 1).
apply Zdivide_mod_minus; auto with zarith.
apply Zdivide_trans with (1 := H).
apply Zmod_divide_minus; auto with zarith.
assert (~(n | a)).
intros H1; absurd (0 = 1); auto with zarith.
rewrite <- HNn; auto.
apply sym_equal; apply Zdivide_mod; auto with zarith.
apply Zdivide_trans with (1 := H1); apply Zpower_divide; auto with zarith.
assert (Hr: rel_prime a n).
apply rel_prime_sym; apply prime_rel_prime; auto.
assert (Hz: 0 < Zorder a n).
apply Zorder_power_pos; auto.
apply Zdivide_trans with (Zorder a n).
apply prime_divide_Zpower_Zdiv with (N - 1); auto with zarith.
apply Zorder_div_power; auto with zarith.
intros H1; absurd (1 < n); auto; apply Zle_not_lt; apply Zdivide_le; auto with zarith.
rewrite <- Ha3; apply Zdivide_Zgcd; auto with zarith.
apply Zmod_divide_minus; auto with zarith.
case H1; intros t Ht; rewrite Ht.
assert (Ht1: 0 <= t).
apply Zmult_le_reg_r with (Zorder a n); auto with zarith.
rewrite Zmult_0_l; rewrite <- Ht.
apply Zge_le; apply Z_div_ge0; auto with zarith.
apply Zlt_gt; apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
rewrite Zmult_comm; rewrite Zpower_mult; auto with zarith.
rewrite Zpower_mod; auto with zarith.
rewrite Zorder_power_is_1; auto with zarith.
rewrite Zpower_1_l; auto with zarith.
apply Zmod_small; auto with zarith.
apply Zdivide_trans with (1:= HiF1); rewrite Neq; apply Zdivide_factor_r.
apply Zorder_div; auto.
Qed.

Theorem PocklingtonCorollary1:
forall N F1 R1, 1 < F1 -> 0 < R1 -> N - 1 = F1 * R1 -> N < F1 * F1 ->
   (forall p, prime p -> (p | F1) -> exists a,  1 < a /\ a^(N - 1) mod N = 1 /\ Zgcd (a ^ ((N - 1)/ p) - 1) N = 1) ->
   prime N.
intros N F1 R1 H H1 H2 H3 H4; case (prime_dec N); intros H5; auto.
assert (HN: 1 < N).
assert (0 < N - 1); auto with zarith.
rewrite H2; auto with zarith.
apply Zlt_le_trans with (1* R1); auto with zarith.
case Zdivide_div_prime_le_square with (2:= H5); auto with zarith.
intros n (Hn, (Hn1, Hn2)).
assert (Hn3: 0 <= n).
apply Zle_trans with 2; try apply prime_ge_2; auto with zarith.
absurd (n = 1).
intros H6; contradict Hn; subst; apply not_prime_1.
rewrite <- (Zmod_small n F1); try split; auto.
apply Pocklington with (R1 := R1) (4 := H4); auto.
apply Zlt_square_mult_inv; auto with zarith.
Qed.

Theorem PocklingtonCorollary2:
forall N F1 R1, 1 < F1 -> 0 < R1 -> N - 1 = F1 * R1 ->
   (forall p,  prime p -> (p | F1) -> exists a,  1 < a /\ a^(N - 1) mod N = 1 /\ Zgcd (a ^ ((N - 1)/ p) - 1) N = 1) ->
  forall n, 0 <= n -> (n | N) -> n mod F1 = 1.
intros N F1 R1 H1 H2 H3 H4 n H5; pattern n; apply prime_induction; auto.
assert (HN: 1 < N).
assert (0 < N - 1); auto with zarith.
rewrite H3; auto with zarith.
apply Zlt_le_trans with (1* R1); auto with zarith.
intros (u, Hu); contradict HN; subst; rewrite Zmult_0_r; auto with zarith.
intro H6; rewrite Zmod_small; auto with zarith.
intros p q Hp Hp1 Hp2; rewrite Zmult_mod; auto with zarith.
rewrite Pocklington with (n := p) (R1 := R1) (4 := H4); auto.
rewrite Hp1.
rewrite Zmult_1_r; rewrite Zmod_small; auto with zarith.
apply Zdivide_trans with (2 := Hp2); apply Zdivide_factor_l.
apply Zdivide_trans with (2 := Hp2); apply Zdivide_factor_r; auto.
Qed.

Definition isSquare x := exists y, x = y * y.

Theorem PocklingtonExtra:
forall N F1 R1, 1 < F1 -> 0 < R1 -> N - 1 = F1 * R1 -> Zeven F1 -> Zodd R1 ->
   (forall p, prime p -> (p | F1) -> exists a,  1 < a /\ a^(N - 1) mod N = 1 /\ Zgcd (a ^ ((N - 1)/ p) - 1) N = 1) ->
   forall m, 1 <= m ->  (forall l, 1 <= l < m -> ~((l * F1 + 1) | N)) ->
    let s := (R1 / (2 * F1)) in
    let r := (R1 mod (2 * F1)) in
      N < (m * F1 + 1) * (2 * F1 * F1 + (r - m) * F1 + 1) ->
      (s = 0 \/ ~ isSquare (r * r - 8 * s)) -> prime N.
intros N F1 R1 H1 H2 H3 OF1 ER1 H4 m H5 H6 s r H7 H8.
case (prime_dec N); auto; intros H9.
assert (HN: 1 < N).
assert (0 < N - 1); auto with zarith.
rewrite H3; auto with zarith.
apply Zlt_le_trans with (1* R1); auto with zarith.
case  Zdivide_div_prime_le_square with N; auto.
intros X (Hx1, (Hx2, Hx3)).
assert (Hx0: 1 < X).
apply Zlt_le_trans with 2; try apply prime_ge_2; auto with zarith.
pose (c := (X /  F1)).
assert(Hc1: 0 <= c); auto with zarith.
apply Zge_le; unfold c; apply Z_div_ge0; auto with zarith.
assert (Hc2: X = c * F1 + 1).
rewrite (Z_div_mod_eq X F1); auto with zarith.
eq_tac; auto.
rewrite (Zmult_comm F1); auto.
apply PocklingtonCorollary2 with (R1 := R1) (4 := H4); auto with zarith.
case Zle_lt_or_eq with (1 := Hc1); clear Hc1; intros Hc1.
2: contradict Hx0; rewrite Hc2; try rewrite <- Hc1; auto with zarith.
case (Zle_or_lt m c); intros Hc3.
2: case Zle_lt_or_eq with (1 := H5); clear H5; intros H5; auto with zarith.
2: case (H6 c); auto with zarith; rewrite <- Hc2; auto.
2: contradict Hc3; rewrite <- H5; auto with zarith.
pose (d := ((N / X) /  F1)).
assert(Hd0: 0 <= N / X); try apply Z_div_pos; auto with zarith.
(*
apply Zge_le; unfold d; repeat apply Z_div_ge0; auto with zarith.
*)
assert(Hd1: 0 <= d); auto with zarith.
apply Zge_le; unfold d; repeat apply Z_div_ge0; auto with zarith.
assert (Hd2: N / X =  d * F1 + 1).
rewrite (Z_div_mod_eq (N / X) F1); auto with zarith.
eq_tac; auto.
rewrite (Zmult_comm F1); auto.
apply PocklingtonCorollary2 with (R1 := R1) (4 := H4); auto with zarith.
exists X; auto with zarith.
apply Zdivide_Zdiv_eq; auto with zarith.
case Zle_lt_or_eq with (1  := Hd0); clear Hd0; intros Hd0.
2: contradict HN; rewrite (Zdivide_Zdiv_eq X N); auto with zarith.
2: rewrite <- Hd0; auto with zarith.
case (Zle_lt_or_eq 1 (N / X)); auto with zarith; clear Hd0; intros Hd0.
2: contradict H9; rewrite (Zdivide_Zdiv_eq X N); auto with zarith.
2: rewrite <- Hd0; rewrite Zmult_1_r; auto with zarith.
case Zle_lt_or_eq with (1 := Hd1); clear Hd1; intros Hd1.
2: contradict Hd0; rewrite Hd2; try rewrite <- Hd1; auto with zarith.
case (Zle_or_lt m d); intros Hd3.
2: case Zle_lt_or_eq with (1 := H5); clear H5; intros H5; auto with zarith.
2: case (H6 d); auto with zarith; rewrite <- Hd2; auto.
2: exists X; auto with zarith.
2: apply Zdivide_Zdiv_eq; auto with zarith.
2: contradict Hd3; rewrite <- H5; auto with zarith.
assert (L5: N = (c * F1 + 1) * (d * F1 + 1)).
rewrite <- Hc2; rewrite <- Hd2; apply Zdivide_Zdiv_eq; auto with zarith.
assert (L6: R1 = c * d * F1 + c + d).
apply trans_equal with ((N - 1) / F1).
rewrite H3; rewrite Zmult_comm; apply sym_equal; apply Z_div_mult; auto with zarith.
rewrite L5.
match goal with |- (?X / ?Y = ?Z) => replace X with (Z * Y) end; try ring; apply Z_div_mult; auto with zarith.
assert (L6_1: Zodd (c + d)).
case (Zeven_odd_dec (c + d)); auto; intros O1.
contradict ER1; apply Zeven_not_Zodd; rewrite L6; rewrite <- Zplus_assoc; apply Zeven_plus_Zeven; auto.
apply Zeven_mult_Zeven_r; auto.
assert (L6_2: Zeven (c * d)).
case (Zeven_odd_dec c); intros HH1.
apply Zeven_mult_Zeven_l; auto.
case (Zeven_odd_dec d); intros HH2.
apply Zeven_mult_Zeven_r; auto.
contradict L6_1; apply Zeven_not_Zodd; apply Zodd_plus_Zodd; auto.
assert ((c + d) mod (2 * F1) = r).
rewrite <- Z_mod_plus with (b := Zdiv2 (c * d)); auto with zarith.
match goal with |- ?X mod _ = _ => replace X with R1 end; auto.
rewrite L6; pattern (c * d) at 1.
rewrite Zeven_div2 with (1 := L6_2); ring.
assert (L9: c + d - r < 2 * F1).
apply Zplus_lt_reg_r with (r - m).
apply Zmult_lt_reg_r with (F1); auto with zarith.
apply Zplus_lt_reg_r with 1.
match goal with |-  ?X < ?Y =>
  replace Y with (2 * F1 * F1 + (r - m) * F1 + 1); try ring;
  replace X with ((((c + d) - m) * F1) + 1); try ring
end.
apply Zmult_lt_reg_r with (m * F1 + 1); auto with zarith.
apply Zlt_trans with (m * F1 + 0); auto with zarith.
rewrite Zplus_0_r; apply Zmult_lt_O_compat; auto with zarith.
repeat rewrite (fun x => Zmult_comm x (m * F1 + 1)).
apply Zle_lt_trans with (2 := H7).
rewrite L5.
match goal with |-  ?X <= ?Y =>
  replace X with ((m * (c + d) - m * m ) * F1 * F1 + (c + d) * F1 + 1); try ring;
  replace Y with ((c * d) * F1 * F1 + (c + d) * F1 + 1); try ring
end.
repeat apply Zplus_le_compat_r.
repeat apply Zmult_le_compat_r; auto with zarith.
assert (tmp: forall p q, 0 <= p - q  -> q <= p); auto with zarith; try apply tmp.
match goal with |-  _ <= ?X =>
  replace X with ((c - m) * (d - m)); try ring; auto with zarith
end.
assert (L10: c + d = r).
apply Zmod_closeby_eq with (2 * F1); auto with zarith.
unfold r; apply Z_mod_lt; auto with zarith.
assert (L11: 2 * s  = c * d).
apply Zmult_reg_r with F1; auto with zarith.
apply trans_equal with (R1 - (c + d)).
rewrite L10; rewrite (Z_div_mod_eq R1 (2 * F1)); auto with zarith.
unfold s, r; ring.
rewrite L6; ring.
case H8; intro H10.
absurd (0 < c * d); auto with zarith.
apply Zmult_lt_O_compat; auto with zarith.
case H10; exists (c - d); auto with zarith.
rewrite <- L10.
replace (8 * s) with (4 * (2 * s)); auto with zarith; try rewrite L11; ring.
Qed.

Theorem PocklingtonExtraCorollary:
forall N F1 R1, 1 < F1 -> 0 < R1 -> N - 1 = F1 * R1 -> Zeven F1 -> Zodd R1 ->
   (forall p, prime p -> (p | F1) -> exists a,  1 < a /\ a^(N - 1) mod N = 1 /\ Zgcd (a ^ ((N - 1)/ p) - 1) N = 1) ->
    let s := (R1 / (2 * F1)) in
    let r := (R1 mod (2 * F1)) in
      N < 2 * F1 * F1 * F1 ->  (s = 0 \/ ~ isSquare (r * r - 8 * s)) -> prime N.
intros N F1 R1 H1 H2 H3 OF1 ER1 H4 s r H5 H6.
apply PocklingtonExtra with (6 := H4) (R1 := R1) (m := 1); auto with zarith.
apply Zlt_le_trans with (1 := H5).
match goal with |-  ?X <= ?K * ((?Y + ?Z) + ?T) =>
    rewrite <- (Zplus_0_l X);
   replace (K * ((Y + Z) + T)) with ((F1 * (Z + T) +  Y + Z + T) + X);[idtac | ring]
end.
apply Zplus_le_compat_r.
case (Zle_lt_or_eq 0 r); unfold r; auto with zarith.
case (Z_mod_lt R1 (2 * F1)); auto with zarith.
intros HH; repeat ((rewrite <- (Zplus_0_r 0); apply Zplus_le_compat)); auto with zarith.
intros HH; contradict ER1; apply Zeven_not_Zodd.
rewrite (Z_div_mod_eq R1 (2 * F1)); auto with zarith.
rewrite <- HH; rewrite Zplus_0_r.
rewrite <- Zmult_assoc; apply Zeven_2p.
Qed.

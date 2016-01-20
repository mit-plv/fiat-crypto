
(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import ZArith Znumtheory Zpow_facts.
Require Import CyclicAxioms DoubleCyclic BigN Cyclic31 Int31.
Require Import ZCAux.
Require Import W.
Require Import Mod_op.
Require Import LucasLehmer.
Require Import Bits.
Import CyclicAxioms DoubleType DoubleBase.

Open Scope Z_scope. 

Section test.

Variable w: Type.
Variable w_op: ZnZ.Ops w.
Variable op_spec: ZnZ.Specs w_op.
Variable p: positive.
Variable b: w.

Notation "[| x |]" :=
   (ZnZ.to_Z x)  (at level 0, x at level 99).


Hypothesis p_more_1: 2 < Zpos p.
Hypothesis b_p: [|b|] = 2 ^ Zpos p - 1.

Lemma b_pos: 0 < [|b|].
rewrite b_p; auto with zarith.
assert (2 ^ 0 < 2 ^ Zpos p); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_0_r in H; auto with zarith.
Qed.

Hint Resolve b_pos.

Variable m_op: mod_op w.
Variable m_op_spec: mod_spec w_op b m_op.

Let w2 := m_op.(add_mod) ZnZ.one ZnZ.one.

Lemma w1_b: [|ZnZ.one|] = 1 mod [|b|].
rewrite ZnZ.spec_1; simpl; auto.
rewrite Zmod_small; auto with zarith.
split; auto with zarith.
rewrite b_p.
assert (2 ^ 1 < 2 ^ Zpos p); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_1_r in H; auto with zarith.
Qed.

Lemma w2_b: [|w2|] = 2 mod [|b|].
unfold w2; rewrite (add_mod_spec m_op_spec _ _ _ _ w1_b w1_b).
rewrite w1_b; rewrite <- Zplus_mod; auto with zarith.
Qed.

Let w4 := m_op.(add_mod) w2 w2.

Lemma w4_b: [|w4|] = 4 mod [|b|].
unfold w4; rewrite (add_mod_spec m_op_spec _ _ _ _ w2_b w2_b).
rewrite w2_b; rewrite <- Zplus_mod; auto with zarith.
Qed.

Let square_m2 :=
   let square := m_op.(square_mod) in
   let sub := m_op.(sub_mod) in
   fun x => sub (square x) w2.

Definition lucastest :=
 ZnZ.to_Z (iter_pos (Pminus p 2) _ square_m2 w4).

Theorem lucastest_aux_correct:
 forall p1 z n, 0 <= n -> [|z|] = fst (s n) mod (2 ^ Zpos p - 1) ->
       [|iter_pos p1 _ square_m2 z|] = fst (s (n + Zpos p1)) mod (2 ^ Zpos p - 1).
intros p1; pattern p1; apply Pind; simpl iter_pos; simpl s; clear p1.
intros z p1 Hp1 H.
unfold square_m2.
rewrite <- b_p in H.
generalize (square_mod_spec m_op_spec _ _ H); intros H1.
rewrite (sub_mod_spec m_op_spec _ _ _ _ H1 w2_b).
rewrite H1; rewrite w2_b; auto with zarith.
rewrite H; rewrite <- Zmult_mod; auto with zarith.
rewrite <- Zminus_mod; auto with zarith.
rewrite sn; simpl; auto with zarith.
rewrite b_p; auto.
intros p1 Rec w1 z Hz Hw1.
rewrite Pplus_one_succ_l; rewrite iter_pos_plus;
 simpl iter_pos.
match goal with |- context[square_m2 ?X] =>
  set (tmp := X); unfold square_m2; unfold tmp; clear tmp
end.
generalize (Rec _ _ Hz Hw1); intros H1.
rewrite <- b_p in H1.
generalize (square_mod_spec m_op_spec _ _ H1); intros H2.
rewrite (sub_mod_spec m_op_spec _ _ _ _ H2 w2_b).
rewrite H2; rewrite w2_b; auto with zarith.
rewrite H1; rewrite <- Zmult_mod; auto with zarith.
rewrite <- Zminus_mod; auto with zarith.
replace (z + Zpos (1 + p1)) with ((z + Zpos p1) + 1); auto with zarith.
rewrite sn; simpl fst; try rewrite b_p; auto with zarith.
rewrite Zpos_plus_distr; auto with zarith.
Qed.

Theorem lucastest_prop: lucastest = fst(s (Zpos p -2)) mod (2 ^ Zpos p - 1).
unfold lucastest.
assert (F: 0 <= 0); auto with zarith.
generalize (lucastest_aux_correct (p -2) w4 F); simpl Zplus;
   rewrite Zpos_minus; auto with zarith.
rewrite Zmax_right; auto with zarith.
intros tmp; apply tmp; clear tmp.
rewrite <- b_p; simpl; exact w4_b.
Qed.

Theorem lucastest_prop_cor: lucastest = 0 -> (2 ^ Zpos p - 1 | fst(s (Zpos p - 2)))%Z.
intros H.
apply Zmod_divide.
assert (H1: 2 ^ 1 < 2 ^ Zpos p); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_1_r in H1; auto with zarith.
apply trans_equal with (2:= H); apply sym_equal; apply lucastest_prop; auto.
Qed.

Theorem lucastest_prime:  lucastest = 0 -> prime (2 ^ Zpos p - 1).
intros H1; case (prime_dec (2 ^ Zpos p - 1)); auto; intros H2.
case Zdivide_div_prime_le_square with (2 := H2).
assert (H3: 2 ^ 1 < 2 ^ Zpos p); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_1_r in H3; auto with zarith.
intros q (H3, (H4, H5)).
contradict H5; apply Zlt_not_le.
generalize q_more_than_square; unfold Mp; intros tmp; apply tmp;
  auto; clear tmp.
apply lucastest_prop_cor; auto.
case (Zle_lt_or_eq 2 q); auto.
apply prime_ge_2; auto.
intros H5; subst.
absurd (2 <= 1); auto with arith.
apply Zdivide_le; auto with zarith.
case H4; intros x Hx.
exists (2 ^ (Zpos p -1) - x).
rewrite Zmult_minus_distr_r; rewrite <- Hx; unfold Mp.
pattern 2 at 2; rewrite <- Zpower_1_r; rewrite <- Zpower_exp; auto with zarith.
replace (Zpos p - 1 + 1) with (Zpos p); auto with zarith.
Qed.

End test.

Definition znz_of_Z (w: Type) (op: ZnZ.Ops w) z :=
 match z with
 | Zpos p => snd (ZnZ.of_pos p)
 | _ => ZnZ.zero
 end.

Definition lucas p :=
 let op := cmk_op (Peano.pred (nat_of_P (get_height 31 p))) in
 let b := znz_of_Z op (Zpower 2 (Zpos p) - 1) in
 let zp := znz_of_Z op (Zpos p) in
 let mod_op := mmake_mod_op op b zp in
  lucastest op p mod_op.

Theorem lucas_prime:
 forall p, 2 < Zpos p -> lucas p = 0 -> prime (2 ^ Zpos p - 1).
unfold lucas; intros p Hp H.
match type of H with lucastest (cmk_op ?x) ?y ?z = _ =>
   set (w_op := (cmk_op x)); assert(A1: ZnZ.Specs w_op)
end.
unfold w_op; apply cmk_spec.
assert (F0: Zpos p <= Zpos (ZnZ.digits w_op)).
unfold w_op, base; rewrite (cmk_op_digits (Peano.pred (nat_of_P (get_height 31 p)))).
generalize (get_height_correct 31 p).
replace (Z_of_nat (Peano.pred (nat_of_P (get_height 31 p)))) with
       ((Zpos (get_height 31 p) - 1) ); auto with zarith.
rewrite pred_of_minus; rewrite inj_minus1; auto with zarith.
rewrite <- Zpos_eq_Z_of_nat_o_nat_of_P; auto with zarith.
generalize (lt_O_nat_of_P (get_height 31 p)); auto with zarith.
assert (F1: ZnZ.to_Z (znz_of_Z w_op (2 ^ (Zpos p) - 1)) = 2 ^ (Zpos p) - 1).
assert (F1: 0 < 2 ^ (Zpos p) - 1).
assert (F2: 2 ^ 0 < 2 ^ (Zpos p)); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_0_r in F2; auto with zarith.
case_eq (2 ^ (Zpos p) - 1); simpl ZnZ.to_Z.
intros HH; contradict F1; rewrite HH; auto with zarith.
2: intros p1 HH; contradict F1; rewrite HH; 
  apply Zle_not_lt; red; simpl; intros; discriminate.
intros p1 Hp1; apply ZnZ.of_pos_correct; auto.
rewrite <- Hp1.
unfold base.
apply Zlt_le_trans with (2 ^ (Zpos p)); auto with zarith.
apply Zpower_le_monotone; auto with zarith.
match type of H with lucastest (cmk_op ?x) ?y ?z = _ =>
  apply  
  (@lucastest_prime _ _ (cmk_spec x) p (znz_of_Z w_op (2 ^ Zpos p  -1)) Hp F1 z)
end; auto with zarith; fold w_op.
eapply mmake_mod_spec with (p := p); auto with zarith.
unfold znz_of_Z; unfold znz_of_Z in F1; rewrite F1.
assert (F2: 2 ^ 1 < 2 ^ (Zpos p)); auto with zarith.
apply Zpower_lt_monotone; auto with zarith.
rewrite Zpower_1_r in F2; auto with zarith.
rewrite ZnZ.of_Z_correct; auto with zarith.
split; auto with zarith.
apply Zle_lt_trans with (1 := F0); auto with zarith.
unfold base; apply Zpower2_lt_lin; auto with zarith.
Qed.



(*************************************************************)
(*      This file is distributed under the terms of the      *)
(*      GNU Lesser General Public License Version 2.1        *)
(*************************************************************)
(*    Benjamin.Gregoire@inria.fr Laurent.Thery@inria.fr      *)
(*************************************************************)

Set Implicit Arguments.

Require Import DoubleBase DoubleSub DoubleMul DoubleSqrt DoubleLift DoubleDivn1 DoubleDiv. 
Require Import CyclicAxioms DoubleCyclic BigN Cyclic31.
Require Import ZArith ZCAux.
Import CyclicAxioms DoubleType DoubleBase.

Theorem Zpos_pos: forall x, 0 < Zpos x.
red; simpl; auto.
Qed.
Hint Resolve Zpos_pos: zarith.

Section Mod_op.

 Variable w : Type.
 
 Record mod_op : Type := mk_mod_op {    
   succ_mod   : w -> w;
   add_mod    : w -> w -> w;
   pred_mod   : w -> w;
   sub_mod    : w -> w -> w;
   mul_mod    : w -> w -> w;
   square_mod : w -> w;
   power_mod  : w -> positive -> w
 }.

 Variable w_op : ZnZ.Ops w.
 
 Let w_digits      := w_op.(ZnZ.digits).
 Let w_zdigits     := w_op.(ZnZ.zdigits).
 Let w_to_Z        := (@ZnZ.to_Z _ w_op).
 Let w_of_pos      := (@ZnZ.of_pos _ w_op).
 Let w_head0       := (@ZnZ.head0 _ w_op).
 Let w0            := (@ZnZ.zero _ w_op).
 Let w1            := (@ZnZ.one _ w_op).
 Let wBm1          := (@ZnZ.minus_one _ w_op).

 Let wWW           := (@ZnZ.WW _ w_op).
 Let wW0           := (@ZnZ.WO _ w_op).
 Let w0W           := (@ZnZ.OW _ w_op).

 Let w_compare     := (@ZnZ.compare _ w_op).
 Let w_opp_c       := (@ZnZ.opp_c _ w_op).
 Let w_opp         := (@ZnZ.opp _ w_op).
 Let w_opp_carry   := (@ZnZ.opp_carry _ w_op).

 Let w_succ        := (@ZnZ.succ _ w_op).
 Let w_succ_c      := (@ZnZ.succ_c _ w_op).
 Let w_add_c       := (@ZnZ.add_c _ w_op).
 Let w_add_carry_c := (@ZnZ.add_carry_c _ w_op).
 Let w_add         := (@ZnZ.add _ w_op).


 Let w_pred_c      := (@ZnZ.pred_c _ w_op).
 Let w_sub_c       := (@ZnZ.sub_c _ w_op).
 Let w_sub_carry   := (@ZnZ.sub_carry _ w_op).
 Let w_sub_carry_c := (@ZnZ.sub_carry_c _ w_op).
 Let w_sub         := (@ZnZ.sub _ w_op).
 Let w_pred        := (@ZnZ.pred _ w_op).

 Let w_mul_c       := (@ZnZ.mul_c _ w_op).
 Let w_mul         := (@ZnZ.mul _ w_op).
 Let w_square_c    := (@ZnZ.square_c _ w_op).

 Let w_div21       := (@ZnZ.div21 _ w_op).
 Let w_add_mul_div := (@ZnZ.add_mul_div _ w_op).

 Variable b : w.
    (* b should be > 1 *)
 Let n := w_head0 b.

 Let b2n := w_add_mul_div n b w0.

 Let bm1 := w_sub b w1.

 Let mb := w_opp b.

 Let wwb := WW w0 b.

 Let low x := match x with WW _ x => x | W0 => w0 end.

 Let w_add2 x y := match w_add_c x y with
                     C0 n => WW w0 n
                    |C1 n => WW w1 n
                    end.
 Let ww_zdigits := w_add2 w_zdigits w_zdigits.
 
 Let ww_compare := 
  Eval lazy beta delta [ww_compare] in ww_compare w0 w_compare.

 Let ww_sub := 
 Eval lazy beta delta [ww_sub] in 
   ww_sub w0 wWW w_opp_c w_opp_carry w_sub_c w_opp w_sub w_sub_carry.

 Let ww_add_mul_div :=
 Eval lazy beta delta [ww_add_mul_div] in 
   ww_add_mul_div w0 wWW wW0 w0W 
              ww_compare w_add_mul_div 
              ww_sub w_zdigits low (w0W n).

 Let ww_lsl_n :=
   Eval lazy beta delta [ww_add_mul_div] in
    fun ww => ww_add_mul_div  ww W0.

 Let w_lsr_n w :=
     w_add_mul_div (w_sub w_zdigits n) w0 w.

 Open Scope Z_scope. 
 Notation "[| x |]" :=
   (@ZnZ.to_Z _ w_op x)  (at level 0, x at level 99).

Notation "[[ x ]]" :=
   (@ww_to_Z _ w_digits w_to_Z x)  (at level 0, x at level 99).

 Section Mod_spec.
 
   Variable m_op : mod_op.

   Record mod_spec : Prop := mk_mod_spec {
      succ_mod_spec     : 
                forall w t, [|w|]= t mod [|b|] ->
                          [|succ_mod m_op w|] = ([|w|] + 1) mod [|b|];
      add_mod_spec      :
            forall w1 w2 t1 t2, [|w1|]= t1 mod [|b|] -> [|w2|]= t2 mod [|b|] ->
                          [|add_mod m_op w1 w2|] = ([|w1|] + [|w2|]) mod [|b|];
      pred_mod_spec     :
                forall w t, [|w|]= t mod [|b|] ->
                          [|pred_mod m_op w|] = ([|w|] - 1) mod [|b|];
      sub_mod_spec      :
            forall w1 w2 t1 t2, [|w1|]= t1 mod [|b|] -> [|w2|]= t2 mod [|b|] ->
                          [|sub_mod m_op w1 w2|] = ([|w1|] - [|w2|]) mod [|b|];
      mul_mod_spec      :
            forall w1 w2 t1 t2, [|w1|]= t1 mod [|b|] -> [|w2|]= t2 mod [|b|] ->
                          [|mul_mod m_op w1 w2|] = ([|w1|] * [|w2|]) mod [|b|];
      square_mod_spec   :
                forall w t, [|w|]= t mod [|b|] ->
                          [|square_mod m_op w|] = ([|w|] * [|w|]) mod [|b|];
      power_mod_spec    :
              forall w t p, [|w|]= t mod [|b|] ->
                          [|power_mod m_op w p|] = (Zpower_pos [|w|] p) mod [|b|]
(*
      shift_spec        :
              forall w p, wf w -> 
                          [|shift m_op w p|] = ([|w|] / (Zpower_pos 2 p)) mod [|b|];
      trunc_spec        :
              forall w p, wf w ->
                          [|power_mod m_op w p|] = ([|w1|] mod (Zpower_pos 2 p)) mod [|b|]
*)
    }.

  End Mod_spec.

 Hypothesis b_pos: 1 < [|b|].
 Variable op_spec: ZnZ.Specs w_op.


 Lemma Zpower_n: 0 < 2 ^ [|n|].
 apply Zpower_gt_0; auto with zarith.
 case (ZnZ.spec_to_Z n); auto with zarith.
 Qed.

 Hint Resolve Zpower_n Zmult_lt_0_compat Zpower_gt_0.

 Variable m_op : mod_op.

 Hint Rewrite 
    ZnZ.spec_0
    ZnZ.spec_1
    ZnZ.spec_m1
    ZnZ.spec_WW
    ZnZ.spec_opp_c
    ZnZ.spec_opp	
    ZnZ.spec_opp_carry 
    ZnZ.spec_succ_c
    ZnZ.spec_add_c
    ZnZ.spec_add_carry_c 
    ZnZ.spec_add
    ZnZ.spec_pred_c
    ZnZ.spec_sub_c
    ZnZ.spec_sub_carry_c
    ZnZ.spec_sub
    ZnZ.spec_mul_c
    ZnZ.spec_mul
    : w_rewrite.

 Let _succ_mod x :=
  let res :=w_succ x in
  match w_compare res b with 
  | Lt => res
  | _ => w0
  end.

 Let split x := 
  match x with
  | W0 => (w0,w0)
  | WW h l => (h,l)
  end. 

 Let _w0_is_0: [|w0|] = 0.
 unfold ZnZ.to_Z; rewrite <- ZnZ.spec_0; auto.
 Qed.

 Let _w1_is_1: [|w1|] = 1.
 unfold ZnZ.to_Z; rewrite <-ZnZ.spec_1; simpl; auto.
 Qed.

 Theorem Zmod_plus_one: forall a1 b1, 0 < b1 -> (a1 + b1) mod b1 = a1 mod b1.
 intros a1 b1 H; rewrite Zplus_mod; auto with zarith.
 rewrite Z_mod_same; try rewrite Zplus_0_r; auto with zarith.
 apply Zmod_mod; auto.
 Qed.

 Theorem Zmod_minus_one: forall a1 b1, 0 < b1 -> (a1 - b1) mod b1 = a1 mod b1.
 intros a1 b1 H; rewrite Zminus_mod; auto with zarith.
 rewrite Z_mod_same; try rewrite Zminus_0_r; auto with zarith.
 apply Zmod_mod; auto.
 Qed.

 Lemma without_c_b: forall w2, [|w2|] < [|b|] -> 
    [|w_succ w2|] = [|w2|] + 1.
 intros w2 H.
 unfold w_succ;rewrite ZnZ.spec_succ.
 rewrite Zmod_small;auto.
 assert (HH := ZnZ.spec_to_Z w2).
 assert (HH' := ZnZ.spec_to_Z b);auto with zarith.
 Qed.

 Lemma _succ_mod_spec: forall w t, [|w|]= t mod [|b|] ->
    [|_succ_mod w|] = ([|w|] + 1) mod [|b|].
 intros w2 t H; unfold _succ_mod, w_compare; simpl.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t [|b|]); auto with zarith.
 rewrite ZnZ.spec_compare; case Zcompare_spec; intros H1;
 match goal with H: context[w_succ _] |- _ =>
   generalize H; clear H; rewrite (without_c_b _ F); intros H1;
   auto with zarith
 end.
 rewrite H1, Z_mod_same, _w0_is_0; auto with zarith.
 rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 Qed.

 Let _add_mod x y :=
  match w_add_c x y with
  | C0 z =>
    match w_compare z b with
    | Lt => z
    | Eq => w0
    | Gt => w_sub z b
    end
  | C1 z => w_add mb z
  end.

 Lemma _add_mod_correct: forall w1 w2, [|w1|] + [|w2|] < 2 * [|b|] ->
     [|_add_mod w1 w2|] = ([|w1|] + [|w2|]) mod [|b|].
 intros w2 w3; unfold _add_mod, w_compare, w_add_c; intros H.
 match goal with |- context[ZnZ.add_c ?x ?y] =>
   generalize (ZnZ.spec_add_c x y); unfold interp_carry;
   case (ZnZ.add_c x y); autorewrite with w_rewrite
 end; auto with zarith.
 intros w4 H2.
 rewrite ZnZ.spec_compare; case Zcompare_spec; intros H1;
 match goal with H: context[b] |- _ =>
   generalize H; clear H; intros H1; rewrite <-H2;
   auto with zarith
 end.
 rewrite H1, Z_mod_same; auto with zarith.
 rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z w4); auto with zarith.
 assert (F1: 0 < [|w4|] - [|b|]); auto with zarith.
 assert (F2: [|w4|] < [|b|] + [|b|]); auto with zarith.
 autorewrite with w_rewrite; auto.
 rewrite (fun x y => Zmod_small (x - y)); auto with zarith.
 rewrite <- (Zmod_minus_one [|w4|]); auto with zarith.
 apply sym_equal; apply Zmod_small; auto with zarith.
 split; auto with zarith.
 apply Zlt_trans with [|b|]; auto with zarith.
 case (ZnZ.spec_to_Z b); unfold base; auto with zarith.
 rewrite Zmult_1_l; intros w4 H2; rewrite <- H2.
 unfold mb, w_add; rewrite ZnZ.spec_add; auto with zarith.
 assert (F1: [|w4|] < [|b|]).
 assert (F2: base (ZnZ.digits w_op) + [|w4|] < base (ZnZ.digits w_op) + [|b|]);
   auto with zarith.
 rewrite H2.
 apply Zlt_trans with ([|b|] +[|b|]); auto with zarith.
 apply Zplus_lt_compat_r; auto with zarith.
 case (ZnZ.spec_to_Z b); auto with zarith.
 assert (F2: [|b|] < base (ZnZ.digits w_op) + [|w4|]); auto with zarith.
 apply Zlt_le_trans with (base (ZnZ.digits w_op)); auto with zarith.
 case (ZnZ.spec_to_Z b); auto with zarith.
 case (ZnZ.spec_to_Z w4); auto with zarith.
 assert (F3: base (ZnZ.digits w_op) + [|w4|] < [|b|] + [|b|]); auto with zarith.
 rewrite <- (fun x => Zmod_minus_one (base x + [|w4|])); auto with zarith.
 rewrite (fun x y => Zmod_small (x - y)); auto with zarith.
 unfold w_opp;rewrite (ZnZ.spec_opp b).
 rewrite <- (fun x => Zmod_plus_one (-x)); auto with zarith.
 rewrite (Zmod_small (- [|b|] + base (ZnZ.digits w_op)));auto with zarith.
 2 : assert (HHH := ZnZ.spec_to_Z b);auto with zarith.
 repeat rewrite Zmod_small; auto with zarith.
 Qed.

 Lemma _add_mod_spec: forall w1 w2 t1 t2, [|w1|] = t1 mod [|b|] -> [|w2|] = t2 mod [|b|] ->
     [|_add_mod w1 w2|] = ([|w1|] + [|w2|]) mod [|b|].
 intros w2 w3 t1 t2 H H1.
 apply _add_mod_correct; auto with zarith.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t1 [|b|]); auto with zarith.
 assert (F': [|w3|] < [|b|]).
 case (Z_mod_lt t2 [|b|]); auto with zarith.
 assert (tmp: forall x, 2 * x = x + x); auto with zarith.
 Qed.

 Let _pred_mod x :=
  match w_compare w0 x with
  | Eq => bm1
  | _ => w_pred x
  end.

 Lemma _pred_mod_spec: forall w t, [|w|] = t mod [|b|] ->
   [|_pred_mod w|] = ([|w|] - 1) mod [|b|].
 intros w2 t H; unfold _pred_mod, w_compare, bm1; simpl.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t [|b|]); auto with zarith.
 rewrite ZnZ.spec_compare; case Zcompare_spec; intros H1;
 match goal with H: context[w2] |- _ =>
   generalize H; clear H; intros H1; autorewrite with w_rewrite;
   auto with zarith
 end; try rewrite _w0_is_0; try rewrite _w1_is_1; auto with zarith.
 rewrite <- H1, _w0_is_0; simpl.
 rewrite <- (Zmod_plus_one (-1)); auto with zarith.
 repeat rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z b); auto with zarith.
 unfold w_pred;rewrite ZnZ.spec_pred; auto.
 assert (HHH := ZnZ.spec_to_Z b);repeat rewrite Zmod_small;auto with
 zarith.
 intros;assert (HHH := ZnZ.spec_to_Z w2);auto with zarith.
 Qed.

 Let _sub_mod x y :=
  match w_sub_c x y with
  | C0 z => z
  | C1 z => w_add z b
  end.

 Lemma _sub_mod_spec: forall w1 w2 t1 t2, [|w1|] = t1 mod [|b|] -> [|w2|] = t2 mod [|b|] ->
   [|_sub_mod w1 w2|] = ([|w1|] - [|w2|]) mod [|b|].
 intros w2 w3 t1 t2; unfold _sub_mod, w_compare, w_sub_c; intros H H1.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t1 [|b|]); auto with zarith.
 assert (F': [|w3|] < [|b|]).
 case (Z_mod_lt t2 [|b|]); auto with zarith.
 match goal with |- context[ZnZ.sub_c ?x ?y] =>
   generalize (ZnZ.spec_sub_c x y); unfold interp_carry;
   case (ZnZ.sub_c x y); autorewrite with w_rewrite
 end; auto with zarith.
 intros w4 H2.
 rewrite Zmod_small; auto with zarith.
 split; auto with zarith.
 rewrite <- H2; case (ZnZ.spec_to_Z w4); auto with zarith.
 apply Zle_lt_trans with [|w2|]; auto with zarith.
 case (ZnZ.spec_to_Z w3); auto with zarith.
 intros w4 H2; rewrite <- H2.
 unfold w_add; rewrite ZnZ.spec_add; auto with zarith.
 case (ZnZ.spec_to_Z w4); intros F1 F2.
 assert (F3: 0 <= - 1 *  base (ZnZ.digits w_op) + [|w4|] + [|b|]); auto with zarith.
 rewrite H2.
 case (ZnZ.spec_to_Z w3); case (ZnZ.spec_to_Z w2); auto with zarith.
 rewrite <- (fun x => Zmod_minus_one ([|w4|] + x)); auto with zarith.
 rewrite <- (fun x y => Zmod_plus_one (-y + x)); auto with zarith.
 repeat rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z b); auto with zarith.
 Qed.

 Let _mul_mod x y :=
  let xy := w_mul_c x y in
  match ww_compare xy wwb with
  | Lt => snd (split xy)
  | Eq => w0
  | Gt => 
    let xy2n := ww_lsl_n xy in
    let (h,l) := split xy2n in
    let (q,r) := w_div21 h l b2n in
    w_lsr_n r 
  end.

 Theorem high_zero:forall x, [[x]] < base w_digits -> [|fst (split x)|] = 0.
  intros x; case x; simpl; auto.
 intros xh xl H; case (Zle_lt_or_eq 0 [|xh|]); auto with zarith.
 case (ZnZ.spec_to_Z xh); auto with zarith.
 intros H1; contradict H; apply Zle_not_lt.
 assert (HHHH := wB_pos w_digits).
 unfold w_to_Z.
 match goal with |- ?X <= ?Y + ?Z =>
  pattern X at 1; rewrite <- (Zmult_1_l X); auto with zarith;
  apply Zle_trans with Y; auto with zarith
 end.
 case (ZnZ.spec_to_Z xl); auto with zarith.
 Qed.

 Theorem n_spec: base (ZnZ.digits w_op) / 2 <= 2 ^ [|n|] * [|b|] 
                        < base (ZnZ.digits w_op).
 unfold n, w_head0; apply (ZnZ.spec_head0); auto with zarith.
 Qed. 

 Theorem b2n_spec: [|b2n|] = 2 ^ [|n|] * [|b|].
 unfold b2n, w_add_mul_div; case n_spec; intros Hp Hp1.
 assert (F1: [|n|] < Zpos (ZnZ.digits w_op)).
 case (Zle_or_lt (Zpos (ZnZ.digits w_op)) [|n|]); auto with zarith.
 intros H1; contradict Hp1; apply Zle_not_lt; unfold base.
 apply Zle_trans with (2 ^ [|n|] * 1); auto with zarith.
 rewrite Zmult_1_r; apply Zpower_le_monotone; auto with zarith.
 rewrite ZnZ.spec_add_mul_div; auto with zarith.
 rewrite _w0_is_0; rewrite Zdiv_0_l; auto with zarith.
 rewrite Zplus_0_r; rewrite Zmult_comm; apply Zmod_small; auto with zarith.
 Qed.

 Theorem ww_lsl_n_spec: forall w, [[w]] < [|b|] * [|b|] ->
   [[ww_lsl_n w]] = 2 ^ [|n|] * [[w]].
 intros w2 H; unfold ww_lsl_n.
 case n_spec; intros Hp Hp1.
 assert (F0: forall x, 2 * x = x + x); auto with zarith.
 assert (F1: [|n|] < Zpos (ZnZ.digits w_op)).
 case (Zle_or_lt (Zpos (ZnZ.digits w_op)) [|n|]); auto.
 intros H1; contradict Hp1; apply Zle_not_lt; unfold base.
 apply Zle_trans with (2 ^ [|n|] * 1); auto with zarith.
 rewrite Zmult_1_r; apply Zpower_le_monotone; auto with zarith.
 assert (F2: [|n|] < Zpos (xO (ZnZ.digits w_op))).
 rewrite (Zpos_xO (ZnZ.digits w_op)); rewrite F0; auto with zarith.
 pattern [|n|]; rewrite <- Zplus_0_r; auto with zarith.
 apply Zplus_lt_compat; auto with zarith.
 change 
  ([[DoubleLift.ww_add_mul_div w0 wWW wW0 w0W 
              ww_compare w_add_mul_div 
              ww_sub w_zdigits low (w0W n) w2 W0]] = 2 ^ [|n|] * [[w2]]).
 rewrite (DoubleLift.spec_ww_add_mul_div ); auto with zarith.
 2: apply ZnZ.spec_to_Z; auto.
 2: refine (spec_ww_to_Z _ _ _); auto.
 2: apply ZnZ.spec_to_Z; auto.
 2: apply ZnZ.spec_WW; auto.
 2: apply ZnZ.spec_WO; auto.
 2: apply ZnZ.spec_OW; auto.
 2: refine (spec_ww_compare _ _ _ _ _ _ _); auto.
 2: apply ZnZ.spec_to_Z; auto.
 2: apply ZnZ.spec_compare; auto.
 2: apply ZnZ.spec_add_mul_div; auto.
 2: refine (spec_ww_sub _ _ _ _ _ _ _ _ _ _
                _ _ _ _ _ _ _ _ _ _ _); auto.
 2: apply ZnZ.spec_to_Z; auto.
 2: apply ZnZ.spec_WW; auto.
 2: apply ZnZ.spec_opp_c; auto.
 2: apply ZnZ.spec_opp; auto.
 2: apply ZnZ.spec_opp_carry; auto.
 2: apply ZnZ.spec_sub_c; auto.
 2: apply ZnZ.spec_sub; auto.
 2: apply ZnZ.spec_sub_carry; auto.
 2: apply ZnZ.spec_zdigits; auto.
 replace ([[w0W n]]) with  [|n|]. 
 change [[W0]] with 0. rewrite Zdiv_0_l; auto with zarith.
 rewrite Zplus_0_r; rewrite Zmod_small; auto with zarith.
 split; auto with zarith.
 case spec_ww_to_Z with (w_digits := w_digits) (w_to_Z := w_to_Z) (x:=w2); auto with zarith. 
 apply ZnZ.spec_to_Z; auto.
 apply Zlt_trans with ([|b|] * [|b|] * 2 ^ [|n|]); auto with zarith.
 apply Zmult_lt_compat_r; auto with zarith.
 rewrite <- Zmult_assoc.
 unfold base; unfold base in Hp.
 unfold ww_digits,w_digits;rewrite (Zpos_xO (ZnZ.digits w_op)); rewrite F0; auto with zarith.
 rewrite Zpower_exp; auto with zarith.
 apply Zmult_lt_compat; auto with zarith.
 case (ZnZ.spec_to_Z b); auto with zarith.
 split; auto with zarith.
 rewrite Zmult_comm; auto with zarith.
 unfold w_digits;auto with zarith.
 generalize (ZnZ.spec_OW n).
 unfold ww_to_Z, w_digits; auto.
 intros x; case x; simpl.
 unfold w_to_Z, w_digits, w0; rewrite ZnZ.spec_0; auto.
 intros w3 w4; rewrite Zplus_comm.
 rewrite Z_mod_plus; auto with zarith.
 rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z w4); auto with zarith.
 unfold base; auto with zarith.  
 unfold ww_to_Z, w_digits, w_to_Z, w0W; auto.
 rewrite ZnZ.spec_OW; auto with zarith.
 Qed.

 Theorem w_lsr_n_spec: forall w, [|w|] < 2 ^ [|n|] *  [|b|]->
   [|w_lsr_n w|] = [|w|] / 2 ^ [|n|].
 intros w2 H.
 case (ZnZ.spec_to_Z w2); intros U1 U2.
 unfold w_lsr_n, w_add_mul_div.
 rewrite ZnZ.spec_add_mul_div; auto with zarith.
 rewrite _w0_is_0; rewrite Zmult_0_l; auto with zarith.
 rewrite Zplus_0_l.
 autorewrite with w_rewrite; auto.
 rewrite (fun x y => Zmod_small (x - y)); auto with zarith.
 unfold w_zdigits; rewrite ZnZ.spec_zdigits; auto.
 assert (tmp: forall p q, p - (p - q) = q); intros; try ring;
  rewrite tmp; clear tmp; auto.
 rewrite Zmod_small; auto with zarith.
 split; auto with zarith.
 apply Zle_lt_trans with (2 := U2); auto with zarith.
 apply Zdiv_le_upper_bound; auto with zarith.
 apply Zle_trans with ([|w2|] * (2 ^ 0)); auto with zarith.
 simpl Zpower; rewrite Zmult_1_r; auto with zarith.
 apply Zmult_le_compat_l; auto with zarith.
 apply Zpower_le_monotone; auto with zarith.
 case (ZnZ.spec_to_Z n); auto with zarith.
 unfold n.
 assert (HH: 0 < [|b|]); auto with zarith.
 split.
   case (Zle_or_lt [|w_head0 b|] [|w_zdigits|]); auto with zarith.
   unfold w_zdigits; rewrite ZnZ.spec_zdigits; auto; intros H1.
   case (ZnZ.spec_head0 b HH); intros _ H2; contradict H2.
   apply Zle_not_lt; unfold base.
   apply Zle_trans with (2^[|ZnZ.head0 b|] * 1); auto with zarith.
   rewrite Zmult_1_r; apply Zpower_le_monotone; auto with zarith.
 unfold w_zdigits; rewrite ZnZ.spec_zdigits; auto.
 apply Zle_lt_trans with (Zpos (ZnZ.digits w_op)); auto with zarith.
    case (ZnZ.spec_to_Z (w_head0 b)); auto with zarith.
 unfold base; apply Zpower2_lt_lin; auto with zarith.
 autorewrite with w_rewrite; auto.
 rewrite Zmod_small; auto with zarith.
 unfold w_zdigits; rewrite ZnZ.spec_zdigits; auto with zarith.
 case (ZnZ.spec_to_Z n); auto with zarith.
 unfold w_zdigits; rewrite ZnZ.spec_zdigits; auto.
 split; auto with zarith.
 case (Zle_or_lt [|n|] (Zpos (ZnZ.digits w_op))); auto with zarith; intros H1.
 case (ZnZ.spec_head0 b); auto with zarith; intros _ H2.
 contradict H2; apply Zle_not_lt; auto with zarith.
 unfold base; apply Zle_trans with (2 ^ [|ZnZ.head0 b|] * 1);
   auto with zarith.
 rewrite Zmult_1_r; unfold base; apply Zpower_le_monotone; auto with zarith.
 apply Zle_lt_trans with (Zpos (ZnZ.digits w_op)); auto with zarith.
 case (ZnZ.spec_to_Z n); auto with zarith.
 unfold base; apply Zpower2_lt_lin; auto with zarith.
 Qed.

 Lemma split_correct: forall x, let (xh, xl) := split x in [[WW xh xl]] = [[x]].
 intros x; case x; simpl; unfold w0, w_to_Z;try rewrite ZnZ.spec_0; auto with zarith.
 Qed. 

 Lemma _mul_mod_spec: forall w1 w2 t1 t2, [|w1|] = t1 mod [|b|] -> [|w2|] = t2 mod [|b|] ->
   [|_mul_mod w1 w2|] = ([|w1|] * [|w2|]) mod [|b|].
 intros w2 w3 t1 t2 H H1; unfold _mul_mod, wwb.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t1 [|b|]); auto with zarith.
 assert (F': [|w3|] < [|b|]).
 case (Z_mod_lt t2 [|b|]); auto with zarith.
 match goal with |- context[ww_compare ?x ?y] =>
   change (ww_compare x y) with (DoubleBase.ww_compare w0 w_compare x y)
 end.
 rewrite (@spec_ww_compare w w0 w_digits w_to_Z w_compare
    ZnZ.spec_0 ZnZ.spec_to_Z ZnZ.spec_compare 
    (w_mul_c w2 w3) (WW w0 b)); case Zcompare_spec; intros H2;
 match goal with H: context[w_mul_c] |- _ =>
   generalize H; clear H
 end; try rewrite _w0_is_0; try rewrite !_w1_is_1; auto with zarith.
 unfold w_mul_c, ww_to_Z, w_to_Z, w_digits; rewrite ZnZ.spec_mul_c; auto with zarith.
 simpl; rewrite _w0_is_0, Zmult_0_l, Zplus_0_l.
 intros H2; rewrite H2; simpl.
 rewrite Z_mod_same; auto with zarith.
 generalize (high_zero (w_mul_c w2 w3)).
 unfold w_mul_c; generalize (ZnZ.spec_mul_c w2 w3); 
  case (ZnZ.mul_c w2 w3); simpl; auto with zarith.
 intros H3 _  _; rewrite <- H3; autorewrite with w_rewrite; auto.
(*  rewrite Zmod_small; auto with zarith. *)
 intros w4 w5.
 change (w_to_Z w0) with [|w0|]; rewrite _w0_is_0.
 change (w_to_Z w4) with [|w4|].
 change (w_to_Z w5) with [|w5|].
 simpl.
 intros H2 H3 H4.
 assert (E1: [|w4|] = 0).
 apply H3; auto with zarith.
 apply Zlt_trans with (1 := H4).
 case (ZnZ.spec_to_Z b); auto with zarith.
 generalize H4 H2; rewrite E1; rewrite Zmult_0_l; rewrite Zplus_0_l;
   clear H4 H2; intros H4 H2.
 rewrite <- H2; rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z w5); auto with zarith.
 intros H2.
 match goal with |- context[split ?x] =>
 generalize (split_correct x); 
  case (split x); auto with zarith
 end.
 assert (F1: [[w_mul_c w2 w3]] < [|b|] * [|b|]).
 unfold w_to_Z, w_mul_c, ww_to_Z,w_digits;
   rewrite ZnZ.spec_mul_c; auto with zarith.
 apply Zmult_lt_compat; auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 case (ZnZ.spec_to_Z w3); auto with zarith.
 intros w4 w5; rewrite ww_lsl_n_spec; auto with zarith.
 intros H3.
 unfold w_div21; match goal with |- context[ZnZ.div21 ?y ?z ?t] =>
   generalize (ZnZ.spec_div21 y z t);
   case (ZnZ.div21 y z t)
 end.
 rewrite b2n_spec; case (n_spec); auto.
 intros H4 H5 w6 w7 H6.
 case H6; auto with zarith.
 case (Zle_or_lt (2 ^ [|n|] * [|b|]) [|w4|]); auto; intros H7.
 match type of H3 with ?X = ?Y =>
    absurd (Y < X)
 end.
 apply Zle_not_lt; rewrite H3; auto with zarith.
 simpl ww_to_Z.
 match goal with |- ?X < ?Y + _ =>
    apply Zlt_le_trans with Y; auto with zarith
 end.
 apply Zlt_trans with (2 ^ [|n|] * ([|b|] * [|b|])); 
   auto with zarith.
 apply Zmult_lt_compat_l; auto with zarith.
 rewrite Zmult_assoc.
 apply Zmult_lt_compat2; auto with zarith.
 case (ZnZ.spec_to_Z b); auto with zarith.
 case (ZnZ.spec_to_Z w5); unfold w_to_Z;auto with zarith.
 clear H6; intros H7 H8.
 rewrite w_lsr_n_spec; auto with zarith.
 rewrite <- (Z_div_mult ([|w2|] * [|w3|]) (2 ^ [|n|]));
  auto with zarith; rewrite Zmult_comm.
 rewrite <- ZnZ.spec_mul_c; auto with zarith.
 unfold w_mul_c in H3; unfold ww_to_Z in H3;simpl H3.
 unfold w_digits,w_to_Z in H3. rewrite <- H3; simpl.
 rewrite H7; rewrite (fun x => Zmult_comm (2 ^ x));
   rewrite Zmult_assoc; rewrite  BigNumPrelude.Z_div_plus_l; auto with zarith.
 rewrite Zplus_mod; auto with zarith.
 rewrite Z_mod_mult; auto with zarith.
 rewrite Zplus_0_l; auto with zarith.
 rewrite Zmod_mod; auto with zarith.
 rewrite Zmod_small; auto with zarith.
 split; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 rewrite Zmult_comm; auto with zarith.
 Qed.

 Let _square_mod x :=
  let x2 := w_square_c x in
  match ww_compare x2 wwb with
  | Lt => snd (split x2)
  | Eq => w0
  | Gt =>
    let x2_2n := ww_lsl_n x2 in
    let (h,l) := split x2_2n in
    let (q,r) := w_div21 h l b2n in
    w_lsr_n r
  end.

 Lemma _square_mod_spec: forall w t, [|w|] = t mod [|b|] ->
    [|_square_mod w|] = ([|w|] * [|w|]) mod [|b|].
 intros w2 t2 H; unfold _square_mod, wwb.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t2 [|b|]); auto with zarith.
 match goal with |- context[ww_compare ?x ?y] =>
   change (ww_compare x y) with (DoubleBase.ww_compare w0 w_compare x y)
 end.
 rewrite (@spec_ww_compare w w0 w_digits w_to_Z w_compare
    ZnZ.spec_0 ZnZ.spec_to_Z ZnZ.spec_compare); case Zcompare_spec;
   intros H2;
 match goal with H: context[w_square_c] |- _ =>
   generalize H; clear H
 end; autorewrite with w_rewrite; try rewrite _w0_is_0; try rewrite !_w1_is_1; auto with zarith.
 unfold w_square_c, ww_to_Z, w_to_Z, w_digits; rewrite ZnZ.spec_square_c; auto with zarith.
 intros H2;rewrite H2; simpl.
 rewrite _w0_is_0; simpl.
 rewrite Z_mod_same; auto with zarith.
 generalize (high_zero (w_square_c w2)).
 unfold w_square_c; generalize (ZnZ.spec_square_c w2); 
  case (ZnZ.square_c w2); simpl; auto with zarith.
 intros H3 _  _; rewrite <- H3; autorewrite with w_rewrite; auto.
 intros w4 w5.
 change (w_to_Z w0) with [|w0|]; rewrite _w0_is_0; simpl.
 change (w_to_Z w4) with [|w4|].
 change (w_to_Z w5) with [|w5|].
 intros H2 H3 H4.
 assert (E1: [|w4|] = 0).
 apply H3; auto with zarith.
 apply Zlt_trans with (1 := H4).
 case (ZnZ.spec_to_Z b); auto with zarith.
 generalize H4 H2; rewrite E1; rewrite Zmult_0_l; rewrite Zplus_0_l;
   clear H4 H2; intros H4 H2.
 rewrite <- H2; rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z w5); auto with zarith.
 intros H2.
 match goal with |- context[split ?x] =>
 generalize (split_correct x); 
  case (split x); auto with zarith
 end.
 assert (F1: [[w_square_c w2]] < [|b|] * [|b|]).
 unfold w_square_c, ww_to_Z, w_digits, w_to_Z.
 rewrite ZnZ.spec_square_c; auto with zarith.
 apply Zmult_lt_compat; auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 intros w4 w5; rewrite ww_lsl_n_spec; auto with zarith.
 intros H3.
 unfold w_div21; match goal with |- context[ZnZ.div21 ?y ?z ?t] =>
   generalize (ZnZ.spec_div21 y z t);
   case (ZnZ.div21 y z t)
 end.
 rewrite b2n_spec; case (n_spec); auto.
 intros H4 H5 w6 w7 H6.
 case H6; auto with zarith.
 case (Zle_or_lt (2 ^ [|n|] * [|b|]) [|w4|]); auto; intros H7.
 match type of H3 with ?X = ?Y =>
    absurd (Y < X)
 end.
 apply Zle_not_lt; rewrite H3; auto with zarith.
 simpl ww_to_Z.
 match goal with |- ?X < ?Y + _ =>
    apply Zlt_le_trans with Y; auto with zarith
 end.
 apply Zlt_trans with (2 ^ [|n|] * ([|b|] * [|b|])); 
   auto with zarith.
 apply Zmult_lt_compat_l; auto with zarith.
 rewrite Zmult_assoc.
 apply Zmult_lt_compat2; auto with zarith.
 case (ZnZ.spec_to_Z b); auto with zarith.
 unfold w_to_Z,w_digits;case (ZnZ.spec_to_Z w5); auto with zarith.
 clear H6; intros H7 H8.
 rewrite w_lsr_n_spec; auto with zarith.
 rewrite <- (Z_div_mult ([|w2|] * [|w2|]) (2 ^ [|n|]));
  auto with zarith; rewrite Zmult_comm.
 rewrite <- ZnZ.spec_square_c; auto with zarith.
 unfold w_square_c, ww_to_Z in H3;  unfold w_digits,w_to_Z in H3.
 rewrite <- H3; simpl.
 rewrite H7; rewrite (fun x => Zmult_comm (2 ^ x));
   rewrite Zmult_assoc; rewrite BigNumPrelude.Z_div_plus_l; auto with zarith.
 rewrite Zplus_mod; auto with zarith.
 rewrite Z_mod_mult; auto with zarith.
 rewrite Zplus_0_l; auto with zarith.
 rewrite Zmod_mod; auto with zarith.
 rewrite Zmod_small; auto with zarith.
 split; auto with zarith.
 apply Zdiv_lt_upper_bound; auto with zarith.
 rewrite Zmult_comm; auto with zarith.
 Qed.

 Let _power_mod :=
   fix pow_mod (x:w) (p:positive) {struct p} : w :=
     match p with
     | xH => x
     | xO p' =>
       let pow := pow_mod x p' in
       _square_mod pow
     | xI p' =>
       let pow := pow_mod x p' in
       _mul_mod (_square_mod pow) x
     end.

 Lemma _power_mod_spec: forall w t p, [|w|] = t mod [|b|] ->
   [|_power_mod w p|] = (Zpower_pos [|w|] p) mod [|b|].
 intros w2 t p; elim p; simpl; auto with zarith.
 intros p' Rec H. 
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t [|b|]); auto with zarith.
 replace (xI p') with (p' + p' + 1)%positive.
 repeat rewrite Zpower_pos_is_exp; auto with zarith.
 pose (t1 := [|_power_mod w2 p'|]).
 rewrite _mul_mod_spec with (t1 := t1 * t1)
                            (t2 := t); auto with zarith.
 rewrite _square_mod_spec with (t := Zpower_pos [|w2|] p'); auto with zarith.
 rewrite Rec; auto with zarith.
 assert (tmp: forall p, Zpower_pos p 1 = p); try (rewrite tmp; clear tmp).
 intros p1; unfold Zpower_pos; simpl; ring.
 rewrite <- Zmult_mod; auto with zarith.
 rewrite Zmult_mod; auto with zarith.
 rewrite Zmod_mod; auto with zarith.
 rewrite <- Zmult_mod; auto with zarith.
 simpl; unfold t1; apply _square_mod_spec with (t := Zpower_pos [|w2|] p'); auto with zarith.
 rewrite xI_succ_xO; rewrite <- Pplus_diag.
 rewrite Pplus_one_succ_r; auto.
 intros p' Rec H. 
 replace (xO p') with (p' + p')%positive.
 repeat rewrite Zpower_pos_is_exp; auto with zarith.
 rewrite _square_mod_spec with (t := Zpower_pos [|w2|] p'); auto with zarith.
 rewrite Rec; auto with zarith.
 rewrite <- Zmult_mod; auto with zarith.
 rewrite <- Pplus_diag; auto.
 intros H.
 assert (tmp: forall p, Zpower_pos p 1 = p); try (rewrite tmp; clear tmp).
 intros p1; unfold Zpower_pos; simpl; ring.
 rewrite Zmod_small; auto with zarith.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t [|b|]); auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 Qed.

 Definition make_mod_op := 
   mk_mod_op
     _succ_mod _add_mod 
     _pred_mod _sub_mod
     _mul_mod _square_mod _power_mod.

  Definition make_mod_spec: mod_spec make_mod_op.
  apply mk_mod_spec.
  exact _succ_mod_spec.
  exact _add_mod_spec.
  exact _pred_mod_spec.
  exact _sub_mod_spec.
  exact _mul_mod_spec.
  exact _square_mod_spec.
  exact _power_mod_spec.
  Defined.

(*********** Mersenne special **********)
  
 Variable p: positive.
 Variable zp: w.

 Hypothesis zp_b: [|zp|] = Zpos p.
 Hypothesis p_lt_w_digits: Zpos p <= Zpos w_digits.

 Let p1 := Pminus (xO w_digits) p.

 Theorem p_p1: Zpos p + Zpos p1 = Zpos (xO w_digits).
 unfold p1.
 rewrite Zpos_minus; auto with zarith.
 rewrite Zmax_right; auto with zarith.
 rewrite Zpos_xO; auto with zarith.
 assert (0 < Zpos w_digits); auto with zarith.
 Qed.

 Let zp1 := ww_sub ww_zdigits (WW w0 zp).

 Let spec_add2: forall x y,
  [[w_add2 x y]] = [|x|] + [|y|].
  unfold w_add2.
  intros xh xl; generalize (ZnZ.spec_add_c xh xl).
  unfold w_add_c; case ZnZ.add_c; unfold interp_carry; simpl ww_to_Z.
    intros w2 Hw2; simpl; unfold w_to_Z; rewrite Hw2.
  unfold w0; rewrite ZnZ.spec_0; simpl; auto with zarith.
  intros w2; rewrite Zmult_1_l; simpl.
  unfold w_to_Z, w1; rewrite ZnZ.spec_1; auto with zarith.
  rewrite Zmult_1_l; auto.
 Qed.

 Let spec_ww_digits:
  [[ww_zdigits]] = Zpos (xO w_digits).
 Proof.
 unfold w_to_Z, ww_zdigits.
 rewrite spec_add2.
 unfold w_to_Z, w_zdigits, w_digits.
 rewrite ZnZ.spec_zdigits; auto.
 rewrite Zpos_xO; auto with zarith.
 Qed.

 Let spec_ww_to_Z := (spec_ww_to_Z _ _ ZnZ.spec_to_Z).
 Let spec_ww_compare := spec_ww_compare _ _ _ _ ZnZ.spec_0  
      ZnZ.spec_to_Z ZnZ.spec_compare.
 Let spec_ww_sub := 
         spec_ww_sub w0 zp wWW zp1 w_opp_c w_opp_carry
              w_sub_c w_opp w_sub w_sub_carry w_digits w_to_Z
             ZnZ.spec_0
             ZnZ.spec_to_Z
             ZnZ.spec_WW
             ZnZ.spec_opp_c
             ZnZ.spec_opp
             ZnZ.spec_opp_carry
             ZnZ.spec_sub_c
             ZnZ.spec_sub
             ZnZ.spec_sub_carry.

 Theorem zp1_b: [[zp1]] = Zpos p1.
 change ([[DoubleSub.ww_sub w0 wWW w_opp_c w_opp_carry w_sub_c w_opp w_sub
            w_sub_carry ww_zdigits (WW w0 zp)]] =
          Zpos p1).
 rewrite spec_ww_sub; auto with zarith.
 rewrite spec_ww_digits; simpl ww_to_Z.
 change (w_to_Z w0) with [|w0|].
 unfold w0; rewrite ZnZ.spec_0; autorewrite with rm10; auto.
 change (w_to_Z zp) with [|zp|].
 rewrite zp_b.
 rewrite Zmod_small; auto with zarith.
 rewrite <- p_p1; auto with zarith.
 unfold ww_digits; split; auto with zarith.
 rewrite <- p_p1; auto with zarith.
 assert (0 < Zpos p1); auto with zarith.
 apply Zle_lt_trans with (Zpos (xO w_digits)); auto with zarith.
 assert (0 < Zpos p); auto with zarith.
 unfold base; apply Zpower2_lt_lin; auto with zarith.
 Qed.

 Hypothesis p_b: [|b|] = 2 ^ (Zpos p) - 1.


 Let w_pos_mod := ZnZ.pos_mod.

 Let add_mul_div := 
   DoubleLift.ww_add_mul_div w0 wWW wW0 w0W 
              ww_compare w_add_mul_div 
              ww_sub w_zdigits low. 

 Let _mmul_mod x y :=
  let xy := w_mul_c x y in
  match xy with
    W0 => w0
  | WW xh xl =>
      let xl1 := w_pos_mod zp xl in
        match add_mul_div zp1 W0 xy with
          W0 => match w_compare xl1 b with
                | Lt => xl1
                | Eq => w0
                | Gt => w1
                end
        | WW _ xl2 => _add_mod xl1 xl2
        end
  end.

 Hint Unfold w_digits.

 Lemma WW_0: forall x y, [[WW x y]] = 0 -> [|x|] = 0 /\ [|y|] =0.
 intros x y; simpl; case (ZnZ.spec_to_Z x); intros H1 H2;
   case (ZnZ.spec_to_Z y); intros H3 H4 H5.
 case Zle_lt_or_eq with (1 := H1); clear H1; intros H1; auto with zarith.
 absurd (0 < [|x|] * base (ZnZ.digits w_op) + [|y|]); auto with zarith.
 unfold w_to_Z, w_digits in H5;auto with zarith.
 match goal with |- _ < ?X + _ =>
  apply Zlt_le_trans with X; auto with zarith
 end.
 case Zle_lt_or_eq with (1 := H3); clear H3; intros H3; auto with zarith.
 absurd (0 < [|x|] * base (ZnZ.digits w_op) + [|y|]); auto with zarith.
 unfold w_to_Z, w_digits in H5;auto with zarith.
 rewrite <- H1; rewrite Zmult_0_l; auto with zarith.
 Qed.

 Theorem WW0_is_0: [[W0]] = 0.
 simpl; auto.
 Qed.
  Hint Rewrite WW0_is_0: w_rewrite.

 Theorem mmul_aux0: Zpos (xO w_digits) - Zpos p1 = Zpos p.
 unfold w_digits.
 apply trans_equal with (Zpos p + Zpos p1 - Zpos p1); auto with zarith.
 rewrite p_p1; auto with zarith.
 Qed.

 Theorem mmul_aux1: 2 ^ Zpos w_digits = 
     2 ^ (Zpos w_digits - Zpos p) * 2 ^ Zpos p.
 rewrite <- Zpower_exp; auto with zarith.
 eq_tac; auto with zarith.
 Qed.

 Theorem mmul_aux2:forall x,
   x mod (2 ^ Zpos p - 1) = 
    ((x / 2 ^ Zpos p) + (x mod 2 ^ Zpos p)) mod (2 ^ Zpos p - 1).
 intros x; pattern x at 1; rewrite Z_div_mod_eq with (b := 2 ^ Zpos p); auto with zarith.
 match goal with |- (?X * ?Y + ?Z) mod (?X - 1) = ?T =>
  replace (X * Y + Z) with (Y * (X - 1) + (Y + Z)); try ring
 end.
 rewrite Zplus_mod; auto with zarith.
 rewrite Z_mod_mult; auto with zarith.
 rewrite Zplus_0_l.
 rewrite Zmod_mod; auto with zarith.
 Qed.

 Theorem mmul_aux3:forall xh xl,
   [[WW xh xl]] mod (2 ^ Zpos p) = [|xl|] mod (2 ^ Zpos p).
 intros xh xl; simpl ww_to_Z; unfold base.
 rewrite Zplus_mod; auto with zarith.
 generalize mmul_aux1; unfold w_digits; intros tmp; rewrite tmp;
   clear tmp. 
 rewrite Zmult_assoc.
 rewrite Z_mod_mult; auto with zarith.
 rewrite Zplus_0_l; apply Zmod_mod; auto with zarith.
 Qed.

 Let spec_low: forall x,
  [|low x|] = [[x]] mod base w_digits.
  intros x; case x; simpl low; auto with zarith.
  intros xh xl; simpl.
  rewrite Zplus_comm; rewrite Z_mod_plus; auto with zarith.
  rewrite Zmod_small; auto with zarith.
  case (ZnZ.spec_to_Z xl); auto with zarith.
  unfold base; auto with zarith.
 Qed.

 Theorem mmul_aux4:forall x,
  [[x]] < [|b|] * 2 ^  Zpos p ->
     match add_mul_div zp1 W0 x with
          W0 => 0
        | WW _ xl2 => [|xl2|]
     end = [[x]] / 2 ^ Zpos p.
 intros x Hx.
 assert (Hp: [[zp1]] <= Zpos (xO w_digits)); auto with zarith.
   rewrite zp1_b; rewrite <- p_p1; auto with zarith.
   assert (0 <= Zpos p); auto with zarith.
 generalize (@DoubleLift.spec_ww_add_mul_div w w0 wWW wW0 w0W
    ww_compare w_add_mul_div ww_sub w_digits w_zdigits low w_to_Z
    ZnZ.spec_0 ZnZ.spec_to_Z spec_ww_to_Z
    ZnZ.spec_WW ZnZ.spec_WO ZnZ.spec_OW
    spec_ww_compare ZnZ.spec_add_mul_div spec_ww_sub
    ZnZ.spec_zdigits spec_low W0 x zp1 Hp).
  unfold add_mul_div; 
    case DoubleLift.ww_add_mul_div; autorewrite with w_rewrite; auto.
 rewrite Zmult_0_l; rewrite Zplus_0_l.
 rewrite zp1_b.
 generalize mmul_aux0; unfold w_digits; intros tmp; rewrite tmp.
 rewrite Zmod_small; auto with zarith.
 split; auto with zarith.
 apply Z_div_pos; auto with zarith.
 case (spec_ww_to_Z x); auto with zarith.
 unfold base.
 apply Zdiv_lt_upper_bound; auto with zarith.
 rewrite <- Zpower_exp; auto with zarith.
 apply Zlt_le_trans with (base (ww_digits (ZnZ.digits w_op))); auto with zarith.
   case (spec_ww_to_Z x); auto with zarith.
 unfold base; apply Zpower_le_monotone; auto with zarith.
 split; auto with zarith.
 assert (0 < Zpos p); auto with zarith.
 intros w2 w3; rewrite Zmult_0_l; rewrite Zplus_0_l.
 rewrite zp1_b.
 generalize mmul_aux0; unfold w_digits; intros tmp; rewrite tmp;
  clear tmp.
 simpl ww_to_Z; rewrite Zmod_small; auto with zarith.
 intros H1; 
   generalize (high_zero (WW w2 w3)); unfold w_digits;intros tmp;
   simpl fst in tmp; simpl ww_to_Z in tmp;auto with zarith.
   unfold w_to_Z in *.
   rewrite tmp in H1; auto with zarith. clear tmp.
 simpl ww_to_Z; rewrite H1; apply Zdiv_lt_upper_bound; auto with zarith.
 unfold base; rewrite <- Zpower_exp; auto with zarith.
 apply Zlt_le_trans with (1 := Hx).
 apply Zle_trans with (2 ^ Zpos p * 2 ^ Zpos p).
 rewrite p_b; apply Zmult_le_compat_r; auto with zarith.
 rewrite <- Zpower_exp; auto with zarith.
 apply Zpower_le_monotone; auto with zarith.
 split; auto with zarith.
 apply Z_div_pos; auto with zarith.
 case (spec_ww_to_Z  x); auto with zarith.
 unfold base.
 apply Zdiv_lt_upper_bound; auto with zarith.
 rewrite <- Zpower_exp; auto with zarith.
 apply Zlt_le_trans with (base (ww_digits (ZnZ.digits w_op))); auto with zarith.
   case (spec_ww_to_Z x); auto with zarith.
 unfold base; apply Zpower_le_monotone; auto with zarith.
 split; auto with zarith.
 assert (0 < Zpos p); auto with zarith.
 Qed.

 Theorem mmul_aux5:forall xh xl, 
      [[WW xh xl]] < [|b|] * 2 ^  Zpos p ->
      let xl1 := w_pos_mod zp xl in
      let r := 
        match add_mul_div zp1 W0 (WW xh xl) with
          W0 => match w_compare xl1 b with
                | Lt => xl1
                | Eq => w0
                | Gt => w1
                end
        | WW _ xl2 => _add_mod xl1 xl2
        end  in
        [|r|] = [[WW xh xl]] mod [|b|].
 intros xh xl Hx xl1 r; unfold r; clear r.
 generalize (mmul_aux4 _ Hx).
 simpl ww_to_Z; rewrite p_b.
 rewrite mmul_aux2.
 assert (Hp: [[zp1]] <= Zpos (xO w_digits)); auto with zarith.
   rewrite zp1_b; rewrite <- p_p1; auto with zarith.
   assert (0 <= Zpos p); auto with zarith.
 generalize (@DoubleLift.spec_ww_add_mul_div w w0 wWW wW0 w0W
    ww_compare w_add_mul_div ww_sub w_digits w_zdigits low w_to_Z
    ZnZ.spec_0 ZnZ.spec_to_Z spec_ww_to_Z
    ZnZ.spec_WW ZnZ.spec_WO ZnZ.spec_OW
    spec_ww_compare ZnZ.spec_add_mul_div spec_ww_sub
    ZnZ.spec_zdigits spec_low W0 (WW xh xl) zp1 Hp).
  unfold add_mul_div; 
    case DoubleLift.ww_add_mul_div; autorewrite with w_rewrite; auto.
 rewrite Zmult_0_l; rewrite Zplus_0_l.
 rewrite zp1_b.
 generalize mmul_aux0; unfold w_digits; intros tmp; rewrite tmp; clear tmp.
 intros H1 H2.
 rewrite <- H2.
 rewrite Zplus_0_l.
 generalize mmul_aux3; simpl ww_to_Z; intros tmp; rewrite tmp; clear tmp;
   auto with zarith.
 unfold xl1; unfold w_pos_mod.
  rewrite <- p_b; rewrite <- zp_b. 
  rewrite <- ZnZ.spec_pos_mod; auto with zarith.
 unfold w_compare; rewrite ZnZ.spec_compare;
   case Zcompare_spec; intros Hc;
 match goal with H: context[b] |- _ =>
   generalize H; clear H
 end; try rewrite _w0_is_0.
 intros H3; rewrite H3.
 rewrite Z_mod_same; auto with zarith.
 intros H3; rewrite Zmod_small; auto with zarith.
 case (ZnZ.spec_to_Z (ZnZ.pos_mod zp xl)); unfold w_to_Z; auto with zarith.
 rewrite p_b; rewrite ZnZ.spec_pos_mod; auto with zarith.
 intros H3; assert (HH: [|xl|] mod 2 ^ Zpos p = 2 ^ Zpos p).
 apply Zle_antisym; auto with zarith.
 case (Z_mod_lt ([|xl|]) (2 ^ Zpos p)); auto with zarith.
 rewrite zp_b in H3; auto with zarith.
 rewrite zp_b; rewrite HH.
 rewrite <- Zmod_minus_one; auto with zarith.
 rewrite _w1_is_1; rewrite Zmod_small; auto with zarith.
 rewrite Zmult_0_l; rewrite Zplus_0_l.
 rewrite zp1_b.
 generalize mmul_aux0; unfold w_digits; intros tmp; rewrite tmp; clear tmp.
 intros w2 w3 H1 H2; rewrite <- H2.
 generalize mmul_aux3; simpl ww_to_Z; intros tmp; rewrite tmp; clear tmp;
   auto with zarith.
 rewrite <- p_b; rewrite <- zp_b. 
 rewrite <- ZnZ.spec_pos_mod; auto with zarith.
 unfold xl1; unfold w_pos_mod.
 rewrite Zplus_comm.
 apply _add_mod_correct; auto with zarith.
 assert (tmp: forall x, 2 * x = x + x); auto with zarith;
   rewrite tmp; apply Zplus_le_lt_compat; clear tmp; auto with zarith.
 rewrite ZnZ.spec_pos_mod; auto with zarith.
 rewrite p_b; case (Z_mod_lt [|xl|] (2 ^ Zpos p)); auto with zarith.
 rewrite zp_b; auto with zarith.
 rewrite H2; apply Zdiv_lt_upper_bound; auto with zarith.
 Qed.

 Lemma _mmul_mod_spec: forall w1 w2 t1 t2, [|w1|] = t1 mod [|b|] -> [|w2|] = t2 mod [|b|] ->
   [|_mmul_mod w1 w2|] = ([|w1|] * [|w2|]) mod [|b|].
 intros w2 w3 t1 t2; unfold _mmul_mod, w_mul_c; intros H H1.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t1 [|b|]); auto with zarith.
 assert (F': [|w3|] < [|b|]).
 case (Z_mod_lt t2 [|b|]); auto with zarith.
 match goal with |- context[ZnZ.mul_c ?x ?y] =>
   generalize (ZnZ.spec_mul_c x y); unfold interp_carry;
   case (ZnZ.mul_c x y); autorewrite with w_rewrite
 end; auto with zarith.
 simpl; intros H2; rewrite <- H2; rewrite Zmod_small;
  auto with zarith.
 intros w4 w5 H2.
 rewrite mmul_aux5; auto with zarith.
 rewrite <- H2; auto.
 unfold ww_to_Z,w_digits,w_to_Z; rewrite H2.
 apply Zmult_lt_compat; auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 case (ZnZ.spec_to_Z w3); auto with zarith.
 Qed.

 Let _msquare_mod x :=
  let xy := w_square_c x in
  match xy with
    W0 => w0
  | WW xh xl =>
      let xl1 := w_pos_mod zp xl in
        match add_mul_div zp1 W0 xy with
          W0 =>  match w_compare xl1 b with
                | Lt => xl1
                | Eq => w0
                | Gt => w1
                end         
        | WW _ xl2 => _add_mod xl1 xl2
        end
  end.

 Lemma _msquare_mod_spec: forall w1 t1, [|w1|] = t1 mod [|b|] -> 
   [|_msquare_mod w1|] = ([|w1|] * [|w1|]) mod [|b|].
 intros w2 t2; unfold _msquare_mod, w_square_c; intros H.
 assert (F: [|w2|] < [|b|]).
 case (Z_mod_lt t2 [|b|]); auto with zarith.
 match goal with |- context[ZnZ.square_c ?x] =>
   generalize (ZnZ.spec_square_c x); unfold interp_carry;
   case (ZnZ.square_c x); autorewrite with w_rewrite
 end; auto with zarith.
 simpl; intros H2; rewrite <- H2; rewrite Zmod_small;
  auto with zarith.
 intros w4 w5 H2.
 rewrite mmul_aux5; auto with zarith.
 unfold ww_to_Z, w_to_Z ,w_digits; rewrite <- H2; auto.
 unfold ww_to_Z,w_to_Z ,w_digits; rewrite H2.
 apply Zmult_lt_compat; auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 case (ZnZ.spec_to_Z w2); auto with zarith.
 Qed.

 Definition mmake_mod_op := 
   mk_mod_op
     _succ_mod _add_mod 
     _pred_mod _sub_mod
     _mmul_mod _msquare_mod _power_mod.

 Definition mmake_mod_spec: mod_spec mmake_mod_op.
  apply mk_mod_spec.
  exact _succ_mod_spec.
  exact _add_mod_spec.
  exact _pred_mod_spec.
  exact _sub_mod_spec.
  exact _mmul_mod_spec.
  exact _msquare_mod_spec.
  exact _power_mod_spec.
  Defined.
 
End Mod_op.
    

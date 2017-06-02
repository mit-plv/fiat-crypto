(** * Proving properties of for-loops via loop-invariants *)
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ForLoop.
Require Import Crypto.Util.ForLoop.Unrolling.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.UniquePose.
Require Import Crypto.Util.Notations.

Lemma repeat_function_ind {stateT} (P : nat -> stateT -> Prop)
      (body : nat -> stateT -> stateT)
      (count : nat) (st : stateT)
      (Pbefore : P count st)
      (Pbody : forall c st, c < count -> P (S c) st -> P c (body (S c) st))
  : P 0 (repeat_function body count st).
Proof.
  revert dependent st; revert dependent body; revert dependent P.
  induction count as [|? IHcount]; intros P body Pbody st Pbefore; [ exact Pbefore | ].
  { rewrite repeat_function_unroll1_end; apply Pbody; [ omega | ].
    apply (IHcount (fun c => P (S c))); auto with omega. }
Qed.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Section for_loop.
  Context (i0 finish : Z) (step : Z) {stateT} (initial : stateT) (body : Z -> stateT -> stateT)
          (P : Z -> stateT -> Prop)
          (Pbefore : P i0 initial)
          (Pbody : forall c st n, c = i0 + n * step -> i0 <= c < finish \/ finish < c <= i0 -> P c st -> P (c + step) (body c st))
          (Hgood : Z.sgn step = Z.sgn (finish - i0)).

  Let countZ := (Z.quot (finish - i0 + step - Z.sgn step) step).
  Let count := Z.to_nat countZ.
  Let of_nat_count c := (i0 + step * Z.of_nat (count - c)).
  Let nat_body := (fun c => body (of_nat_count c)).

  Local Arguments Z.mul !_ !_.
  Local Arguments Z.add !_ !_.
  Local Arguments Z.sub !_ !_.

  Local Lemma Hgood_complex : Z.sgn step = Z.sgn (finish - i0 + step - Z.sgn step).
  Proof using Hgood.
    clear -Hgood.
    revert Hgood.
    generalize dependent (finish - i0); intro z; intros.
    destruct step, z; simpl in * |- ; try (simpl; omega);
      repeat change (Z.sgn (Z.pos _)) with 1;
      repeat change (Z.sgn (Z.neg _)) with (-1);
      symmetry;
      [ apply Z.sgn_pos_iff | apply Z.sgn_neg_iff ];
      lia.
  Qed.

  Local Lemma Hcount_nonneg : 0 <= countZ.
  Proof using Hgood.
    apply Z.quot_nonneg_same_sgn.
    symmetry; apply Hgood_complex.
  Qed.

  Lemma for_loop_ind
    : P (finish - Z.sgn (finish - i0 + step - Z.sgn step) * (Z.abs (finish - i0 + step - Z.sgn step) mod Z.abs step) + step - Z.sgn step)
        (for_loop i0 finish step initial body).
  Proof using Pbody Pbefore Hgood.
    destruct (Z_zerop step).
    { subst; unfold for_loop; simpl in *.
      rewrite Z.quot_div_full; simpl.
      symmetry in Hgood; rewrite Z.sgn_null_iff in Hgood.
      assert (finish = i0) by omega; subst.
      simpl; autorewrite with zsimplify_const; simpl; auto. }
    assert (Hsgn_step : Z.sgn step <> 0) by (rewrite Z.sgn_null_iff; auto).
    assert (Hsgn : Z.sgn ((finish - i0 + step - Z.sgn step) / step) = Z.sgn ((finish - i0 + step - Z.sgn step) / step) * Z.sgn (finish - i0 + step - Z.sgn step) * Z.sgn step)
           by (rewrite <- Hgood_complex, <- Z.mul_assoc, <- Z.sgn_mul, (Z.sgn_pos (_ * _)) by nia; omega).
    assert (Hfis_div : 0 <= (finish - i0 + step - Z.sgn step) / step)
      by (apply Z.sgn_nonneg; rewrite Hsgn; apply Zdiv_sgn).
    clear Hsgn.
    let rhs := match goal with |- ?P ?rhs _ => rhs end in
    assert (Heq : i0 + step * Z.of_nat count = rhs).
    { unfold count, countZ.
      rewrite Z.mod_eq by (rewrite Z.abs_0_iff; assumption).
      rewrite Z.quot_div_full, <- !Z.sgn_abs, <- !Hgood_complex, !Zdiv_mult_cancel_r, !Z.mul_sub_distr_l by auto.
      rewrite <- !Z.sgn_mul, !(Z.mul_comm _ (Z.sgn _)), !(Z.mul_assoc (Z.sgn _) _), <- Z.sgn_mul, Z.sgn_pos, !Z.mul_1_l by nia.
      repeat rewrite ?Z.sub_add_distr, ?Z.sub_sub_distr; rewrite Z.sub_diag.
      autorewrite with zsimplify_const.
      rewrite Z2Nat.id by omega.
      omega. }
    rewrite <- Heq; clear Heq.
    unfold for_loop.
    generalize (@repeat_function_ind stateT (fun c => P (of_nat_count c)) nat_body count initial);
      cbv beta in *.
    unfold of_nat_count in *; cbv beta in *.
    rewrite Nat.sub_diag, !Nat.sub_0_r.
    autorewrite with zsimplify_const.
    intro H; specialize (H Pbefore).
    destruct (Z_dec' i0 finish) as [ Hs | Hs].
    { apply H; clear H Pbefore.
      { intros c st Hc.
        assert (Hclt : 0 < Z.of_nat (count - c)) by (apply (inj_lt 0); omega).
        intro H'; specialize (fun pf' n pf => Pbody _ _ n pf pf' H').
        move Pbody at bottom.
        { let T := match type of Pbody with ?T -> _ => T end in
          let H := fresh in
          cut T; [ intro H; specialize (Pbody H) | ].
          { revert Pbody.
            subst nat_body; cbv beta.
            rewrite Nat.sub_succ_r, Nat2Z.inj_pred by omega.
            rewrite <- Z.sub_1_r, Z.mul_sub_distr_l, Z.mul_1_r.
            rewrite <- !Z.add_assoc, !Z.sub_add in *.
            refine (fun p => p (Z.of_nat (count - c) - 1) _).
            lia. }
          { destruct Hs; [ left | right ].
            { assert (Hstep : 0 < step)
                by (rewrite <- Z.sgn_pos_iff, Hgood, Z.sgn_pos_iff; omega).
              assert (0 < Z.of_nat (S c)) by (apply (inj_lt 0); omega).
              assert (0 <= (finish - i0 + step - Z.sgn step) mod step) by auto with zarith.
              assert (0 < step <= step * Z.of_nat (S c)) by nia.
              split; [ nia | ].
              rewrite Nat2Z.inj_sub, Z.mul_sub_distr_l by omega.
              unfold count.
              rewrite Z2Nat.id by auto using Hcount_nonneg.
              unfold countZ.
              rewrite Z.mul_quot_eq_full by auto.
              rewrite <- !Hgood_complex, Z.abs_sgn.
              rewrite !Z.add_sub_assoc, !Z.add_assoc, Zplus_minus.
              rewrite Z.sgn_pos in * by omega.
              omega. }
            { assert (Hstep : step < 0)
                by (rewrite <- Z.sgn_neg_iff, Hgood, Z.sgn_neg_iff; omega).
              assert (Hcsc0 : 0 <= Z.of_nat (count - S c)) by auto with zarith.
              assert (Hsc0 : 0 < Z.of_nat (S c)) by lia.
              assert (step * Z.of_nat (count - S c) <= 0) by (clear -Hcsc0 Hstep; nia).
              assert (step * Z.of_nat (S c) <= step < 0) by (clear -Hsc0 Hstep; nia).
              assert (finish - i0 < 0)
                by (rewrite <- Z.sgn_neg_iff, <- Hgood, Z.sgn_neg_iff; omega).
              assert (finish - i0 + step - Z.sgn step < 0)
                by (rewrite <- Z.sgn_neg_iff, <- Hgood_complex, Z.sgn_neg_iff; omega).
              assert ((finish - i0 + step - Z.sgn step) mod step <= 0) by (apply Z_mod_neg; auto with zarith).
              split; [ | nia ].
              rewrite Nat2Z.inj_sub, Z.mul_sub_distr_l by omega.
              unfold count.
              rewrite Z2Nat.id by auto using Hcount_nonneg.
              unfold countZ.
              rewrite Z.mul_quot_eq_full by auto.
              rewrite <- !Hgood_complex, Z.abs_sgn.
              rewrite Z.sgn_neg in * by omega.
              omega. } } } } }
    { subst.
      subst count nat_body countZ.
      repeat first [ assumption
                   | rewrite Z.sub_diag
                   | progress autorewrite with zsimplify_const in *
                   | rewrite Z.quot_sub_sgn ]. }
  Qed.
End for_loop.

Lemma for_loop_notation_ind {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {step : Z} {finish : Z} {initial : stateT}
      {cmp : Z -> Z -> bool}
      {step_expr finish_expr} (body : Z -> stateT -> stateT)
      {Hstep : class_eq (fun i => i = step) step_expr}
      {Hfinish : class_eq (fun i => cmp i finish) finish_expr}
      {Hgood : for_loop_is_good i0 step finish cmp}
      (Pbefore : P i0 initial)
      (Pbody : forall c st n, c = i0 + n * step -> i0 <= c < finish \/ finish < c <= i0 -> P c st -> P (c + step) (body c st))
  : P (finish - Z.sgn (finish - i0 + step - Z.sgn step) * (Z.abs (finish - i0 + step - Z.sgn step) mod Z.abs step) + step - Z.sgn step)
      (@for_loop_notation i0 step finish _ initial cmp step_expr finish_expr body Hstep Hfinish Hgood).
Proof.
  unfold for_loop_notation, for_loop_is_good in *; split_andb; Z.ltb_to_lt.
  apply for_loop_ind; auto.
Qed.

Local Ltac pre_t :=
  lazymatch goal with
  | [ Pbefore : ?P ?i0 ?initial
      |- ?P _ (@for_loop_notation ?i0 ?step ?finish _ ?initial _ ?step_expr ?finish_expr ?body ?Hstep ?Hfinish ?Hgood) ]
    => generalize (@for_loop_notation_ind
                     _ P i0 step finish initial _ step_expr finish_expr body Hstep Hfinish Hgood Pbefore)
  end.
Local Ltac t_step :=
  first [ progress unfold for_loop_is_good, for_loop_notation in *
        | progress split_andb
        | progress Z.ltb_to_lt
        | rewrite Z.sgn_pos by lia
        | rewrite Z.abs_eq by lia
        | rewrite Z.sgn_neg by lia
        | rewrite Z.abs_neq by lia
        | progress autorewrite with zsimplify_const
        | match goal with
          | [ Hsgn : Z.sgn ?step = Z.sgn _ |- _ ]
            => unique assert (0 < step) by (rewrite <- Z.sgn_pos_iff, Hsgn, Z.sgn_pos_iff; omega); clear Hsgn
          | [ Hsgn : Z.sgn ?step = Z.sgn _ |- _ ]
            => unique assert (step < 0) by (rewrite <- Z.sgn_neg_iff, Hsgn, Z.sgn_neg_iff; omega); clear Hsgn
          | [ |- (_ -> ?P ?x ?y) -> ?P ?x' ?y' ]
            => replace x with x' by lia; let H' := fresh in intro H'; apply H'; clear H'
          | [ |- (_ -> _) -> _ ]
            => let H := fresh "Hbody" in intro H; progress Z.replace_all_neg_with_pos; revert H
          end
        | rewrite !Z.opp_sub_distr
        | rewrite !Z.opp_add_distr
        | rewrite !Z.opp_involutive
        | rewrite !Z.sub_opp_r
        | rewrite (Z.add_opp_r _ 1)
        | progress (push_Zmod; pull_Zmod)
        | progress Z.replace_all_neg_with_pos
        | solve [ eauto with omega ] ].
Local Ltac t := pre_t; repeat t_step.

Lemma for_loop_ind_lt {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {step : Z} {finish : Z} {initial : stateT}
      {step_expr finish_expr} (body : Z -> stateT -> stateT)
      {Hstep : class_eq (fun i => i = step) step_expr}
      {Hfinish : class_eq (fun i => Z.ltb i finish) finish_expr}
      {Hgood : for_loop_is_good i0 step finish Z.ltb}
      (Pbefore : P i0 initial)
      (Pbody : forall c st n, c = i0 + n * step -> i0 <= c < finish -> P c st -> P (c + step) (body c st))
  : P (finish + step - 1 - ((finish - i0 - 1) mod step))
      (@for_loop_notation i0 step finish _ initial Z.ltb (fun i => step_expr i) (fun i => finish_expr i) (fun i st => body i st) Hstep Hfinish Hgood).
Proof. t. Qed.

Lemma for_loop_ind_gt {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {step : Z} {finish : Z} {initial : stateT}
      {step_expr finish_expr} (body : Z -> stateT -> stateT)
      {Hstep : class_eq (fun i => i = step) step_expr}
      {Hfinish : class_eq (fun i => Z.gtb i finish) finish_expr}
      {Hgood : for_loop_is_good i0 step finish Z.gtb}
      (Pbefore : P i0 initial)
      (Pbody : forall c st n, c = i0 + n * step -> finish < c <= i0 -> P c st -> P (c + step) (body c st))
  : P (finish + step + 1 + (i0 - finish - step - 1) mod (-step))
      (@for_loop_notation i0 step finish _ initial Z.gtb (fun i => step_expr i) (fun i => finish_expr i) (fun i st => body i st) Hstep Hfinish Hgood).
Proof.
  replace (i0 - finish) with (-(finish - i0)) by omega.
  t.
Qed.

Lemma for_loop_ind_lt1 {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {finish : Z} {initial : stateT}
      (body : Z -> stateT -> stateT)
      {Hgood : for_loop_is_good i0 1 finish _}
      (Pbefore : P i0 initial)
      (Pbody : forall c st, i0 <= c < finish -> P c st -> P (c + 1) (body c st))
  : P finish
      (for (int i = i0; i < finish; i++) updating (st = initial) {{
         body i st
      }}).
Proof.
  generalize (@for_loop_ind_lt
                stateT P i0 1 finish initial _ _ body eq_refl eq_refl Hgood Pbefore).
  rewrite Z.mod_1_r, Z.sub_0_r, Z.add_simpl_r.
  auto.
Qed.

Lemma for_loop_ind_gt1 {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {finish : Z} {initial : stateT}
      (body : Z -> stateT -> stateT)
      {Hgood : for_loop_is_good i0 (-1) finish _}
      (Pbefore : P i0 initial)
      (Pbody : forall c st, finish < c <= i0 -> P c st -> P (c - 1) (body c st))
  : P finish
      (for (int i = i0; i > finish; i--) updating (st = initial) {{
         body i st
      }}).
Proof.
  generalize (@for_loop_ind_gt
                stateT P i0 (-1) finish initial _ _ body eq_refl eq_refl Hgood Pbefore).
  simpl; rewrite Z.mod_1_r, Z.add_0_r, (Z.add_opp_r _ 1), Z.sub_simpl_r.
  intro H; apply H; intros *.
  rewrite (Z.add_opp_r _ 1); auto.
Qed.

Local Hint Extern 1 (for_loop_is_good (?i0 + ?step) ?step ?finish _)
=> refine (for_loop_is_good_step_lt _); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 + ?step) ?step ?finish _)
=> refine (for_loop_is_good_step_gt _); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 - ?step') _ ?finish _)
=> refine (for_loop_is_good_step_gt (step:=-step') _); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 + 1) 1 ?finish _)
=> refine (for_loop_is_good_step_lt' _); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 - 1) (-1) ?finish _)
=> refine (for_loop_is_good_step_gt' _); try assumption : typeclass_instances.

(** The Hoare-logic-like conditions for ≤ and ≥ loops seem slightly
    unnatural; you have to choose either to state your correctness
    property in terms of [i + 1], or talk about the correctness
    condition when the loop counter is [i₀ - 1] (which is strange;
    it's like saying the loop has run -1 times), or give the
    correctness condition after the first run of the loop body, rather
    than before it.  We give lemmas for the second two options; if
    you're using the first one, Coq probably won't be able to infer
    the motive ([P], below) automatically, and you might as well use
    the vastly more general version [for_loop_ind_lt] /
    [for_loop_ind_gt]. *)
Lemma for_loop_ind_le1 {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {finish : Z} {initial : stateT}
      (body : Z -> stateT -> stateT)
      {Hgood : for_loop_is_good i0 1 (finish+1) _}
      (Pbefore : P i0 (body i0 initial))
      (Pbody : forall c st, i0 <= c <= finish -> P (c-1) st -> P c (body c st))
  : P finish
      (for (int i = i0; i <= finish; i++) updating (st = initial) {{
         body i st
      }}).
Proof.
  rewrite for_loop_le1_unroll1.
  edestruct Sumbool.sumbool_of_bool; Z.ltb_to_lt; cbv zeta.
  { generalize (@for_loop_ind_lt
                  stateT (fun n => P (n - 1)) (i0+1) 1 (finish+1) (body i0 initial) _ _ body eq_refl eq_refl _).
    rewrite Z.mod_1_r, Z.sub_0_r, !Z.add_simpl_r.
    intro H; apply H; auto with omega; intros *.
    rewrite !Z.add_simpl_r; auto with omega. }
  { unfold for_loop_is_good, ForNotationConstants.Z.ltb', ForNotationConstants.Z.ltb in *; split_andb; Z.ltb_to_lt.
    assert (i0 = finish) by omega; subst.
    assumption. }
Qed.

Lemma for_loop_ind_le1_offset {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {finish : Z} {initial : stateT}
      (body : Z -> stateT -> stateT)
      {Hgood : for_loop_is_good i0 1 (finish+1) _}
      (Pbefore : P (i0-1) initial)
      (Pbody : forall c st, i0 <= c <= finish -> P (c-1) st -> P c (body c st))
  : P finish
      (for (int i = i0; i <= finish; i++) updating (st = initial) {{
         body i st
      }}).
Proof.
  apply for_loop_ind_le1; auto with omega.
  unfold for_loop_is_good, ForNotationConstants.Z.ltb', ForNotationConstants.Z.ltb in *; split_andb; Z.ltb_to_lt.
  auto with omega.
Qed.

Lemma for_loop_ind_ge1 {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {finish : Z} {initial : stateT}
      (body : Z -> stateT -> stateT)
      {Hgood : for_loop_is_good i0 (-1) (finish-1) _}
      (Pbefore : P i0 (body i0 initial))
      (Pbody : forall c st, finish <= c <= i0 -> P (c+1) st -> P c (body c st))
  : P finish
      (for (int i = i0; i >= finish; i--) updating (st = initial) {{
         body i st
      }}).
Proof.
  rewrite for_loop_ge1_unroll1.
  edestruct Sumbool.sumbool_of_bool; Z.ltb_to_lt; cbv zeta.
  { generalize (@for_loop_ind_gt
                  stateT (fun n => P (n + 1)) (i0-1) (-1) (finish-1) (body i0 initial) _ _ body eq_refl eq_refl _).
    simpl; rewrite Z.mod_1_r, Z.add_0_r, (Z.add_opp_r _ 1), !Z.sub_simpl_r.
    intro H; apply H; intros *; auto with omega.
    rewrite (Z.add_opp_r _ 1), !Z.sub_simpl_r; auto with omega. }
  { unfold for_loop_is_good, ForNotationConstants.Z.gtb', ForNotationConstants.Z.gtb in *; split_andb; Z.ltb_to_lt.
    assert (i0 = finish) by omega; subst.
    assumption. }
Qed.

Lemma for_loop_ind_ge1_offset {stateT} (P : Z -> stateT -> Prop)
      {i0 : Z} {finish : Z} {initial : stateT}
      (body : Z -> stateT -> stateT)
      {Hgood : for_loop_is_good i0 (-1) (finish-1) _}
      (Pbefore : P (i0+1) initial)
      (Pbody : forall c st, finish <= c <= i0 -> P (c+1) st -> P c (body c st))
  : P finish
      (for (int i = i0; i >= finish; i--) updating (st = initial) {{
         body i st
      }}).
Proof.
  apply for_loop_ind_ge1; auto with omega.
  unfold for_loop_is_good, ForNotationConstants.Z.gtb', ForNotationConstants.Z.gtb in *; split_andb; Z.ltb_to_lt.
  auto with omega.
Qed.

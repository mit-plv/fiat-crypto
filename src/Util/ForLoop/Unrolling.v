(** * Proving properties of for-loops via loop-unrolling *)
Require Import Coq.micromega.Psatz.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Util.ForLoop.
Require Import Crypto.Util.ForLoop.Instances.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Notations.

Section with_body.
  Context {stateT : Type}
          (body : nat -> stateT -> stateT).

  Lemma unfold_repeat_function (count : nat) (st : stateT)
    : repeat_function body count st
      = match count with
        | O => st
        | S count' => repeat_function body count' (body count st)
        end.
  Proof using Type. destruct count; reflexivity. Qed.

  Lemma repeat_function_unroll1_start (count : nat) (st : stateT)
    : repeat_function body (S count) st
      = repeat_function body count (body (S count) st).
  Proof using Type. rewrite unfold_repeat_function; reflexivity. Qed.

  Lemma repeat_function_unroll1_end (count : nat) (st : stateT)
    : repeat_function body (S count) st
      = body 1 (repeat_function (fun count => body (S count)) count st).
  Proof using Type.
    revert st; induction count as [|? IHcount]; [ reflexivity | ].
    intros; simpl in *; rewrite <- IHcount; reflexivity.
  Qed.

  Lemma repeat_function_unroll1_start_match (count : nat) (st : stateT)
    : repeat_function body count st
      = match count with
        | 0 => st
        | S count' => repeat_function body count' (body count st)
        end.
  Proof using Type. destruct count; [ reflexivity | apply repeat_function_unroll1_start ]. Qed.

  Lemma repeat_function_unroll1_end_match (count : nat) (st : stateT)
    : repeat_function body count st
      = match count with
        | 0 => st
        | S count' => body 1 (repeat_function (fun count => body (S count)) count' st)
        end.
  Proof using Type. destruct count; [ reflexivity | apply repeat_function_unroll1_end ]. Qed.
End with_body.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Section for_loop.
  Context (i0 finish : Z) (step : Z) {stateT} (initial : stateT) (body : Z -> stateT -> stateT)
          (Hgood : Z.sgn step = Z.sgn (finish - i0)).

  Let countZ := (Z.quot (finish - i0 + step - Z.sgn step) step).
  Let count := Z.to_nat countZ.
  Let of_nat_count c := (i0 + step * Z.of_nat (count - c)).
  Let nat_body := (fun c => body (of_nat_count c)).

  Lemma for_loop_empty
        (Heq : finish = i0)
    : for_loop i0 finish step initial body = initial.
  Proof.
    subst; unfold for_loop.
    rewrite Z.sub_diag, Z.quot_sub_sgn; autorewrite with zsimplify_const.
    reflexivity.
  Qed.

  Lemma for_loop_unroll1
    : for_loop i0 finish step initial body
      = if finish =? i0
        then initial
        else let initial' := body i0 initial in
             if Z.abs (finish - i0) <=? Z.abs step
             then initial'
             else for_loop (i0 + step) finish step initial' body.
  Proof.
    break_innermost_match_step; Z.ltb_to_lt.
    { apply for_loop_empty; assumption. }
    { unfold for_loop.
      rewrite repeat_function_unroll1_start_match.
      destruct (Z_zerop step);
        repeat first [ progress break_innermost_match
                     | congruence
                     | lia
                     | progress Z.ltb_to_lt
                     | progress subst
                     | progress rewrite Nat.sub_diag
                     | progress autorewrite with zsimplify_const in *
                     | progress rewrite Z.quot_small_iff in * by omega
                     | progress rewrite Z.quot_small_abs in * by lia
                     | rewrite Nat.sub_succ_l by omega
                     | progress destruct_head' and
                     | rewrite !Z.sub_add_distr
                     | match goal with
                       | [ H : ?x = Z.of_nat _ |- context[?x] ] => rewrite H
                       | [ H : Z.abs ?x <= 0 |- _ ] => assert (x = 0) by lia; clear H
                       | [ H : 0 = Z.sgn ?x |- _ ] => assert (x = 0) by lia; clear H
                       | [ H : ?x - ?y = 0 |- _ ] => is_var x; assert (x = y) by omega; subst x
                       | [ H : Z.to_nat _ = _ |- _ ] => apply Nat2Z.inj_iff in H
                       | [ H : context[Z.abs ?x] |- _ ] => rewrite (Z.abs_eq x) in H by omega
                       | [ H : context[Z.abs ?x] |- _ ] => rewrite (Z.abs_neq x) in H by omega
                       | [ H : Z.of_nat (Z.to_nat _) = _ |- _ ]
                         => rewrite Z2Nat.id in H by (apply Z.quot_nonneg_same_sgn; lia)
                       | [ H : _ = Z.of_nat (S ?x) |- _ ]
                         => is_var x; destruct x; [ reflexivity | ]
                       | [ H : ?x + 1 = Z.of_nat (S ?y) |- _ ]
                         => assert (x = Z.of_nat y) by lia; clear H
                       | [ |- repeat_function _ ?x ?y = repeat_function _ ?x ?y ]
                         => apply repeat_function_Proper_le; intros
                       | [ |- ?f _ ?x = ?f _ ?x ]
                         => is_var f; apply f_equal2; [ | reflexivity ]
                       end
                     | progress rewrite Z.quot_add_sub_sgn_small in * |- by lia
                     | progress autorewrite with zsimplify ]. }
  Qed.
End for_loop.

Lemma for_loop_notation_empty {stateT}
      {i0 : Z} {step : Z} {finish : Z} {initial : stateT}
      {cmp : Z -> Z -> bool}
      {step_expr finish_expr} (body : Z -> stateT -> stateT)
      {Hstep : class_eq (fun i => i = step) step_expr}
      {Hfinish : class_eq (fun i => cmp i finish) finish_expr}
      {Hgood : for_loop_is_good i0 step finish cmp}
      (Heq : i0 = finish)
  : @for_loop_notation i0 step finish _ initial cmp step_expr finish_expr body Hstep Hfinish Hgood = initial.
Proof.
  unfold for_loop_notation, for_loop_is_good in *; split_andb; Z.ltb_to_lt.
  apply for_loop_empty; auto.
Qed.

Local Notation adjust_bool b p
  := (match b as b' return b' = true -> b' = true with
      | true => fun _ => eq_refl
      | false => fun x => x
      end p).

Lemma for_loop_is_good_step_gen
      cmp
      (Hcmp : cmp = Z.ltb \/ cmp = Z.gtb)
      {i0 step finish}
      {H : for_loop_is_good i0 step finish cmp}
      (H' : cmp (i0 + step) finish = true)
  : for_loop_is_good (i0 + step) step finish cmp.
Proof.
  unfold for_loop_is_good in *.
  rewrite H', Bool.andb_true_r.
  destruct Hcmp; subst;
    split_andb; Z.ltb_to_lt;
      [ rewrite (Z.sgn_pos (finish - i0)) in * by omega
      | rewrite (Z.sgn_neg (finish - i0)) in * by omega ];
      destruct step; simpl in *; try congruence;
        symmetry;
        [ apply Z.sgn_pos_iff | apply Z.sgn_neg_iff ]
        ; omega.
Qed.

Definition for_loop_is_good_step_lt
           {i0 step finish}
           {H : for_loop_is_good i0 step finish Z.ltb}
           (H' : Z.ltb (i0 + step) finish = true)
  : for_loop_is_good (i0 + step) step finish Z.ltb
  := for_loop_is_good_step_gen Z.ltb (or_introl eq_refl) (H:=H) H'.
Definition for_loop_is_good_step_gt
           {i0 step finish}
           {H : for_loop_is_good i0 step finish Z.gtb}
           (H' : Z.gtb (i0 + step) finish = true)
  : for_loop_is_good (i0 + step) step finish Z.gtb
  := for_loop_is_good_step_gen Z.gtb (or_intror eq_refl) (H:=H) H'.
Definition for_loop_is_good_step_lt'
           {i0 finish}
           {H : for_loop_is_good i0 1 (finish + 1) Z.ltb}
           (H' : Z.ltb i0 finish = true)
  : for_loop_is_good (i0 + 1) 1 (finish + 1) Z.ltb.
Proof.
  apply for_loop_is_good_step_lt; Z.ltb_to_lt; omega.
Qed.
Definition for_loop_is_good_step_gt'
           {i0 finish}
           {H : for_loop_is_good i0 (-1) (finish - 1) Z.gtb}
           (H' : Z.gtb i0 finish = true)
  : for_loop_is_good (i0 - 1) (-1) (finish - 1) Z.gtb.
Proof.
  apply for_loop_is_good_step_gt; Z.ltb_to_lt; omega.
Qed.

Local Hint Extern 1 (for_loop_is_good (?i0 + ?step) ?step ?finish _)
=> refine (adjust_bool _ (for_loop_is_good_step_lt _)); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 + ?step) ?step ?finish _)
=> refine (adjust_bool _ (for_loop_is_good_step_gt _)); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 - ?step') _ ?finish _)
=> refine (adjust_bool _ (for_loop_is_good_step_gt (step:=-step') _)); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 + 1) 1 ?finish _)
=> refine (adjust_bool _ (for_loop_is_good_step_lt' _)); try assumption : typeclass_instances.
Local Hint Extern 1 (for_loop_is_good (?i0 - 1) (-1) ?finish _)
=> refine (adjust_bool _ (for_loop_is_good_step_gt' _)); try assumption : typeclass_instances.

Local Ltac t :=
  repeat match goal with
         | _ => progress unfold for_loop_is_good, for_loop_notation in *
         | _ => progress rewrite for_loop_unroll1 by auto
         | _ => omega
         | _ => progress subst
         | _ => reflexivity
         | _ => progress split_andb
         | _ => progress Z.ltb_to_lt
         | _ => progress break_innermost_match_step
         | [ H : context[Z.abs ?x] |- _ ] => rewrite (Z.abs_eq x) in H by omega
         | [ H : context[Z.abs ?x] |- _ ] => rewrite (Z.abs_neq x) in H by omega
         | [ H : context[Z.sgn ?x] |- _ ] => rewrite (Z.sgn_pos x) in H by omega
         | [ H : context[Z.sgn ?x] |- _ ] => rewrite (Z.sgn_neg x) in H by omega
         | [ H : Z.sgn _ = 1 |- _ ] => apply Z.sgn_pos_iff in H
         | [ H : Z.sgn _ = -1 |- _ ] => apply Z.sgn_neg_iff in H
         end.

Lemma for_loop_lt_unroll1 {stateT}
      {i0 : Z} {step : Z} {finish : Z} {initial : stateT}
      {step_expr finish_expr} (body : Z -> stateT -> stateT)
      {Hstep : class_eq (fun i => i = step) step_expr}
      {Hfinish : class_eq (fun i => Z.ltb i finish) finish_expr}
      {Hgood : for_loop_is_good i0 step finish Z.ltb}
  : (@for_loop_notation i0 step finish _ initial Z.ltb (fun i => step_expr i) (fun i => finish_expr i) (fun i st => body i st) Hstep Hfinish Hgood)
    = let initial' := body i0 initial in
      if Sumbool.sumbool_of_bool (Z.ltb (i0 + step) finish)
      then @for_loop_notation (i0 + step) step finish _ initial' Z.ltb (fun i => step_expr i) (fun i => finish_expr i) (fun i st => body i st) Hstep Hfinish _
      else initial'.
Proof. t. Qed.

Lemma for_loop_gt_unroll1 {stateT}
      {i0 : Z} {step : Z} {finish : Z} {initial : stateT}
      {step_expr finish_expr} (body : Z -> stateT -> stateT)
      {Hstep : class_eq (fun i => i = step) step_expr}
      {Hfinish : class_eq (fun i => Z.gtb i finish) finish_expr}
      {Hgood : for_loop_is_good i0 step finish Z.gtb}
  : (@for_loop_notation i0 step finish _ initial Z.gtb (fun i => step_expr i) (fun i => finish_expr i) (fun i st => body i st) Hstep Hfinish Hgood)
    = let initial' := body i0 initial in
      if Sumbool.sumbool_of_bool (Z.gtb (i0 + step) finish)
      then @for_loop_notation (i0 + step) step finish _ initial' Z.gtb (fun i => step_expr i) (fun i => finish_expr i) (fun i st => body i st) Hstep Hfinish _
      else initial'.
Proof. t. Qed.

Lemma for_loop_lt1_unroll1 {stateT}
      {i0 : Z} {finish : Z} {initial : stateT}
      {body : Z -> stateT -> stateT}
      {Hgood : for_loop_is_good i0 1 finish _}
  : for (int i = i0; i < finish; i++) updating (st = initial) {{
      body i st
    }}
    = let initial' := body i0 initial in
      if Sumbool.sumbool_of_bool (Z.ltb (i0 + 1) finish)
      then for (int i = i0+1; i < finish; i++) updating (st = initial') {{
             body i st
           }}
      else initial'.
Proof. apply for_loop_lt_unroll1. Qed.

Lemma for_loop_gt1_unroll1 {stateT}
      {i0 : Z} {finish : Z} {initial : stateT}
      {body : Z -> stateT -> stateT}
      {Hgood : for_loop_is_good i0 (-1) finish _}
  : for (int i = i0; i > finish; i--) updating (st = initial) {{
      body i st
    }}
    = let initial' := body i0 initial in
      if Sumbool.sumbool_of_bool (Z.gtb (i0 - 1) finish)
      then for (int i = i0-1; i > finish; i--) updating (st = initial') {{
             body i st
           }}
      else initial'.
Proof. apply for_loop_gt_unroll1. Qed.

Lemma for_loop_le1_unroll1 {stateT}
      {i0 : Z} {finish : Z} {initial : stateT}
      {body : Z -> stateT -> stateT}
      {Hgood : for_loop_is_good i0 1 (finish+1) _}
  : for (int i = i0; i <= finish; i++) updating (st = initial) {{
      body i st
    }}
    = let initial' := body i0 initial in
      if Sumbool.sumbool_of_bool (Z.ltb i0 finish)
      then for (int i = i0+1; i <= finish; i++) updating (st = initial') {{
             body i st
           }}
      else initial'.
Proof.
  rewrite for_loop_lt_unroll1; unfold for_loop_notation.
  break_innermost_match; Z.ltb_to_lt; try omega; try reflexivity.
Qed.

Lemma for_loop_ge1_unroll1 {stateT}
      {i0 : Z} {finish : Z} {initial : stateT}
      {body : Z -> stateT -> stateT}
      {Hgood : for_loop_is_good i0 (-1) (finish-1) _}
  : for (int i = i0; i >= finish; i--) updating (st = initial) {{
      body i st
    }}
    = let initial' := body i0 initial in
      if Sumbool.sumbool_of_bool (Z.gtb i0 finish)
      then for (int i = i0-1; i >= finish; i--) updating (st = initial') {{
             body i st
           }}
      else initial'.
Proof.
  rewrite for_loop_gt_unroll1; unfold for_loop_notation.
  break_innermost_match; Z.ltb_to_lt; try omega; try reflexivity.
Qed.

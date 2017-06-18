(*** Word-By-Word Montgomery Multiplication Proofs *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Dependent.Proofs.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Tactics.BreakMatch.

Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Section WordByWordMontgomery.
  (** XXX TODO: pick better names for things like [R_numlimbs] *)
  Context (r : positive)
          (R_numlimbs : nat).
  Local Notation small := (@small (Z.pos r)).
  Local Notation eval := (@eval (Z.pos r)).
  Local Notation add' := (fun n => @add (Z.pos r) (S n) n (S n)).
  Local Notation add := (fun n => @add (Z.pos r) n n n).
  Local Notation scmul := (@scmul (Z.pos r)).
  Local Notation eval_zero := (@eval_zero (Z.pos r)).
  Local Notation eval_join0 := (@eval_zero (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_div := (@eval_div (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_mod := (@eval_mod (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation small_div := (@small_div (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_scmul := (fun n a v _ _ => @eval_scmul (Z.pos r) (Zorder.Zgt_pos_0 _) n a v).
  Local Notation eval_add := (@eval_add_same (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_add' := (@eval_add_S1 (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation small_add := (fun n => @small_add (Z.pos r) (Zorder.Zgt_pos_0 _) _ _ _).
  Local Notation drop_high := (@drop_high (S R_numlimbs)).
  Context (A_numlimbs : nat)
          (N : T R_numlimbs)
          (A : T A_numlimbs)
          (B : T R_numlimbs)
          (k : Z).
  Context ri
          (r_big : r > 1)
          (small_A : small A)
          (A_bound : 0 <= eval A < Z.pos r ^ Z.of_nat A_numlimbs)
          (ri_correct : r*ri mod (eval N) = 1 mod (eval N))
          (N_bound : 0 < eval N < r^Z.of_nat R_numlimbs)
          (B_bound' : 0 <= eval B < r^Z.of_nat R_numlimbs)
          (k_correct : k * eval N mod r = -1).
  Let R : positive := match (Z.pos r ^ Z.of_nat R_numlimbs)%Z with
                      | Z.pos R => R
                      | _ => 1%positive
                      end.
  Let Npos : positive := match eval N with
                         | Z.pos N => N
                         | _ => 1%positive
                         end.
  Local Lemma R_correct : Z.pos R = Z.pos r ^ Z.of_nat R_numlimbs.
  Proof.
    assert (0 < r^Z.of_nat R_numlimbs) by (apply Z.pow_pos_nonneg; lia).
    subst R; destruct (Z.pos r ^ Z.of_nat R_numlimbs) eqn:?; [ | reflexivity | ];
      lia.
  Qed.
  Local Lemma Npos_correct: eval N = Z.pos Npos.
  Proof. subst Npos; destruct (eval N); [ | reflexivity | ]; lia. Qed.
  Local Lemma N_lt_R : eval N < R.
  Proof. rewrite R_correct; apply N_bound. Qed.
  Local Lemma B_bound : 0 <= eval B < R.
  Proof. rewrite R_correct; apply B_bound'. Qed.


  Local Lemma eval_drop_high : forall v, small v -> eval (drop_high v) = eval v mod (r * r^Z.of_nat R_numlimbs).
  Proof.
    intros; erewrite eval_drop_high by (eassumption || lia).
    f_equal; unfold uweight.
    rewrite Znat.Nat2Z.inj_succ, Z.pow_succ_r by lia; reflexivity.
  Qed.

  Local Notation redc_body_no_cps := (@redc_body_no_cps r R_numlimbs N).
  Local Notation redc_body_cps := (@redc_body_cps r R_numlimbs N).
  Local Notation redc_body := (@redc_body r R_numlimbs N).
  Local Notation redc_loop_no_cps := (@redc_loop_no_cps r R_numlimbs N B k).
  Local Notation redc_loop_cps := (@redc_loop_cps r R_numlimbs N B k).
  Local Notation redc_loop := (@redc_loop r R_numlimbs N B k).
  Local Notation redc_no_cps := (@redc_no_cps r R_numlimbs N A_numlimbs A B k).
  Local Notation redc_cps := (@redc_cps r R_numlimbs N A_numlimbs A B k).
  Local Notation redc := (@redc r R_numlimbs N A_numlimbs A B k).

  Definition redc_no_cps_bound : 0 <= eval redc_no_cps < eval N + eval B
    := @redc_bound T (@eval) (@zero) (@divmod) r r_big R R_numlimbs R_correct (@small) eval_zero eval_div eval_mod small_div (@scmul) eval_scmul (@add) eval_add small_add (@add') eval_add' small_add drop_high eval_drop_high N Npos Npos_correct N_lt_R B B_bound ri k A_numlimbs A small_A.
  Definition redc_no_cps_mod_N
    : (eval redc_no_cps) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N)
    := @redc_mod_N T (@eval) (@zero) (@divmod) r r_big R R_numlimbs R_correct (@small) eval_zero eval_div eval_mod small_div (@scmul) eval_scmul (@add) eval_add small_add (@add') eval_add' small_add drop_high eval_drop_high N Npos Npos_correct N_lt_R B B_bound ri ri_correct k k_correct A_numlimbs A small_A A_bound.

  Lemma redc_body_cps_id pred_A_numlimbs (A' : T (S pred_A_numlimbs)) (S' : T (S R_numlimbs)) {cpsT} f
    : @redc_body_cps pred_A_numlimbs A' B k S' cpsT f = f (redc_body A' B k S').
  Proof.
    unfold redc_body, redc_body_cps, LetIn.Let_In.
    repeat first [ reflexivity
                 | break_innermost_match_step
                 | progress autorewrite with uncps ].
  Qed.

  Lemma redc_loop_cps_id (count : nat) (A_S : T count * T (S R_numlimbs)) {cpsT} f
    : @redc_loop_cps cpsT count f A_S = f (redc_loop count A_S).
  Proof.
    unfold redc_loop.
    revert A_S f.
    induction count as [|count IHcount].
    { reflexivity. }
    { intros [A' S']; simpl; intros.
      etransitivity; rewrite @redc_body_cps_id; [ rewrite IHcount | ]; reflexivity. }
  Qed.
  Lemma redc_cps_id {cpsT} f : @redc_cps cpsT f = f redc.
  Proof.
    unfold redc, redc_cps.
    etransitivity; rewrite redc_loop_cps_id; [ | reflexivity ]; break_innermost_match; reflexivity.
  Qed.

  Lemma redc_body_id_no_cps pred_A_numlimbs A' S'
    : @redc_body pred_A_numlimbs A' B k S' = redc_body_no_cps B k (A', S').
  Proof.
    unfold redc_body, redc_body_cps, redc_body_no_cps, Abstract.Dependent.Definition.redc_body, LetIn.Let_In, id.
    repeat autounfold with word_by_word_montgomery.
    repeat first [ reflexivity
                 | progress cbn [fst snd id]
                 | progress autorewrite with uncps
                 | break_innermost_match_step
                 | f_equal; [] ].
  Qed.
  Lemma redc_loop_cps_id_no_cps count A_S
    : redc_loop count A_S = redc_loop_no_cps count A_S.
  Proof.
    unfold redc_loop_no_cps, id.
    revert A_S.
    induction count as [|count IHcount]; simpl; [ reflexivity | ].
    intros [A' S']; unfold redc_loop; simpl.
    rewrite redc_body_cps_id, redc_loop_cps_id, IHcount, redc_body_id_no_cps.
    reflexivity.
  Qed.
  Lemma redc_cps_id_no_cps : redc = redc_no_cps.
  Proof.
    unfold redc, redc_no_cps, redc_cps, Abstract.Dependent.Definition.redc.
    rewrite redc_loop_cps_id, (surjective_pairing (redc_loop _ _)).
    rewrite redc_loop_cps_id_no_cps; reflexivity.
  Qed.

  Lemma redc_bound : 0 <= eval redc < eval N + eval B.
  Proof. rewrite redc_cps_id_no_cps; apply redc_no_cps_bound. Qed.
  Lemma redc_mod_N
    : (eval redc) mod (eval N) = (eval A * eval B * ri^(Z.of_nat A_numlimbs)) mod (eval N).
  Proof. rewrite redc_cps_id_no_cps; apply redc_no_cps_mod_N. Qed.
End WordByWordMontgomery.

Hint Rewrite redc_body_cps_id redc_loop_cps_id redc_cps_id : uncps.

(*** Word-By-Word Montgomery Multiplication Proofs *)
Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Crypto.Arithmetic.Saturated.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Definition.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Abstract.Proofs.
Require Import Crypto.Arithmetic.MontgomeryReduction.WordByWord.Definition.
Require Import Crypto.Util.ZUtil.

Local Open Scope Z_scope.
Local Coercion Z.pos : positive >-> Z.
Section WordByWordMontgomery.
  (** XXX TODO: pick better names for things like [R_numlimbs] *)
  Context (r : positive)
          (R_numlimbs : nat).
  Local Notation small := (@small (Z.pos r)).
  Local Notation eval := (@eval (Z.pos r)).
  Local Notation add := (@add (Z.pos r)).
  Local Notation scmul := (@scmul (Z.pos r)).
  Local Notation eval_zero := (@eval_zero (Z.pos r)).
  Local Notation eval_div := (@eval_div (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_mod := (@eval_mod (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation small_div := (@small_div (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation numlimbs_div := (@numlimbs_div (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_scmul := (@eval_scmul (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation numlimbs_scmul := (@numlimbs_scmul (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation eval_add := (@eval_add (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation small_add := (@small_add (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation numlimbs_add := (@numlimbs_add (Z.pos r) (Zorder.Zgt_pos_0 _)).
  Local Notation drop_high := (@drop_high (S R_numlimbs)).
  Local Notation numlimbs_drop_high := (@numlimbs_drop_high (Z.pos r) (Zorder.Zgt_pos_0 _) (S R_numlimbs)).
  Context (N A B : T)
          (k : Z)
          ri
          (r_big : r > 1)
          (small_A : small A)
          (Hnumlimbs_le : (R_numlimbs <= numlimbs B)%nat)
          (Hnumlimbs_eq : R_numlimbs = numlimbs B)
          (A_bound : 0 <= eval A < Z.pos r ^ Z.of_nat (numlimbs A))
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

  Local Notation redc_cps := (@redc_cps r R_numlimbs N A B k).
  Local Notation redc := (@redc_cps _ id).

  Definition redc_bound : 0 <= eval redc < eval N + eval B
    := @redc_bound T eval numlimbs zero divmod r r_big small eval_zero eval_div eval_mod small_div scmul eval_scmul R R_numlimbs R_correct add eval_add small_add drop_high eval_drop_high N Npos Npos_correct N_lt_R B B_bound ri k A small_A.
  Definition numlimbs_redc_gen
    : numlimbs redc
      = match numlimbs A with
        | O => S (numlimbs B)
        | _ => S R_numlimbs
        end
    := @numlimbs_redc_gen T eval numlimbs zero divmod r r_big small eval_zero numlimbs_zero eval_div eval_mod small_div numlimbs_div scmul eval_scmul numlimbs_scmul R R_numlimbs R_correct add eval_add small_add numlimbs_add drop_high eval_drop_high numlimbs_drop_high N Npos Npos_correct N_lt_R B B_bound ri k A small_A Hnumlimbs_le.
  Definition numlimbs_redc : numlimbs redc = S (numlimbs B)
    := @numlimbs_redc T eval numlimbs zero divmod r r_big small eval_zero numlimbs_zero eval_div eval_mod small_div numlimbs_div scmul eval_scmul numlimbs_scmul R R_numlimbs R_correct add eval_add small_add numlimbs_add drop_high eval_drop_high numlimbs_drop_high N Npos Npos_correct N_lt_R B B_bound ri k A small_A Hnumlimbs_eq.
  Definition redc_mod_N
    : (eval redc) mod (eval N) = (eval A * eval B * ri^(Z.of_nat (numlimbs A))) mod (eval N)
    := @redc_mod_N T eval numlimbs zero divmod r r_big small eval_zero eval_div eval_mod small_div scmul eval_scmul R R_numlimbs R_correct add eval_add small_add drop_high eval_drop_high N Npos Npos_correct N_lt_R B B_bound ri ri_correct k k_correct A small_A A_bound.
  Definition redc_cps_ind
    : forall {cpsT} (rest : _ -> cpsT)
             (P : cpsT -> Prop)
             (H : forall redcv,
                 (eval redcv) mod (eval N) = (eval A * eval B * ri^(Z.of_nat (numlimbs A))) mod (eval N)
                 -> numlimbs redcv = S (numlimbs B)
                 -> 0 <= eval redcv < eval N + eval B
                 -> P (rest redcv)),
      P (redc_cps rest)
    := @redc_cps_ind T eval numlimbs zero divmod r r_big small eval_zero numlimbs_zero eval_div eval_mod small_div numlimbs_div scmul eval_scmul numlimbs_scmul R R_numlimbs R_correct add eval_add small_add numlimbs_add drop_high eval_drop_high numlimbs_drop_high N Npos Npos_correct N_lt_R B B_bound ri ri_correct k k_correct A small_A Hnumlimbs_eq A_bound.
End WordByWordMontgomery.

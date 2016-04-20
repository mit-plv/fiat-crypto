Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemOpt.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParams.
Require Import Crypto.ModularArithmetic.PseudoMersenneBaseParamProofs.
Require Import Coq.Lists.List Crypto.Util.ListUtil.
Require Import Crypto.ModularArithmetic.PrimeFieldTheorems.
Require Import Crypto.Tactics.VerdiTactics.
Require Import Crypto.BaseSystem.
Import ListNotations.
Require Import Coq.ZArith.ZArith Coq.ZArith.Zpower Coq.ZArith.ZArith Coq.ZArith.Znumtheory.
Local Open Scope Z.

(* BEGIN PseudoMersenneBaseParams instance construction. *)

Definition modulus : Z := 2^255 - 19.
Lemma prime_modulus : prime modulus. Admitted.

Definition limb_widths : list Z := [26;25;26;25;26;25;26;25;26;25].

(* TODO : move to ListUtil *)
Lemma fold_right_and_True_forall_In_iff : forall {T} (l : list T) (P : T -> Prop),
  (forall x, In x l -> P x) <-> fold_right and True (map P l).
Proof.
  induction l; intros; simpl; try tauto.
  rewrite <- IHl.
  intuition (subst; auto).
Qed.

Ltac brute_force_indices := intros; unfold sum_firstn, limb_widths; simpl in *;
  repeat match goal with
  | _ => progress simpl in *
  | _ => reflexivity
  | [H : (S _ < S _)%nat |- _ ] => apply lt_S_n in H
  | [H : (?x + _ < _)%nat |- _ ] => is_var x; destruct x
  | [H : (?x < _)%nat |- _ ] => is_var x; destruct x
  | _ => omega
  end.

Instance params25519 : PseudoMersenneBaseParams modulus := { limb_widths := limb_widths }.
Proof.
  + abstract (apply fold_right_and_True_forall_In_iff; simpl; repeat (split; [omega |]); auto).
  + abstract (unfold limb_widths; congruence).
  + abstract brute_force_indices.
  + abstract apply prime_modulus.
  + abstract brute_force_indices.
Defined.

(* END PseudoMersenneBaseParams instance construction. *)

(* Precompute k and c *)
Definition k_ := 255.
Lemma k_subst : k_ = k. reflexivity. Qed.
Definition c_ := 19.
Lemma c_subst : c_ = c. reflexivity. Qed.

Local Open Scope nat_scope.
Lemma GF25519Base25Point5_mul_reduce_formula :
  forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
    {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                      -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                      -> rep ls (f*g)%F}.
Proof.
  eexists.
  intros f g Hf Hg.
  pose proof (carry_mul_opt_correct k_ c_ k_subst c_subst [0;9;8;7;6;5;4;3;2;1;0]_ _ _ _ Hf Hg) as Hfg.
  forward Hfg; [abstract (clear; cbv; intros; repeat break_or_hyp; intuition)|].
  specialize (Hfg H); clear H.
  forward Hfg; [exact eq_refl|].
  specialize (Hfg H); clear H.

  set (p := params25519) in Hfg at 1.
  change (params25519) with p at 1.
  set (fg := (f * g)%F) in Hfg |- * .

  Opaque Z.shiftl
  Pos.iter
  Z.div2
  Pos.div2
  Pos.div2_up
  Pos.succ
  Z.land
  Z.of_N
  Pos.land
  N.ldiff
  Pos.pred_N
  Pos.pred_double
  Z.opp Z.mul Pos.mul Let_In digits Z.add Pos.add Z.pos_sub.
cbv [
     carry_mul_opt

     mul_opt mul'_opt firstn skipn map_opt
     limb_widths base_from_limb_widths_opt 
     k_ c_ Z_shiftl_by_opt
     length rev app zeros
     mul'_opt_step mul_bi'_opt add
     mul_bi'_opt_step
     nth_default_opt nth_error plus
     Z_div_opt Z_mul_opt
     params25519

     carry_sequence_opt_cps carry_opt_cps fold_right
     List.app List.rev length
     base limb_widths base_from_limb_widths_opt
     nth_default_opt set_nth_opt pred beq_nat id
     Z.shiftr
   ] in Hfg.
  change (Z.shiftl 1 26 + -1)%Z with 67108863%Z in Hfg.
  change (Z.shiftl 1 25 + -1)%Z with 33554431%Z in Hfg.
  repeat rewrite ?Z.mul_1_r, ?Z.add_0_l, ?Z.add_assoc, ?Z.mul_assoc in Hfg.

  exact Hfg.
Time Defined.

Extraction "/tmp/test.ml" GF25519Base25Point5_mul_reduce_formula.
(* It's easy enough to use extraction to get the proper nice-looking formula.
 * More Ltac acrobatics will be needed to get out that formula for further use in Coq.
 * The easiest fix will be to make the proof script above fully automated,
 * using [abstract] to contain the proof part. *)

Lemma GF25519Base25Point5_add_reduce_formula :
  forall f0 f1 f2 f3 f4 f5 f6 f7 f8 f9
    g0 g1 g2 g3 g4 g5 g6 g7 g8 g9,
    {ls | forall f g, rep [f0;f1;f2;f3;f4;f5;f6;f7;f8;f9] f
                   -> rep [g0;g1;g2;g3;g4;g5;g6;g7;g8;g9] g
                   -> rep ls (f + g)%F}.
Proof.
  eexists.
  intros f g Hf Hg.
  pose proof (carry_add_opt_correct c_ c_subst [0;9;8;7;6;5;4;3;2;1;0]_ _ _ _ Hf Hg) as Hfg.
  forward Hfg; [abstract (clear; cbv; intros; repeat break_or_hyp; intuition)|].
  specialize (Hfg H); clear H.
  forward Hfg; [exact eq_refl|].
  specialize (Hfg H); clear H.

  set (p := params25519) in Hfg at 1.
  change (params25519) with p at 1.
  set (fg := (f + g)%F) in Hfg |- * .

  cbv [
     carry_sequence_opt_cps carry_opt_cps fold_right
     carry_add_opt add_opt c_
     nth_default_opt set_nth_opt nth_error set_nth
     limb_widths params25519 base_from_limb_widths_opt
     List.app List.rev pred length
     beq_nat
   ] in Hfg.
  change (Z.shiftl 1 26 + -1)%Z with 67108863%Z in Hfg.
  change (Z.shiftl 1 25 + -1)%Z with 33554431%Z in Hfg.
  exact Hfg.
Defined.

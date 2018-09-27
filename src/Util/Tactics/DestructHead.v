Require Export Crypto.Util.FixCoqMistakes.

Require Import Crypto.Util.Tactics.Head.
Require Import Crypto.Util.Tactics.DestructHyps.

Ltac destruct_head_matcher T HT :=
  match head HT with
  | T => idtac
  end.
Ltac destruct_head T := destruct_all_matches ltac:(destruct_head_matcher T).
Ltac destruct_one_head T := destruct_one_match ltac:(destruct_head_matcher T).
Ltac destruct_head' T := destruct_all_matches' ltac:(destruct_head_matcher T).

Ltac inversion_head T := inversion_all_matches ltac:(destruct_head_matcher T).
Ltac inversion_one_head T := inversion_one_match ltac:(destruct_head_matcher T).
Ltac inversion_head' T := inversion_all_matches' ltac:(destruct_head_matcher T).


Ltac head_hnf_matcher T HT :=
  match head_hnf HT with
  | T => idtac
  end.
Ltac destruct_head_hnf T := destruct_all_matches ltac:(head_hnf_matcher T).
Ltac destruct_one_head_hnf T := destruct_one_match ltac:(head_hnf_matcher T).
Ltac destruct_head_hnf' T := destruct_all_matches' ltac:(head_hnf_matcher T).

Ltac inversion_head_hnf T := inversion_all_matches ltac:(head_hnf_matcher T).
Ltac inversion_one_head_hnf T := inversion_one_match ltac:(head_hnf_matcher T).
Ltac inversion_head_hnf' T := inversion_all_matches' ltac:(head_hnf_matcher T).

(** Faster versions for some common connectives *)
Ltac destruct_one_head'_ex := match goal with H : ex _ |- _ => destruct H end.
Ltac destruct_one_head_ex := destruct_one_head'_ex; simpl in *.
Ltac destruct_head'_ex := repeat destruct_one_head'_ex.
Ltac destruct_head_ex := repeat destruct_one_head_ex.

Ltac destruct_one_head'_sig := match goal with H : sig _ |- _ => destruct H end.
Ltac destruct_one_head_sig := destruct_one_head'_sig; simpl in *.
Ltac destruct_head'_sig := repeat destruct_one_head'_sig.
Ltac destruct_head_sig := repeat destruct_one_head_sig.

Ltac destruct_one_head'_sigT := match goal with H : sigT _ |- _ => destruct H end.
Ltac destruct_one_head_sigT := destruct_one_head'_sigT; simpl in *.
Ltac destruct_head'_sigT := repeat destruct_one_head'_sigT.
Ltac destruct_head_sigT := repeat destruct_one_head_sigT.

Ltac destruct_one_head'_prod := match goal with H : prod _ _ |- _ => destruct H end.
Ltac destruct_one_head_prod := destruct_one_head'_prod; simpl in *.
Ltac destruct_head'_prod := repeat destruct_one_head'_prod.
Ltac destruct_head_prod := repeat destruct_one_head_prod.

Ltac destruct_one_head'_and := match goal with H : and _ _ |- _ => destruct H end.
Ltac destruct_one_head_and := destruct_one_head'_and; simpl in *.
Ltac destruct_head'_and := repeat destruct_one_head'_and.
Ltac destruct_head_and := repeat destruct_one_head_and.

Ltac destruct_one_head'_or := match goal with H : or _ _ |- _ => destruct H end.
Ltac destruct_one_head_or := destruct_one_head'_or; simpl in *.
Ltac destruct_head'_or := repeat destruct_one_head'_or.
Ltac destruct_head_or := repeat destruct_one_head_or.

Ltac destruct_one_head'_sum := match goal with H : sum _ _ |- _ => destruct H end.
Ltac destruct_one_head_sum := destruct_one_head'_sum; simpl in *.
Ltac destruct_head'_sum := repeat destruct_one_head'_sum.
Ltac destruct_head_sum := repeat destruct_one_head_sum.

Ltac destruct_one_head'_unit := match goal with H : unit |- _ => clear H || destruct H end.
Ltac destruct_one_head_unit := destruct_one_head'_unit; simpl in *.
Ltac destruct_head'_unit := repeat destruct_one_head'_unit.
Ltac destruct_head_unit := repeat destruct_one_head_unit.

Ltac destruct_one_head'_True := match goal with H : True |- _ => clear H || destruct H end.
Ltac destruct_one_head_True := destruct_one_head'_True; simpl in *.
Ltac destruct_head'_True := repeat destruct_one_head'_True.
Ltac destruct_head_True := repeat destruct_one_head_True.

Ltac destruct_one_head'_bool := match goal with H : bool |- _ => clear H || destruct H end.
Ltac destruct_one_head_bool := destruct_one_head'_bool; simpl in *.
Ltac destruct_head'_bool := repeat destruct_one_head'_bool.
Ltac destruct_head_bool := repeat destruct_one_head_bool.

Ltac destruct_one_head'_False := match goal with H : False |- _ => destruct H end.
Ltac destruct_one_head_False := destruct_one_head'_False; simpl in *.
Ltac destruct_head'_False := repeat destruct_one_head'_False.
Ltac destruct_head_False := repeat destruct_one_head_False.

Ltac destruct_one_head'_Empty_set := match goal with H : Empty_set |- _ => destruct H end.
Ltac destruct_one_head_Empty_set := destruct_one_head'_Empty_set; simpl in *.
Ltac destruct_head'_Empty_set := repeat destruct_one_head'_Empty_set.
Ltac destruct_head_Empty_set := repeat destruct_one_head_Empty_set.

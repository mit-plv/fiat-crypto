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

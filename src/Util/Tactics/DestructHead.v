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

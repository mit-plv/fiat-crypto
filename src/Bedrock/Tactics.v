Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Rewriter.Language.Wf.

Import Wf.Compilers.expr.

(** Tactics ***)
Ltac cleanup :=
  repeat first [ progress cbn [fst snd eq_rect] in *
               | progress destruct_head'_and
               | match goal with H : exists _, _ |- _ => destruct H end
               | match goal with H : ?x = ?x |- _ => clear H end ].

(* borrowed from Fancy/Compiler.v *)
(* TODO : replace calls to this with simpler/faster tactics *)
Ltac hammer_wf :=
  repeat first [ progress subst
               | progress cbn [eq_rect fst snd projT1 projT2] in *
               | progress destruct_head'_False
               | progress inversion_wf_one_constr
               | progress Inversion.Compilers.expr.invert_subst
               | progress destruct_head'_and
               | progress destruct_head'_sig
               | progress Inversion.Compilers.expr.inversion_expr
               | break_innermost_match_hyps_step
               | match goal with
                 | H : existT _ _ _ = existT _ _ _ |- _ =>
                   apply Eqdep_dec.inj_pair2_eq_dec in H;
                   [ | solve [ apply Inversion.Compilers.type.type_eq_Decidable] ]
                 end ]; cleanup.
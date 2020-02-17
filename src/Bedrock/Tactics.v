Require Import bedrock2.WeakestPreconditionProperties.
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

(* call after inversion or induction on a wf hypothesis *)
Ltac cleanup_wf :=
  repeat (first
            [ progress subst
            | progress Inversion.Compilers.expr.inversion_expr
            | match goal with
              | H:existT _ _ _ = existT _ _ _
                |- _ =>
                apply Eqdep_dec.inj_pair2_eq_dec in H;
                [  | solve [ apply Inversion.Compilers.type.type_eq_Decidable ] ]
              end ]); cleanup.

Ltac propers_step :=
  match goal with
  | H : WeakestPrecondition.literal ?v _
    |- WeakestPrecondition.literal ?v _ =>
    eapply Proper_literal
  | H : WeakestPrecondition.get ?l ?x _
    |- WeakestPrecondition.get ?l ?x _ =>
    eapply Proper_get
  | H : WeakestPrecondition.load ?s ?m ?a _
    |- WeakestPrecondition.load ?s ?m ?a _ =>
    eapply Proper_load
  | H : WeakestPrecondition.store ?s ?m ?a ?v _
    |- WeakestPrecondition.store ?s ?m ?a ?v _ =>
    eapply Proper_store
  | H : WeakestPrecondition.expr ?m ?l ?e _
    |- WeakestPrecondition.expr ?m ?l ?e _ =>
    eapply Proper_expr
  | H : WeakestPrecondition.list_map ?f ?xs _
    |- WeakestPrecondition.list_map ?f ?xs _ =>
    eapply Proper_list_map
  | H : WeakestPrecondition.cmd ?call ?c ?t ?m ?l _
    |- WeakestPrecondition.cmd ?call ?c ?t ?m ?l _ =>
    eapply Proper_cmd
  | H : WeakestPrecondition.cmd ?call ?c ?t ?m ?l _
    |- WeakestPrecondition.cmd ?call ?c ?t ?m ?l _ =>
    eapply Proper_cmd
  end; [ repeat intro .. | eassumption ]; cbv beta in *.

Ltac propers :=
  propers_step;
  match goal with
  | _ => solve [propers]
  | H : _ |- _ => apply H; solve [eauto]
  | _ => congruence
  end.

Ltac peel_expr :=
  progress (
      repeat
        progress match goal with
                 | H : WeakestPrecondition.expr ?m ?l ?e _ |- _ =>
                   match goal with
                   | |- WeakestPrecondition.expr m l e _ => idtac
                   | _ =>
                     apply expr_sound with (mc:=MetricLogging.EmptyMetricLog) in H;
                     destruct H as [? [_ [_ H] ] ]
                   end
                 end).

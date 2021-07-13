Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.

Import API.Compilers.

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
              | H:existT _ _ _ = existT _ _ _
                |- _ =>
                apply Eqdep_dec.inj_pair2_eq_dec in H;
                [ | apply base.type.type_eq_dec with (eq_base_type:=Compilers.base_beq);
                    intros *; apply Bool.reflect_iff;
                    solve [auto using Compilers.reflect_base_beq] ]
              end ]); cleanup.

Ltac sepsimpl_step' :=
  match goal with
  | |- sep (emp _) _ _ => apply sep_emp_l
  | |- sep _ (emp _) _ => apply sep_emp_r
  | |- sep (fun m => emp _ m) _ _ => apply sep_emp_l
  | |- sep _ (fun m => emp _ m) _ => apply sep_emp_r
  | |- sep (Lift1Prop.ex1 _) _ _ => apply sep_ex1_l
  | |- sep _ (Lift1Prop.ex1 _) _ => apply sep_ex1_r
  | |- sep (fun m => Lift1Prop.ex1 _ m) _ _ => apply sep_ex1_l
  | |- sep _ (fun m => Lift1Prop.ex1 _ m) _ => apply sep_ex1_r
  | |- emp _ _ => split; [ congruence | ]
  end.

Ltac sepsimpl_step_no_comm :=
  match goal with
  | _ => sepsimpl_step'
  | |- sep (sep _ _) _ _ => apply sep_assoc; sepsimpl_step'
  | |- sep (sep (sep _ _) _) _ _ =>
    apply sep_assoc; apply sep_assoc; sepsimpl_step'
  end.

Ltac sepsimpl_step :=
  match goal with
  | _ => sepsimpl_step_no_comm
  | |- sep _ (sep _ _) _ =>
    apply sep_comm, sep_assoc; sepsimpl_step_no_comm
  | |- sep _ _ _ => apply sep_comm; sepsimpl_step_no_comm
  end.

Ltac sepsimpl_in H :=
  match type of H with
  | sep (emp _) _ _ =>
    eapply sep_emp_l in H
  | sep _ (emp _) _ =>
    eapply sep_emp_r in H
  | sep (fun m => emp _ m) _ _ =>
    eapply sep_emp_l in H
  | sep _ (fun m => emp _ m) _ =>
    eapply sep_emp_r in H
  | sep (Lift1Prop.ex1 _) _ _ =>
    eapply sep_ex1_l in H; destruct H
  | sep _ (Lift1Prop.ex1 _) _ =>
    eapply sep_ex1_r in H; destruct H
  | sep (fun m => Lift1Prop.ex1 _ m) _ _ =>
    eapply sep_ex1_l in H; destruct H
  | sep _ (fun m => Lift1Prop.ex1 _ m) _ =>
    eapply sep_ex1_r in H; destruct H
  | sep _ _ map.empty =>
    apply sep_empty_iff in H
  end.

Ltac sepsimpl_hyps_step_no_comm :=
  match goal with
  | H : False |- _ => tauto
  | H : emp _ _ |- _ => cbv [emp] in H; destruct H
  | H : Lift1Prop.ex1 _ _ |- _ => destruct H
  | H : sep (sep ?p ?q) _ _ |- _ =>
    eapply (sep_assoc p q) in H; sepsimpl_in H
  | H : sep (sep (sep ?p ?q) ?r) _ _ |- _ =>
    eapply (sep_assoc (sep p q) r) in H;
    eapply (sep_assoc p q) in H;
    sepsimpl_in H
  | H : sep _ _ _ |- _ => sepsimpl_in H
  end.

Ltac sepsimpl_hyps_step :=
  match goal with
  | _ => sepsimpl_hyps_step_no_comm
  | H : sep _ (sep ?p ?q) _ |- _ =>
    (* reverse order and try simplifying again *)
    eapply sep_comm, (sep_assoc p q) in H;
    sepsimpl_hyps_step_no_comm
  end.

Ltac sepsimpl_hyps :=
  repeat first [ progress cleanup
               | progress sepsimpl_hyps_step ].

Ltac sepsimpl :=
  repeat first [ progress cleanup
               | match goal with |- _ /\ _ => split end
               | progress sepsimpl_step
               | progress sepsimpl_hyps_step ].

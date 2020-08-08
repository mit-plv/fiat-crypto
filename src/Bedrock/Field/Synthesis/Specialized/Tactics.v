Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Operation.

Ltac clear_old_seps :=
  lazymatch goal with
  | H:sep _ _ ?mem |- context [?mem] =>
    repeat
      match goal with
      | H':sep _ _ ?m |- _ => assert_fails unify m mem; clear H'
      end
  end.

(* first step of straightline is inlined here so we can do a [change]
   instead of [replace] *)
Ltac straightline_init_with_change :=
  match goal with
  | |- program_logic_goal_for ?f _ =>
    enter f; cbv zeta; intros;
    WeakestPrecondition.unfold1_call_goal;
    (cbv beta match delta [WeakestPrecondition.call_body]);
    lazymatch goal with
    | |- if ?test then ?T else _ =>
      (* this change is a replace in the original straightline, but that hangs for
    unclear reasons *)
      change test with true; change_no_check T
    end;
    (cbv beta match delta [WeakestPrecondition.func])
  end.

Ltac post_call :=
  repeat straightline;
  lazymatch goal with
  | |- context [ WeakestPrecondition.cmd ] => clear_old_seps
  | _ => idtac
  end; sepsimpl_hyps.

Ltac do_call :=
  straightline_call; [ sepsimpl .. | ];
  (* do ecancel_assumption before any other preconditions
     to fill in evars *)
  lazymatch goal with
  | |- sep _ _ _ => ecancel_assumption
  | _ => idtac
  end.

Ltac handle_call := do_call; [ .. | post_call ].

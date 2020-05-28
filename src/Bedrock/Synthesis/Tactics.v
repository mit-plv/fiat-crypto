Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Tactics.Tactics.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Interfaces.Operation.

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
  lazymatch goal with
  | |- context [WeakestPrecondition.cmd] =>
    clear_old_seps
  | _ => idtac
  end;
  let Hpost := lazymatch goal with
                 H : postcondition _ _ _ |- _ => H end in
  autounfold with defs in Hpost;
  cbn [fst snd postcondition] in Hpost;
  cleanup; subst.

Ltac do_call precondition_t length_t :=
  straightline_call; sepsimpl;
  (* do ecancel_assumption first to fill in evars *)
  lazymatch goal with
  | |- sep _ _ _ => ecancel_assumption
  | _ => idtac
  end;
  (* simplify preconditions *)
  lazymatch goal with
  | |- precondition _ _ =>
    autounfold with defs; cbn [fst snd precondition];
    ssplit; precondition_t
  | |- context [length] => length_t
  | _ => idtac
  end.

Ltac handle_call precondition_t length_t :=
  do_call precondition_t length_t; post_call.

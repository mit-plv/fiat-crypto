Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Bedrock.Parameters.Defaults.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Interfaces.Operation.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.Examples.X25519_64.
Require Import Crypto.COperationSpecifications.
Require Import bedrock2.Semantics.
Import Types ListNotations.
Local Open Scope Z_scope.

Existing Instances Defaults64.default_parameters names curve25519_bedrock2.
Local Open Scope string_scope.
Local Coercion name_of_func (f : bedrock_func) := fst f.

(* Notations to make spec more readable *)
Local Notation M := (X25519_64.s - Associational.eval X25519_64.c).
Local Notation eval :=
  (Positional.eval
              (Interfaces.UnsaturatedSolinas.weight
                 X25519_64.n X25519_64.s X25519_64.c)
              X25519_64.n).
Local Notation loose_bounds :=
  (UnsaturatedSolinas.loose_bounds X25519_64.n X25519_64.s X25519_64.c).
Local Notation tight_bounds :=
  (UnsaturatedSolinas.tight_bounds X25519_64.n X25519_64.s X25519_64.c).
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

(* test function; computes x * y * y *)
Definition mul_twice : bedrock_func :=
  let x := "x" in
  let y := "y" in
  let xy := "xy" in
  let out := "out" in
  ("mul_twice",
   ([x; y; out], [],
    (cmd.seq
       (cmd.call [] "curve25519_carry_mul" [expr.var x; expr.var y; expr.var out])
       (cmd.call [] "curve25519_carry_mul" [expr.var out; expr.var y; expr.var out])))).

Instance spec_of_mul_twice : spec_of mul_twice :=
  fun functions =>
    forall x y old_out px py pout t m
           (R : Interface.map.rep
                  (map:=Semantics.mem) -> Prop),
      let xz := map word.unsigned x in
      let yz := map word.unsigned y in
      list_Z_bounded_by loose_bounds xz ->
      list_Z_bounded_by loose_bounds yz ->
      length old_out = X25519_64.n ->
      (Bignum px x * Bignum py y * Bignum pout old_out * R)%sep m ->
      WeakestPrecondition.call
        (p:=Types.semantics)
        functions mul_twice t m
        (px :: py :: pout :: nil)
        (fun t' m' rets =>
           t = t' /\
           rets = []%list /\
           exists out,
             let outz := map word.unsigned out in
             eval outz mod M
             = (eval xz * eval yz * eval yz) mod M
             /\ list_Z_bounded_by tight_bounds outz
             /\ (Bignum px x * Bignum py y * Bignum pout out * R)%sep m').

Instance spec_of_curve25519_carry_mul :
  spec_of "curve25519_carry_mul" := spec_of_carry_mul.

Ltac prove_bounds :=
  match goal with
  | H : list_Z_bounded_by tight_bounds ?x
    |- list_Z_bounded_by loose_bounds ?x =>
    apply UnsaturatedSolinas.relax_correct; apply H
  | H : list_Z_bounded_by ?b ?x |- list_Z_bounded_by ?b ?x =>
    apply H
  end.
Ltac prove_length :=
  match goal with
  | |- length _ = _ => rewrite ?map_length; solve [eauto]
  | |- length _ = X25519_64.n =>
    apply bounded_by_loose_bounds_length
      with (s:=X25519_64.s) (c:=X25519_64.c); prove_bounds
  end.

Lemma mul_twice_correct :
  program_logic_goal_for_function! mul_twice.
Proof.
  (* first step of straightline is inlined here so we can do a [change]
       instead of [replace] *)
  enter mul_twice. cbv zeta. intros.
  WeakestPrecondition.unfold1_call_goal.
  (cbv beta match delta [WeakestPrecondition.call_body]).
  lazymatch goal with
  | |- if ?test then ?T else _ =>
    (* this change is a replace in the original straightline, but that hangs
      here for some reason *)
    change test with true; change_no_check T
  end.
  (cbv beta match delta [WeakestPrecondition.func]).

  repeat straightline.
  straightline_call; sepsimpl;
    [ try ecancel_assumption .. | ].
  all: try prove_bounds.
  all: try prove_length.

  (* clean up post-call guarantees *)
  let Hpost := lazymatch goal with
                 H : postcondition _ _ _ |- _ => H end in
  cbn [fst snd postcondition
           Interfaces.UnsaturatedSolinas.carry_mul] in Hpost;
  repeat specialize (Hpost ltac:(prove_bounds)).
  cleanup.

  repeat straightline.
  straightline_call; sepsimpl;
    [ try ecancel_assumption .. | ].
  all:try prove_bounds.
  all:try prove_length.

  (* clean up post-call guarantees *)
  let Hpost := lazymatch goal with
                 H : postcondition _ _ _ |- _ => H end in
  cbn [fst snd postcondition
           Interfaces.UnsaturatedSolinas.carry_mul] in Hpost;
  repeat specialize (Hpost ltac:(prove_bounds)).
  cleanup.

  repeat straightline.

  repeat split; try reflexivity.
  sepsimpl_hyps.
  eexists; sepsimpl;
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end.
  all: try prove_bounds.
  repeat match goal with
         | H : eval _ mod _ = (eval _ * eval _) mod _ |- _ =>
           rewrite H
         | _ => progress Modulo.push_Zmod
         end.
  reflexivity.
Qed.

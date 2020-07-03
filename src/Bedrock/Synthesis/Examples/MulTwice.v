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
Require Import Crypto.Bedrock.Field.Bignum.
Require Import Crypto.Bedrock.Field.Operation.
Require Import Crypto.Bedrock.Field.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.Tactics.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.Examples.X25519_64.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import bedrock2.Semantics.
Import ListNotations.
Local Open Scope Z_scope.

Existing Instances
         Defaults64.default_parameters names
         curve25519_bedrock2_funcs curve25519_bedrock2_specs
         curve25519_bedrock2_correctness.
Local Open Scope string_scope.
Local Coercion name_of_func (f : bedrock_func) := fst f.

(* Notations to make spec more readable *)
Local Notation n := X25519_64.n.
Local Notation s := X25519_64.s.
Local Notation c := X25519_64.c.
Local Notation machine_wordsize := X25519_64.machine_wordsize.
Local Notation M := (UnsaturatedSolinas.m s c).
Local Notation weight :=
  (ModOps.weight (QArith_base.Qnum
                    (UnsaturatedSolinas.limbwidth n s c))
                 (Z.pos (QArith_base.Qden
                           (UnsaturatedSolinas.limbwidth n s c)))).
Local Notation eval := (Positional.eval weight n).
Local Notation loose_bounds := (UnsaturatedSolinasHeuristics.loose_bounds n s c).
Local Notation tight_bounds := (UnsaturatedSolinasHeuristics.tight_bounds n s c).
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

(* test function; computes x * y * y *)
Definition mul_twice : bedrock_func :=
  let x := "x" in
  let y := "y" in
  let xy := "xy" in
  let out := "out" in
  ("mul_twice",
   ([out; x; y], [],
    (cmd.seq
       (cmd.call [] "curve25519_carry_mul" [expr.var out; expr.var x; expr.var y])
       (cmd.call [] "curve25519_carry_mul" [expr.var out; expr.var out; expr.var y])))).

(* TODO: update to have three separation-logic preconditions, one for each input
   and one for output *)
Instance spec_of_mul_twice : spec_of mul_twice :=
  fun functions =>
    forall x y old_out px py pout t m
           (R : Interface.map.rep
                  (map:=Semantics.mem) -> Prop),
      let xz := map word.unsigned x in
      let yz := map word.unsigned y in
      list_Z_bounded_by loose_bounds xz ->
      list_Z_bounded_by loose_bounds yz ->
      (Bignum n px x * Bignum n py y * Bignum n pout old_out * R)%sep m ->
      WeakestPrecondition.call
        (p:=Types.semantics)
        functions mul_twice t m
        (pout :: px :: py ::  nil)
        (fun t' m' rets =>
           t = t' /\
           rets = []%list /\
           exists out,
             let outz := map word.unsigned out in
             eval outz mod M
             = (eval xz * eval yz * eval yz) mod M
             /\ list_Z_bounded_by tight_bounds outz
             /\ (Bignum n px x * Bignum n py y
                 * Bignum n pout out * R)%sep m').

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
  | |- length _ = n =>
    apply bounded_by_loose_bounds_length
      with (s:=s) (c:=c); prove_bounds
  end.
Ltac prove_preconditions :=
  lazymatch goal with
  | |- length _ = _ => prove_length
  | |- list_Z_bounded_by _ _ => prove_bounds
  end.

Lemma mul_twice_correct :
  program_logic_goal_for_function! mul_twice.
Proof.
  straightline_init_with_change.

  repeat straightline.
  handle_call; [ prove_preconditions .. | ].
  repeat straightline.
  handle_call; [ prove_preconditions .. | ].

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

Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Array.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Bedrock.Parameters.Defaults.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Interfaces.Operation.
Require Import Crypto.Bedrock.Interfaces.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.Tactics.
Require Import Crypto.Bedrock.Synthesis.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Synthesis.Examples.X25519_64.
Require Import Crypto.COperationSpecifications.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Import bedrock2.Semantics.
Import Types ListNotations.
Local Open Scope Z_scope.

Existing Instances
         Defaults64.default_parameters names
         curve25519_bedrock2_funcs curve25519_bedrock2_specs
         curve25519_bedrock2_correctness.
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
  (UnsaturatedSolinasHeuristics.loose_bounds X25519_64.n X25519_64.s X25519_64.c).
Local Notation tight_bounds :=
  (UnsaturatedSolinasHeuristics.tight_bounds X25519_64.n X25519_64.s X25519_64.c).
Local Notation n_bytes :=
  (UnsaturatedSolinas.n_bytes X25519_64.n X25519_64.s X25519_64.c).
Local Notation prime_bytes_bounds :=
  (map (fun v : Z => Some {| ZRange.lower := 0; ZRange.upper := v |})
       (Positional.encode_no_reduce
          (ModOps.weight 8 1) n_bytes (X25519_64.s - 1))).
Local Infix "*" := sep : sep_scope.
Delimit Scope sep_scope with sep.

Definition encode_decode : bedrock_func :=
  let x := "x" in
  let tmp := "tmp" in
  ("encode_decode",
   ([x; tmp], [],
    (cmd.seq
       (cmd.call [] "curve25519_to_bytes" [expr.var x; expr.var tmp])
       (cmd.call [] "curve25519_from_bytes" [expr.var tmp; expr.var x])))).

Instance spec_of_encode_decode : spec_of encode_decode :=
  fun functions =>
    forall x old_tmp px ptmp t m R,
      let xz := map word.unsigned x in
      list_Z_bounded_by tight_bounds xz ->
      length old_tmp = n_bytes ->
      (Bignum px x * EncodedBignum ptmp old_tmp * R)%sep m ->
      WeakestPrecondition.call
        functions encode_decode t m
        (px :: ptmp :: nil)
        (fun t' m' rets =>
           t = t' /\
           rets = []%list /\
           exists out tmp',
             let outz := map word.unsigned out in
             eval outz mod M = eval xz mod M
             /\ list_Z_bounded_by tight_bounds outz
             /\ length tmp' = n_bytes
             /\ (Bignum px out * EncodedBignum ptmp tmp' * R)%sep m').

(* TODO: currently this extra step is required so the literal string isn't
  hidden *)
Instance spec_of_curve25519_to_bytes :
  spec_of "curve25519_to_bytes" := spec_of_to_bytes.
Instance spec_of_curve25519_from_bytes :
  spec_of "curve25519_from_bytes" := spec_of_from_bytes.

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
  | H : map Byte.byte.unsigned ?x = Partition.partition _ _ _
    |- length ?x = n_bytes =>
    erewrite <-map_length; erewrite H;
    rewrite length_partition; reflexivity
  end.
Ltac prove_preconditions :=
  lazymatch goal with
  | |- length _ = _ => prove_length
  | |- list_Z_bounded_by _ _ => prove_bounds
  end.

(* TODO: need to replace encode_no_reduce with partition (lingering technical
   debt); then this proof is very easy *)
Lemma bounded_by_partition x :
  0 <= x < M ->
  list_Z_bounded_by
    prime_bytes_bounds (Partition.partition (ModOps.weight 8 1) n_bytes x).
Admitted.

Lemma encode_decode_correct :
  program_logic_goal_for_function! encode_decode.
Proof.
  straightline_init_with_change.

  repeat straightline.
  handle_call; [ prove_preconditions .. | ].
  repeat match goal with
           H : context [Freeze.bytes_n ?a ?b ?c] |- _ =>
           change (Freeze.bytes_n a b c) with n_bytes in H
         end.

  (* to_bytes doesn't explicitly mention bounds in the postcondition, so we need
     to extract them *)
  lazymatch goal with
    H : ?out = Partition.partition _ _ _ |- _ =>
    assert (list_Z_bounded_by prime_bytes_bounds out)
      by (rewrite H; apply bounded_by_partition;
          apply Z.mod_pos_bound; reflexivity)
  end.

  repeat straightline.
  handle_call; [ prove_preconditions .. | ].
  repeat match goal with
           H : context [Freeze.bytes_n ?a ?b ?c] |- _ =>
           change (Freeze.bytes_n a b c) with n_bytes in H
         end.

  repeat split; try reflexivity.
  sepsimpl_hyps.
  do 2 eexists; sepsimpl;
    lazymatch goal with
    | |- sep _ _ _ => ecancel_assumption
    | _ => idtac
    end.
  all: try prove_bounds.
  all: try prove_length.

  repeat match goal with
         | H : eval _ mod M = _ |- _ => rewrite H
         | H : map Byte.byte.unsigned _ = _ |- _ => rewrite H
         end.
  rewrite eval_partition
    by (apply UniformWeight.uwprops; lia).
  match goal with
    |- context [(((eval ?a) mod ?m1) mod ?m2) mod ?m1] =>
    let x1 := (eval vm_compute in m1) in
    let x2 := (eval vm_compute in m2) in
    change m2 with x2; change m1 with x1;
      pose proof (Z.mod_pos_bound (eval a) x1 ltac:(lia));
      rewrite (Z.mod_small _ x2) by lia
  end.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

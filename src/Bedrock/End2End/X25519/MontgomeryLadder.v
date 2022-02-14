Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.MMIO.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.AdditionChains.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.CSwap.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Local Open Scope string_scope.
Import ListNotations.

Definition ladderstep : func :=
  Eval vm_compute in
    (ladderstep_body
      (field_parameters:=field_parameters)
      (field_representaton:=field_representation n s c)).

Definition montladder : func :=
  Eval vm_compute in
    (montladder_body (Z.to_nat (Z.log2_up Curve25519.l))
      (field_parameters:=field_parameters)
      (field_representaton:=field_representation n s c)).

(* TODO: replace these stubs with real implementations. *)
Definition felem_cswap : func :=
  let mask := "mask" in
  let ptr1 := "ptr1" in
  let ptr2 := "ptr2" in
  let tmp1 := "tmp1" in
  let tmp2 := "tmp2" in
  (felem_cswap, ([mask; ptr1; ptr2], [],
   cmd.cond (expr.var mask)
     (cmd.seq
       (cmd.set tmp1 (expr.load access_size.word (expr.var ptr1)))
       (cmd.seq
         (cmd.set tmp2 (expr.load access_size.word (expr.var ptr2)))
         (cmd.seq
           (cmd.store access_size.word (expr.var ptr2) (expr.var tmp1))
           (cmd.store access_size.word (expr.var ptr1) (expr.var tmp2)))))
    (cmd.skip))).
Definition fe25519_copy : func :=
  let pout := "pout" in
  let px := "px" in
  ("fe25519_copy", ([pout; px], [],
   cmd.set pout (expr.var px))).
Definition fe25519_small_literal : func :=
  let pout := "pout" in
  let x := "x" in
  ("fe25519_small_literal", ([pout; x], [],
    cmd.store access_size.word (expr.var pout) (expr.var x))).

Definition funcs : list func :=
  [
    fe25519_to_bytes;
    fe25519_from_bytes;
    montladder;
    felem_cswap;
    fe25519_copy;
    fe25519_small_literal;
    fe25519_inv(word:=BasicC32Semantics.word)(field_parameters:=field_parameters);
    ladderstep;
    fe25519_mul;
    fe25519_add;
    fe25519_sub;
    fe25519_square;
    fe25519_scmula24 ].

Compute
  match compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list funcs) with
  Success ((x, z), y) => (length x, z) | _ => (O, map.empty) end.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import compiler.MMIO.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.ScalarMult.ECC.
Require Import Crypto.Bedrock.Group.ScalarMult.LadderStep.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.Specs.ScalarField.
Local Open Scope string_scope.
Import ListNotations.

Print ScalarFieldParameters.

(* TODO: move to a separate file? *)
Local Instance scalar_field_parameters : ScalarFieldParameters :=
  {  L_pos := 7237005577332262213973186563042994240857116359379907606001950938285454250989%positive;
     scalarbits := 253;
     sctestbit := "sc25519_testbit";
  }.

Definition ladderstep : func :=
  Eval vm_compute in
    (ladderstep_body
      (field_parameters:=field_parameters)
      (field_representaton:=field_representation n s c)).

Definition montladder : func :=
  Eval vm_compute in
    (montladder_body
      (field_parameters:=field_parameters)
      (field_representaton:=field_representation n s c)
      (scalar_field_parameters:=scalar_field_parameters)).

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
Definition sc25519_testbit : func :=
  let px := "px" in
  let wi := "wi" in
  let r := "r" in
  let tmp := "tmp" in
  ("sc25519_testbit", ([px; wi], [r],
  cmd.seq
    (cmd.set tmp (expr.op bopname.add (expr.var px) (expr.var wi))) 
    (cmd.set r (expr.literal 0)))).
Definition fe25519_inv : func.
  let r := eval vm_compute in
    (exp_large_body (word:=BasicC64Semantics.word) (field_parameters:=field_parameters)) in
  match r with
  | (?bad_name, ?f) => exact ("fe25519_inv", f)
  end.
Defined.

Check montladder_correct.

Definition funcs : list func :=
  [
    fe25519_to_bytes;
    fe25519_from_bytes;
    montladder;
    felem_cswap;
    fe25519_copy;
    fe25519_small_literal;
    sc25519_testbit ;
    fe25519_inv;
    ladderstep;
    fe25519_mul;
    fe25519_add;
    fe25519_sub;
    fe25519_square;
    fe25519_scmula24 ].

Compute
  match compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list (skipn 3 funcs)) with
  Some ((x, z), y) => (length x, z) | _ => (O, map.empty) end.
(*
= (4977%nat,
       {|
         SortedList.value :=
           [("exp_57896044618658097711785492504343953926634992332820282019728792003956564819951",
            (2%nat, 0%nat, 19628)); ("fe25519_add", (3%nat, 0%nat, 18904));
           ("fe25519_copy", (2%nat, 0%nat, 18844));
           ("fe25519_mul", (3%nat, 0%nat, 8476));
           ("fe25519_scmula24", (2%nat, 0%nat, 7088));
           ("fe25519_small_literal", (2%nat, 0%nat, 7028));
           ("fe25519_square", (2%nat, 0%nat, 1428));
           ("fe25519_sub", (3%nat, 0%nat, 576));
           ("felem_cswap", (3%nat, 0%nat, 476));
           ("ladderstep", (5%nat, 0%nat, 68));
           ("sc25519_testbit", (2%nat, 1%nat, 0))];
         SortedList._value_ok := eq_refl
       |})
     : nat * map.rep
*)
Compute
  match compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list (skipn 2 funcs)) with
  Some ((x, z), y) => (length x, z) | _ => (O, map.empty) end.
(*
= (0%nat, {| SortedList.value := []; SortedList._value_ok := eq_refl |})
     : nat * map.rep
*)
Require Import bedrock2.NotationsInConstr. Import bedrock2.Syntax.Coercions.
Compute nth_error funcs 2.
(* = Some ("montladder", (["OUT"; "K"; "U"], [],
         cmd.stackalloc "X1" 80
           (cmd.call [] "fe25519_small_literal"
              [expr.var "X1"; (uintptr_t)1ULL%bedrock_expr];;
            cmd.stackalloc "Z1" 80
              (cmd.call [] "fe25519_small_literal"
                 [expr.var "Z1"; (uintptr_t)0ULL%bedrock_expr];;
               cmd.stackalloc "X2" 80
                 (cmd.call [] "fe25519_copy" [expr.var "X2"; expr.var "U"];;
                  cmd.stackalloc "Z2" 80
                    (cmd.call [] "fe25519_small_literal"
                       [expr.var "Z2"; (uintptr_t)1ULL%bedrock_expr];;
                     "swap" = (uintptr_t)0ULL;;
                     "count" = (uintptr_t)253ULL;;
                     "_gs_i0" = (uintptr_t)253ULL;;
                     (while ((uintptr_t)0ULL < expr.var "_gs_i0") {{
                        "_gs_i0" = expr.var "_gs_i0" - (uintptr_t)1ULL;;
                        cmd.call ["s_i"] "sc25519_testbit"
                          [expr.var "K"; expr.var "_gs_i0"];;
                        "swap" = expr.var "swap" .^ expr.var "s_i";;
                        cmd.call [] "felem_cswap"
                          [expr.var "swap"; expr.var "X1"; expr.var "X2"];;
                        cmd.call [] "felem_cswap"
                          [expr.var "swap"; expr.var "Z1"; expr.var "Z2"];;
                        cmd.call [] "ladderstep"
                          [expr.var "U"; expr.var "X1"; 
                          expr.var "Z1"; expr.var "X2"; 
                          expr.var "Z2"];;
                        "swap" = expr.var "s_i";;
                        cmd.unset "s_i"
                      }});;
                     cmd.call [] "felem_cswap"
                       [expr.var "swap"; expr.var "X1"; expr.var "X2"];;
                     cmd.call [] "felem_cswap"
                       [expr.var "swap"; expr.var "Z1"; expr.var "Z2"];;
                     cmd.call [] "fe25519_inv"
                       [expr.var "OUT"; expr.var "Z1"];;
                     cmd.call [] "fe25519_mul"
                       [expr.var "OUT"; expr.var "X1"; expr.var "OUT"]))))))
*)

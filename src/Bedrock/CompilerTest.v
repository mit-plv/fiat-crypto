Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.derive.Derive.
Require Import Coq.Lists.List.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Import Crypto.CStringification.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import Crypto.Bedrock.Compiler.
Require Import bedrock2.Syntax.
Require bedrock2.NotationsCustomEntry.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.

Import
  Language.Compilers
  CStringification.Compilers.

Import Language.Compilers.defaults.

Import Associational Positional.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

(* taken from SlowPrimeSynthesisExamples.v *)
Module debugging_remove_mul_split.
  Section __.
    Context (n : nat := 5%nat)
            (s : Z := 2^255)
            (c : list (Z * Z) := [(1,19)])
            (machine_wordsize : Z := 64)
            (should_split_mul : should_split_mul_opt := true)
            (widen_carry : widen_carry_opt := true)
            (widen_bytes : widen_bytes_opt := true).

    Local Existing Instances should_split_mul widen_carry widen_bytes.

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

    Definition possible_values_of_machine_wordsize
      := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.

    Let possible_values := possible_values_of_machine_wordsize.

    Local Instance split_mul_to : split_mul_to_opt := split_mul_to_of_should_split_mul machine_wordsize possible_values.

    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition tight_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp base.type.Z)
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.


    Let limbwidth_num := Eval vm_compute in Qnum limbwidth.
    Let limbwidth_den := Eval vm_compute in QDen limbwidth.

    Set Printing Depth 100000.
    Local Open Scope string_scope.
    Local Notation "'uint64,uint64'" := (ident.Z_cast2
                                           (r[0 ~> 18446744073709551615]%zrange,
                                            r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
    Local Notation "'uint64'" := (ident.Z_cast r[0 ~> 18446744073709551615]%zrange) : expr_scope.
    Local Open Scope expr_scope.
    Local Open Scope core_scope.

    Definition mulmod_ : Pipeline.ErrorT (Expr _) :=
        Pipeline.BoundsPipeline
        false (* subst01 *)
        None (* fancy *)
        possible_values
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n idxs)) in
              exact r)
               (Some loose_bounds, (Some loose_bounds, tt))
               (Some tight_bounds).
    Definition mulmod := Eval compute in mulmod_.
(*     = ErrorT.Success
         (fun var : type -> Type =>
          λ x x0 : var (type.base (base.type.list (base.type.type_base base.type.Z))),
          expr_let x1 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x2 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x3 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[2]]))%expr_pat * ##19))))%expr_pat in
          expr_let x4 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[4]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[1]]))%expr_pat * ##19))))%expr_pat in
          expr_let x5 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x6 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x7 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[3]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[2]]))%expr_pat * ##19))))%expr_pat in
          expr_let x8 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[2]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x9 := ((#uint64,uint64)%expr @
                          ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                           ((#uint64)%expr @ ($x [[2]])) @
                           ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[3]]))%expr_pat * ##19))))%expr_pat in
          expr_let x10 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @
                            ((#uint64)%expr @ (((#uint64)%expr @ ($x0 [[4]]))%expr_pat * ##19))))%expr_pat in
          expr_let x11 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[4]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x12 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[3]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x13 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[3]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x14 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[2]])) @ ((#uint64)%expr @ ($x0 [[2]]))))%expr_pat in
          expr_let x15 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[2]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x16 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[2]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x17 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[3]]))))%expr_pat in
          expr_let x18 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[2]]))))%expr_pat in
          expr_let x19 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x20 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[1]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x21 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[4]]))))%expr_pat in
          expr_let x22 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[3]]))))%expr_pat in
          expr_let x23 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[2]]))))%expr_pat in
          expr_let x24 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[1]]))))%expr_pat in
          expr_let x25 := ((#uint64,uint64)%expr @
                           ((#ident.Z_mul_split)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ($x [[0]])) @ ((#uint64)%expr @ ($x0 [[0]]))))%expr_pat in
          expr_let x26 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x7)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x4))))%expr_pat in
          expr_let x27 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x26)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x7)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x4))))%expr_pat in
          expr_let x28 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x9)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x26))))%expr_pat in
          expr_let x29 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x28)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x9)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x27))))%expr_pat in
          expr_let x30 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x10)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x28))))%expr_pat in
          expr_let x31 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x30)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x10)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x29))))%expr_pat in
          expr_let x32 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x25)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x30))))%expr_pat in
          expr_let x33 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x32)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x25)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x31))))%expr_pat in
          expr_let x34 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x32))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @
                                 ((#uint64)%expr @ ((#ident.fst)%expr @ $x33)) @ ##13))%expr_pat))%expr_pat in
          expr_let x35 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x32))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x36 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x12)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x11))))%expr_pat in
          expr_let x37 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x36)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x12)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x11))))%expr_pat in
          expr_let x38 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x14)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x36))))%expr_pat in
          expr_let x39 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x38)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x14)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x37))))%expr_pat in
          expr_let x40 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x17)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x38))))%expr_pat in
          expr_let x41 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x40)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x17)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x39))))%expr_pat in
          expr_let x42 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x21)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x40))))%expr_pat in
          expr_let x43 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x42)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x21)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x41))))%expr_pat in
          expr_let x44 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x13)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x1))))%expr_pat in
          expr_let x45 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x44)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x13)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x1))))%expr_pat in
          expr_let x46 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x15)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x44))))%expr_pat in
          expr_let x47 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x46)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x15)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x45))))%expr_pat in
          expr_let x48 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x18)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x46))))%expr_pat in
          expr_let x49 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x48)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x18)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x47))))%expr_pat in
          expr_let x50 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x22)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x48))))%expr_pat in
          expr_let x51 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x50)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x22)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x49))))%expr_pat in
          expr_let x52 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x5)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x2))))%expr_pat in
          expr_let x53 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x52)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x5)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x2))))%expr_pat in
          expr_let x54 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x16)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x52))))%expr_pat in
          expr_let x55 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x54)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x16)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x53))))%expr_pat in
          expr_let x56 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x19)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x54))))%expr_pat in
          expr_let x57 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x56)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x19)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x55))))%expr_pat in
          expr_let x58 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x23)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x56))))%expr_pat in
          expr_let x59 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x58)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x23)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x57))))%expr_pat in
          expr_let x60 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x6)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x3))))%expr_pat in
          expr_let x61 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x60)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x6)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x3))))%expr_pat in
          expr_let x62 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x8)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x60))))%expr_pat in
          expr_let x63 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x62)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x8)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x61))))%expr_pat in
          expr_let x64 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x20)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x62))))%expr_pat in
          expr_let x65 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x64)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x20)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x63))))%expr_pat in
          expr_let x66 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x24)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x64))))%expr_pat in
          expr_let x67 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_with_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x66)) @
                            ((#uint64)%expr @ ((#ident.snd)%expr @ $x24)) @
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x65))))%expr_pat in
          expr_let x68 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x34) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x66))))%expr_pat in
          expr_let x69 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x68))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x67))%expr_pat))%expr_pat in
          expr_let x70 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x68))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x69) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x71 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x68))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x72 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x70) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x58))))%expr_pat in
          expr_let x73 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x72))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x59))%expr_pat))%expr_pat in
          expr_let x74 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x72))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x73) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x75 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x72))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x76 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x74) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x50))))%expr_pat in
          expr_let x77 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x76))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x51))%expr_pat))%expr_pat in
          expr_let x78 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x76))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x77) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x79 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x76))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x80 := ((#uint64,uint64)%expr @
                           ((#ident.Z_add_get_carry)%expr @ ##18446744073709551616 @
                            ((#uint64)%expr @ $x78) @ ((#uint64)%expr @ ((#ident.fst)%expr @ $x42))))%expr_pat in
          expr_let x81 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.snd)%expr @ $x80))%expr_pat +
                            ((#uint64)%expr @ ((#ident.fst)%expr @ $x43))%expr_pat))%expr_pat in
          expr_let x82 := ((#uint64)%expr @
                           (((#uint64)%expr @
                             (((#uint64)%expr @ ((#ident.fst)%expr @ $x80))%expr_pat >> ##51))%expr_pat
                            || ((#uint64)%expr @
                                ((#ident.Z_truncating_shiftl)%expr @ ##64 @ ((#uint64)%expr @ $x81) @
                                 ##13))%expr_pat))%expr_pat in
          expr_let x83 := ((#uint64)%expr @
                           (((#uint64)%expr @ ((#ident.fst)%expr @ $x80))%expr_pat &'
                            ##2251799813685247))%expr_pat in
          expr_let x84 := ((#uint64)%expr @ (((#uint64)%expr @ $x82)%expr_pat * ##19))%expr_pat in
          expr_let x85 := ((#uint64)%expr @
                           (((#uint64)%expr @ $x35)%expr_pat + ((#uint64)%expr @ $x84)%expr_pat))%expr_pat in
          expr_let x86 := ((#uint64)%expr @ (((#uint64)%expr @ $x85)%expr_pat >> ##51))%expr_pat in
          expr_let x87 := ((#uint64)%expr @ (((#uint64)%expr @ $x85)%expr_pat &' ##2251799813685247))%expr_pat in
          expr_let x88 := ((#uint64)%expr @
                           (((#uint64)%expr @ $x86)%expr_pat + ((#uint64)%expr @ $x71)%expr_pat))%expr_pat in
          expr_let x89 := ((#uint64)%expr @ (((#uint64)%expr @ $x88)%expr_pat >> ##51))%expr_pat in
          expr_let x90 := ((#uint64)%expr @ (((#uint64)%expr @ $x88)%expr_pat &' ##2251799813685247))%expr_pat in
          expr_let x91 := ((#uint64)%expr @
                           (((#uint64)%expr @ $x89)%expr_pat + ((#uint64)%expr @ $x75)%expr_pat))%expr_pat in
          [((#uint64)%expr @ $x87)%expr_pat; ((#uint64)%expr @ $x90)%expr_pat;
          ((#uint64)%expr @ $x91)%expr_pat; ((#uint64)%expr @ $x79)%expr_pat;
          ((#uint64)%expr @ $x83)%expr_pat])
     : Pipeline.ErrorT
         (Expr
            (type.base (base.type.list (base.type.type_base base.type.Z)) ->
             type.base (base.type.list (base.type.type_base base.type.Z)) ->
             type.base (base.type.list (base.type.type_base base.type.Z))))
 *)

    Import Coq.Strings.String. Local Open Scope string_scope.
    Let ERROR : Syntax.expr.expr := (Syntax.expr.var "ERROR"%string).
    Let nv : String.string -> String.string :=
      fun old_varname =>
        let old_num := List.nth_default ""%string (String.split "x" old_varname) 1 in
        let new_num := Decimal.decimal_string_of_Z (Decimal.Z_of_decimal_string old_num + 1) in
        String.append "x" new_num.
    Local Notation of_expr e := (@Compiler.of_expr BasicC64Semantics.parameters nv ERROR _ e "x0").

    Definition mulmod_bedrock : Syntax.cmd.cmd :=
      match mulmod with
      | ErrorT.Success e => snd (of_expr (e Compiler.var)
                                         (Syntax.expr.var "y0", (Syntax.expr.var "y1", tt))
                                         (fun _ _ => Syntax.expr.var "ret"))
      | ErrorT.Error _ => Syntax.cmd.skip
      end.

    Import NotationsCustomEntry.
    Eval compute in mulmod_bedrock.
  (* using bedrock_format.sh:
= bedrock_func_body
    : (((x0 = (load(y0 + 4) * (load(y1 + 4) * 19)));
        x1 = ((mulhuu(load(y0 + 4))(load(y1 + 4) * 19))));
       ((x2 = (load(y0 + 4) * (load(y1 + 3) * 19)));
        x3 = ((mulhuu(load(y0 + 4))(load(y1 + 3) * 19))));
       ((x4 = (load(y0 + 4) * (load(y1 + 2) * 19)));
        x5 = ((mulhuu(load(y0 + 4))(load(y1 + 2) * 19))));
       ((x6 = (load(y0 + 4) * (load(y1 + 1) * 19)));
        x7 = ((mulhuu(load(y0 + 4))(load(y1 + 1) * 19))));
       ((x8 = (load(y0 + 3) * (load(y1 + 4) * 19)));
        x9 = ((mulhuu(load(y0 + 3))(load(y1 + 4) * 19))));
       ((x10 = (load(y0 + 3) * (load(y1 + 3) * 19)));
        x11 = ((mulhuu(load(y0 + 3))(load(y1 + 3) * 19))));
       ((x12 = (load(y0 + 3) * (load(y1 + 2) * 19)));
        x13 = ((mulhuu(load(y0 + 3))(load(y1 + 2) * 19))));
       ((x14 = (load(y0 + 2) * (load(y1 + 4) * 19)));
        x15 = ((mulhuu(load(y0 + 2))(load(y1 + 4) * 19))));
       ((x16 = (load(y0 + 2) * (load(y1 + 3) * 19)));
        x17 = ((mulhuu(load(y0 + 2))(load(y1 + 3) * 19))));
       ((x18 = (load(y0 + 1) * (load(y1 + 4) * 19)));
        x19 = ((mulhuu(load(y0 + 1))(load(y1 + 4) * 19))));
       ((x20 = (load(y0 + 4) * load(y1 + 0)));
        x21 = ((mulhuu(load(y0 + 4))(load(y1 + 0)))));
       ((x22 = (load(y0 + 3) * load(y1 + 1)));
        x23 = ((mulhuu(load(y0 + 3))(load(y1 + 1)))));
       ((x24 = (load(y0 + 3) * load(y1 + 0)));
        x25 = ((mulhuu(load(y0 + 3))(load(y1 + 0)))));
       ((x26 = (load(y0 + 2) * load(y1 + 2)));
        x27 = ((mulhuu(load(y0 + 2))(load(y1 + 2)))));
       ((x28 = (load(y0 + 2) * load(y1 + 1)));
        x29 = ((mulhuu(load(y0 + 2))(load(y1 + 1)))));
       ((x30 = (load(y0 + 2) * load(y1 + 0)));
        x31 = ((mulhuu(load(y0 + 2))(load(y1 + 0)))));
       ((x32 = (load(y0 + 1) * load(y1 + 3)));
        x33 = ((mulhuu(load(y0 + 1))(load(y1 + 3)))));
       ((x34 = (load(y0 + 1) * load(y1 + 2)));
        x35 = ((mulhuu(load(y0 + 1))(load(y1 + 2)))));
       ((x36 = (load(y0 + 1) * load(y1 + 1)));
        x37 = ((mulhuu(load(y0 + 1))(load(y1 + 1)))));
       ((x38 = (load(y0 + 1) * load(y1 + 0)));
        x39 = ((mulhuu(load(y0 + 1))(load(y1 + 0)))));
       ((x40 = (load(y0 + 0) * load(y1 + 4)));
        x41 = ((mulhuu(load(y0 + 0))(load(y1 + 4)))));
       ((x42 = (load(y0 + 0) * load(y1 + 3)));
        x43 = ((mulhuu(load(y0 + 0))(load(y1 + 3)))));
       ((x44 = (load(y0 + 0) * load(y1 + 2)));
        x45 = ((mulhuu(load(y0 + 0))(load(y1 + 2)))));
       ((x46 = (load(y0 + 0) * load(y1 + 1)));
        x47 = ((mulhuu(load(y0 + 0))(load(y1 + 1)))));
       ((x48 = (load(y0 + 0) * load(y1 + 0)));
        x49 = ((mulhuu(load(y0 + 0))(load(y1 + 0)))));
       ((x50 = (x12 + x6)); x51 = (x50 < x12));
       ((((x52 = (x51 + x13)); x53 = (x52 < x13)); x52 = (x52 + x7));
        x53 = (x53 + (x52 < x7)));
       ((x54 = (x16 + x50)); x55 = (x54 < x16));
       ((((x56 = (x55 + x17)); x57 = (x56 < x17)); x56 = (x56 + x52));
        x57 = (x57 + (x56 < x52)));
       ((x58 = (x18 + x54)); x59 = (x58 < x18));
       ((((x60 = (x59 + x19)); x61 = (x60 < x19)); x60 = (x60 + x56));
        x61 = (x61 + (x60 < x56)));
       ((x62 = (x48 + x58)); x63 = (x62 < x48));
       ((((x64 = (x63 + x49)); x65 = (x64 < x49)); x64 = (x64 + x60));
        x65 = (x65 + (x64 < x60)));
       (x66 = (x62 >> 51 | x64 << 13)); (x67 = (x62 & 2251799813685247));
       ((x68 = (x22 + x20)); x69 = (x68 < x22));
       ((((x70 = (x69 + x23)); x71 = (x70 < x23)); x70 = (x70 + x21));
        x71 = (x71 + (x70 < x21)));
       ((x72 = (x26 + x68)); x73 = (x72 < x26));
       ((((x74 = (x73 + x27)); x75 = (x74 < x27)); x74 = (x74 + x70));
        x75 = (x75 + (x74 < x70)));
       ((x76 = (x32 + x72)); x77 = (x76 < x32));
       ((((x78 = (x77 + x33)); x79 = (x78 < x33)); x78 = (x78 + x74));
        x79 = (x79 + (x78 < x74)));
       ((x80 = (x40 + x76)); x81 = (x80 < x40));
       ((((x82 = (x81 + x41)); x83 = (x82 < x41)); x82 = (x82 + x78));
        x83 = (x83 + (x82 < x78)));
       ((x84 = (x24 + x0)); x85 = (x84 < x24));
       ((((x86 = (x85 + x25)); x87 = (x86 < x25)); x86 = (x86 + x1));
        x87 = (x87 + (x86 < x1)));
       ((x88 = (x28 + x84)); x89 = (x88 < x28));
       ((((x90 = (x89 + x29)); x91 = (x90 < x29)); x90 = (x90 + x86));
        x91 = (x91 + (x90 < x86)));
       ((x92 = (x34 + x88)); x93 = (x92 < x34));
       ((((x94 = (x93 + x35)); x95 = (x94 < x35)); x94 = (x94 + x90));
        x95 = (x95 + (x94 < x90)));
       ((x96 = (x42 + x92)); x97 = (x96 < x42));
       ((((x98 = (x97 + x43)); x99 = (x98 < x43)); x98 = (x98 + x94));
        x99 = (x99 + (x98 < x94)));
       ((x100 = (x8 + x2)); x101 = (x100 < x8));
       ((((x102 = (x101 + x9)); x103 = (x102 < x9)); x102 = (x102 + x3));
        x103 = (x103 + (x102 < x3)));
       ((x104 = (x30 + x100)); x105 = (x104 < x30));
       ((((x106 = (x105 + x31)); x107 = (x106 < x31)); x106 = (x106 + x102));
        x107 = (x107 + (x106 < x102)));
       ((x108 = (x36 + x104)); x109 = (x108 < x36));
       ((((x110 = (x109 + x37)); x111 = (x110 < x37)); x110 = (x110 + x106));
        x111 = (x111 + (x110 < x106)));
       ((x112 = (x44 + x108)); x113 = (x112 < x44));
       ((((x114 = (x113 + x45)); x115 = (x114 < x45)); x114 = (x114 + x110));
        x115 = (x115 + (x114 < x110)));
       ((x116 = (x10 + x4)); x117 = (x116 < x10));
       ((((x118 = (x117 + x11)); x119 = (x118 < x11)); x118 = (x118 + x5));
        x119 = (x119 + (x118 < x5)));
       ((x120 = (x14 + x116)); x121 = (x120 < x14));
       ((((x122 = (x121 + x15)); x123 = (x122 < x15)); x122 = (x122 + x118));
        x123 = (x123 + (x122 < x118)));
       ((x124 = (x38 + x120)); x125 = (x124 < x38));
       ((((x126 = (x125 + x39)); x127 = (x126 < x39)); x126 = (x126 + x122));
        x127 = (x127 + (x126 < x122)));
       ((x128 = (x46 + x124)); x129 = (x128 < x46));
       ((((x130 = (x129 + x47)); x131 = (x130 < x47)); x130 = (x130 + x126));
        x131 = (x131 + (x130 < x126)));
       ((x132 = (x66 + x128)); x133 = (x132 < x66)); (x134 = (x133 + x130));
       (x135 = (x132 >> 51 | x134 << 13)); (x136 = (x132 & 2251799813685247));
       ((x137 = (x135 + x112)); x138 = (x137 < x135)); (x139 = (x138 + x114));
       (x140 = (x137 >> 51 | x139 << 13)); (x141 = (x137 & 2251799813685247));
       ((x142 = (x140 + x96)); x143 = (x142 < x140)); (x144 = (x143 + x98));
       (x145 = (x142 >> 51 | x144 << 13)); (x146 = (x142 & 2251799813685247));
       ((x147 = (x145 + x80)); x148 = (x147 < x145)); (x149 = (x148 + x82));
       (x150 = (x147 >> 51 | x149 << 13)); (x151 = (x147 & 2251799813685247));
       (x152 = (x150 * 19)); (x153 = (x67 + x152)); (x154 = (x153 >> 51));
       (x155 = (x153 & 2251799813685247)); (x156 = (x154 + x136));
       (x157 = (x156 >> 51)); (x158 = (x156 & 2251799813685247));
       (x159 = (x157 + x141)); ((store(ret, x155)); x160 = (ret + 1));
       ((store(x160, x158)); x161 = (x160 + 1));
       ((store(x161, x159)); x162 = (x161 + 1));
       ((store(x162, x146)); x163 = (x162 + 1));
       ((store(x163, x151)); x164 = (x163 + 1));
       /*skip*/)
    : cmd
   *)
  End __.
End debugging_remove_mul_split.
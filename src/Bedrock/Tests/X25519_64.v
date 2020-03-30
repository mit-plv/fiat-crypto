Require Import Coq.ZArith.ZArith.
Require Import Coq.derive.Derive.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.BasicC64Semantics.
Require bedrock2.NotationsCustomEntry.

Import Language.Compilers.
Import Associational Positional.
Import Types.Notations Defaults.Notations.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope expr_scope.
Local Open Scope core_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

(* Curve25519 64-bit *)
Module X25519_64.
  Section __.
    Context (n : nat := 5%nat)
            (s : Z := 2^255)
            (c : list (Z * Z) := [(1,19)]%list).

    Let limbwidth := (Z.log2_up (s - Associational.eval c) / Z.of_nat n)%Q.
    Let idxs := (List.seq 0 n ++ [0; 1])%list%nat.

    Let prime_upperbound_list : list Z
      := encode_no_reduce (weight (Qnum limbwidth) (Qden limbwidth)) n (s-1).
    Let tight_upperbounds : list Z
      := List.map
           (fun v : Z => Qceiling (11/10 * v))
           prime_upperbound_list.
    Definition tight_bounds : list (ZRange.type.option.interp (type.base (base.type.type_base base.type.Z)))
      := List.map (fun u => Some r[0~>u]%zrange) tight_upperbounds.
    Definition loose_bounds : list (ZRange.type.option.interp (type.base (base.type.type_base base.type.Z)))
      := List.map (fun u => Some r[0 ~> 3*u]%zrange) tight_upperbounds.

    Definition limbwidth_num := Eval vm_compute in Qnum limbwidth.
    Definition limbwidth_den := Eval vm_compute in QDen limbwidth.

    Definition mulmod_ : Pipeline.ErrorT (Expr _) :=
      Pipeline.BoundsPipeline
        false (* subst01 *)
        None (* fancy *)
        possible_values
        ltac:(let r := Reify ((carry_mulmod limbwidth_num limbwidth_den s c n idxs)) in
              exact r)
               (Some loose_bounds, (Some loose_bounds, tt))
               (Some tight_bounds).
    Derive mulmod
           SuchThat (mulmod_ = ErrorT.Success mulmod)
           As mulmod_eq.
    Proof. vm_compute; reflexivity. Qed.

    Definition mulmod_bedrock : bedrock_func :=
      ("mulmod_bedrock",
       fst (translate_func mulmod
                           ("in0", ("in1", tt)) (* argument names *)
                           (n, (n, tt)) (* lengths for list arguments *)
                           "out0" (* return value name *))).

    Goal (error_free_cmd (snd (snd mulmod_bedrock)) = true).
    Proof. vm_compute. reflexivity. Qed.

    Import NotationsCustomEntry.
    Local Set Printing Width 150.
    (* Compute mulmod_bedrock. *)
    Redirect "Crypto.Bedrock.Tests.X25519_64.mulmod_bedrock" Compute mulmod_bedrock.
  End __.
End X25519_64.

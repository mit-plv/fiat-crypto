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
Require Import Crypto.Bedrock.Defaults64.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Func.
Require Import Crypto.Language.API.
Require Import Crypto.PushButtonSynthesis.UnsaturatedSolinas.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.ZUtil.ModInv.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.BasicC64Semantics.
Require bedrock2.NotationsCustomEntry.

Import Language.Compilers.
Import Associational Positional.
Import Types.Notations Defaults64.Notations.

Require Import Crypto.Util.Notations.
Import ListNotations. Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope expr_scope.
Local Open Scope core_scope.

Local Coercion Z.of_nat : nat >-> Z.
Local Coercion QArith_base.inject_Z : Z >-> Q.
Local Coercion Z.pos : positive >-> Z.

Existing Instances split_mul_to split_multiret_to.
Existing Instance Defaults64.default_parameters.

(* Curve25519 64-bit *)
Module X25519_64.
  Section __.
    Context (n : nat := 5%nat)
            (s : Z := 2^255)
            (c : list (Z * Z) := [(1,19)]%list).

    Derive mulmod
           SuchThat
           (carry_mul n s c machine_wordsize = ErrorT.Success mulmod)
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

    Derive addmod
           SuchThat
           (UnsaturatedSolinas.add
              n s c machine_wordsize = ErrorT.Success addmod)
           As addmod_eq.
    Proof. vm_compute; reflexivity. Qed.

    Definition addmod_bedrock : bedrock_func :=
      ("addmod_bedrock",
       fst (translate_func addmod
                           ("in0", ("in1", tt)) (* argument names *)
                           (n, (n, tt)) (* lengths for list arguments *)
                           "out0" (* return value name *))).

    Goal (error_free_cmd (snd (snd addmod_bedrock)) = true).
    Proof. vm_compute. reflexivity. Qed.

    Import NotationsCustomEntry.
    Local Set Printing Width 150.
    (* Compute mulmod_bedrock. *)
    Redirect "Crypto.Bedrock.Tests.X25519_64.mulmod_bedrock" Compute mulmod_bedrock.
  End __.
End X25519_64.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Defaults.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.VarnameGenerator.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Import API.Compilers.

Require Import Crypto.Util.Notations.
Import Types.Notations ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* Declares default parameters for the bedrock2 backend specific to systems with
a 64-bit word size. *)

Section Defaults_64.
  Definition machine_wordsize := 64.

  (* Define how to split mul/multi-return functions *)
  Definition possible_values
    := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.
  Instance no_select_size : no_select_size_opt :=
    no_select_size_of_no_select machine_wordsize.
  Instance split_mul_to : split_mul_to_opt :=
    split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Instance split_multiret_to : split_multiret_to_opt :=
    split_multiret_to_of_should_split_multiret machine_wordsize possible_values.
  Let wordsize_bytes := Eval vm_compute in (machine_wordsize / 8)%Z.
  Instance default_parameters : Types.parameters :=
    {| semantics := BasicC64Semantics.parameters;
       varname_gen := default_varname_gen;
       error := expr.var Defaults.ERROR;
       word_size_in_bytes := wordsize_bytes;
    |}.
  Instance default_parameters_ok : Types.ok.
  Proof.
    constructor.
    { exact BasicC64Semantics.parameters_ok. }
    { reflexivity. }
    { reflexivity. }
    { reflexivity. }
    { apply prefix_name_gen_unique. }
  Defined.
End Defaults_64.

Module Notations.
  Notation "'uint64,uint64'" := (ident.Literal
                                   (r[0 ~> 18446744073709551615]%zrange,
                                    r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
  Notation "'uint64'" :=
    (ident.Literal (t:=Compilers.zrange) r[0 ~> 18446744073709551615]%zrange) : expr_scope.
End Notations.

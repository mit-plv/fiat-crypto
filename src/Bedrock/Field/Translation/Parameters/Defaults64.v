Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Names.VarnameGenerator.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults.
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
  Global Instance no_select_size : no_select_size_opt :=
    no_select_size_of_no_select machine_wordsize.
  Global Instance split_mul_to : split_mul_to_opt :=
    split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Global Instance split_multiret_to : split_multiret_to_opt :=
    split_multiret_to_of_should_split_multiret machine_wordsize possible_values.
  Let wordsize_bytes := Eval vm_compute in (machine_wordsize / 8)%Z.
  Global Instance default_parameters : Types.parameters
    (word := BasicC64Semantics.word)
    (varname_gen := default_varname_gen)
    (error := expr.var Defaults.ERROR)
    := tt.
  Global Instance default_parameters_ok : Types.ok.
  Proof. constructor; try exact _; try apply prefix_name_gen_unique. Qed.
End Defaults_64.

Module Notations.
  Notation "'uint64,uint64'" := (ident.Literal
                                   (r[0 ~> 18446744073709551615]%zrange,
                                    r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
  Notation "'uint64'" :=
    (ident.Literal (t:=Compilers.zrange) r[0 ~> 18446744073709551615]%zrange) : expr_scope.
End Notations.

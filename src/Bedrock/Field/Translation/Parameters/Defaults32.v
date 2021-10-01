Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.BasicC32Semantics.
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
a 32-bit word size. *)

Section Defaults_32.
  Definition machine_wordsize := 32.

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
  Instance default_parameters : Types.parameters
    (word := BasicC32Semantics.word)
    (varname_gen := default_varname_gen)
    (error := expr.var Defaults.ERROR)
    := tt.
  Instance default_parameters_ok : Types.ok.
  Proof. constructor; try exact _; try apply prefix_name_gen_unique. Qed.
End Defaults_32.

Module Notations.
  Notation "'uint32,uint32'" := (ident.Literal
                                   (r[0 ~> 4294967295]%zrange,
                                    r[0 ~> 4294967295]%zrange)%core) : expr_scope.
  Notation "'uint32'" :=
    (ident.Literal (t:=Compilers.zrange) r[0 ~> 4294967295]%zrange) : expr_scope.
End Notations.

From Coq Require Import ZArith.
From Coq Require Import String.
From Coq Require Import List.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.FE310CSemantics.
Require Import coqutil.Word.Naive.
Require Import coqutil.Map.SortedListWord.
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

  Let wordsize_bytes := Eval vm_compute in (machine_wordsize / 8)%Z.

  Instance default_parameters : Types.parameters
    (word := Naive.word32)
    (mem:=SortedListWord.map _ _)
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

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.Language.API.
Require Import Crypto.Util.ZRange.
Import API.Compilers.

Require Import Crypto.Util.Notations.
Import Types.Notations ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* Declares default parameters for the bedrock2 backend and includes useful
   definitions/proofs that apply specifically to the defaults. Do NOT import
   this file unless you're prepared to have a bunch of global typeclass
   instances and notations declared for you. *)

Section Defaults.
  Definition machine_wordsize := 64.

  (* Reification/bounds pipeline options *)
  Global Existing Instance default_low_level_rewriter_method.
  (* Split multiplications into two outputs, not just one huge word *)
  Global Instance should_split_mul : should_split_mul_opt := true.
  (* For functions that return multiple values, split into two LetIns (this is
     because bedrock2 does not support multiple-sets, so they would have to be
     split anyway) *)
  Global Instance should_split_multiret : should_split_multiret_opt := true.
  (* Make all words 64-bit, even if they could be smaller *)
  Global Instance widen_carry : widen_carry_opt := true.
  Global Instance widen_bytes : widen_bytes_opt := true.
  (* Unsigned integers *)
  Global Instance only_signed : only_signed_opt := false.

  (* Define how to split mul/multi-return functions *)
  Definition possible_values
    := prefix_with_carry [machine_wordsize; 2 * machine_wordsize]%Z.
  Global Instance split_mul_to : split_mul_to_opt :=
    split_mul_to_of_should_split_mul machine_wordsize possible_values.
  Global Instance split_multiret_to : split_multiret_to_opt :=
    split_multiret_to_of_should_split_multiret machine_wordsize possible_values.

  (* bedrock2 backend parameters *)
  Global Existing Instances Types.rep.Z Types.rep.listZ_mem.
  Let wordsize_bytes := Eval vm_compute in (machine_wordsize / 8)%Z.
  Local Definition ERROR := "ERROR".
  Global Instance default_parameters : Types.parameters :=
    {| semantics := BasicC64Semantics.parameters;
       varname_gen := fun i => String.append "x" (Decimal.decimal_string_of_Z (Z.of_nat i));
       error := expr.var ERROR;
       word_size_in_bytes := wordsize_bytes;
    |}.

  Definition bedrock_func : Type :=
    string * (list string * list string * cmd.cmd).

  (* quick check to make sure the expression produced no errors *)
  Fixpoint error_free_expr (x : Syntax.expr) : bool :=
    match x with
    | expr.literal _ => true
    | expr.var x => negb (String.eqb x ERROR)
    | expr.load _ a => error_free_expr a
    | expr.op _ x y => (error_free_expr x && error_free_expr y)%bool
    end.
  Fixpoint error_free_cmd (x : cmd.cmd) : bool :=
    match x with
    | cmd.skip => true
    | cmd.unset _ => true 
    | cmd.set _ v => error_free_expr v
    | cmd.store _ a v =>
      (error_free_expr a && error_free_expr v)%bool
    | cmd.cond c t f =>
      (error_free_expr c && error_free_cmd t && error_free_cmd f)%bool
    | cmd.seq x y => (error_free_cmd x && error_free_cmd y)%bool
    | cmd.while c b => (error_free_expr c && error_free_cmd b)
    | cmd.call _ _ args => forallb error_free_expr args
    | cmd.interact _ _ args => forallb error_free_expr args
    end.
End Defaults.

Module Notations.
  Notation "'uint64,uint64'" := (ident.Literal
                                   (r[0 ~> 18446744073709551615]%zrange,
                                    r[0 ~> 18446744073709551615]%zrange)%core) : expr_scope.
  Notation "'uint64'" :=
    (ident.Literal (t:=Compilers.zrange) r[0 ~> 18446744073709551615]%zrange) : expr_scope.
End Notations.

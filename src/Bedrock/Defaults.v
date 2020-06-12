Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.String.

(* Declares default parameters for the bedrock2 backend that apply to all
   machine word sizes. Do NOT import this file unless you're prepared to have a
   bunch of global typeclass instances declared for you. *)

(* use in-memory lists; local ones are only used internally *)
Global Existing Instances Types.rep.Z Types.rep.listZ_mem.

(* Reification/bounds pipeline options *)
Global Existing Instance default_low_level_rewriter_method.
(* Split multiplications into two outputs, not just one huge word *)
Global Instance should_split_mul : should_split_mul_opt := true.
(* For functions that return multiple values, split into two LetIns (this is
     because bedrock2 does not support multiple-sets, so they would have to be
     split anyway) *)
Global Instance should_split_multiret : should_split_multiret_opt := true.
(* Make all words full-size, even if they could be smaller *)
Global Instance widen_carry : widen_carry_opt := true.
Global Instance widen_bytes : widen_bytes_opt := true.
(* Unsigned integers *)
Global Instance only_signed : only_signed_opt := false.
(* Rewrite selects into expressions that don't require cmov *)
Global Instance no_select : no_select_opt := true.
Global Instance tight_upperbound_fraction : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.

(* bedrock2 backend parameters *)
Global Existing Instances Types.rep.Z Types.rep.listZ_mem.

Local Definition ERROR := "ERROR"%string.

Section Defs.
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
End Defs.

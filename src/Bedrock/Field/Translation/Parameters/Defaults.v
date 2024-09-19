From Coq Require Import ZArith.
From Coq Require Import String.
From Coq Require Import List.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Syntax.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.BoundsPipeline.
Require Import Crypto.PushButtonSynthesis.Primitives.
Require Import Crypto.UnsaturatedSolinasHeuristics.
Require Crypto.Util.Strings.Decimal.
Require Import Crypto.Util.Strings.String.
Import ListNotations.

(* Declares default parameters for the bedrock2 backend that apply to all
   machine word sizes. Do NOT import this file unless you're prepared to have a
   bunch of global typeclass instances declared for you. *)

(* use in-memory lists; local ones are only used internally *)
Global Existing Instances Types.rep.Z Types.rep.listZ_mem.

Global Instance pipeline_opts : PipelineOptions :=
  let _ := default_PipelineOptions in
  {| (* Abstract interpretation options; currently only involving (>>) uint1 bounds, which is not relevant to bedrock2 *)
    absint_opts :=
    {| AbstractInterpretation.shiftr_avoid_uint1 := false (* we need to not avoid uint1 to pass bounds analysis tightness, for some reason? *) |}
  (* Split multiplications into two outputs, not just one huge word *)
  ; should_split_mul := true
  (* For functions that return multiple values, split into two LetIns (this is
     because bedrock2 does not support multiple-sets, so they would have to be
     split anyway) *)
  ; should_split_multiret := true
  (* Make all words full-size, even if they could be smaller *)
  ; widen_carry := true
  ; widen_bytes := true
  (* Unsigned integers *)
  ; only_signed := false
  (* Rewrite selects into expressions that don't require cmov *)
  ; no_select := true
  (* We don't handle value_barrier in bedrock2 *)
  ; unfold_value_barrier := true
  |}.

Global Instance tight_upperbound_fraction : tight_upperbound_fraction_opt := default_tight_upperbound_fraction.

(* bedrock2 backend parameters *)
Global Existing Instances Types.rep.Z Types.rep.listZ_mem.

Local Definition ERROR := "ERROR"%string.

Section Defs.
  (* quick check to make sure the expression produced no errors *)
  Fixpoint error_free_expr (x : Syntax.expr) : bool :=
    match x with
    | expr.literal _ => true
    | expr.var x => negb (String.eqb x ERROR)
    | expr.load _ a => error_free_expr a
    | expr.op _ x y => (error_free_expr x && error_free_expr y)%bool
    | expr.inlinetable _ _ index => error_free_expr index
    | expr.ite c a b => (error_free_expr c && error_free_expr a && error_free_expr b)%bool
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
    | cmd.stackalloc _ _ x => error_free_cmd x
    | cmd.interact _ _ args => forallb error_free_expr args
    end.
End Defs.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Bedrock.Translation.Cmd.
Require Import Crypto.Bedrock.Translation.Flatten.
Require Import Crypto.Bedrock.Translation.LoadStoreList.
Require Import Crypto.Language.API.
Import ListNotations.

Import API.Compilers.
Import Types.Notations Types.Types.

Section Func.
  Context {p : parameters}.
  Existing Instance rep.Z.
  Local Notation bedrock_func := (string * (list string * list string * cmd))%type.

  (* Feeds arguments to function one by one and then calls translate_cmd *)
  Fixpoint translate_func' {t} (e : @API.expr ltype t) (nextn : nat)
    : type.for_each_lhs_of_arrow ltype t -> (* args *)
      type.for_each_lhs_of_arrow list_lengths t -> (* list lengths *)
      nat * base_ltype (type.final_codomain t) * cmd.cmd :=
    match e with
    | expr.Abs (type.base s) d f =>
      (* if we have an abs, peel off one argument and recurse *)
      fun (args : base_ltype s * type.for_each_lhs_of_arrow _ d)
          (lengths : base_list_lengths s * _) =>
        translate_func' (f (fst args)) nextn (snd args) (snd lengths)
    (* if any expression that outputs a base type, call translate_cmd *)
    | expr.Ident (type.base b) idc =>
      fun (_ _:unit) => translate_cmd (expr.Ident idc) nextn
    | expr.Var (type.base b) v =>
      fun (_ _:unit) => translate_cmd (expr.Var v) nextn
    | expr.App _ (type.base b) f x =>
      fun (_ _:unit) => translate_cmd (expr.App f x) nextn
    | expr.LetIn _ (type.base b) x f =>
      fun (_ _:unit) => translate_cmd (expr.LetIn x f) nextn
    (* if the expression does not have a base type and is not an Abs,
       return garbage *)
    | _ => fun _ _ => (0%nat, dummy_base_ltype _, cmd.skip)
    end.

  (* Translates functions in 3 steps:
     1) load any lists from the arguments
     2) call translate_cmd to translate the function body and get the
        return values
     3) store the return values in the designated variables (with
        lists being written into memory)

    The reason for the load/translate/store pattern is so that, for
    the inductive proof of translate_cmd, there is no need to reason
    about the memory. Since fiat-crypto doesn't do any list
    manipulations in the middle of functions, but only uses lists in
    arguments/return values, it's a convenient formalization. *)
  Definition translate_func {t} (e : @API.expr ltype t)
             (argnames : type.for_each_lhs_of_arrow ltype t)
             (lengths : type.for_each_lhs_of_arrow list_lengths t)
             (rets : base_ltype (type.final_codomain t))
    : list string * list string * cmd :=
    (* load arguments *)
    let load_args_out := load_arguments 0%nat argnames lengths in
    let nextn := fst (fst load_args_out) in
    let args := snd (fst load_args_out) in
    let load_args_cmd := snd load_args_out in
    (* translate *)
    let out := translate_func' e nextn args lengths in
    (* store return values *)
    let store_rets_cmd := store_return_values (snd (fst out)) rets in
    (* assemble function (arg varnames, return varnames, executable body) *)
    let body := cmd.seq (cmd.seq load_args_cmd (snd out)) store_rets_cmd in
    (flatten_argnames argnames, flatten_retnames rets, body).
End Func.

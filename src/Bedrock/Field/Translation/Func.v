Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Cmd.
Require Import Crypto.Bedrock.Field.Translation.Flatten.
Require Import Crypto.Bedrock.Field.Translation.LoadStoreList.
Require Import Crypto.Language.API.
Import ListNotations.

Import API.Compilers.
Import Types.Notations.

Section Func.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Existing Instance rep.Z.

  (* Feeds arguments to function one by one and then calls translate_cmd *)
  Fixpoint translate_func' {t} (e : @API.expr ltype t) (nextn : nat)
    : type.for_each_lhs_of_arrow ltype t -> (* args *)
      nat * base_ltype (type.final_codomain t) * cmd.cmd :=
    match e with
    | expr.Abs (type.base s) d f =>
      (* if we have an abs, peel off one argument and recurse *)
      fun (args : base_ltype s * type.for_each_lhs_of_arrow _ d) =>
        translate_func' (f (fst args)) nextn (snd args)
    (* if any expression that outputs a base type, call translate_cmd *)
    | expr.Ident (type.base b) idc =>
      fun (_:unit) => translate_cmd (expr.Ident idc) nextn
    | expr.Var (type.base b) v =>
      fun (_:unit) => translate_cmd (expr.Var v) nextn
    | expr.App _ (type.base b) f x =>
      fun (_:unit) => translate_cmd (expr.App f x) nextn
    | expr.LetIn _ (type.base b) x f =>
      fun (_:unit) => translate_cmd (expr.LetIn x f) nextn
    (* if the expression does not have a base type and is not an Abs,
       return garbage *)
    | _ => fun _ => (0%nat, dummy_base_ltype _, cmd.skip)
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
  Definition translate_func {t}
             (e : API.Expr t)
             (* argument variables *)
             (argnames : type.for_each_lhs_of_arrow ltype t)
             (* lengths of argument lists *)
             (lengths : type.for_each_lhs_of_arrow list_lengths t)
             (* integer sizes of argument lists *)
             (argsizes : type.for_each_lhs_of_arrow access_sizes t)
             (* return variables *)
             (rets : base_ltype (type.final_codomain t))
             (* integer sizes of return lists *)
             (retsizes : base_access_sizes (type.final_codomain t))
    : list string * list string * cmd (* bedrock function *)
      * list_lengths (type.base (type.final_codomain t)) (* output list lengths *) :=
    (* load arguments *)
    let load_args_out := load_arguments 0%nat argnames lengths argsizes in
    let nextn := fst (fst load_args_out) in
    let args := snd (fst load_args_out) in
    let load_args_cmd := snd load_args_out in
    (* translate *)
    let out := translate_func' (e _) nextn args in
    (* store return values *)
    let store_rets := store_return_values (snd (fst out)) rets retsizes in
    (* make new arguments for pointers to returned lists *)
    let part := extract_listnames rets in
    let out_ptrs := flatten_listonly_base_ltype (fst part) in
    let innames := out_ptrs ++ flatten_argnames argnames in
    let outnames := flatten_listexcl_base_ltype (snd part) in
    (* assemble executable body: load arguments, function body, store rets *)
    let body := cmd.seq (cmd.seq load_args_cmd (snd out)) (snd store_rets) in
    (* assemble func (arg varnames, return varnames, executable body),
       also add in output list lengths *)
    (innames, outnames, body, fst store_rets).
End Func.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Cmd.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Func.
Require Import Crypto.Bedrock.Field.Translation.Proofs.ValidComputable.Cmd.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ZRange.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.Bool.Reflect.
Local Open Scope Z_scope.
Local Open Scope bool_scope.

Import API.Compilers.
Import Types.Notations.

Section Func.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok }.
  Local Existing Instance Types.rep.Z.

  Definition valid_cmd_bool_if_base
           {t} : @API.expr (fun _ => unit) t -> bool :=
    match t as t0 return API.expr t0 -> bool with
    | type.base _ => valid_cmd_bool
    | _ => fun _ => false
    end.

  Fixpoint valid_func_bool {t} (e : @API.expr (fun _ => unit) t) : bool :=
    if valid_cmd_bool_if_base e
    then true
    else
      match e with
      | expr.Abs (type.base _) _ f => valid_func_bool (f tt)
      | _ => false
      end.

  Lemma valid_func_valid_cmd {t} e :
    valid_cmd_bool_if_base (t:=t) e = true ->
    valid_func e.
  Proof.
    cbv [valid_cmd_bool_if_base];
      break_match; try congruence; intros;
      repeat match goal with
             | H: valid_cmd_bool _ = true |- _ =>
               apply valid_cmd_bool_iff in H end.
    constructor; eauto.
  Qed.

  Lemma valid_func_bool_impl1 {t} e :
    valid_func_bool (t:=t) e = true -> valid_func e.
  Proof.
    induction e; cbn [valid_func_bool]; break_match; intros;
      repeat match goal with
             | H : false = true |- _ => congruence
             | H : valid_cmd_bool_if_base _ = true |- _ =>
               apply valid_func_valid_cmd in H
             | _ => assumption
             end; [ ].
    constructor; eauto.
  Qed.

  Lemma valid_cmd_valid_cmd_bool_if_base {t} e :
    Cmd.valid_cmd e ->
    valid_cmd_bool_if_base (t:=type.base t) e = true.
  Proof.
    rewrite <-valid_cmd_bool_iff.
    destruct t; cbn [valid_cmd_bool_if_base]; congruence.
  Qed.

  Lemma valid_func_bool_impl2 {t} e :
    valid_func e -> valid_func_bool (t:=t) e = true.
  Proof.
    induction 1; cbn [valid_func_bool]; break_match;
      try congruence; [ ].
    match goal with H : _ |- _ =>
                    apply valid_cmd_valid_cmd_bool_if_base in H end.
    destruct e; cbn [valid_func_bool]; break_match; congruence.
  Qed.

  Lemma valid_func_bool_iff {t} e :
    valid_func_bool (t:=t) e = true <-> valid_func e.
  Proof.
    split;
      eauto using valid_func_bool_impl1, valid_func_bool_impl2.
  Qed.
End Func.

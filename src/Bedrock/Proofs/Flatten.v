Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import Crypto.Bedrock.Tactics.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Util.
Require Import Crypto.Bedrock.Translation.Flatten.
Require Import Crypto.Util.Tactics.BreakMatch.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations Types.Types.

(* For argument and return variable names, fiat-crypto expects a nested
   structure while bedrock2 expects flat lists; this file contains mechanical
   conversions between the two. *)


Section Flatten.
  Context {p : parameters} {p_ok : @ok p}.
  (* these conversions should happen before loading arguments and after
       storing return values, so they use in-memory lists *)
  Local Existing Instance rep.listZ_mem.
  Local Existing Instance rep.Z.
  Local Instance sem_ok : Semantics.parameters_ok semantics
    := semantics_ok.

  Lemma flatten_base_samelength {t}
        (names : base_ltype t)
        (value : base.interp t) :
    forall (words : list Semantics.word) R mem,
      sep (equivalent_flat_base value words) R mem ->
      length words = length (flatten_base_ltype names).
  Proof.
    induction t; cbn [flatten_base_ltype equivalent_flat_base];
      break_match;
      repeat match goal with
             | _ => progress (intros; subst)
             | _ => progress sepsimpl
             | _ => rewrite app_length
             | _ => solve [eauto]
             end.
    erewrite <-IHt1, <-IHt2 by ecancel_assumption.
    rewrite skipn_length, firstn_length.
    apply Min.min_case_strong; intros; lia.
  Qed.

  (* given these structures have the same type, they'll have the same size in
       flattened form *)
  Lemma flatten_args_samelength {t}
        (argnames : type.for_each_lhs_of_arrow ltype t)
        (args : type.for_each_lhs_of_arrow API.interp_type t) :
    forall (flat_args : list Semantics.word) R mem,
      sep (equivalent_flat_args args flat_args) R mem ->
      length flat_args = length (flatten_argnames argnames).
  Proof.
    induction t;
      repeat match goal with
             | _ => progress (intros; subst)
             | _ => progress cbn [equivalent_flat_args
                                    equivalent_flat_base
                                    flatten_argnames] in *
             | _ => progress break_match 
             | _ => progress sepsimpl 
             | _ => rewrite app_length
             | _ => solve [eauto]
             end.
    erewrite <-IHt2, <-flatten_base_samelength by ecancel_assumption.
    rewrite skipn_length, firstn_length.
    apply Min.min_case_strong; intros; lia.
  Qed.

  Lemma of_list_zip_flatten_argnames {t}
        (argnames : type.for_each_lhs_of_arrow ltype t)
        (args : type.for_each_lhs_of_arrow API.interp_type t)
        (flat_args : list Semantics.word) R mem :
    sep (equivalent_flat_args args flat_args) R mem ->
    (exists l,
        map.of_list_zip (flatten_argnames argnames) flat_args = Some l).
  Proof.
    intros. apply map.sameLength_putmany_of_list.
    erewrite flatten_args_samelength; eauto.
  Qed.

  Lemma varname_set_flatten {t} (names : base_ltype t) :
    PropSet.sameset (varname_set names)
                    (PropSet.of_list (flatten_base_ltype names)).
  Proof.
    apply sameset_iff.
    induction t;
      cbn [varname_set
             flatten_base_ltype rep.varname_set rep.Z rep.listZ_mem];
      break_match;
      cbv [PropSet.singleton_set
             PropSet.of_list PropSet.union PropSet.elem_of];
      cbn [In]; try tauto; [ ].
    intros. rewrite in_app_iff, IHt1, IHt2.
    cbv [PropSet.of_list]. reflexivity.
  Qed.

  Lemma varname_set_args_flatten {t}
        (argnames : type.for_each_lhs_of_arrow ltype t) :
    PropSet.sameset (varname_set_args argnames)
                    (PropSet.of_list (flatten_argnames argnames)).
  Proof.
    revert argnames; induction t; intros;
      cbn [varname_set_args flatten_argnames];
      break_match; rewrite ?of_list_nil; try reflexivity; [ ].
    rewrite PropSet.of_list_app.
    rewrite varname_set_flatten, IHt2.
    reflexivity.
  Qed.
End Flatten.

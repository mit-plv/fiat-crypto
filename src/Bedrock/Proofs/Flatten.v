Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import Crypto.Bedrock.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Proofs.Dexprs.
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
    forall (words : list Semantics.word) R locals mem,
      sep (equivalent_flat_base value words locals) R mem ->
      length words = length (flatten_base_ltype names).
  Proof.
    induction t; cbn [flatten_base_ltype equivalent_flat_base];
      break_match;
      repeat match goal with
             | _ => progress (intros; subst)
             | H : sep (sep (emp _) _) _ _ |- _ =>
               apply sep_assoc in H; [ ]
             | H : sep (emp _) _ _ |- _ =>
               apply sep_emp_l in H; destruct H
             | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
               apply sep_ex1_l in H; destruct H
             | _ => rewrite app_length
             | H : False |- _ => tauto
             | _ => solve [eauto]
             end.
    erewrite <-IHt1, <-IHt2
      by match goal with
           H : sep _ _ _ |- _ =>
           simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H);
             ecancel
         end.
    rewrite skipn_length, firstn_length.
    apply Min.min_case_strong; intros; lia.
  Qed.

  (* given these structures have the same type, they'll have the same size in
       flattened form *)
  Lemma flatten_args_samelength {t}
        (argnames : type.for_each_lhs_of_arrow ltype t)
        (args : type.for_each_lhs_of_arrow API.interp_type t) :
    forall (flat_args : list Semantics.word) R locals mem,
      sep (equivalent_flat_args args flat_args locals) R mem ->
      length flat_args = length (flatten_argnames argnames).
  Proof.
    induction t;
      repeat match goal with
             | _ => progress (intros; subst)
             | _ => progress cbn [equivalent_flat_args
                                    equivalent_flat_base
                                    flatten_argnames] in *
             | _ => progress break_match 
             | H : sep (emp _) _ _ |- _ =>
               apply sep_emp_l in H; destruct H
             | H : sep (Lift1Prop.ex1 _) _ _ |- _ =>
               apply sep_ex1_l in H; destruct H
             | _ => rewrite app_length
             | H : False |- _ => tauto
             | _ => solve [eauto]
             end.
    erewrite <-IHt2, <-flatten_base_samelength
      by match goal with
           H : sep _ _ _ |- _ =>
           simple refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H);
             ecancel
         end.
    rewrite skipn_length, firstn_length.
    apply Min.min_case_strong; intros; lia.
  Qed.

  Lemma of_list_zip_flatten_argnames {t}
        (argnames : type.for_each_lhs_of_arrow ltype t)
        (args : type.for_each_lhs_of_arrow API.interp_type t)
        (flat_args : list Semantics.word) R locals mem :
    sep (equivalent_flat_args args flat_args locals) R mem ->
    (exists l,
        map.of_list_zip (flatten_argnames argnames) flat_args = Some l).
  Proof.
    intros. apply map.sameLength_putmany_of_list.
    erewrite flatten_args_samelength; eauto.
  Qed.
End Flatten.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import bedrock2.Syntax.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.PropSet.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Language.API.
Require Import Crypto.Bedrock.Field.Common.Util.
Require Import Crypto.Bedrock.Field.Translation.Flatten.
Require Import Crypto.Bedrock.Field.Translation.LoadStoreList.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Equivalence.
Require Import Crypto.Bedrock.Field.Translation.Proofs.EquivalenceProperties.
Require Import Crypto.Bedrock.Field.Translation.Proofs.UsedVarnames.
Require Import Crypto.Bedrock.Field.Translation.Proofs.VarnameSet.
Require Import Crypto.Util.Tactics.BreakMatch.
Import ListNotations. Local Open Scope Z_scope.

Import API.Compilers.
Import Types.Notations.

(* For argument and return variable names, fiat-crypto expects a nested
   structure while bedrock2 expects flat lists; this file contains mechanical
   conversions between the two. *)

Section Flatten.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {ok : ok}.
  (* these conversions should happen before loading arguments and after
       storing return values, so they use in-memory lists *)
  Local Existing Instance rep.listZ_mem.
  Local Existing Instance rep.Z.

  Lemma flatten_base_samelength {t}
        (names : base_ltype t)
        (value : base.interp t) :
    forall (words : list word) s R mem,
      sep (equivalent_flat_base value words s) R mem ->
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
    forall (flat_args : list word) s mem,
      equivalent_flat_args args flat_args s mem ->
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
        (flat_args : list word) s : forall (mem : mem),
    equivalent_flat_args args flat_args s mem ->
    (exists l,
        map.of_list_zip (flatten_argnames argnames) flat_args = Some l).
  Proof.
    intros. apply map.sameLength_putmany_of_list.
    erewrite flatten_args_samelength; eauto.
  Qed.

  Lemma varname_set_flatten {t} (names : base_ltype t) :
    PropSet.sameset (varname_set_base names)
                    (PropSet.of_list (flatten_base_ltype names)).
  Proof.
    apply sameset_iff.
    induction t;
      cbn [varname_set_base
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

  Lemma flatten_listonly_subset {t} names :
    PropSet.subset
      (PropSet.of_list (flatten_listonly_base_ltype (t:=t)
                          (fst (extract_listnames names))))
      (varname_set_base names).
  Proof.
    induction t;
      cbn [fst snd varname_set extract_listnames
               flatten_listonly_base_ltype];
      break_match; intros; cbn [fst snd];
        eauto using subset_empty_l; [ | ].
    { rewrite PropSet.of_list_app.
      eauto using subset_union_l, subset_union_rr, subset_union_rl. }
    { rewrite of_list_singleton. reflexivity. }
  Qed.

  Lemma flatten_listonly_sublist {t} names :
    forall x,
      In x (flatten_listonly_base_ltype (fst (extract_listnames names))) ->
      In x (flatten_base_ltype (t:=t) names).
  Proof.
    intros.
    pose proof (flatten_listonly_subset names) as Hsubset.
    rewrite varname_set_flatten in Hsubset.
    apply Hsubset. assumption.
  Qed.

  Lemma flatten_listonly_NoDup {t} names :
    NoDup (flatten_base_ltype (t:=t) names) ->
    NoDup (flatten_listonly_base_ltype (fst (extract_listnames names))).
  Proof.
    induction t;
      cbn [extract_listnames fst snd flatten_base_ltype
                             flatten_listonly_base_ltype];
      intros; break_match;
        repeat match goal with
               | |- NoDup [] => constructor
               | |- NoDup (_ :: _) => constructor
               | H : NoDup (_ :: _) |- _ => inversion H; subst; clear H
               | H : NoDup (_ ++ _) |- _ =>
                 apply NoDup_app_iff in H; cleanup
               | |- ~ (In _ []) => cbv [In]; tauto
               end; [ ].
    apply NoDup_app_iff; repeat split; eauto; repeat intro;
      repeat match goal with
             | H : In _ (flatten_listonly_base_ltype _) |- _ =>
               apply flatten_listonly_sublist in H
             | H : context [~ In _ _] |- _ =>
               eapply H; solve [eauto]
             end.
  Qed.

  Lemma varname_set_flatten_listonly {t} (names : _ t) :
    PropSet.sameset
      (PropSet.of_list
         (flatten_listonly_base_ltype (fst (extract_listnames names))))
      (varname_set_listonly names).
  Proof.
    induction t;
      cbn [extract_listnames fst snd varname_set_listonly 
                             flatten_listonly_base_ltype];
      break_match; intros; rewrite ?of_list_nil; try reflexivity;
        [ | ].
    { rewrite PropSet.of_list_app.
      rewrite IHt1, IHt2. reflexivity. }
    { rewrite of_list_singleton. reflexivity. }
  Qed.

  Lemma varname_set_flatten_listexcl {t} (names : _ t) :
    PropSet.sameset
      (PropSet.of_list
         (flatten_listexcl_base_ltype (snd (extract_listnames names))))
      (varname_set_listexcl names).
  Proof.
    induction t;
      cbn [extract_listnames fst snd varname_set_listexcl
                             flatten_listexcl_base_ltype];
      break_match; intros; cbn [fst snd];
        rewrite ?of_list_singleton; try reflexivity; [ ].
    rewrite PropSet.of_list_app.
    rewrite IHt1, IHt2.
    reflexivity.
  Qed.

  Lemma flatten_listonly_flatten_listexcl_disjoint {t} (names : _ t) :
    NoDup (flatten_base_ltype names) ->
    PropSet.disjoint
      (PropSet.of_list
         (flatten_listonly_base_ltype (fst (extract_listnames names))))
      (PropSet.of_list
         (flatten_listexcl_base_ltype (snd (extract_listnames names)))).
  Proof.
    induction t;
      cbn [extract_listnames fst snd flatten_base_ltype
                             flatten_listexcl_base_ltype
                             flatten_listonly_base_ltype];
      intros; break_match;
        try match goal with
            | H : NoDup (_ ++ _) |- _ =>
              let H' := fresh in
              pose proof H as H'; apply NoDup_disjoint in H
            end;
        repeat match goal with
               | H : NoDup (_ ++ _) |- _ =>
                 apply NoDup_app_iff in H; cleanup
               | _ => rewrite of_list_nil
               | _ => rewrite PropSet.of_list_app
               | _ => solve [eauto using disjoint_empty_l, disjoint_empty_r]
               end; [ ].
    apply disjoint_union_l_iff; split;
      (apply disjoint_union_r_iff; split; eauto; [ ]);
    repeat match goal with
               | H : _ |- _ => erewrite <-!varname_set_flatten in H
               | H : _ |- _ => erewrite varname_set_listonly_listexcl in H
               | H : PropSet.disjoint (PropSet.union _ _) _ |- _ =>
                 apply disjoint_union_l_iff in H; cleanup
               | H : PropSet.disjoint _ (PropSet.union _ _) |- _ =>
                 apply disjoint_union_r_iff in H; cleanup
               | _ => rewrite varname_set_flatten_listonly
               | _ => rewrite varname_set_flatten_listexcl
               | _ => solve [eauto]
               | _ => symmetry; solve [eauto]
           end.
  Qed.

  Lemma flatten_listonly_disjoint {t} (names : _ t) :
    NoDup (flatten_base_ltype names) ->
    PropSet.disjoint
      (PropSet.of_list
         (flatten_listonly_base_ltype (fst (extract_listnames names))))
      (varname_set_listexcl names).
  Proof.
    intros. rewrite <-varname_set_flatten_listexcl.
    eauto using flatten_listonly_flatten_listexcl_disjoint.
  Qed.

  Lemma flatten_listonly_samelength {t}
        (names : listonly_base_ltype t) (value : base.interp t) :
    forall (words : list word) s R mem,
      sep (equivalent_listonly_flat_base value words s) R mem ->
      length words = length (flatten_listonly_base_ltype names).
  Proof.
    induction t;
      cbn [flatten_listonly_base_ltype equivalent_listonly_flat_base
                                       equivalent_flat_base];
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
End Flatten.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.PropSet.
Require Import Crypto.Bedrock.Field.Common.Tactics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Bedrock.Field.Translation.Proofs.Flatten.
Require Import Crypto.Bedrock.Field.Translation.Proofs.VarnameSet.
Require Import Crypto.Bedrock.Field.Translation.Flatten.
Require Import Crypto.Language.API.
Require Import Crypto.Util.Tactics.BreakMatch.

Import Language.API.Compilers.
Import Types.Notations.
Import ListNotations.
Existing Instances rep.Z rep.listZ_mem.

Section with_parameters.
  Context 
    {width BW word mem locals env ext_spec varname_gen error}
   `{parameters_sentinel : @parameters width BW word mem locals env ext_spec varname_gen error}.
  Context {inname_gen outname_gen : nat -> string}.

  Fixpoint make_names
           (name_gen : nat -> string) (nextn : nat) (t : base.type)
    : nat * base_ltype t :=
    match t as t0 return nat * base_ltype t0 with
    | base.type.prod a b =>
      let resa := make_names name_gen nextn a in
      let resb := make_names name_gen (fst resa) b in
      (fst resb, (snd resa, snd resb))
    | base_listZ =>
      (S nextn, name_gen nextn)
    | _ =>
      (S nextn, name_gen nextn)
    end.
  Fixpoint make_innames' (nextn : nat) (t : API.type)
    : nat * type.for_each_lhs_of_arrow ltype t :=
    match t as t0 return
          nat * type.for_each_lhs_of_arrow ltype t0 with
    | type.base _ => (nextn, tt)
    | type.arrow (type.base s) d =>
      let ress := make_names inname_gen nextn s in
      let resd := make_innames' (fst ress) d in
      (fst resd, (snd ress, snd resd))
    | type.arrow _ d =>
      let resd := make_innames' nextn d in
      (fst resd, (tt, snd resd))
    end.
  Definition make_innames t : type.for_each_lhs_of_arrow ltype t :=
    snd (make_innames' 0 t).
  Definition make_outnames t : base_ltype t :=
    snd (make_names outname_gen 0 t).

  Section proofs.
    Context (inname_gen_varname_gen_ok :
               forall n m, inname_gen n <> varname_gen m)
            (outname_gen_varname_gen_ok :
               forall n m, outname_gen n <> varname_gen m)
            (outname_gen_inname_gen_ok :
               forall n m, outname_gen n <> inname_gen m).
    Context (inname_gen_unique :
               forall i j : nat, inname_gen i = inname_gen j <-> i = j)
            (outname_gen_unique :
               forall i j : nat, outname_gen i = outname_gen j <-> i = j).

    Lemma make_names_no_collision name_gen1 name_gen2 t :
      (forall n m : nat, name_gen1 n <> name_gen2 m) ->
      forall nextn n,
        ~ varname_set_base (snd (make_names name_gen1 nextn t))
          (name_gen2 n).
    Proof.
      intro Hdisjoint; induction t; intros;
        cbn [varname_set_base rep.varname_set rep.Z rep.listZ_mem
                              make_names fst snd ];
        repeat match goal with
               | _ => progress cbn [fst snd]
               | |- ~ PropSet.singleton_set _ _ =>
                 apply disjoint_singleton_r_iff, disjoint_singleton_singleton; auto
               | |- ~ PropSet.union _ _ _ =>
                 apply not_union_iff; split; solve [auto]
               | _ => progress break_innermost_match
               end.
    Qed.

    Lemma make_innames'_varname_gen_disjoint t :
      forall nextn n,
        ~ varname_set_args
          (snd (make_innames' nextn t)) (varname_gen n).
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress
                        cbn [fst snd make_innames'
                                 varname_set_args] in *
               | |- ~ PropSet.empty_set _ => cbv [PropSet.empty_set]; tauto
               | |- ~ PropSet.union _ _ _ =>
                 apply not_union_iff; split
               | _ => progress break_innermost_match
               | _ => solve [auto using make_names_no_collision]
               end.
    Qed.

    Lemma make_innames_varname_gen_disjoint t :
      forall n,
        ~ varname_set_args (make_innames t)
          (varname_gen n).
    Proof. apply make_innames'_varname_gen_disjoint. Qed.

    Lemma make_outnames_varname_gen_disjoint t :
      forall n,
        ~ varname_set_base (make_outnames t) (varname_gen n).
    Proof. apply make_names_no_collision; auto. Qed.

    Lemma fst_make_names_lower_bound name_gen t :
      forall nextn, (nextn <= fst (make_names name_gen nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_names] in *
               | _ => progress break_innermost_match
               | _ => lia
               end; [ ].
      eapply Nat.le_trans; [ | solve [eauto] ]. eauto.
    Qed.

    Lemma flatten_make_names_range name_gen t :
      forall x nextn,
        In x (flatten_base_ltype
                (snd (make_names name_gen nextn t))) ->
        exists n, x = name_gen n
                  /\ (nextn <= n < fst (make_names name_gen nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_names
                                        flatten_base_ltype] in *
               | H : _ /\ _ |- _ => destruct H
               | H : In _ [_] |- _ => inversion H; clear H
               | H : In _ [] |- _ => solve [inversion H]
               | H : In _ (_ ++ _) |- _ =>
                 apply in_app_iff in H; destruct H
               | H : name_gen ?x = ?y |- exists n, ?y = name_gen n /\ _ =>
                 exists x; split; [ congruence | ]
               | H : ?y = name_gen ?x |- exists n, ?y = name_gen n /\ _ =>
                 exists x; split; [ assumption | ]
               | _ => specialize (IHt1 _ _ ltac:(eassumption));
                        destruct IHt1
               | _ => specialize (IHt2 _ _ ltac:(eassumption));
                        destruct IHt2
               | _ => progress break_innermost_match
               | _ => lia
              end; [ | ];
          pose proof fst_make_names_lower_bound name_gen t1 nextn;
          pose proof fst_make_names_lower_bound
               name_gen t2 (fst (make_names name_gen nextn t1));
          lia.
    Qed.

    Lemma flatten_make_names_NoDup name_gen t :
      (forall i j, name_gen i = name_gen j <-> i = j) ->
      forall nextn,
        NoDup (flatten_base_ltype
                 (snd (make_names name_gen nextn t))).
    Proof.
      intro name_gen_unique.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_names
                                        flatten_base_ltype]
               | H : In _ _ |- _ => apply flatten_make_names_range in H;
                                      destruct H
               | H : _ /\ _ |- _ => destruct H
               | H1 : ?x = name_gen ?n1, H2 : ?x = name_gen ?n2 |- _ =>
                 pose proof (proj1 (name_gen_unique n1 n2)
                                   ltac:(congruence)); clear H1 H2
               | _ => apply NoDup_cons
               | |- NoDup (_ ++ _) => apply NoDup_app_iff
               | |- _ /\ _ => split
               | |- ~ In _ _ => try apply in_nil; intro
               | _ => progress break_innermost_match
               | _ => solve [auto using in_nil, NoDup_nil]
               | _ => lia
               end.
    Qed.

    Lemma fst_make_innames'_lower_bound t :
      forall nextn,
        (nextn <= fst (make_innames' nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_innames'] in *
               | _ => progress break_innermost_match
               | _ => progress break_innermost_match_hyps
               | _ => lia
               | _ => solve [eauto]
               end; [ ].
      eapply Nat.le_trans; [ apply fst_make_names_lower_bound | ].
      eauto.
    Qed.

    Lemma flatten_make_innames'_range t :
      forall x nextn,
        In x (flatten_argnames (snd (make_innames' nextn t))) ->
        exists n,
          x = inname_gen n
          /\ (nextn <= n < fst (make_innames' nextn t))%nat.
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_innames'
                                        flatten_argnames] in *
               | H : _ /\ _ |- _ => destruct H
               | H : In _ [] |- _ => solve [inversion H]
               | H : In _ (_ ++ _) |- _ =>
                 apply in_app_iff in H; destruct H
               | H : In _ _ |- _ => apply flatten_make_names_range in H;
                                      destruct H
               | H : ?y = inname_gen ?x
                 |- exists n, ?y = inname_gen n /\ _ =>
                 exists x; split; [ assumption | ]
               | _ => specialize (IHt2 _ _ ltac:(eassumption));
                        destruct IHt2
               | _ => progress break_innermost_match
               | _ => lia
               end; [ | ].
      { pose proof fst_make_innames'_lower_bound t2 (fst (make_names inname_gen nextn t)).
        lia. }
      { pose proof fst_make_names_lower_bound inname_gen t nextn.
        lia. }
    Qed.

    Lemma flatten_make_innames'_NoDup t :
      forall nextn,
        NoDup (flatten_argnames (snd (make_innames' nextn t))).
    Proof.
      induction t; intros;
        repeat match goal with
               | _ => progress intros
               | _ => progress cbn [fst snd make_innames' flatten_argnames]
               | _ => apply NoDup_nil
               | H : _ /\ _ |- _ => destruct H
               | H : In _ _ |- _ => apply flatten_make_names_range in H;
                                      destruct H
               | H : In _ _ |- _ => apply flatten_make_innames'_range in H;
                                      destruct H
               | H1 : ?x = inname_gen ?n1, H2 : ?x = inname_gen ?n2 |- _ =>
                 pose proof (proj1 (inname_gen_unique n1 n2)
                                   ltac:(congruence)); clear H1 H2
               | |- NoDup (_ ++ _) => apply NoDup_app_iff
               | |- _ /\ _ => split
               | |- ~ In _ _ => intro
               | _ => progress break_innermost_match
               | _ => solve [ auto using flatten_make_names_NoDup]
               | _ => lia
               end.
    Qed.

    Lemma flatten_make_innames_NoDup t :
      NoDup
        (flatten_argnames (make_innames t)).
    Proof. apply flatten_make_innames'_NoDup. Qed.

    Lemma flatten_make_innames_exists t x :
      In x (flatten_argnames (make_innames t)) ->
      exists n : nat, x = inname_gen n.
    Proof.
      cbv [make_innames]; intros.
      destruct (flatten_make_innames'_range t _ _ ltac:(eassumption)).
      cleanup. eexists; eauto.
    Qed.

    Lemma flatten_make_outnames_exists t x :
      In x (flatten_base_ltype (make_outnames t)) ->
      exists n : nat, x = outname_gen n.
    Proof.
      cbv [make_outnames]; intros.
      destruct (flatten_make_names_range
                  outname_gen t _ _ ltac:(eassumption)).
      cleanup. eexists; eauto.
    Qed.

    Lemma flatten_make_outnames_NoDup t :
      NoDup (flatten_base_ltype (make_outnames t)).
    Proof. apply flatten_make_names_NoDup; auto. Qed.

    Lemma make_innames_make_outnames_disjoint t1 t2 :
      PropSet.disjoint
        (varname_set_args (make_innames t1))
        (varname_set_base (make_outnames t2)).
    Proof.
      rewrite varname_set_args_flatten.
      rewrite varname_set_flatten.
      apply NoDup_disjoint, NoDup_app_iff.
      repeat match goal with
             | _ => progress intros
             | H : In _ _ |- _ => apply flatten_make_innames_exists in H;
                                    destruct H
             | H : In _ _ |- _ => apply flatten_make_outnames_exists in H;
                                    destruct H
             | H1 : ?x = inname_gen ?n1, H2 : ?x = outname_gen ?n2 |- _ =>
               specialize (outname_gen_inname_gen_ok n2 n1); congruence
             | |- ~ In _ _ => intro
             | |- _ /\ _ => split
             | _ => solve [eauto using flatten_make_innames_NoDup,
                           flatten_make_names_NoDup]
             end.
    Qed.
  End proofs.
End with_parameters.

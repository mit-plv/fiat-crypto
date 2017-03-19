Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.NatUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.

Local Open Scope core_scope.
Section language.
  Context {base_type_code : Type}
          {Name : Type}.

  Section monad.
    Context (MName : Type) (force : MName -> option Name).

    Lemma split_mnames_firstn_skipn
          (t : flat_type base_type_code) (ls : list MName)
      : split_mnames force t ls
        = (fst (split_mnames force t (firstn (count_pairs t) ls)),
           skipn (count_pairs t) ls).
    Proof.
      apply path_prod_uncurried; simpl.
      revert ls; induction t; split; split_prod;
        repeat first [ progress simpl in *
                     | progress intros
                     | rewrite <- skipn_skipn
                     | reflexivity
                     | progress break_innermost_match_step
                     | apply (f_equal2 (@pair _ _))
                     | rewrite_hyp <- !*
                     | match goal with
                       | [ H : forall ls, snd (split_mnames _ _ _) = _, H' : context[snd (split_mnames _ _ _)] |- _ ]
                         => rewrite H in H'
                       | [ H : _ |- _ ] => first [ rewrite <- firstn_skipn_add in H ]
                       | [ H : forall ls', fst (split_mnames _ _ _) = _, H' : context[fst (split_mnames _ _ (skipn ?n ?ls))] |- _ ]
                         => rewrite (H (skipn n ls)) in H'
                       | [ H : forall ls', fst (split_mnames _ _ _) = _, H' : context[fst (split_mnames _ ?t (firstn (count_pairs ?t + ?n) ?ls))] |- _ ]
                         => rewrite (H (firstn (count_pairs t + n) ls)), firstn_firstn in H' by omega
                       | [ H : forall ls', fst (split_mnames _ _ _) = _, H' : context[fst (split_mnames _ ?t ?ls)] |- _ ]
                         => is_var ls; rewrite (H ls) in H'
                       | [ H : ?x = Some _, H' : ?x = None |- _ ] => congruence
                       | [ H : ?x = Some ?a, H' : ?x = Some ?b |- _ ]
                         => assert (a = b) by congruence; (subst a || subst b)
                       end ].
    Qed.

    Lemma snd_split_mnames_skipn
          (t : flat_type base_type_code) (ls : list MName)
      : snd (split_mnames force t ls) = skipn (count_pairs t) ls.
    Proof. rewrite split_mnames_firstn_skipn; reflexivity. Qed.
    Lemma fst_split_mnames_firstn
          (t : flat_type base_type_code) (ls : list MName)
      : fst (split_mnames force t ls) = fst (split_mnames force t (firstn (count_pairs t) ls)).
    Proof. rewrite split_mnames_firstn_skipn at 1; reflexivity. Qed.

    Lemma mname_list_unique_firstn_skipn n ls
      : mname_list_unique force ls
        -> (mname_list_unique force (firstn n ls)
            /\ mname_list_unique force (skipn n ls)).
    Proof.
      unfold mname_list_unique; intro H; split; intros k N;
        rewrite <- ?firstn_map, <- ?skipn_map, ?skipn_skipn, ?firstn_firstn_min, ?firstn_skipn_add;
        intros; eapply H; try eassumption.
      { apply Min.min_case_strong.
        { match goal with H : _ |- _ => rewrite skipn_firstn in H end;
            eauto using In_firstn. }
        { intro; match goal with H : _ |- _ => rewrite skipn_all in H by (rewrite firstn_length; omega * ) end.
          simpl in *; tauto. } }
      { eauto using In_skipn. }
    Qed.
    Definition mname_list_unique_firstn n ls
      : mname_list_unique force ls -> mname_list_unique force (firstn n ls)
      := fun H => proj1 (@mname_list_unique_firstn_skipn n ls H).
    Definition mname_list_unique_skipn n ls
      : mname_list_unique force ls -> mname_list_unique force (skipn n ls)
      := fun H => proj2 (@mname_list_unique_firstn_skipn n ls H).
    Lemma mname_list_unique_nil
      : mname_list_unique force nil.
    Proof.
      unfold mname_list_unique; simpl; intros ??.
      rewrite firstn_nil, skipn_nil; simpl; auto.
    Qed.
  End monad.

  Lemma split_onames_firstn_skipn
        (t : flat_type base_type_code) (ls : list (option Name))
    : split_onames t ls
      = (fst (split_onames t (firstn (count_pairs t) ls)),
         skipn (count_pairs t) ls).
  Proof. apply split_mnames_firstn_skipn. Qed.
  Lemma snd_split_onames_skipn
        (t : flat_type base_type_code) (ls : list (option Name))
    : snd (split_onames t ls) = skipn (count_pairs t) ls.
  Proof. apply snd_split_mnames_skipn. Qed.
  Lemma fst_split_onames_firstn
        (t : flat_type base_type_code) (ls : list (option Name))
    : fst (split_onames t ls) = fst (split_onames t (firstn (count_pairs t) ls)).
  Proof. apply fst_split_mnames_firstn. Qed.

  Lemma oname_list_unique_firstn n (ls : list (option Name))
    : oname_list_unique ls -> oname_list_unique (firstn n ls).
  Proof. apply mname_list_unique_firstn. Qed.
  Lemma oname_list_unique_skipn n (ls : list (option Name))
    : oname_list_unique ls -> oname_list_unique (skipn n ls).
  Proof. apply mname_list_unique_skipn. Qed.
  Lemma oname_list_unique_specialize (ls : list (option Name))
    : oname_list_unique ls
      -> forall k n,
        List.In (Some n) (firstn k ls)
        -> List.In (Some n) (skipn k ls)
        -> False.
  Proof.
    intros H k n; specialize (H k n).
    rewrite map_id in H; assumption.
  Qed.
  Definition oname_list_unique_nil : oname_list_unique (@nil (option Name))
    := mname_list_unique_nil _ (fun x => x).


  Lemma split_names_firstn_skipn
        (t : flat_type base_type_code) (ls : list Name)
    : split_names t ls
      = (fst (split_names t (firstn (count_pairs t) ls)),
         skipn (count_pairs t) ls).
  Proof. apply split_mnames_firstn_skipn. Qed.
  Lemma snd_split_names_skipn
        (t : flat_type base_type_code) (ls : list Name)
    : snd (split_names t ls) = skipn (count_pairs t) ls.
  Proof. apply snd_split_mnames_skipn. Qed.
  Lemma fst_split_names_firstn
        (t : flat_type base_type_code) (ls : list Name)
    : fst (split_names t ls) = fst (split_names t (firstn (count_pairs t) ls)).
  Proof. apply fst_split_mnames_firstn. Qed.

  Lemma name_list_unique_firstn n (ls : list Name)
    : name_list_unique ls -> name_list_unique (firstn n ls).
  Proof. apply mname_list_unique_firstn. Qed.
  Lemma name_list_unique_skipn n (ls : list Name)
    : name_list_unique ls -> name_list_unique (skipn n ls).
  Proof. apply mname_list_unique_skipn. Qed.
  Lemma name_list_unique_specialize (ls : list Name)
    : name_list_unique ls
      -> forall k n,
        List.In n (firstn k ls)
        -> List.In n (skipn k ls)
        -> False.
  Proof.
    intros H k n; specialize (H k n).
    rewrite firstn_map, skipn_map in H.
    eauto using in_map.
  Qed.
  Definition name_list_unique_nil : name_list_unique nil
    := mname_list_unique_nil _ (@Some Name).
End language.

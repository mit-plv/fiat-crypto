Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.

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
                       | [ H : _ |- _ ] => first [ rewrite <- firstn_skipn in H ]
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
End language.

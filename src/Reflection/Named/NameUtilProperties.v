Require Import Coq.Lists.List.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.ListUtil.

Local Open Scope core_scope.
Section language.
  Context {base_type_code : Type}
          {Name : Type}.

  Section monad.
    Context (MName : Type) (force : MName -> option Name).

    Lemma snd_split_mnames_skipn
          (t : flat_type base_type_code) (ls : list MName)
      : snd (split_mnames force t ls) = skipn (count_pairs t) ls.
    Proof.
      revert ls; induction t;
        repeat first [ progress simpl in *
                     | progress intros
                     | rewrite <- skipn_skipn
                     | reflexivity
                     | progress break_innermost_match_step
                     | rewrite_hyp !* ].
    Qed.
  End monad.

  Lemma snd_split_onames_skipn
          (t : flat_type base_type_code) (ls : list (option Name))
    : snd (split_onames t ls) = skipn (count_pairs t) ls.
  Proof. apply snd_split_mnames_skipn. Qed.

  Lemma snd_split_names_skipn
          (t : flat_type base_type_code) (ls : list Name)
    : snd (split_names t ls) = skipn (count_pairs t) ls.
  Proof. apply snd_split_mnames_skipn. Qed.
End language.

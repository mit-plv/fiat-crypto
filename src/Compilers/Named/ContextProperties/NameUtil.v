Require Import Coq.omega.Omega.
Require Import Crypto.Util.FixCoqMistakes.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.NameUtil.
Require Import Crypto.Compilers.Named.NameUtilProperties.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.ContextProperties.Tactics.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.

Section with_context.
  Context {base_type_code Name var} (Context : @Context base_type_code Name var)
          (base_type_code_dec : DecidableRel (@eq base_type_code))
          (Name_dec : DecidableRel (@eq Name))
          (ContextOk : ContextOk Context).

  Local Notation find_Name := (@find_Name base_type_code Name Name_dec).
  Local Notation find_Name_and_val := (@find_Name_and_val base_type_code Name base_type_code_dec Name_dec).

  Hint Rewrite (@find_Name_and_val_default_to_None _ base_type_code_dec _ Name_dec) using congruence : ctx_db.
  Hint Rewrite (@find_Name_and_val_different _ base_type_code_dec _ Name_dec) using assumption : ctx_db.
  Hint Rewrite (@find_Name_and_val_wrong_type _ base_type_code_dec _ Name_dec) using congruence : ctx_db.
  Hint Rewrite (@snd_split_onames_skipn base_type_code Name) : ctx_db.

  Local Ltac misc_oname_t_step :=
    match goal with
    | [ H : oname_list_unique (List.skipn _ _) -> _ |- _ ]
      => specialize (fun pf => H (@oname_list_unique_skipn _ _ _ pf))
    | [ H : ((_, _) = (_, _))%core -> _ |- _ ]
      => specialize (fun a b => H (f_equal2 (@pair _ _) a b))
    | [ H : ?x = (_,_)%core -> _ |- _ ]
      => rewrite (surjective_pairing x) in H;
           specialize (fun a b => H (f_equal2 (@pair _ _) a b))
    end.

  Lemma split_onames_find_Name
        {n T N ls ls'}
        (H : split_onames _ ls = (Some N, ls')%core)
    : (exists t, @find_Name n T N = Some t)
      <-> List.In (Some n) (List.firstn (CountLets.count_pairs T) ls).
  Proof using Type.
    revert dependent ls; intro ls; revert ls ls'; induction T; intros ls ls' H;
      [ | | specialize (IHT1 (fst N) ls (snd (split_onames T1 ls)));
            specialize (IHT2 (snd N) (snd (split_onames T1 ls)) (snd (split_onames (T1 * T2) ls))) ];
      repeat first [ misc_oname_t_step
                   | t_step
                   | progress split_iff
                   | progress specialize_by (eexists; eauto)
                   | solve [ eauto using In_skipn, In_firstn ]
                   | match goal with
                     | [ H : List.In ?x (List.firstn ?n ?ls) |- List.In ?x (List.firstn (?n + ?m) ?ls) ]
                       => apply (In_firstn n); rewrite firstn_firstn by omega
                     | [ H : _ |- _ ] => first [ rewrite firstn_skipn_add in H
                                               | rewrite firstn_firstn in H by omega ]
                     | [ H : List.In ?x' (List.firstn (?n + ?m) ?ls) |- List.In ?x' (List.firstn ?m (List.skipn ?n ?ls)) ]
                       => apply (In_firstn_skipn_split n) in H
                     end ].
  Qed.

  Lemma split_onames_find_Name_Some_unique_iff
        {n T N ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
    : (exists t, @find_Name n T N = Some t)
      <-> List.In (Some n) ls /\ ~List.In (Some n) ls'.
  Proof using Type.
    rewrite (split_onames_find_Name (ls':=ls') (ls:=ls)) by assumption.
    rewrite (surjective_pairing (split_onames _ _)) in H.
    rewrite fst_split_onames_firstn, snd_split_onames_skipn in H.
    inversion_prod; subst.
    split; [ split | intros [? ?] ]; eauto using In_firstn, oname_list_unique_specialize.
    match goal with
    | [ H : List.In (Some _) ?ls |- _ ]
      => is_var ls;
           eapply In_firstn_skipn_split in H; destruct_head' or; eauto; exfalso; eauto
    end.
  Qed.

  Lemma split_onames_find_Name_Some_unique
        {t n T N ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
        (Hfind : @find_Name n T N = Some t)
    : List.In (Some n) ls /\ ~List.In (Some n) ls'.
  Proof using Type.
    eapply split_onames_find_Name_Some_unique_iff; eauto.
  Qed.

  Lemma flatten_binding_list_find_Name_and_val_unique
        {var' t n T N V v ls ls'}
        (Hls : oname_list_unique ls)
        (H : split_onames _ ls = (Some N, ls')%core)
    : @find_Name_and_val var' t n T N V None = Some v
      <-> List.In (existT (fun t => (Name * var' t)%type) t (n, v)) (Wf.flatten_binding_list N V).
  Proof using Type.
    revert dependent ls; intro ls; revert ls ls'; induction T; intros ls ls' Hls H;
      [ | | specialize (IHT1 (fst N) (fst V) ls (snd (split_onames T1 ls)));
            specialize (IHT2 (snd N) (snd V) (snd (split_onames T1 ls)) (snd (split_onames (T1 * T2) ls))) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | progress simpl in *
                   | rewrite List.in_app_iff
                   | misc_oname_t_step
                   | t_step
                   | progress split_iff
                   | lazymatch goal with
                     | [ H : find_Name ?n ?x = Some ?t, H' : find_Name_and_val ?t' ?n ?X ?V None = Some ?v |- _ ]
                       => apply find_Name_and_val_find_Name_Some in H'
                     | [ H : find_Name ?n ?x = Some ?t, H' : find_Name ?n ?x' = Some ?t' |- _ ]
                       => let apply_in_tac H :=
                              (eapply split_onames_find_Name_Some_unique in H;
                               [ | | apply path_prod_uncurried; split; [ eassumption | simpl; reflexivity ] ];
                               [ | solve [ eauto using oname_list_unique_firstn, oname_list_unique_skipn ] ]) in
                          first [ constr_eq x x'; fail 1
                                | apply_in_tac H; apply_in_tac H' ]
                     end ].
  Qed.

  Lemma fst_split_mnames__flatten_binding_list__find_Name
        (MName : Type) (force : MName -> option Name)
        {var' t n T N V v} {ls : list MName}
        (Hs : fst (split_mnames force T ls) = Some N)
        (HN : List.In (existT _ t (n, v)%core) (Wf.flatten_binding_list (var2:=var') N V))
    : find_Name n N = Some t.
  Proof.
    revert dependent ls; induction T;
      [ | | specialize (IHT1 (fst N) (fst V));
            specialize (IHT2 (snd N) (snd V)) ];
      repeat first [ misc_oname_t_step
                   | t_step
                   | match goal with
                     | [ H : _ |- _ ] => first [ rewrite snd_split_mnames_skipn in H
                                               | rewrite List.in_app_iff in H ]
                     | [ H : context[fst (split_mnames _ _ ?ls)] |- _ ]
                       => is_var ls; rewrite (@fst_split_mnames_firstn _ _ _ _ _ ls) in H
                     end ].
  Abort.

  Lemma fst_split_mnames__find_Name__flatten_binding_list
        (MName : Type) (force : MName -> option Name)
        {var' t n T N V v default} {ls : list MName}
        (Hs : fst (split_mnames force T ls) = Some N)
        (Hfind : find_Name n N = Some t)
        (HN : List.In (existT _ t (n, v)%core) (Wf.flatten_binding_list N V))
    : @find_Name_and_val var' t n T N V default = Some v.
  Proof.
    revert default; revert dependent ls; induction T;
      [ | | specialize (IHT1 (fst N) (fst V));
            specialize (IHT2 (snd N) (snd V)) ];
      repeat first [ find_Name_and_val_default_to_None_step
                   | rewrite List.in_app_iff in *
                   | t_step ].
  Abort.
End with_context.

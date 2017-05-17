(** * PHOAS → Named Representation of Gallina *)
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Wf.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.ContextProperties.NameUtil.
Require Import Crypto.Compilers.Named.NameUtil.
Require Import Crypto.Compilers.Named.NameUtilProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Named.Compile.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Tactics.DestructHead.

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code var}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {base_type_dec : DecidableRel (@eq base_type_code)}
          {Name_dec : DecidableRel (@eq Name)}
          {Context : @Context base_type_code Name var}
          {ContextOk : ContextOk Context}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code op (fun _ => Name)).
  Local Notation wff := (@wff base_type_code op (fun _ => Name) var).
  Local Notation wf := (@wf base_type_code op (fun _ => Name) var).
  Local Notation nexprf := (@Named.exprf base_type_code op Name).
  Local Notation nexpr := (@Named.expr base_type_code op Name).
  Local Notation nwff := (@Named.wff base_type_code Name op var Context).
  Local Notation nwf := (@Named.wf base_type_code Name op var Context).
  Local Notation ocompilef := (@ocompilef base_type_code op Name).
  Local Notation ocompile := (@ocompile base_type_code op Name).
  Local Notation compilef := (@compilef base_type_code op Name).
  Local Notation compile := (@compile base_type_code op Name).

  Lemma wff_ocompilef (ctx : Context) G
        (HG : forall t n v,
            List.In (existT _ t (n, v)%core) G -> lookupb t ctx n = Some v)
        {t} (e : exprf t) e' (ls : list (option Name))
        (Hwf : wff G e e')
        v
        (H : ocompilef e ls = Some v)
        (Hls : oname_list_unique ls)
        (HGls : forall t n x, List.In (existT _ t (n, x)%core) G -> List.In (Some n) ls -> False)
    : prop_of_option (nwff ctx v).
  Proof using ContextOk Name_dec base_type_dec.
    revert dependent ctx; revert dependent ls; induction Hwf;
      repeat first [ progress intros
                   | progress subst
                   | progress inversion_option
                   | solve [ auto ]
                   | progress simpl in *
                   | progress unfold option_map in *
                   | progress break_innermost_match_step
                   | progress break_match_hyps
                   | progress autorewrite with push_prop_of_option in *
                   | progress specialize_by tauto
                   | progress specialize_by auto using oname_list_unique_nil
                   | solve [ unfold not in *; eauto using In_skipn, oname_list_unique_firstn, oname_list_unique_skipn ]
                   | progress destruct_head' or
                   | match goal with
                     | [ IH : forall v ls, ocompilef ?e ls = Some v -> _, H : ocompilef ?e ?ls' = Some ?v' |- _ ]
                       => specialize (IH _ _ H)
                     | [ IH : forall x1 x2 v ls, ocompilef (?e2 x1) ls = Some v -> _, H : ocompilef (?e2 ?x1') ?ls' = Some ?v' |- _ ]
                       => specialize (fun x2 => IH _ x2 _ _ H)
                     | [ HG : forall t n v, List.In _ _ -> _ = Some _, H : _ = None |- _ ]
                       => erewrite HG in H by eassumption
                     | [ |- _ /\ _ ] => split
                     | [ H : context[List.In _ (_ ++ _)] |- _ ]
                       => setoid_rewrite List.in_app_iff in H
                     | [ H : split_onames _ _ = (_, _)%core |- _ ]
                       => pose proof (f_equal (@fst _ _) H);
                          pose proof (f_equal (@snd _ _) H);
                          clear H
                     | [ H : context[snd (split_onames _ _)] |- _ ]
                       => rewrite snd_split_onames_skipn in H
                     | [ H : forall a, (forall x y z, _ \/ _ -> _) -> _ |- _ ]
                       => specialize (fun a pf1 pf2
                                      => H a (fun x y z pf
                                              => match pf with
                                                 | or_introl pf' => pf1 x y z pf'
                                                 | or_intror pf' => pf2 x y z pf'
                                                 end))
                     | [ H : forall a b, (forall x y z, _ \/ _ -> _) -> _ |- _ ]
                       => specialize (fun a b pf1 pf2
                                      => H a b (fun x y z pf
                                                => match pf with
                                                   | or_introl pf' => pf1 x y z pf'
                                                   | or_intror pf' => pf2 x y z pf'
                                                   end))
                     | [ H : forall a b c, (forall x y z, _ \/ _ -> _) -> _ |- _ ]
                       => specialize (fun a b c pf1 pf2
                                      => H a b c (fun x y z pf
                                                  => match pf with
                                                     | or_introl pf' => pf1 x y z pf'
                                                     | or_intror pf' => pf2 x y z pf'
                                                     end))
                     | [ H : forall a b c d, (forall x y z, _ \/ _ -> _) -> _ |- _ ]
                       => specialize (fun a b c d pf1 pf2
                                      => H a b c d (fun x y z pf
                                                    => match pf with
                                                       | or_introl pf' => pf1 x y z pf'
                                                       | or_intror pf' => pf2 x y z pf'
                                                       end))
                     | [ H : _ |- _ ]
                       => progress rewrite ?firstn_nil, ?skipn_nil, ?skipn_skipn in H
                     | [ H : List.In ?x (List.firstn ?a (List.skipn ?b ?ls)), H' : List.In ?x (List.skipn (?b + ?a) ?ls) |- False ]
                       => rewrite firstn_skipn_add in H; apply In_skipn in H
                     | [ H : _ |- prop_of_option (nwff _ ?v) ]
                       => eapply H; clear H
                     end ];
      repeat match goal with
             | _ => erewrite lookupb_extend by assumption
             | [ |- context[find_Name_and_val ?tdec ?ndec ?a ?b ?c ?d ?default] ]
               => lazymatch default with None => fail | _ => idtac end;
                    rewrite (find_Name_and_val_split tdec ndec (default:=default))
             | [ H : _ |- _ ] => erewrite H by eassumption
             | _ => progress unfold dec in *
             | _ => progress break_innermost_match_step
             | _ => progress subst
             | _ => progress destruct_head' and
             | _ => congruence
             | [ H : List.In _ (flatten_binding_list _ _) |- _ ]
               => erewrite <- (flatten_binding_list_find_Name_and_val_unique _ _) in H;
                    [ | | apply path_prod_uncurried; split; [ eassumption | simpl; reflexivity ] ];
                    [ | solve [ eauto using oname_list_unique_firstn, oname_list_unique_skipn ] ]
             | [ H : _ |- _ ]
               => first [ erewrite find_Name_and_val_wrong_type in H by eassumption
                        | rewrite find_Name_and_val_different in H by assumption
                        | rewrite snd_split_onames_skipn in H ]
             | _ => solve [ eauto using In_skipn, In_firstn
                          | eapply split_onames_find_Name_Some_unique; [ | apply path_prod; simpl | ]; eauto ]
             | [ H : find_Name_and_val _ _ ?t ?n ?N ?V None = Some _, H' : List.In (Some ?n) (List.skipn _ ?ls) |- False ]
               => eapply find_Name_and_val_find_Name_Some, split_onames_find_Name_Some_unique in H;
                    [ | | apply path_prod_uncurried; split; [ eassumption | simpl; reflexivity ] ];
                    [ | solve [ eauto using oname_list_unique_firstn, oname_list_unique_skipn ] ]
             | [ H : List.In (existT _ ?t (?n, _)%core) ?G,
                     H' : List.In (Some ?n) (List.skipn _ ?ls),
                          IH : forall t' n' x', List.In (existT _ t' (n', x')%core) ?G -> List.In (Some n') ?ls -> False
                                                |- False ]
               => apply (IH _ _ _ H); clear IH H
             | [ H : List.In (existT _ ?t (?n, _)%core) ?G,
                     H' : find_Name _ ?n ?N = Some ?t',
                          IH : forall t' n' x', List.In (existT _ t' (n', x')%core) ?G -> List.In (Some n') ?ls -> False
                                                |- _ ]
               => exfalso; apply (IH _ _ _ H); clear IH H
             end.
  Qed.

  Lemma wf_ocompile (ctx : Context) {t} (e : expr t) e' (ls : list (option Name))
        (Hwf : wf e e')
        f
        (Hls : oname_list_unique ls)
        (H : ocompile e ls = Some f)
    : nwf ctx f.
  Proof using ContextOk Name_dec base_type_dec.
    revert H; destruct Hwf;
      repeat first [ progress simpl in *
                   | progress unfold option_map, Named.interp in *
                   | congruence
                   | progress break_innermost_match
                   | progress inversion_option
                   | progress subst
                   | progress intros ].
    intro; simpl.
    eapply wff_ocompilef;
      [ | solve [ eauto ] | eassumption
        | inversion_prod; subst; rewrite snd_split_onames_skipn; eauto using oname_list_unique_skipn
        | intros ???; erewrite <- (flatten_binding_list_find_Name_and_val_unique _ _) by eassumption;
          let H := fresh in
          intro H; apply find_Name_and_val_find_Name_Some in H;
          eapply split_onames_find_Name_Some_unique in H; [ | eassumption.. ];
          intuition ].
    { intros ???.
      repeat first [ solve [ auto ]
                   | rewrite (lookupb_extend _ _ _)
                   | progress subst
                   | progress break_innermost_match
                   | erewrite <- (flatten_binding_list_find_Name_and_val_unique _ _) by eassumption
                   | congruence
                   | eassumption
                   | match goal with
                     | [ |- context[find_Name_and_val ?tdec ?ndec ?a ?b ?c ?d ?default] ]
                       => lazymatch default with None => fail | _ => idtac end;
                          rewrite (find_Name_and_val_split tdec ndec (default:=default))
                     | [ H : _ |- _ ] => first [ erewrite find_Name_and_val_wrong_type in H by eassumption
                                               | erewrite find_Name_and_val_different in H by eassumption ]
                     end
                   | progress intros ]. }
  Qed.

  Lemma wff_compilef (ctx : Context) {t} (e : exprf t) e' (ls : list Name)
        G
        (Hwf : wff G e e')
        (HG : forall t n x, List.In (existT _ t (n, x)%core) G -> lookupb t ctx n = Some x)
        v
        (H : compilef e ls = Some v)
        (Hls : name_list_unique ls)
        (HGls : forall t n x, List.In (existT _ t (n, x)%core) G -> List.In n ls -> False)
    : prop_of_option (nwff ctx v).
  Proof using ContextOk Name_dec base_type_dec.
    eapply wff_ocompilef; try eassumption.
    setoid_rewrite List.in_map_iff; intros; destruct_head' ex; destruct_head' and; inversion_option; subst.
    eauto.
  Qed.

  Lemma wf_compile (ctx : Context) {t} (e : expr t) e' (ls : list Name)
        (Hwf : wf e e')
        f
        (Hls : name_list_unique ls)
        (H : compile e ls = Some f)
    : nwf ctx f.
  Proof using ContextOk Name_dec base_type_dec. eapply wf_ocompile; eassumption. Qed.
End language.

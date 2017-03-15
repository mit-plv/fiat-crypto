(** * PHOAS → Named Representation of Gallina *)
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Wf.
Require Import Crypto.Reflection.Named.ContextDefinitions.
Require Import Crypto.Reflection.Named.ContextProperties.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Reflection.Named.NameUtilProperties.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Option.
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
            List.In (existT _ t (n, v)%core) G -> lookupb ctx n t = Some v)
        {t} (e : exprf t) e' (ls : list (option Name))
        (Hwf : wff G e e')
        v
        (H : ocompilef e ls = Some v)
        (HGls : forall t n v,
            List.In (existT _ t (n, v)%core) G -> ~List.In (Some n) ls)
        (Hls_unique : forall n k,
            List.In (Some n) (List.firstn k ls)
            -> List.In (Some n) (List.skipn k ls)
            -> False)
    : prop_of_option (nwff ctx v).
  Proof.
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
                   | solve [ unfold not in *; eauto using In_skipn ]
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
                     end ].
      repeat match goal with
             | _ => erewrite lookupb_extend by assumption
             | [ |- context[find_Name_and_val ?tdec ?ndec ?a ?b ?c ?d ?default] ]
               => lazymatch default with None => fail | _ => idtac end;
                    rewrite (find_Name_and_val_split tdec ndec (default:=default))
             | [ H : _ |- _ ] => erewrite H by eassumption
             | _ => progress break_innermost_match_step
             | _ => progress subst
             | _ => congruence
             end.
  Abort.
  (*Fixpoint ocompilef {t} (e : exprf t) (ls : list (option Name)) {struct e}
    : option (nexprf t)
    := match e in @Syntax.exprf _ _ _ t return option (nexprf t) with
       | TT => Some Named.TT
       | Var _ x => Some (Named.Var x)
       | Op _ _ op args => option_map (Named.Op op) (@ocompilef _ args ls)
       | LetIn tx ex _ eC
         => match @ocompilef _ ex nil, split_onames tx ls with
            | Some x, (Some n, ls')%core
              => option_map (fun C => Named.LetIn tx n x C) (@ocompilef _ (eC n) ls')
            | _, _ => None
            end
       | Pair _ ex _ ey => match @ocompilef _ ex nil, @ocompilef _ ey nil with
                           | Some x, Some y => Some (Named.Pair x y)
                           | _, _ => None
                           end
       end.

  Definition ocompile {t} (e : expr t) (ls : list (option Name))
    : option (nexpr t)
    := match e in @Syntax.expr _ _ _ t return option (nexpr t) with
       | Abs src _ f
         => match split_onames src ls with
            | (Some n, ls')%core
              => option_map (Named.Abs n) (@ocompilef _ (f n) ls')
            | _ => None
            end
       end.

  Definition compilef {t} (e : exprf t) (ls : list Name) := @ocompilef t e (List.map (@Some _) ls).
  Definition compile {t} (e : expr t) (ls : list Name) := @ocompile t e (List.map (@Some _) ls).*)
End language.

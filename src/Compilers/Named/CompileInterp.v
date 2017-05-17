(** * PHOAS → Named Representation of Gallina *)
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.NameUtil.
Require Import Crypto.Compilers.Named.NameUtilProperties.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.ContextProperties.
Require Import Crypto.Compilers.Named.ContextProperties.NameUtil.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Named.Compile.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SpecializeBy.

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context {base_type_code}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {Name : Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
          {base_type_dec : DecidableRel (@eq base_type_code)}
          {Name_dec : DecidableRel (@eq Name)}
          {Context : @Context base_type_code Name interp_base_type}
          {ContextOk : ContextOk Context}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprf := (@exprf base_type_code op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code op (fun _ => Name)).
  Local Notation Expr := (@Expr base_type_code op).
  Local Notation wff := (@wff base_type_code op (fun _ => Name) interp_base_type).
  Local Notation wf := (@wf base_type_code op (fun _ => Name) interp_base_type).
  Local Notation nexprf := (@Named.exprf base_type_code op Name).
  Local Notation nexpr := (@Named.expr base_type_code op Name).
  Local Notation ocompilef := (@ocompilef base_type_code op Name).
  Local Notation ocompile := (@ocompile base_type_code op Name).
  Local Notation compilef := (@compilef base_type_code op Name).
  Local Notation compile := (@compile base_type_code op Name).

  Lemma interpf_ocompilef (ctx : Context) {t} (e : exprf t) e' (ls : list (option Name))
        G
        (Hwf : wff G e e')
        (HG : forall t n x, List.In (existT _ t (n, x)%core) G -> lookupb t ctx n = Some x)
        v
        (H : ocompilef e ls = Some v)
        (Hls : oname_list_unique ls)
        (HGls : forall t n x, List.In (existT _ t (n, x)%core) G -> List.In (Some n) ls -> False)
    : Named.interpf (interp_op:=interp_op) (ctx:=ctx) v
      = Some (interpf interp_op e').
  Proof using ContextOk Name_dec base_type_dec.
    revert dependent ctx; revert dependent ls; induction Hwf;
      repeat first [ progress intros
                   | progress subst
                   | progress inversion_option
                   | apply (f_equal (@Some _))
                   | apply (f_equal (@interp_op _ _ _))
                   | solve [ eauto ]
                   | progress simpl in *
                   | progress unfold option_map, LetIn.Let_In in *
                   | progress break_innermost_match_step
                   | progress break_match_hyps
                   | progress destruct_head' or
                   | progress inversion_prod
                   | progress specialize_by_assumption
                   | progress specialize_by auto using oname_list_unique_nil
                   | match goal with
                     | [ H : forall x, oname_list_unique ?ls -> _ |- _ ]
                       => specialize (fun pf x => H x pf)
                     | [ H : context[snd (split_onames _ _)] |- _ ]
                       => rewrite snd_split_onames_skipn in H
                     | [ H : oname_list_unique (List.skipn _ _) -> _ |- _ ]
                       => specialize (fun pf => H (@oname_list_unique_skipn _ _ _ pf))
                     | [ IH : forall v ls, ocompilef ?e ls = Some v -> _, H : ocompilef ?e ?ls' = Some ?v' |- _ ]
                       => specialize (IH _ _ H)
                     | [ IH : forall x1 x2 v ls, ocompilef (?e x1) ls = Some v -> _, H : ocompilef (?e ?x1') ?ls' = Some ?v' |- _ ]
                       => specialize (fun x2 => IH _ x2 _ _ H)
                     | [ H : context[List.In _ (_ ++ _)] |- _ ]
                       => rewrite List.in_app_iff in H
                     | [ H : forall ctx, _ -> Named.interpf ?e = Some _, H' : context[Named.interpf ?e] |- _ ]
                       => rewrite H in H' by assumption
                     | [ H : forall x2 ctx, _ -> Named.interpf ?e = Some _ |- Named.interpf ?e = Some _ ]
                       => apply H; clear H
                     | [ H : forall x2, _ -> forall ctx, _ -> Named.interpf ?e = Some _ |- Named.interpf ?e = Some _ ]
                       => apply H; clear H
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

  Lemma interp_ocompile (ctx : Context) {t} (e : expr t) e' (ls : list (option Name))
        (Hwf : wf e e')
        f
        (Hls : oname_list_unique ls)
        (H : ocompile e ls = Some f)
    : forall v, Named.interp (interp_op:=interp_op) (ctx:=ctx) f v
                = Some (interp interp_op e' v).
  Proof using ContextOk Name_dec base_type_dec.
    revert H; destruct Hwf;
      repeat first [ progress simpl in *
                   | progress unfold option_map, Named.interp in *
                   | congruence
                   | progress break_innermost_match
                   | progress inversion_option
                   | progress subst
                   | progress intros ].
    eapply interpf_ocompilef;
      [ eauto | | eassumption
        | inversion_prod; subst; rewrite snd_split_onames_skipn; eauto using oname_list_unique_skipn
        |intros ???; erewrite <- (flatten_binding_list_find_Name_and_val_unique _ _) by eassumption;
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
                   | match goal with
                     | [ |- context[find_Name_and_val ?tdec ?ndec ?a ?b ?c ?d ?default] ]
                       => lazymatch default with None => fail | _ => idtac end;
                          rewrite (find_Name_and_val_split tdec ndec (default:=default))
                     | [ H : _ |- _ ] => first [ erewrite find_Name_and_val_wrong_type in H by eassumption
                                               | erewrite find_Name_and_val_different in H by eassumption ]
                     end
                   | progress intros ]. }
  Qed.

  Lemma interpf_compilef (ctx : Context) {t} (e : exprf t) e' (ls : list Name)
        G
        (Hwf : wff G e e')
        (HG : forall t n x, List.In (existT _ t (n, x)%core) G -> lookupb t ctx n = Some x)
        v
        (H : compilef e ls = Some v)
        (Hls : name_list_unique ls)
        (HGls : forall t n x, List.In (existT _ t (n, x)%core) G -> List.In n ls -> False)
    : Named.interpf (interp_op:=interp_op) (ctx:=ctx) v
      = Some (interpf interp_op e').
  Proof using ContextOk Name_dec base_type_dec.
    eapply interpf_ocompilef; try eassumption.
    setoid_rewrite List.in_map_iff; intros; destruct_head' ex; destruct_head' and; inversion_option; subst.
    eauto.
  Qed.

  Lemma interp_compile (ctx : Context) {t} (e : expr t) e' (ls : list Name)
        (Hwf : wf e e')
        f
        (Hls : name_list_unique ls)
        (H : compile e ls = Some f)
    : forall v, Named.interp (interp_op:=interp_op) (ctx:=ctx) f v
                = Some (interp interp_op e' v).
  Proof using ContextOk Name_dec base_type_dec. eapply interp_ocompile; eassumption. Qed.

  Lemma Interp_compile {t} (e : Expr t) (ls : list Name)
        (Hwf : Wf e)
        f
        (Hls : name_list_unique ls)
        (H : compile (e _) ls = Some f)
    : forall v, Named.Interp (Context:=Context) (interp_op:=interp_op) f v
                = Some (Interp interp_op e v).
  Proof using ContextOk Name_dec base_type_dec. eapply interp_compile; eauto. Qed.
End language.

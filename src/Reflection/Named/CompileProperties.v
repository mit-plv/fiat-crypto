Require Import Coq.omega.Omega.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.NameUtil.
Require Import Crypto.Reflection.Named.NameUtilProperties.
Require Import Crypto.Reflection.Named.Compile.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.CountLets.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.SpecializeBy.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.ListUtil.

Local Notation eta x := (fst x, snd x).

Local Open Scope ctype_scope.
Local Open Scope nexpr_scope.
Local Open Scope expr_scope.
Section language.
  Context (base_type_code : Type)
          (op : flat_type base_type_code -> flat_type base_type_code -> Type)
          (Name : Type)
          (dummy : base_type_code -> Name).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).
  Local Notation exprft := (@exprf base_type_code op (fun _ => unit)).
  Local Notation exprt := (@expr base_type_code op (fun _ => unit)).
  Local Notation exprf := (@exprf base_type_code op (fun _ => Name)).
  Local Notation expr := (@expr base_type_code op (fun _ => Name)).
  Local Notation nexprf := (@Named.exprf base_type_code op Name).
  Local Notation nexpr := (@Named.expr base_type_code op Name).

  Lemma compilef_count_let_bindersf_enough {t}
        (e1 : exprf t) (e2 : exprft t)
        G
        (Hwf : wff G e1 e2)
    : forall (ls1 : list Name)
             (He : compilef e1 ls1 <> None)
             (ls2 : list Name)
             (Hls : List.length ls2 >= count_let_bindersf dummy e1),
      compilef e1 ls2 <> None.
  Proof.
    unfold compilef; induction Hwf;
      repeat first [ progress simpl in *
                   | progress cbv [option_map] in *
                   | progress subst
                   | progress inversion_prod
                   | congruence
                   | omega
                   | progress break_innermost_match_step
                   | progress break_match_hyps
                   | progress intros
                   | progress specialize_by congruence
                   | match goal with
                     | [ H : forall ls1, ocompilef ?e _ <> None -> _, H' : ocompilef ?e (List.map _ ?ls') = Some _ |- _ ]
                       => specialize (H ls'); rewrite H' in H
                     | [ H : forall ls1, ocompilef ?e _ <> None -> _, H' : ocompilef ?e nil = Some _ |- _ ]
                       => specialize (H nil); simpl in H; rewrite H' in H
                     | [ H : forall v ls1, ocompilef (?e v) _ <> None -> _, H' : ocompilef (?e ?v') _ = Some _ |- _ ]
                       => specialize (H v')
                     | [ H : forall ls1, List.length ls1 >= ?k -> _, H' : List.length _ >= ?k |- _ ]
                       => specialize (H _ H')
                     | [ H : context[snd (split_onames _ _)] |- _ ]
                       => rewrite snd_split_onames_skipn in H
                     | [ H : context[List.skipn _ (List.map _ _)] |- _]
                       => rewrite skipn_map in H
                     | [ H : fst (split_onames ?t (List.map _ ?ls)) = None |- _ ]
                       => rewrite split_onames_split_names in H
                     | [ H : fst (split_names _ _) = None |- _ ]
                       => apply length_fst_split_names_None_iff in H
                     end ].
  Abort.
End language.

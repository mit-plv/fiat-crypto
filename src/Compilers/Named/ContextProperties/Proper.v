Require Import Coq.Classes.Morphisms.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Tactics.BreakMatch.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.DestructHead.

Section with_context.
  Context {base_type_code}
          {base_type_code_dec : DecidableRel (@eq base_type_code)}
          {Name}
          {Name_dec : DecidableRel (@eq Name)}
          {var} {Context : @Context base_type_code Name var}
          {ContextOk : ContextOk Context}.

  Local Notation context_equiv := (@context_equiv base_type_code Name var Context).
  Local Notation extendb := (@extendb base_type_code Name var Context).
  Local Notation removeb := (@removeb base_type_code Name var Context).
  Local Notation lookupb := (@lookupb base_type_code Name var Context).
  Local Notation extend := (@extend base_type_code Name var Context).
  Local Notation remove := (@remove base_type_code Name var Context).
  Local Notation lookup := (@lookup base_type_code Name var Context).

  Global Instance context_equiv_Equivalence : Equivalence context_equiv | 10.
  Proof. split; repeat intro; congruence. Qed.
  Global Instance context_equiv_Reflexive : Reflexive context_equiv | 10 := _.
  Global Instance context_equiv_Symmetric : Symmetric context_equiv | 10 := _.
  Global Instance context_equiv_Transitive : Transitive context_equiv | 10 := _.

  Local Ltac proper_t n n' t t' :=
    destruct (dec (n = n')), (dec (t = t')); subst;
    repeat first [ reflexivity
                 | rewrite lookupb_extendb_same by assumption
                 | rewrite lookupb_extendb_different by assumption
                 | rewrite lookupb_extendb_wrong_type by assumption
                 | rewrite lookupb_removeb_same by assumption
                 | rewrite lookupb_removeb_different by assumption
                 | solve [ auto ] ].

  Global Instance extendb_Proper : forall {t}, Proper (context_equiv ==> eq ==> eq ==> context_equiv) (@extendb t) | 10.
  Proof.
    intros t ??? n n0 ???? n' t'; subst n0; subst; proper_t n n' t t'.
  Qed.
  Global Instance removeb_Proper : forall {t}, Proper (context_equiv ==> eq ==> context_equiv) (@removeb t) | 10.
  Proof.
    intros t ??? n n0 ? n' t'; subst n0; subst; proper_t n n' t t'.
  Qed.
  Global Instance lookupb_Proper : forall {t}, Proper (context_equiv ==> eq ==> eq) (@lookupb t) | 10.
  Proof. repeat intro; subst; auto. Qed.

  Local Ltac proper_t2 t :=
    let IHt1 := fresh "IHt1" in
    let IHt2 := fresh "IHt2" in
    induction t as [ | | ? IHt1 ? IHt2];
    simpl;
    repeat match goal with
           | [ |- context[fun a b => ?f a b] ]
             => change (fun a b => f a b) with f
           end;
    [ try exact _
    | repeat intro; auto
    | repeat intro; subst;
      destruct_head_prod;
      first [ eapply IHt2; [ eapply IHt1 | .. ]; auto
            | idtac ] ].

  Global Instance extend_Proper : forall {t}, Proper (context_equiv ==> eq ==> eq ==> context_equiv) (@extend t) | 10.
  Proof. intro t; proper_t2 t. Qed.
  Global Instance remove_Proper : forall {t}, Proper (context_equiv ==> eq ==> context_equiv) (@remove t) | 10.
  Proof. intro t; proper_t2 t. Qed.

  Global Instance lookup_Proper : forall {t}, Proper (context_equiv ==> eq ==> eq) (@lookup t) | 10.
  Proof.
    intro t; proper_t2 t.
    repeat match goal with
           | [ |- context G[lookup (?A * ?B) ?ctx (?na, ?nb)] ]
             => let G' := context G[match lookup A ctx na, lookup B ctx nb with
                                    | Some a, Some b => Some (a, b)
                                    | _, _ => None
                                    end] in
                change G'
           end.
    break_innermost_match;
      repeat match goal with
             | _ => progress subst
             | _ => progress inversion_option
             | _ => reflexivity
             | [ IHt2 : Proper _ (lookup t2), H : lookup _ _ _ = ?x, H' : lookup _ _ _ = ?y |- _ ]
               => assert (x = y)
                 by (rewrite <- H, <- H'; first [ eapply IHt1 | eapply IHt2 ]; (assumption || reflexivity));
                    clear H H'
             end.
  Qed.
End with_context.

Section language.
  Context {base_type_code}
          {base_type_code_dec : DecidableRel (@eq base_type_code)}
          {Name}
          {Name_dec : DecidableRel (@eq Name)}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          {interp_base_type : base_type_code -> Type}
          {interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst}
          {Context : @Context base_type_code Name interp_base_type}
          {ContextOk : ContextOk Context}.

  Local Notation context_equiv := (@context_equiv base_type_code Name interp_base_type Context).
  Local Notation interpf := (@interpf base_type_code interp_base_type op Name Context interp_op).
  Local Notation interp := (@interp base_type_code interp_base_type op Name Context interp_op).

  Global Instance interpf_Proper {t} : Proper (context_equiv ==> eq ==> eq) (@interpf t).
  Proof.
    intros c0 c1 Hc e e' ?; subst e'; revert c0 c1 Hc.
    induction e;
      repeat first [ progress subst
                   | reflexivity
                   | progress inversion_option
                   | progress simpl in *
                   | progress unfold LetIn.Let_In
                   | intros; eapply lookupb_Proper; (assumption || reflexivity)
                   | intros; eapply extendb_Proper; (assumption || reflexivity)
                   | intros; eapply lookup_Proper; (assumption || reflexivity)
                   | intros; eapply extend_Proper; (assumption || reflexivity)
                   | intros; erewrite_hyp *; [ | eassumption ]
                   | intros; erewrite_hyp *; [ reflexivity | ]
                   | break_innermost_match_step
                   | match goal with
                     | [ H : interpf _ = ?x, H' : interpf _ = ?y |- _ ]
                       => assert (x = y) by (rewrite <- H, <- H'; eauto); clear H H'
                     end ].
  Qed.

  Global Instance interp_Proper {t} : Proper (context_equiv ==> eq ==> eq ==> eq) (@interp t).
  Proof.
    intros ??? e e' ????; subst e'; subst.
    eapply interpf_Proper; [ eapply extend_Proper; auto | reflexivity ].
  Qed.
End language.

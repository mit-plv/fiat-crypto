Require Import Coq.Classes.Morphisms.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Util.Decidable.

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

  Global Instance extendb_Proper {t} : Proper (context_equiv ==> eq ==> eq ==> context_equiv) (@extendb t) | 10.
  Proof.
    intros ??? n n0 ???? n' t'; subst n0; subst; proper_t n n' t t'.
  Qed.
  Global Instance removeb_Proper {t} : Proper (context_equiv ==> eq ==> context_equiv) (@removeb t) | 10.
  Proof.
    intros ??? n n0 ? n' t'; subst n0; subst; proper_t n n' t t'.
  Qed.
  Global Instance lookupb_Proper {t} : Proper (context_equiv ==> eq ==> eq) (@lookupb t) | 10.
  Proof. repeat intro; subst; auto. Qed.
End with_context.

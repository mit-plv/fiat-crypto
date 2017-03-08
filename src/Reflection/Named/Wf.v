Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Util.PointedProp.

Section with_context.
  Context {base_type_code Name var} (Context : @Context base_type_code Name var).

  Class ContextOk :=
    { lookupb_extendb_same
      : forall (ctx : Context) n t v, lookupb (extendb ctx n (t:=t) v) n t = Some v;
      lookupb_extendb_different
      : forall (ctx : Context) n n' t t' v, n <> n' -> lookupb (extendb ctx n (t:=t) v) n' t'
                                                                                 = lookupb ctx n' t';
      lookupb_extendb_wrong_type
      : forall (ctx : Context) n t t' v, t <> t' -> lookupb (extendb ctx n (t:=t) v) n t' = None;
      lookupb_removeb
      : forall (ctx : Context) n n' t t', n <> n' -> lookupb (removeb ctx n t) n' t'
                                                                     = lookupb ctx n' t';
      lookupb_empty
      : forall n t, lookupb (@empty _ _ _ Context) n t = None }.

  Context (ContextOk : ContextOk).

  Lemma lookupb_eq_cast
    : forall (ctx : Context) n t t' (pf : t = t'),
      lookupb ctx n t' = option_map (fun v => eq_rect _ var v _ pf) (lookupb ctx n t).
  Proof.
    intros; subst; edestruct lookupb; reflexivity.
  Defined.
  Lemma lookupb_extendb_eq
    : forall (ctx : Context) n t t' (pf : t = t') v,
      lookupb (extendb ctx n (t:=t) v) n t' = Some (eq_rect _ var v _ pf).
  Proof.
    intros; subst; apply lookupb_extendb_same; assumption.
  Defined.
End with_context.

Module Export Named.
  Section language.
    Context {base_type_code Name var}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            (Context : @Context base_type_code Name var)
            (ContextOk : @ContextOk base_type_code Name var Context).

    Fixpoint wff (ctx : Context) {t} (e : @exprf base_type_code op Name t) : option pointed_Prop
      := match e with
         | TT => Some trivial
         | Var t n => match lookupb ctx n t return bool with
                      | Some _ => true
                      | None => false
                      end
         | Op _ _ op args => @wff ctx _ args
         | LetIn _ n ex _ eC => @wff ctx _ ex /\ inject (forall v, prop_of_option (@wff (extend ctx n v) _ eC))
         | Pair _ ex _ ey => @wff ctx _ ex /\ @wff ctx _ ey
         end%option_pointed_prop.

    Definition wf (ctx : Context) {t} (e : @expr base_type_code op Name t) : Prop
      := match e with
         | Abs src _ n f => forall v, prop_of_option (@wff (extend ctx (t:=src) n v) _ f)
         end.
  End language.
End Named.

Global Arguments wff {_ _ _ _ _} ctx {t} _.
Global Arguments wf {_ _ _ _ _} ctx {t} _.

Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Util.PointedProp.

Module Export Named.
  Section language.
    Context {base_type_code Name var}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            (Context : @Context base_type_code Name var).

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

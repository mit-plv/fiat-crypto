Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Util.PointedProp.

Module Export Named.
  Section language.
    Context {base_type_code Name : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
    Section with_var.
      Context {var}
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
        := forall v, prop_of_option (@wff (extend ctx (Abs_name e) v) _ (invert_Abs e)).
    End with_var.

    Definition Wf (Context : forall var, @Context base_type_code Name var) {t} (e : @expr base_type_code op Name t)
      := forall var, wf (Context var) empty e.
  End language.
End Named.

Global Arguments wff {_ _ _ _ _} ctx {t} _.
Global Arguments wf {_ _ _ _ _} ctx {t} _.
Global Arguments Wf {_ _ _} Context {t} _.

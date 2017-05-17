Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Util.PointedProp.

Module Export Named.
  Section language.
    Context {base_type_code Name : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}.
    Section with_var.
      Context {var}
              (Context : @Context base_type_code Name var).

      Section gen.
        Context (quantify : forall tx, (interp_flat_type var tx -> option pointed_Prop) -> option pointed_Prop).

        Fixpoint wff_gen (ctx : Context) {t} (e : @exprf base_type_code op Name t) : option pointed_Prop
          := match e with
             | TT => Some trivial
             | Var t n => match lookupb t ctx n return bool with
                          | Some _ => true
                          | None => false
                          end
             | Op _ _ op args => @wff_gen ctx _ args
             | LetIn _ n ex _ eC => @wff_gen ctx _ ex
                                    /\ quantify _ (fun v => @wff_gen (extend ctx n v) _ eC)
             | Pair _ ex _ ey => @wff_gen ctx _ ex /\ @wff_gen ctx _ ey
             end%option_pointed_prop.
      End gen.

      Definition wff := wff_gen (fun tx f => inject (forall v, prop_of_option (f v))).
      Definition wf (ctx : Context) {t} (e : @expr base_type_code op Name t) : Prop
        := forall v, prop_of_option (@wff (extend ctx (Abs_name e) v) _ (invert_Abs e)).
    End with_var.

    Section unit.
      Context (Context : @Context base_type_code Name (fun _ => unit)).

      Local Notation TT := (SmartValf _ (fun _ => tt) _).
      Definition wff_unit := wff_gen Context (fun tx f => f TT).
      Definition wf_unit ctx {t} (e : @expr base_type_code op Name t) : option pointed_Prop
        := @wff_unit (extend ctx (Abs_name e) TT) _ (invert_Abs e).
    End unit.

    Definition Wf (Context : forall var, @Context base_type_code Name var) {t} (e : @expr base_type_code op Name t)
      := forall var, wf (Context var) empty e.
  End language.
End Named.

Global Arguments wff_gen {_ _ _ _ _} quantify ctx {t} _.
Global Arguments wff_unit {_ _ _ _} ctx {t} _.
Global Arguments wf_unit {_ _ _ _} ctx {t} _.
Global Arguments wff {_ _ _ _ _} ctx {t} _.
Global Arguments wf {_ _ _ _ _} ctx {t} _.
Global Arguments Wf {_ _ _} Context {t} _.

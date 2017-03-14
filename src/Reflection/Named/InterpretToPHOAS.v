Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Wf.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.PointedProp.

Local Notation eta_and x := (conj (let (a, b) := x in a) (let (a, b) := x in b)).

Module Export Named.
  Section language.
    Context {base_type_code : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            {Name : Type}.
    Section with_var.
      Context {var : base_type_code -> Type}
              {Context : Context Name var}.

      Fixpoint interpf_to_phoas
               (ctx : Context)
               {t} (e : @Named.exprf base_type_code op Name t)
               {struct e}
        : prop_of_option (wff ctx e) -> @Syntax.exprf base_type_code op var t
        := match e in Named.exprf _ _ _ t return prop_of_option (wff ctx e) -> @Syntax.exprf base_type_code op var t with
           | Named.Var t' x
             => match lookupb ctx x t' as v return prop_of_option (if v return bool then true else false) -> _ with
                | Some v => fun _ => Var v
                | None => fun b => match b : False with end
                end
           | Named.TT => fun _ => TT
           | Named.Pair tx ex ty ey
             => fun Hwf : prop_of_option (Named.wff _ _ /\ Named.wff _ _)%option_pointed_prop
                => let (Hwf'1, Hwf'2) := eta_and (proj1 (prop_of_option_and _ _) Hwf) in
                   Pair (@interpf_to_phoas ctx tx ex Hwf'1) (@interpf_to_phoas ctx ty ey Hwf'2)
           | Named.Op _ _ opc args
             => fun Hwf
                => Op opc (@interpf_to_phoas ctx _ args Hwf)
           | Named.LetIn _ n ex _ eC
             => fun Hwf : prop_of_option (Named.wff _ _ /\ inject (forall k, prop_of_option (Named.wff _ _)))%option_pointed_prop
                => let (Hwf'1, Hwf'2) := eta_and (proj1 (prop_of_option_and _ _) Hwf) in
                   LetIn (@interpf_to_phoas ctx _ ex Hwf'1)
                         (fun v
                          => @interpf_to_phoas (extend ctx n v) _ eC (Hwf'2 _))
           end.

      Definition interp_to_phoas
                 (ctx : Context)
                 {t} (e : @Named.expr base_type_code op Name t)
                 (Hwf : wf ctx e)
        : @Syntax.expr base_type_code op var (domain t -> codomain t)
        := Abs (fun v => interpf_to_phoas (extend ctx (Abs_name e) v) (invert_Abs e) (Hwf v)).
    End with_var.

    Section all.
      Context {Context : forall var, @Context base_type_code Name var}.
      Definition InterpToPHOAS_gen
                 (ctx : forall var, Context var)
                 {t} (e : @Named.expr base_type_code op Name t)
                 (Hwf : forall var, wf (ctx var) e)
        : @Syntax.Expr base_type_code op (domain t -> codomain t)
        := fun var => interp_to_phoas (ctx var) e (Hwf var).

      Definition InterpToPHOAS {t} e (Hwf : forall var, wf empty e)
        := @InterpToPHOAS_gen (fun var => empty) t e Hwf.
    End all.
  End language.
End Named.

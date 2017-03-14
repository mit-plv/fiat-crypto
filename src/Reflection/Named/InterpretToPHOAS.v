Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.Wf.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.PointedProp.

Module Export Named.
  Section language.
    Context {base_type_code : Type}
            {op : flat_type base_type_code -> flat_type base_type_code -> Type}
            {var : base_type_code -> Type}
            (base_type_code_beq : base_type_code -> base_type_code -> bool)
            (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y)
            {Name}
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
              => let Hwf' := proj1 (prop_of_option_and _ _) Hwf in
                 Pair (@interpf_to_phoas ctx tx ex (proj1 Hwf')) (@interpf_to_phoas ctx ty ey (proj2 Hwf'))
         | Named.Op _ _ opc args
           => fun Hwf
              => Op opc (@interpf_to_phoas ctx _ args Hwf)
         | Named.LetIn _ n ex _ eC
           => fun Hwf : prop_of_option (Named.wff _ _ /\ inject (forall k, prop_of_option (Named.wff _ _)))%option_pointed_prop
              => let Hwf' := proj1 (prop_of_option_and _ _) Hwf in
                 LetIn (@interpf_to_phoas ctx _ ex (proj1 Hwf'))
                       (fun v
                        => @interpf_to_phoas (extend ctx n v) _ eC (proj2 Hwf' _))
         end.

    Definition interp_to_phoas
             (ctx : Context)
             {t} (e : @Named.expr base_type_code op Name t)
             (Hwf : wf ctx e)
      : @Syntax.expr base_type_code op var (domain t -> codomain t)
      := Abs (fun v => interpf_to_phoas (extend ctx (Abs_name e) v) (invert_Abs e) (Hwf v)).
  End language.
End Named.

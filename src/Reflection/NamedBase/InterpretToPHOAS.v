Require Import Crypto.Reflection.NamedBase.PositiveContext.
Require Import Crypto.Reflection.NamedBase.Syntax.
Require Import Crypto.Reflection.Syntax.

Module Export Named.
  Section language.
    Context {base_type_code : Type}
            {var : base_type_code -> Type}
            (base_type_code_beq : base_type_code -> base_type_code -> bool)
            (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y).

    Local Notation Context := (@PositiveContext base_type_code var _ base_type_code_bl_transparent).

    Definition interpf_to_phoas
               (ctx : Context)
               {t} (e : @Named.exprf base_type_code _ t)
               (Hwf : PointedProp.prop_of_option (wff ctx e))
      : @Syntax.exprf base_type_code (fun _ _ => unit) var (Tbase t)
      := interp_genf
           (fun t => @Syntax.exprf base_type_code (fun _ _ => unit) var (Tbase t))
           (fun t => Syntax.Var)
           (fun _ _ _ x y => Syntax.Op tt (Pair x y))
           (fun _ ex _ eC => Syntax.LetIn ex eC)
           e Hwf.
  End language.
End Named.

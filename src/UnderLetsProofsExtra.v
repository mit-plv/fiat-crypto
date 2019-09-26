Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.Identifier.
Require Import Crypto.IdentifierExtra.
Require Import Crypto.LanguageWfExtra.
Require Import Crypto.UnderLetsProofs.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import Identifier.Compilers.
  Import IdentifierExtra.Compilers.
  Import LanguageWfExtra.Compilers.
  Import UnderLetsProofs.Compilers.
  Import Compilers.defaults.

  Module SubstVarLike.
    Import UnderLetsProofs.Compilers.SubstVarLike.

    Definition Interp_gen_SubstVar {cast_outside_of_range} {t} e Hwf
      := @Interp_SubstVar _ ident _ (@ident.gen_interp cast_outside_of_range) (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.

    Definition Interp_gen_SubstVarLike {cast_outside_of_range} {t} e Hwf
      := @Interp_SubstVarLike _ ident _ (@ident.gen_interp cast_outside_of_range) (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.

    Definition Interp_gen_SubstVarOrIdent {cast_outside_of_range} {t} e Hwf
      := @Interp_SubstVarOrIdent _ ident _ (@ident.gen_interp cast_outside_of_range) (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.
  End SubstVarLike.

  Hint Resolve SubstVarLike.Wf_SubstVar SubstVarLike.Wf_SubstVarLike SubstVarLike.Wf_SubstVarOrIdent : wf_extra.
  Hint Rewrite @SubstVarLike.Interp_gen_SubstVar @SubstVarLike.Interp_gen_SubstVarLike @SubstVarLike.Interp_gen_SubstVarOrIdent : interp_extra.

  Module UnderLets.
    Import UnderLetsProofs.Compilers.UnderLets.

    Definition Wf_LetBindReturn {ident_is_var_like} {t} e Hwf
      := @Wf_LetBindReturn
           base.type.base ident.ident
           base.base_interp base.type.base_beq base.reflect_base_beq
           base.try_make_base_transport_cps invert_expr.ident.InvertIdent ident.buildIdent
           invert_expr.ident.buildInvertIdentCorrect
           base.try_make_base_transport_cps_correct
           ident_is_var_like t e Hwf.

    Definition Interp_gen_LetBindReturn {cast_outside_of_range} {ident_is_var_like} {t} e Hwf
      := @Interp_LetBindReturn
           base.type.base ident.ident
           base.base_interp base.type.base_beq base.reflect_base_beq
           base.try_make_base_transport_cps invert_expr.ident.InvertIdent ident.buildIdent
           invert_expr.ident.buildInvertIdentCorrect
           base.try_make_base_transport_cps_correct
           ident_is_var_like
           (@ident.gen_interp cast_outside_of_range) (@ident.gen_interp_Proper cast_outside_of_range)
           t e Hwf.
  End UnderLets.

  Hint Resolve UnderLets.Wf_LetBindReturn : wf_extra.
  Hint Rewrite @UnderLets.Interp_gen_LetBindReturn : interp_extra.
End Compilers.

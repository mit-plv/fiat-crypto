Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.API.
Require Import Crypto.Language.WfExtra.
Require Import Rewriter.Language.UnderLetsProofs.

Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import Language.API.Compilers.
  Import Language.WfExtra.Compilers.
  Import UnderLets.Compilers.
  Import UnderLetsProofs.Compilers.
  Import Compilers.API.

  Module SubstVarLike.
    Import UnderLetsProofs.Compilers.SubstVarLike.

    Definition Interp_SubstVar {t} e Hwf
      := @Interp_SubstVar _ ident _ (@ident.interp) (@ident.interp_Proper) t e Hwf.

    Definition Interp_SubstVarLike {t} e Hwf
      := @Interp_SubstVarLike _ ident _ (@ident.interp) (@ident.interp_Proper) t e Hwf.

    Definition Interp_SubstVarOrIdent {t} e Hwf
      := @Interp_SubstVarOrIdent _ ident _ (@ident.interp) (@ident.interp_Proper) t e Hwf.
  End SubstVarLike.

  Hint Resolve SubstVarLike.Wf_SubstVar SubstVarLike.Wf_SubstVarLike SubstVarLike.Wf_SubstVarOrIdent : wf_extra.
  Hint Opaque SubstVarLike.SubstVar SubstVarLike.SubstVarLike SubstVarLike.SubstVarOrIdent : wf_extra interp_extra.
  Hint Rewrite @SubstVarLike.Interp_SubstVar @SubstVarLike.Interp_SubstVarLike @SubstVarLike.Interp_SubstVarOrIdent : interp_extra.

  Module UnderLets.
    Import UnderLetsProofs.Compilers.UnderLets.

    Definition Wf_LetBindReturn {ident_is_var_like} {t} e Hwf
      := @Wf_LetBindReturn
           base.type.base ident.ident
           base.base_interp base.type.base_beq base.reflect_base_beq
           base.try_make_base_transport_cps invert_expr.ident.invertIdent ident.buildIdent
           invert_expr.ident.buildInvertIdentCorrect
           base.try_make_base_transport_cps_correct
           ident_is_var_like t e Hwf.

    Definition Interp_LetBindReturn {ident_is_var_like} {t} e Hwf
      := @Interp_LetBindReturn
           base.type.base ident.ident
           base.base_interp base.type.base_beq base.reflect_base_beq
           base.try_make_base_transport_cps invert_expr.ident.invertIdent ident.buildIdent
           invert_expr.ident.buildInvertIdentCorrect
           base.try_make_base_transport_cps_correct
           ident_is_var_like
           (@ident.interp) (@ident.interp_Proper)
           t e Hwf.
  End UnderLets.

  Hint Resolve UnderLets.Wf_LetBindReturn : wf_extra.
  Hint Opaque UnderLets.LetBindReturn : wf_extra interp_extra.
  Hint Rewrite @UnderLets.Interp_LetBindReturn : interp_extra.
End Compilers.

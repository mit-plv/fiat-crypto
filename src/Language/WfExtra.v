Require Import Rewriter.Language.Language.
Require Import Rewriter.Language.Wf.
Require Import Crypto.Language.API.

Module Compilers.
  Import Language.Compilers.
  Import Language.Inversion.Compilers.
  Import Language.Wf.Compilers.
  Import Language.API.Compilers.
  Import Compilers.API.

  Create HintDb wf_extra discriminated.
  Create HintDb interp_extra discriminated.
  Hint Constants Opaque : wf_extra interp_extra.

  Hint Opaque expr.interp expr.Interp : interp_extra.
  Hint Opaque expr.Wf expr.Wf3 : wf_extra interp_extra.

  Module expr.
    Import Language.Wf.Compilers.expr.
    Global Hint Constructors wf : wf_extra.
    Global Hint Resolve Wf_APP : wf_extra.
    Global Hint Opaque expr.APP : wf_extra interp_extra.
    Hint Rewrite @expr.Interp_APP : interp_extra.
    Global Hint Immediate Wf_of_Wf3 : wf_extra.
    Global Hint Resolve Wf3_of_Wf : wf_extra.

    Definition Wf_base_Reify_as {t} v
      := @Wf_base_Reify_as base.type.base base.base_interp base.type.base_beq ident ident.buildIdent base.reflect_base_beq t v.

    Definition Wf_Reify_as {t} v
      := @Wf_Reify_as base.type.base base.base_interp base.type.base_beq ident ident.buildIdent base.reflect_base_beq t v.

    Definition Wf_base_reify {t} v
      := @Wf_base_reify base.type.base base.base_interp base.type.base_beq ident ident.buildIdent base.reflect_base_beq t v.

    Definition Wf_reify {t} v
      := @Wf_reify base.type.base base.base_interp base.type.base_beq ident ident.buildIdent base.reflect_base_beq t v.

    Definition Interp_Reify_as {t} v
      := @Interp_Reify_as base.type.base base.base_interp ident ident.buildIdent (@ident.interp) ident.buildInterpIdentCorrect t v.

    Definition Interp_reify {t} v
      := @Interp_reify base.type.base base.base_interp ident ident.buildIdent (@ident.interp) ident.buildInterpIdentCorrect t v.

    Definition interp_reify {t} v
      := @interp_reify base.type.base base.base_interp ident ident.buildIdent (@ident.interp) ident.buildInterpIdentCorrect t v.

    Definition interp_reify_list {t} v
      := @interp_reify_list base.type.base base.base_interp ident ident.buildIdent (@ident.interp) ident.buildInterpIdentCorrect t v.

    Definition interp_reify_option {t} v
      := @interp_reify_option base.type.base base.base_interp ident ident.buildIdent (@ident.interp) ident.buildInterpIdentCorrect t v.

    Definition Wf_Interp_Proper {t} e Hwf
      := @Wf_Interp_Proper_gen _ ident _ _ (@ident.interp) (@ident.interp_Proper) t e Hwf.
  End expr.

  Hint Constructors expr.wf : wf_extra.
  Hint Resolve expr.Wf_APP expr.Wf_Reify_as expr.Wf_base_Reify_as expr.Wf_reify expr.Wf_base_reify : wf_extra.
  (** Work around COQBUG(https://github.com/coq/coq/issues/11536) *)
  Hint Extern 0 (expr.Wf (GallinaReify.base.Reify_as _ _)) => simple apply (@expr.Wf_base_Reify) : wf_extra.
  Hint Extern 0 (expr.Wf (GallinaReify.Reify_as _ _)) => simple apply (@expr.Wf_Reify) : wf_extra.
  (** Work around COQBUG(https://github.com/coq/coq/issues/11536) *)
  Hint Extern 0 (expr.Wf (fun var => GallinaReify.base.reify _)) => simple apply (@expr.Wf_base_reify) : wf_extra.
  Hint Extern 0 (expr.Wf (fun var => GallinaReify.reify _)) => simple apply (@expr.Wf_reify) : wf_extra.
  Hint Opaque expr.APP GallinaReify.Reify_as GallinaReify.base.reify : wf_extra interp_extra.
  Hint Rewrite @expr.Interp_Reify_as @expr.interp_reify @expr.interp_reify_list @expr.interp_reify_option @expr.Interp_reify @expr.Interp_APP : interp_extra.

  Module GeneralizeVar.
    Import Language.Wf.Compilers.GeneralizeVar.

    Definition Wf_FromFlat_ToFlat {t} e Hwf
      := @Wf_FromFlat_ToFlat _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ t e Hwf.

    Definition Wf_GeneralizeVar {t} e Hwf
      := @Wf_GeneralizeVar _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ t e Hwf.

    Definition Interp_FromFlat_ToFlat {t} e Hwf
      := @Interp_gen1_FromFlat_ToFlat _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ _ (@ident.interp) _ (@ident.interp_Proper) t e Hwf.

    Definition Interp_GeneralizeVar {t} e Hwf
      := @Interp_gen1_GeneralizeVar _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ _ (@ident.interp) _ (@ident.interp_Proper) t e Hwf.
  End GeneralizeVar.

  Global Hint Extern 0 (?x == ?x) => apply expr.Wf_Interp_Proper_gen : wf_extra interp_extra.
  Hint Resolve GeneralizeVar.Wf_FromFlat_ToFlat GeneralizeVar.Wf_GeneralizeVar : wf_extra.
  Hint Opaque GeneralizeVar.FromFlat GeneralizeVar.ToFlat GeneralizeVar.GeneralizeVar : wf_extra interp_extra.
  Hint Rewrite @GeneralizeVar.Interp_GeneralizeVar @GeneralizeVar.Interp_FromFlat_ToFlat : interp_extra.
End Compilers.

Require Import Crypto.Language.
Require Import Crypto.LanguageWf.
Require Import Crypto.Identifier.
Require Import Crypto.IdentifierExtra.

Module Compilers.
  Import Language.Compilers.
  Import LanguageInversion.Compilers.
  Import LanguageWf.Compilers.
  Import Identifier.Compilers.
  Import IdentifierExtra.Compilers.
  Import Compilers.defaults.

  Create HintDb wf_extra discriminated.
  Create HintDb interp_extra discriminated.

  Module expr.
    Import LanguageWf.Compilers.expr.
    Global Hint Constructors wf : wf_extra.
    Global Hint Resolve @Wf_APP : wf_extra.
    Hint Rewrite @expr.Interp_APP : interp_extra.
    Global Hint Resolve Wf_of_Wf3 : wf_extra.

    Definition Wf_Reify_as {t} v
      := @Wf_Reify_as base.type.base base.base_interp base.type.base_beq ident ident.buildIdent base.reflect_base_beq t v.

    Definition Wf_reify {t} v
      := @Wf_reify base.type.base base.base_interp base.type.base_beq ident ident.buildIdent base.reflect_base_beq t v.

    Definition Interp_gen_Reify_as {cast_outside_of_range} {t} v
      := @Interp_Reify_as base.type.base base.base_interp ident ident.buildIdent (@ident.gen_interp cast_outside_of_range) ident.buildInterpIdentCorrect t v.

    Definition Interp_gen_reify {cast_outside_of_range} {t} v
      := @Interp_reify base.type.base base.base_interp ident ident.buildIdent (@ident.gen_interp cast_outside_of_range) ident.buildInterpIdentCorrect t v.

    Definition interp_gen_reify {cast_outside_of_range} {t} v
      := @interp_reify base.type.base base.base_interp ident ident.buildIdent (@ident.gen_interp cast_outside_of_range) ident.buildInterpIdentCorrect t v.

    Definition interp_gen_reify_list {cast_outside_of_range} {t} v
      := @interp_reify_list base.type.base base.base_interp ident ident.buildIdent (@ident.gen_interp cast_outside_of_range) ident.buildInterpIdentCorrect t v.

    Definition interp_gen_reify_option {cast_outside_of_range} {t} v
      := @interp_reify_option base.type.base base.base_interp ident ident.buildIdent (@ident.gen_interp cast_outside_of_range) ident.buildInterpIdentCorrect t v.

    Definition Wf_Interp_Proper_gen {cast_outside_of_range} {t} e Hwf
      := @Wf_Interp_Proper_gen _ ident _ _ (@ident.gen_interp cast_outside_of_range) (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.
  End expr.

  Hint Constructors expr.wf : wf_extra.
  Hint Resolve @expr.Wf_APP @expr.Wf_Reify_as @expr.Wf_reify : wf_extra.
  Hint Rewrite @expr.Interp_gen_Reify_as @expr.interp_gen_reify @expr.interp_gen_reify_list @expr.interp_gen_reify_option @expr.Interp_gen_reify @expr.Interp_APP : interp_extra.

  Module GeneralizeVar.
    Import LanguageWf.Compilers.GeneralizeVar.

    Definition Wf_FromFlat_ToFlat {t} e Hwf
      := @Wf_FromFlat_ToFlat _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ t e Hwf.

    Definition Wf_GeneralizeVar {t} e Hwf
      := @Wf_GeneralizeVar _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ t e Hwf.

    Definition Wf3_FromFlat_ToFlat {t} e Hwf
      := @Wf3_FromFlat_ToFlat _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ t e Hwf.

    Definition Wf3_GeneralizeVar {t} e Hwf
      := @Wf3_GeneralizeVar _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ t e Hwf.

    Definition Interp_gen1_FromFlat_ToFlat {cast_outside_of_range} {t} e Hwf
      := @Interp_gen1_FromFlat_ToFlat _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ _ (@ident.gen_interp cast_outside_of_range) _ (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.

    Definition Interp_gen1_GeneralizeVar {cast_outside_of_range} {t} e Hwf
      := @Interp_gen1_GeneralizeVar _ ident (@base.try_make_transport_cps _ base.try_make_base_transport_cps) (base.type.type_beq _ base.type.base_beq) base.reflect_type_beq base.try_make_transport_cps_correct _ _ (@ident.gen_interp cast_outside_of_range) _ (@ident.gen_interp_Proper cast_outside_of_range) t e Hwf.
  End GeneralizeVar.

  Global Hint Extern 0 (?x == ?x) => apply expr.Wf_Interp_Proper_gen : wf_extra interp_extra.
  Hint Resolve GeneralizeVar.Wf_FromFlat_ToFlat GeneralizeVar.Wf_GeneralizeVar : wf_extra.
  Hint Resolve GeneralizeVar.Wf3_FromFlat_ToFlat GeneralizeVar.Wf3_GeneralizeVar : wf_extra.
  Hint Rewrite @GeneralizeVar.Interp_gen1_GeneralizeVar @GeneralizeVar.Interp_gen1_FromFlat_ToFlat : interp_extra.
End Compilers.

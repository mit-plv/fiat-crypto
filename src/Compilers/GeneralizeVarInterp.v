Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.InterpretToPHOASInterp.
Require Import Crypto.Compilers.Named.CompileInterp.
Require Import Crypto.Compilers.Named.CompileInterpSideConditions.
Require Import Crypto.Compilers.Named.CompileWf.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.PositiveContext.Defaults.
Require Import Crypto.Compilers.Named.PositiveContext.DefaultsProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.GeneralizeVar.
Require Import Crypto.Compilers.InterpSideConditions.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
Require Import Crypto.Util.PointedProp.
Require Import Crypto.Util.Tactics.BreakMatch.

Section language.
  Context {base_type_code : Type}
          {op : flat_type base_type_code -> flat_type base_type_code -> Type}
          (base_type_code_beq : base_type_code -> base_type_code -> bool)
          (base_type_code_bl_transparent : forall x y, base_type_code_beq x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> base_type_code_beq x y = true)
          (failb : forall var t, @Syntax.exprf base_type_code op var (Tbase t))
          {interp_base_type : base_type_code -> Type}
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst).

  Local Notation GeneralizeVar
    := (@GeneralizeVar
          base_type_code op base_type_code_beq base_type_code_bl_transparent
          failb).

  Local Notation PositiveContextOk := (@PositiveContextOk base_type_code _ base_type_code_beq base_type_code_bl_transparent base_type_code_lb).

  Local Instance dec_base_type_code_eq : DecidableRel (@eq base_type_code).
  Proof.
    refine (fun x y => (if base_type_code_beq x y as b return base_type_code_beq x y = b -> Decidable (x = y)
                        then fun pf => left (base_type_code_bl_transparent _ _ pf)
                        else fun pf => right _) eq_refl).
    { clear -pf base_type_code_lb.
      let pf := pf in
      abstract (intro; erewrite base_type_code_lb in pf by eassumption; congruence). }
  Defined.

  Local Arguments Compile.compile : simpl never.
  Lemma interp_GeneralizeVar
        {t} (e1 e2 : expr base_type_code op t)
        (Hwf : wf e1 e2)
        e'
        (He' : GeneralizeVar e1 = Some e')
    : forall v, Interp interp_op e' v = interp interp_op e2 v.
  Proof using base_type_code_lb.
    unfold GeneralizeVar.GeneralizeVar, option_map in *.
    break_innermost_match_hyps; inversion_option; subst; intro.
    change (interp interp_op (?e ?var) ?v') with (Interp interp_op e v').
    unfold Interp, InterpretToPHOAS.Named.InterpToPHOAS, InterpretToPHOAS.Named.InterpToPHOAS_gen.
    match goal with |- ?L = ?R => cut (Some L = Some R); [ congruence | ] end.
    setoid_rewrite <- interp_interp_to_phoas.
    { erewrite (interp_compile (ContextOk:=PositiveContextOk)) with (e':=e2);
        [ reflexivity | auto | .. | eassumption ];
        auto using name_list_unique_default_names_for. }
    { eapply (wf_compile (ContextOk:=PositiveContextOk) (make_var':=fun _ => id)) with (e':= e2);
        [ auto | .. | eassumption ];
        auto using name_list_unique_default_names_for. }
  Qed.

  Lemma InterpGeneralizeVar
        {t} (e : Expr base_type_code op t)
        (Hwf : Wf e)
        e'
        (He' : GeneralizeVar (e _) = Some e')
    : forall v, Interp interp_op e' v = Interp interp_op e v.
  Proof using base_type_code_lb. eapply interp_GeneralizeVar; eauto. Qed.
End language.

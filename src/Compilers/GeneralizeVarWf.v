Require Import Coq.PArith.BinPos.
Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.InterpretToPHOASWf.
Require Import Crypto.Compilers.Named.CompileWf.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.PositiveContext.Defaults.
Require Import Crypto.Compilers.Named.PositiveContext.DefaultsProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.GeneralizeVar.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Sigma.
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
  Proof using base_type_code_lb base_type_code_bl_transparent.
    refine (fun x y => (if base_type_code_beq x y as b return base_type_code_beq x y = b -> Decidable (x = y)
                        then fun pf => left (base_type_code_bl_transparent _ _ pf)
                        else fun pf => right _) eq_refl).
    { clear -pf base_type_code_lb.
      let pf := pf in
      abstract (intro; erewrite base_type_code_lb in pf by eassumption; congruence). }
  Defined.

  Local Arguments Compile.compile : simpl never.
  Lemma Wf_GeneralizeVar'
        {var'} {make_var' : forall t, var' t}
        {t} (e1 e2 : expr base_type_code op t)
        e'
        (He' : GeneralizeVar e1 = Some e')
        (Hwf : wf (var2:=var') e1 e2)
    : Wf e'.
  Proof using base_type_code_lb.
    unfold GeneralizeVar, option_map in *.
    break_innermost_match_hyps; try congruence; intros v v'; [].
    inversion_option; subst.
    unfold InterpretToPHOAS.Named.InterpToPHOAS, InterpretToPHOAS.Named.InterpToPHOAS_gen.
    destruct t as [src dst].
    eapply (@wf_interp_to_phoas
              base_type_code op FMapPositive.PositiveMap.key _ _ _ _
              (PositiveContext base_type_code _ base_type_code_beq base_type_code_bl_transparent)
              (PositiveContext base_type_code _ base_type_code_beq base_type_code_bl_transparent)
              PositiveContextOk PositiveContextOk
              (failb _) (failb _) _ _);
      eapply (wf_compile (ContextOk:=PositiveContextOk) (make_var':=fun t _ => make_var' t));
      try eassumption;
      auto using name_list_unique_default_names_for.
  Qed.

  Lemma Wf_GeneralizeVar
        {t} (e : expr base_type_code op t)
        e'
        (He' : GeneralizeVar e = Some e')
        (Hwf : wf e e)
    : Wf e'.
  Proof using base_type_code_lb.
    eapply @Wf_GeneralizeVar'; eauto; intros; exact 1%positive.
  Qed.

  Lemma Wf_GeneralizeVar'_arrow
        {var'} {make_var' : forall t, var' t}
        {s d} (e1 e2 : expr base_type_code op (Arrow s d))
        e'
        (He' : GeneralizeVar e1 = Some e')
        (Hwf : wf (var2:=var') e1 e2)
    : Wf e'.
  Proof using base_type_code_lb. eapply @Wf_GeneralizeVar'; eassumption. Qed.

  Lemma Wf_GeneralizeVar_arrow
        {s d} (e : expr base_type_code op (Arrow s d))
        e'
        (He' : GeneralizeVar e = Some e')
        (Hwf : wf e e)
    : Wf e'.
  Proof using base_type_code_lb. eapply Wf_GeneralizeVar; eassumption. Qed.
End language.

Hint Resolve Wf_GeneralizeVar Wf_GeneralizeVar_arrow Wf_GeneralizeVar' Wf_GeneralizeVar'_arrow : wf.

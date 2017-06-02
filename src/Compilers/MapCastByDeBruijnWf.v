Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.MapCastWf.
Require Import Crypto.Compilers.Named.InterpretToPHOASWf.
Require Import Crypto.Compilers.Named.CompileWf.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.PositiveContext.Defaults.
Require Import Crypto.Compilers.Named.PositiveContext.DefaultsProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.MapCastByDeBruijn.
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
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          {interp_base_type_bounds : base_type_code -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (pick_typeb : forall t, interp_base_type_bounds t -> base_type_code).
  Local Notation pick_type v := (SmartFlatTypeMap pick_typeb v).
  Context (cast_op : forall t tR (opc : op t tR) args_bs,
              op (pick_type args_bs) (pick_type (interp_op_bounds t tR opc args_bs)))
          (cast_backb: forall t b, interp_base_type (pick_typeb t b) -> interp_base_type t).
  Let cast_back : forall t b, interp_flat_type interp_base_type (pick_type b) -> interp_flat_type interp_base_type t
    := fun t b => SmartFlatTypeMapUnInterp cast_backb.
  Context (inboundsb : forall t, interp_base_type_bounds t -> interp_base_type t -> Prop).
  Let inbounds : forall t, interp_flat_type interp_base_type_bounds t -> interp_flat_type interp_base_type t -> Prop
    := fun t => interp_flat_type_rel_pointwise inboundsb (t:=t).
  Context (interp_op_bounds_correct
           : forall t tR opc bs
                    (v : interp_flat_type interp_base_type t)
                    (H : inbounds t bs v),
              inbounds tR (interp_op_bounds t tR opc bs) (interp_op t tR opc v))
          (pull_cast_back
           : forall t tR opc bs
                    (v : interp_flat_type interp_base_type (pick_type bs))
                    (H : inbounds t bs (cast_back t bs v)),
              interp_op t tR opc (cast_back t bs v)
              =
              cast_back _ _ (interp_op _ _ (cast_op _ _ opc bs) v)).

  Local Notation MapCast
    := (@MapCast
          base_type_code op base_type_code_beq base_type_code_bl_transparent
          failb interp_base_type_bounds interp_op_bounds pick_typeb cast_op).

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
  Lemma Wf_MapCast
        {t} (e : Expr base_type_code op t)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : forall {b} e' (He':MapCast e input_bounds = Some (existT _ b e')) (Hwf : Wf e),
      Wf e'.
  Proof using base_type_code_lb.
    unfold MapCastByDeBruijn.MapCast, MapCastCompile, MapCastDoCast, MapCastDoInterp, option_map; intros b e'.
    break_innermost_match; try congruence; intros ? v v'.
    inversion_option; inversion_sigma; subst; simpl in *; intros.
    unfold InterpretToPHOAS.Named.InterpToPHOAS, InterpretToPHOAS.Named.InterpToPHOAS_gen.
    destruct t as [src dst].
    eapply (@wf_interp_to_phoas
              base_type_code op FMapPositive.PositiveMap.key _ _ _ _
              (PositiveContext base_type_code _ base_type_code_beq base_type_code_bl_transparent)
              (PositiveContext base_type_code _ base_type_code_beq base_type_code_bl_transparent)
              PositiveContextOk PositiveContextOk
              (failb _) (failb _) _ e1);
      (eapply wf_map_cast with (fValues:=empty); eauto using PositiveContextOk with typeclass_instances);
      try (eapply (wf_compile (ContextOk:=PositiveContextOk));
           [ eauto
           | ..
           | eassumption ]);
      try solve [ auto using name_list_unique_DefaultNamesFor
                | intros ???; rewrite lookupb_empty by apply PositiveContextOk; congruence ].
  Qed.

  Lemma Wf_MapCast_arrow
        {s d} (e : Expr base_type_code op (Arrow s d))
        (input_bounds : interp_flat_type interp_base_type_bounds s)
    : forall {b} (e' : Expr _ _ (Arrow (pick_type input_bounds) (pick_type b)))
             (He':MapCast e input_bounds = Some (existT _ b e'))
             (Hwf : Wf e),
      Wf e'.
  Proof using base_type_code_lb. exact (@Wf_MapCast (Arrow s d) e input_bounds). Qed.
End language.

Hint Resolve Wf_MapCast Wf_MapCast_arrow : wf.

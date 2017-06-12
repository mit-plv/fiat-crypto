Require Import Crypto.Compilers.SmartMap.
Require Import Crypto.Compilers.Wf.
Require Import Crypto.Compilers.Relations.
Require Import Crypto.Compilers.Named.Context.
Require Import Crypto.Compilers.Named.Syntax.
Require Import Crypto.Compilers.Named.ContextDefinitions.
Require Import Crypto.Compilers.Named.MapCastInterp.
Require Import Crypto.Compilers.Named.MapCastWf.
Require Import Crypto.Compilers.Named.InterpretToPHOASInterp.
Require Import Crypto.Compilers.Named.CompileInterp.
Require Import Crypto.Compilers.Named.CompileInterpSideConditions.
Require Import Crypto.Compilers.Named.CompileWf.
Require Import Crypto.Compilers.Named.PositiveContext.
Require Import Crypto.Compilers.Named.PositiveContext.Defaults.
Require Import Crypto.Compilers.Named.PositiveContext.DefaultsProperties.
Require Import Crypto.Compilers.Syntax.
Require Import Crypto.Compilers.MapCastByDeBruijn.
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
          (interp_op : forall src dst, op src dst -> interp_flat_type interp_base_type src -> interp_flat_type interp_base_type dst)
          {interp_base_type_bounds : base_type_code -> Type}
          (interp_op_bounds : forall src dst, op src dst -> interp_flat_type interp_base_type_bounds src -> interp_flat_type interp_base_type_bounds dst)
          (interped_op_side_conditions : forall s d, op s d -> interp_flat_type interp_base_type s -> pointed_Prop)
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
                    (H : inbounds t bs v)
                    (Hside : to_prop (interped_op_side_conditions _ _ opc v)),
              inbounds tR (interp_op_bounds t tR opc bs) (interp_op t tR opc v))
          (pull_cast_back
           : forall t tR opc bs
                    (v : interp_flat_type interp_base_type (pick_type bs))
                    (H : inbounds t bs (cast_back t bs v))
                    (Hside : to_prop (interped_op_side_conditions _ _ opc (cast_back t bs v))),
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
  Lemma MapCastCorrect
        {t} (e : Expr base_type_code op t)
        (Hwf : Wf e)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : forall {b} e' (He':MapCast e input_bounds = Some (existT _ b e'))
             v v' (Hv : @inbounds _ input_bounds v /\ cast_back _ _ v' = v)
             (Hside : to_prop (InterpSideConditions interp_op interped_op_side_conditions e v)),
      Interp interp_op_bounds e input_bounds = b
      /\ @inbounds _ b (Interp interp_op e v)
      /\ cast_back _ _ (Interp interp_op e' v') = (Interp interp_op e v).
  Proof using base_type_code_lb interp_op_bounds_correct pull_cast_back.
    unfold MapCastByDeBruijn.MapCast, MapCastCompile, MapCastDoCast, MapCastDoInterp, option_map; intros b e'.
    break_innermost_match; try congruence; intros ? v v'.
    inversion_option; inversion_sigma; subst; simpl in *; intros.
    lazymatch goal with
    | [ H : MapCast.map_cast _ _ _ _ _ _ = Some _ |- _ ]
      => eapply map_cast_correct with (t:=Arrow _ _) (oldValues:=empty) (newValues:=empty) in H;
           [ destruct H; split; [ | eassumption ] | try eassumption.. ]
    end;
      try solve [ eassumption
                | auto using PositiveContextOk with typeclass_instances
                | repeat first [ rewrite !lookupb_empty by (apply PositiveContextOk; assumption)
                               | intro
                               | congruence ] ];
      unfold Interp;
      [ match goal with
        | [ H : ?y = Some ?b |- ?x = ?b ]
          => cut (y = Some x); [ congruence | ]
        end
      |
      | change (interp interp_op (?e ?var) ?v') with (Interp interp_op e v');
        unfold Interp, InterpretToPHOAS.Named.InterpToPHOAS, InterpretToPHOAS.Named.InterpToPHOAS_gen;
        rewrite <- interp_interp_to_phoas; [ reflexivity | ]
      | ].
    { erewrite (interp_compile (ContextOk:=PositiveContextOk)) with (e':=e _);
        [ reflexivity | auto | .. | eassumption ];
        auto using name_list_unique_DefaultNamesFor. }
    { erewrite (interp_compile (ContextOk:=PositiveContextOk)) with (e':=e _);
        [ reflexivity | auto | .. | eassumption ];
        auto using name_list_unique_DefaultNamesFor. }
    { intro; eapply wf_map_cast with (t := Arrow _ _) (fValues := empty); eauto using PositiveContextOk with typeclass_instances.
      { eapply (wf_compile (ContextOk:=PositiveContextOk)) with (e':= e _);
          [ auto | .. | eassumption ];
          auto using name_list_unique_DefaultNamesFor. }
      { intros ???; rewrite lookupb_empty by apply PositiveContextOk; congruence. } }
    { erewrite (interp_side_conditions_compile (ContextOk:=PositiveContextOk)) with (e':=e _);
        [ assumption | auto | .. | eassumption ];
        auto using name_list_unique_DefaultNamesFor. }
  Qed.
End language.

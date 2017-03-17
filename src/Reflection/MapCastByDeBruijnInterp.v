Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Named.Syntax.
Require Import Crypto.Reflection.Named.ContextDefinitions.
Require Import Crypto.Reflection.Named.MapCastInterp.
Require Import Crypto.Reflection.Named.InterpretToPHOASInterp.
Require Import Crypto.Reflection.Named.CompileInterp.
Require Import Crypto.Reflection.Named.PositiveContext.
Require Import Crypto.Reflection.Named.PositiveContext.Defaults.
Require Import Crypto.Reflection.LinearizeInterp.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.MapCastByDeBruijn.
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
  Context (cast_op : forall var t tR (opc : op t tR) args_bs
                            (args : exprf base_type_code op (var:=var) (pick_type args_bs)),
              option (exprf base_type_code op (var:=var) (pick_type (interp_op_bounds t tR opc args_bs))))
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
          (wff_cast_op
           : forall var1 var2 t tR opc args_bs args1 args2 G v1 v2,
              cast_op var1 t tR opc args_bs args1 = Some v1
              -> cast_op var2 t tR opc args_bs args2 = Some v2
              -> wff G args1 args2
              -> wff G v1 v2)
          (pull_cast_back
           : forall t tR opc bs
                    (args : exprf base_type_code op (pick_type bs))
                    new_e
                    (Hnew : cast_op _ _ _ opc bs args = Some new_e)
                    (H : inbounds t bs (cast_back t bs (interpf interp_op args))),
              interp_op t tR opc (cast_back t bs (interpf interp_op args))
              =
              cast_back _ _ (interpf interp_op new_e)).

  Local Notation MapCast
    := (@MapCast
          base_type_code op base_type_code_beq base_type_code_bl_transparent
          failb interp_base_type_bounds interp_op_bounds pick_typeb cast_op).

  Local Instance dec_base_type_code_eq : DecidableRel (@eq base_type_code).
  Proof.
    refine (fun x y => (if base_type_code_beq x y as b return base_type_code_beq x y = b -> Decidable (x = y)
                        then fun pf => left (base_type_code_bl_transparent _ _ pf)
                        else fun pf => right _) eq_refl).
    { clear -pf base_type_code_lb.
      abstract (intro; erewrite base_type_code_lb in pf by eassumption; congruence). }
  Defined.

  Lemma MapCastCorrect
        {t} (e : Expr base_type_code op t)
        (input_bounds : interp_flat_type interp_base_type_bounds (domain t))
    : forall {b} e' (He':MapCast e input_bounds = Some (existT _ b e'))
             v v' (Hv : @inbounds _ input_bounds v /\ cast_back _ _ v' = v),
      @inbounds _ b (Interp interp_op e v)
      /\ cast_back _ _ (Interp interp_op e' v') = (Interp interp_op e v).
  Proof.
    unfold MapCastByDeBruijn.MapCast, option_map; intros b e'.
    break_innermost_match; try congruence; intros ? v v'.
    inversion_option; inversion_sigma; subst; simpl in *; intros.
    match goal with
    | [ H : MapCast.map_cast _ _ _ _ _ _ = Some _ |- _ ]
      => eapply map_cast_correct with (oldValues:=empty) (newValues:=empty) in H; try eassumption
    end;
      try solve [ auto using PositiveContextOk with typeclass_instances
                | repeat first [ rewrite !lookupb_empty by (apply PositiveContextOk; assumption)
                               | intro
                               | congruence ] ].
  Admitted.
End language.

Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Z.InterpretationsGen.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Import Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.

Module Relations.
  Section proj.
    Context {interp_base_type1 interp_base_type2}
            (proj : forall t : base_type, interp_base_type1 t -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      SmartVarfMap (t:=t) proj f = g.

    Definition interp_type_rel_pointwise_uncurried_proj
               {t : type base_type}
      : interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop
      := fun f g
         => forall x : interp_flat_type interp_base_type1 (domain t),
             let y := SmartVarfMap proj x in
             let fx := f x in
             let gy := g y in
             @R _ fx gy.

    Lemma uncurry_interp_type_rel_pointwise_proj
          {t : type base_type}
          {f}
          {g}
      : (forall x y, @R (domain t) x y -> @R (codomain t) (f x) (g y))
        -> interp_type_rel_pointwise_uncurried_proj (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise_uncurried_proj.
      destruct t as [A B]; simpl in *.
      subst R; simpl in *.
      eauto.
    Qed.
  End proj.

  Section proj_option.
    Context {interp_base_type1 : Type} {interp_base_type2 : base_type -> Type}
            (proj_option : forall t, interp_base_type1 -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      let f' := LiftOption.of' (t:=t) f in
      match f' with
      | Some f' => SmartVarfMap proj_option f' = g
      | None => True
      end.

    Definition interp_type_rel_pointwise_uncurried_proj_option
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop
      := fun f g
         => forall x : interp_flat_type (fun _ => interp_base_type1) (domain t),
             let y := SmartVarfMap proj_option x in
             let fx := f (LiftOption.to' (Some x)) in
             let gy := g y in
             @R _ fx gy.

    Lemma uncurry_interp_type_rel_pointwise_proj_option
          {t : type base_type}
          {f}
          {g}
      : (forall x y, @R (domain t) x y -> @R (codomain t) (f x) (g y))
        -> interp_type_rel_pointwise_uncurried_proj_option (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise_uncurried_proj_option.
      destruct t as [A B]; simpl in *.
      subst R; simpl in *.
      intros H x; apply H; simpl.
      rewrite LiftOption.of'_to'; reflexivity.
    Qed.
  End proj_option.

  Section proj_option2.
    Context {interp_base_type1 : Type} {interp_base_type2 : Type}
            (proj : interp_base_type1 -> interp_base_type2).

    Let R {t : flat_type base_type} f g :=
      let f' := LiftOption.of' (t:=t) f in
      let g' := LiftOption.of' (t:=t) g in
      match f', g' with
      | Some f', Some g' => SmartVarfMap (fun _ => proj) f' = g'
      | None, None => True
      | Some _, _ => False
      | None, _ => False
      end.

    Definition interp_type_rel_pointwise_uncurried_proj_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type (LiftOption.interp_base_type' interp_base_type2) t -> Prop
      := fun f g
         => forall x : interp_flat_type (fun _ => interp_base_type1) (domain t),
             let y := SmartVarfMap (fun _ => proj) x in
             let fx := f (LiftOption.to' (Some x)) in
             let gy := g (LiftOption.to' (Some y)) in
             @R _ fx gy.

    Lemma uncurry_interp_type_rel_pointwise_proj_option2
          {t : type base_type}
          {f}
          {g}
      : (forall x y, @R (domain t) x y -> @R (codomain t) (f x) (g y))
        -> interp_type_rel_pointwise_uncurried_proj_option2 (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise_uncurried_proj_option2.
      destruct t as [A B]; simpl in *.
      subst R; simpl in *.
      intros H x; apply H; simpl.
      rewrite !LiftOption.of'_to'; reflexivity.
    Qed.
  End proj_option2.

  Local Ltac t proj012 :=
    repeat match goal with
           | _ => progress cbv beta in *
           | _ => progress break_match; try tauto; []
           | _ => progress subst
           | [ H : _ |- _ ]
             => first [ rewrite !LiftOption.lift_relation_flat_type_pointwise in H
                        by (eassumption || rewrite LiftOption.of'_to'; reflexivity)
                      | rewrite !LiftOption.lift_relation2_flat_type_pointwise in H
                        by (eassumption || rewrite LiftOption.of'_to'; reflexivity)
                      | rewrite !@lift_interp_flat_type_rel_pointwise_f_eq_id2 in H
                      | rewrite !@lift_interp_flat_type_rel_pointwise_f_eq in H ]
           | _ => progress unfold proj_eq_rel in *
           | _ => progress specialize_by reflexivity
           | _ => rewrite SmartVarfMap_compose
           | _ => setoid_rewrite proj012
           | [ |- context G[fun x y => ?f x y] ]
             => let G' := context G[f] in change G'
           | [ |- context G[fun (_ : ?T) x => ?f x] ]
             => let G' := context G[fun _ : T => f] in change G'
           | [ H : context G[fun (_ : ?T) x => ?f x] |- _ ]
             => let G' := context G[fun _ : T => f] in change G' in H
           | _ => rewrite_hyp <- !*; []
           | _ => reflexivity
           | _ => rewrite interp_flat_type_rel_pointwise_SmartVarfMap
           end.

  Section proj_from_option2.
    Context {interp_base_type0 : Type} {interp_base_type1 interp_base_type2 : base_type -> Type}
            (proj01 : forall t, interp_base_type0 -> interp_base_type1 t)
            (proj02 : forall t, interp_base_type0 -> interp_base_type2 t)
            (proj : forall t, interp_base_type1 t -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      proj_eq_rel (SmartVarfMap proj (t:=t)) f g.

    Definition interp_type_rel_pointwise_uncurried_proj_from_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type0) t -> interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop
      := fun f0 f g
         => forall x : interp_flat_type (fun _ => interp_base_type0) (domain t),
             let x' := SmartVarfMap proj01 x in
             let y' := SmartVarfMap proj x' in
             let fx := f x' in
             let gy := g y' in
             let f0x := LiftOption.of' (f0 (LiftOption.to' (Some x))) in
             match f0x with
             | Some _ => True
             | None => False
             end
             -> @R _ fx gy.

    Lemma uncurry_interp_type_rel_pointwise_proj_from_option2
          {t : type base_type}
          {f0}
          {f : interp_type interp_base_type1 t}
          {g : interp_type interp_base_type2 t}
          (proj012 : forall t x, proj t (proj01 t x) = proj02 t x)
      : interp_type_rel_pointwise (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj01 t))) f0 f
        -> interp_type_rel_pointwise (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj02 t))) f0 g
        -> interp_type_rel_pointwise_uncurried_proj_from_option2 (t:=t) f0 f g.
    Proof.
      unfold interp_type_rel_pointwise_uncurried_proj_from_option2, Morphisms.respectful_hetero.
      intros H0 H1 x.
      specialize (H0 (LiftOption.to' (Some x)) (SmartVarfMap proj01 x)).
      specialize (H1 (LiftOption.to' (Some x)) (SmartVarfMap proj02 x)).
      subst R.
      t proj012.
    Qed.
  End proj_from_option2.
  Global Arguments uncurry_interp_type_rel_pointwise_proj_from_option2 {_ _ _ _ _} proj {t f0 f g} _ _ _.

  Section proj1_from_option2.
    Context {interp_base_type0 interp_base_type1 : Type} {interp_base_type2 : base_type -> Type}
            (proj01 : interp_base_type0 -> interp_base_type1)
            (proj02 : forall t, interp_base_type0 -> interp_base_type2 t)
            (R : forall t, interp_base_type1 -> interp_base_type2 t -> Prop).

    Definition interp_type_rel_pointwise_uncurried_proj1_from_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type0) t -> interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop
      := fun f0 f g
         => forall x : interp_flat_type (fun _ => interp_base_type0) (domain t),
             let x' := SmartVarfMap (fun _ => proj01) x in
             let y' := SmartVarfMap proj02 x in
             let fx := LiftOption.of' (f (LiftOption.to' (Some x'))) in
             let gy := g y' in
             let f0x := LiftOption.of' (f0 (LiftOption.to' (Some x))) in
             match f0x with
             | Some _ => True
             | None => False
             end
             -> match fx with
                | Some fx' => interp_flat_type_rel_pointwise (@R) fx' gy
                | None => True
                end.

    Lemma uncurry_interp_type_rel_pointwise_proj1_from_option2
          {t : type base_type}
          {f0}
          {f : interp_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g : interp_type interp_base_type2 t}
          (proj012R : forall t, Reflexive (fun x y => @R _ (proj01 x) (proj02 t y)))
      : interp_type_rel_pointwise (t:=t) (LiftOption.lift_relation2 (proj_eq_rel proj01)) f0 f
        -> interp_type_rel_pointwise (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj02 t))) f0 g
        -> interp_type_rel_pointwise_uncurried_proj1_from_option2 (t:=t) f0 f g.
    Proof.
      unfold interp_type_rel_pointwise_uncurried_proj1_from_option2, Morphisms.respectful_hetero.
      intros H0 H1 x.
      specialize (H0 (LiftOption.to' (Some x)) (LiftOption.to' (Some (SmartVarfMap (fun _ => proj01) x)))).
      specialize (H1 (LiftOption.to' (Some x)) (SmartVarfMap proj02 x)).
      t proj012.
    Qed.
  End proj1_from_option2.
  Global Arguments uncurry_interp_type_rel_pointwise_proj1_from_option2 {_ _ _ _ _} R {t f0 f g} _ _ _.

  Section combine_related.
    Lemma related_flat_transitivity {interp_base_type1 interp_base_type2 interp_base_type3}
          {R1 : forall t : base_type, interp_base_type1 t -> interp_base_type2 t -> Prop}
          {R2 : forall t : base_type, interp_base_type1 t -> interp_base_type3 t -> Prop}
          {R3 : forall t : base_type, interp_base_type2 t -> interp_base_type3 t -> Prop}
          {t x y z}
    : (forall t a b c, (R1 t a b : Prop) -> (R2 t a c : Prop) -> (R3 t b c : Prop))
      -> interp_flat_type_rel_pointwise (t:=t) R1 x y
      -> interp_flat_type_rel_pointwise (t:=t) R2 x z
      -> interp_flat_type_rel_pointwise (t:=t) R3 y z.
    Proof.
      intro HRel; induction t; simpl; intuition eauto.
    Qed.
  End combine_related.
End Relations.

Require Import Coq.ZArith.ZArith.
Require Import Crypto.Reflection.Z.Syntax.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Relations.
Require Import Crypto.Reflection.Application.
Require Import Crypto.Reflection.Z.InterpretationsGen.
Require Import Crypto.Reflection.Z.Interpretations64.
Require Import Crypto.Reflection.Z.Interpretations64.Relations.
Require Import Crypto.Util.Option.
Require Import Crypto.Util.Bool.
Require Import Crypto.Util.ZUtil.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Tactics.

Module Relations.
  Section lift.
    Context {interp_base_type1 interp_base_type2 : base_type -> Type}
            (R : forall t, interp_base_type1 t -> interp_base_type2 t -> Prop).

    Definition interp_type_rel_pointwise2_uncurried
               {t : type base_type}
      := match t return interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> _ with
         | Tflat T => fun f g => interp_flat_type_rel_pointwise2 (t:=T) R f g
         | Arrow A B
           => fun f g
              => forall x y, interp_flat_type_rel_pointwise2 R x y
                             -> interp_flat_type_rel_pointwise2 R (ApplyInterpedAll f x) (ApplyInterpedAll g y)
         end.

    Lemma uncurry_interp_type_rel_pointwise2
          {t f g}
      : interp_type_rel_pointwise2 (t:=t) R f g
        <-> interp_type_rel_pointwise2_uncurried (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried.
      induction t as [|A B IHt]; [ reflexivity | ].
      { simpl; unfold Morphisms.respectful_hetero in *; destruct B.
        { reflexivity. }
        { setoid_rewrite IHt; clear IHt.
          split; intro H; intros.
          { destruct_head_hnf' prod; simpl in *; intuition. }
          { eapply (H (_, _) (_, _)); simpl in *; intuition. } } }
    Qed.
  End lift.

  Section proj.
    Context {interp_base_type1 interp_base_type2}
            (proj : forall t : base_type, interp_base_type1 t -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      SmartVarfMap (t:=t) proj f = g.

    Definition interp_type_rel_pointwise2_uncurried_proj
               {t : type base_type}
      : interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop  with
         | Tflat T => @R _
         | Arrow A B
           => fun f g
              => forall x : interp_flat_type interp_base_type1 (all_binders_for (Arrow A B)),
                  let y := SmartVarfMap proj x in
                  let fx := ApplyInterpedAll f x in
                  let gy := ApplyInterpedAll g y in
                  @R _ fx gy
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj
          {t : type base_type}
          {f : interp_type interp_base_type1 t}
          {g}
      : interp_type_rel_pointwise2 (t:=t) (fun t => @R _) f g
        -> interp_type_rel_pointwise2_uncurried_proj (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit;
          [ solve [ trivial | reflexivity ] | reflexivity | ].
        intros [HA HB].
        specialize (IHA _ _ HA); specialize (IHB _ _ HB).
        unfold R in *.
        repeat first [ progress destruct_head_hnf' prod
                     | progress simpl in *
                     | progress subst
                     | reflexivity ]. }
      { destruct B; intros H ?; apply IHt, H; clear IHt;
          repeat first [ reflexivity
                       | progress simpl in *
                       | progress unfold R, LiftOption.of' in *
                       | progress break_match ]. }
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

    Definition interp_type_rel_pointwise2_uncurried_proj_option
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop  with
         | Tflat T => @R _
         | Arrow A B
           => fun f g
              => forall x : interp_flat_type (fun _ => interp_base_type1) (all_binders_for (Arrow A B)),
                  let y := SmartVarfMap proj_option x in
                  let fx := ApplyInterpedAll f (LiftOption.to' (Some x)) in
                  let gy := ApplyInterpedAll g y in
                  @R _ fx gy
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj_option
          {t : type base_type}
          {f : interp_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g}
      : interp_type_rel_pointwise2 (t:=t) (fun t => @R _) f g
        -> interp_type_rel_pointwise2_uncurried_proj_option (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj_option.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit;
          [ solve [ trivial | reflexivity ] | reflexivity | ].
        intros [HA HB].
        specialize (IHA _ _ HA); specialize (IHB _ _ HB).
        unfold R in *.
        repeat first [ progress destruct_head_hnf' prod
                     | progress simpl in *
                     | progress unfold LiftOption.of' in *
                     | progress break_match
                     | progress break_match_hyps
                     | progress inversion_prod
                     | progress inversion_option
                     | reflexivity
                     | progress intuition subst ]. }
      { destruct B; intros H ?; apply IHt, H; clear IHt.
        { repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of' in *
                       | progress break_match
                       | reflexivity ]. }
        { simpl in *; break_match; reflexivity. } }
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

    Definition interp_type_rel_pointwise2_uncurried_proj_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type (LiftOption.interp_base_type' interp_base_type2) t -> Prop
      := match t return interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type (LiftOption.interp_base_type' interp_base_type2) t -> Prop  with
         | Tflat T => @R _
         | Arrow A B
           => fun f g
              => forall x : interp_flat_type (fun _ => interp_base_type1) (all_binders_for (Arrow A B)),
                  let y := SmartVarfMap (fun _ => proj) x in
                  let fx := ApplyInterpedAll f (LiftOption.to' (Some x)) in
                  let gy := ApplyInterpedAll g (LiftOption.to' (Some y)) in
                  @R _ fx gy
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj_option2
          {t : type base_type}
          {f : interp_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g : interp_type (LiftOption.interp_base_type' interp_base_type2) t}
      : interp_type_rel_pointwise2 (t:=t) (fun t => @R _) f g
        -> interp_type_rel_pointwise2_uncurried_proj_option2 (t:=t) f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj_option2.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit;
          [ solve [ trivial | reflexivity ] | reflexivity | ].
        intros [HA HB].
        specialize (IHA _ _ HA); specialize (IHB _ _ HB).
        unfold R in *.
        repeat first [ progress destruct_head_hnf' prod
                     | progress simpl in *
                     | progress unfold LiftOption.of' in *
                     | progress break_match
                     | progress break_match_hyps
                     | progress inversion_prod
                     | progress inversion_option
                     | reflexivity
                     | progress intuition subst ]. }
      { destruct B; intros H ?; apply IHt, H; clear IHt.
        { repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of' in *
                       | progress break_match
                       | reflexivity ]. }
        { simpl in *; break_match; reflexivity. } }
    Qed.
  End proj_option2.

  Section proj_from_option2.
    Context {interp_base_type0 : Type} {interp_base_type1 interp_base_type2 : base_type -> Type}
            (proj01 : forall t, interp_base_type0 -> interp_base_type1 t)
            (proj02 : forall t, interp_base_type0 -> interp_base_type2 t)
            (proj : forall t, interp_base_type1 t -> interp_base_type2 t).

    Let R {t : flat_type base_type} f g :=
      proj_eq_rel (SmartVarfMap proj (t:=t)) f g.

    Definition interp_type_rel_pointwise2_uncurried_proj_from_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type0) t -> interp_type interp_base_type1 t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type _ t -> interp_type _ t -> interp_type _ t -> Prop  with
         | Tflat T => fun f0 f g => match LiftOption.of' f0 with
                                    | Some _ => True
                                    | None => False
                                    end -> @R _ f g
         | Arrow A B
           => fun f0 f g
              => forall x : interp_flat_type (fun _ => interp_base_type0) (all_binders_for (Arrow A B)),
                  let x' := SmartVarfMap proj01 x in
                  let y' := SmartVarfMap proj x' in
                  let fx := ApplyInterpedAll f x' in
                  let gy := ApplyInterpedAll g y' in
                  let f0x := LiftOption.of' (ApplyInterpedAll f0 (LiftOption.to' (Some x))) in
                  match f0x with
                  | Some _ => True
                  | None => False
                  end
                  -> @R _ fx gy
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj_from_option2
          {t : type base_type}
          {f0}
          {f : interp_type interp_base_type1 t}
          {g : interp_type interp_base_type2 t}
          (proj012 : forall t x, proj t (proj01 t x) = proj02 t x)
      : interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj01 t))) f0 f
        -> interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj02 t))) f0 g
        -> interp_type_rel_pointwise2_uncurried_proj_from_option2 (t:=t) f0 f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj_from_option2.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit; try reflexivity.
        { cbv [LiftOption.lift_relation proj_eq_rel R].
          break_match; try tauto; intros; subst.
          apply proj012. }
        { intros [HA HB] [HA' HB'] Hrel.
          specialize (IHA _ _ _ HA HA'); specialize (IHB _ _ _ HB HB').
          unfold R, proj_eq_rel in *.
          repeat first [ progress destruct_head_hnf' prod
                       | progress simpl in *
                       | progress unfold LiftOption.of' in *
                       | progress break_match
                       | progress break_match_hyps
                       | progress inversion_prod
                       | progress inversion_option
                       | reflexivity
                       | progress intuition subst ]. } }
      { destruct B; intros H0 H1 ?; apply IHt; clear IHt; first [ apply H0 | apply H1 ];
          repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of', proj_eq_rel, LiftOption.lift_relation in *
                       | break_match; rewrite <- ?proj012; reflexivity ]. }
    Qed.
  End proj_from_option2.
  Global Arguments uncurry_interp_type_rel_pointwise2_proj_from_option2 {_ _ _ _ _} proj {t f0 f g} _ _ _.

  Section proj1_from_option2.
    Context {interp_base_type0 interp_base_type1 : Type} {interp_base_type2 : base_type -> Type}
            (proj01 : interp_base_type0 -> interp_base_type1)
            (proj02 : forall t, interp_base_type0 -> interp_base_type2 t)
            (R : forall t, interp_base_type1 -> interp_base_type2 t -> Prop).

    Definition interp_type_rel_pointwise2_uncurried_proj1_from_option2
               {t : type base_type}
      : interp_type (LiftOption.interp_base_type' interp_base_type0) t -> interp_type (LiftOption.interp_base_type' interp_base_type1) t -> interp_type interp_base_type2 t -> Prop
      := match t return interp_type _ t -> interp_type _ t -> interp_type _ t -> Prop  with
         | Tflat T => fun f0 f g => match LiftOption.of' f0 with
                                    | Some _ => True
                                    | None => False
                                    end -> match LiftOption.of' f with
                                           | Some f' => interp_flat_type_rel_pointwise2 (@R) f' g
                                           | None => True
                                           end
         | Arrow A B
           => fun f0 f g
              => forall x : interp_flat_type (fun _ => interp_base_type0) (all_binders_for (Arrow A B)),
                  let x' := SmartVarfMap (fun _ => proj01) x in
                  let y' := SmartVarfMap proj02 x in
                  let fx := LiftOption.of' (ApplyInterpedAll f (LiftOption.to' (Some x'))) in
                  let gy := ApplyInterpedAll g y' in
                  let f0x := LiftOption.of' (ApplyInterpedAll f0 (LiftOption.to' (Some x))) in
                  match f0x with
                  | Some _ => True
                  | None => False
                  end
                  -> match fx with
                     | Some fx' => interp_flat_type_rel_pointwise2 (@R) fx' gy
                     | None => True
                     end
         end.

    Lemma uncurry_interp_type_rel_pointwise2_proj1_from_option2
          {t : type base_type}
          {f0}
          {f : interp_type (LiftOption.interp_base_type' interp_base_type1) t}
          {g : interp_type interp_base_type2 t}
          (proj012R : forall t x, @R _ (proj01 x) (proj02 t x))
      : interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation2 (proj_eq_rel proj01)) f0 f
        -> interp_type_rel_pointwise2 (t:=t) (LiftOption.lift_relation (fun t => proj_eq_rel (proj02 t))) f0 g
        -> interp_type_rel_pointwise2_uncurried_proj1_from_option2 (t:=t) f0 f g.
    Proof.
      unfold interp_type_rel_pointwise2_uncurried_proj1_from_option2.
      induction t as [t|A B IHt]; simpl; unfold Morphisms.respectful_hetero in *.
      { induction t as [t| |A IHA B IHB]; simpl; destruct_head_hnf' unit; try reflexivity.
        { cbv [LiftOption.lift_relation proj_eq_rel LiftOption.lift_relation2].
          break_match; try tauto; intros; subst.
          apply proj012R. }
        { intros [HA HB] [HA' HB'] Hrel.
          specialize (IHA _ _ _ HA HA'); specialize (IHB _ _ _ HB HB').
          unfold proj_eq_rel in *.
          repeat first [ progress destruct_head_hnf' prod
                       | progress simpl in *
                       | progress unfold LiftOption.of' in *
                       | progress break_match
                       | progress break_match_hyps
                       | progress inversion_prod
                       | progress inversion_option
                       | reflexivity
                       | progress intuition subst ]. } }
      { destruct B; intros H0 H1 ?; apply IHt; clear IHt; first [ apply H0 | apply H1 ];
          repeat first [ progress simpl in *
                       | progress unfold R, LiftOption.of', proj_eq_rel, LiftOption.lift_relation in *
                       | break_match; reflexivity ]. }
    Qed.
  End proj1_from_option2.
  Global Arguments uncurry_interp_type_rel_pointwise2_proj1_from_option2 {_ _ _ _ _} R {t f0 f g} _ _ _.

  Section combine_related.
    Lemma related_flat_transitivity {interp_base_type1 interp_base_type2 interp_base_type3}
          {R1 : forall t : base_type, interp_base_type1 t -> interp_base_type2 t -> Prop}
          {R2 : forall t : base_type, interp_base_type1 t -> interp_base_type3 t -> Prop}
          {R3 : forall t : base_type, interp_base_type2 t -> interp_base_type3 t -> Prop}
          {t x y z}
    : (forall t a b c, (R1 t a b : Prop) -> (R2 t a c : Prop) -> (R3 t b c : Prop))
      -> interp_flat_type_rel_pointwise2 (t:=t) R1 x y
      -> interp_flat_type_rel_pointwise2 (t:=t) R2 x z
      -> interp_flat_type_rel_pointwise2 (t:=t) R3 y z.
    Proof.
      intro HRel; induction t; simpl; intuition eauto.
    Qed.
  End combine_related.
End Relations.

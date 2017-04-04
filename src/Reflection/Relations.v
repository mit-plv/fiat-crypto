Require Import Coq.Lists.List Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Util.Tactics.RewriteHyp.
Require Import Crypto.Util.Tactics.DestructHead.
Require Import Crypto.Util.Tactics.SplitInContext.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.

Local Coercion is_true : bool >-> Sortclass.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).

  Local Ltac rel_relb_t :=
    repeat first [ progress simpl in *
                 | reflexivity
                 | intuition congruence
                 | setoid_rewrite Bool.andb_true_iff
                 | intro
                 | rewrite_hyp <- !* ].

  Section flat_type.
    Context {interp_base_type1 interp_base_type2 : base_type_code -> Type}.
    Local Notation interp_flat_type1 := (interp_flat_type interp_base_type1).
    Local Notation interp_flat_type2 := (interp_flat_type interp_base_type2).

    Section gen_Prop.
      Context (P : Type)
              (and : P -> P -> P)
              (True : P)
              (False : P).
      Section pointwise1.
        Context (R : forall t, interp_base_type1 t -> P).
        Fixpoint interp_flat_type_rel_pointwise1_gen_Prop (t : flat_type)
          : interp_flat_type1 t -> P :=
          match t with
          | Tbase t => R t
          | Unit => fun _ => True
          | Prod A B => fun x : interp_flat_type _ A * interp_flat_type _ B
                        => and (interp_flat_type_rel_pointwise1_gen_Prop _ (fst x))
                               (interp_flat_type_rel_pointwise1_gen_Prop _ (snd x))
          end.
      End pointwise1.
      Section pointwise2.
        Context (R : forall t, interp_base_type1 t -> interp_base_type2 t -> P).
        Fixpoint interp_flat_type_rel_pointwise_gen_Prop (t : flat_type)
          : interp_flat_type1 t -> interp_flat_type2 t -> P :=
          match t with
          | Tbase t => R t
          | Unit => fun _ _ => True
          | Prod A B
            => fun (x : interp_flat_type _ A * interp_flat_type _ B)
                   (y : interp_flat_type _ A * interp_flat_type _ B)
               => and (interp_flat_type_rel_pointwise_gen_Prop _ (fst x) (fst y))
                      (interp_flat_type_rel_pointwise_gen_Prop _ (snd x) (snd y))
          end.
      End pointwise2.
      Section pointwise2_hetero.
        Context (R : forall t1 t2, interp_base_type1 t1 -> interp_base_type2 t2 -> P).
        Fixpoint interp_flat_type_rel_pointwise_hetero_gen_Prop (t1 t2 : flat_type)
          : interp_flat_type1 t1 -> interp_flat_type2 t2 -> P
          := match t1, t2 with
             | Tbase t1, Tbase t2 => R t1 t2
             | Unit, Unit => fun _ _ => True
             | Prod x1 y1, Prod x2 y2
               => fun (a b : interp_flat_type _ _ * interp_flat_type _ _)
                  => and (interp_flat_type_rel_pointwise_hetero_gen_Prop x1 x2 (fst a) (fst b))
                         (interp_flat_type_rel_pointwise_hetero_gen_Prop y1 y2 (snd a) (snd b))
             | Tbase _, _
             | Unit, _
             | Prod _ _, _
               => fun _ _ => False
             end.
      End pointwise2_hetero.
    End gen_Prop.

    Definition interp_flat_type_relb_pointwise1
      := @interp_flat_type_rel_pointwise1_gen_Prop bool andb true.
    Global Arguments interp_flat_type_relb_pointwise1 _ !_ _ / .
    Definition interp_flat_type_rel_pointwise1
      := @interp_flat_type_rel_pointwise1_gen_Prop Prop and True.
    Global Arguments interp_flat_type_rel_pointwise1 _ !_ _ / .
    Lemma interp_flat_type_rel_pointwise1_iff_relb {R} t x
      : interp_flat_type_relb_pointwise1 R t x <-> interp_flat_type_rel_pointwise1 R t x.
    Proof using Type. clear; induction t; rel_relb_t. Qed.
    Definition interp_flat_type_rel_pointwise1_gen_Prop_iff_bool
      : forall {R} t x,
        interp_flat_type_rel_pointwise1_gen_Prop bool _ _ R t x
        <-> interp_flat_type_rel_pointwise1_gen_Prop Prop _ _ R t x
      := @interp_flat_type_rel_pointwise1_iff_relb.
    Definition interp_flat_type_relb_pointwise
      := @interp_flat_type_rel_pointwise_gen_Prop bool andb true.
    Global Arguments interp_flat_type_relb_pointwise _ !_ _ _ / .
    Definition interp_flat_type_rel_pointwise
      := @interp_flat_type_rel_pointwise_gen_Prop Prop and True.
    Global Arguments interp_flat_type_rel_pointwise _ !_ _ _ / .
    Lemma interp_flat_type_rel_pointwise_iff_relb {R} t x y
      : interp_flat_type_relb_pointwise R t x y <-> interp_flat_type_rel_pointwise R t x y.
    Proof using Type. clear; induction t; rel_relb_t. Qed.
    Definition interp_flat_type_rel_pointwise_gen_Prop_iff_bool
      : forall {R} t x y,
        interp_flat_type_rel_pointwise_gen_Prop bool _ _ R t x y
        <-> interp_flat_type_rel_pointwise_gen_Prop Prop _ _ R t x y
      := @interp_flat_type_rel_pointwise_iff_relb.
    Definition interp_flat_type_relb_pointwise_hetero
      := @interp_flat_type_rel_pointwise_hetero_gen_Prop bool andb true false.
    Global Arguments interp_flat_type_relb_pointwise_hetero _ !_ !_ _ _ / .
    Definition interp_flat_type_rel_pointwise_hetero
      := @interp_flat_type_rel_pointwise_hetero_gen_Prop Prop and True False.
    Global Arguments interp_flat_type_rel_pointwise_hetero _ !_ !_ _ _ / .
    Lemma interp_flat_type_rel_pointwise_hetero_iff_relb {R} t1 t2 x y
      : interp_flat_type_relb_pointwise_hetero R t1 t2 x y <-> interp_flat_type_rel_pointwise_hetero R t1 t2 x y.
    Proof using Type. clear; revert dependent t2; induction t1, t2; rel_relb_t. Qed.
    Definition interp_flat_type_rel_pointwise_hetero_gen_Prop_iff_bool
      : forall {R} t1 t2 x y,
        interp_flat_type_rel_pointwise_hetero_gen_Prop bool _ _ _ R t1 t2 x y
        <-> interp_flat_type_rel_pointwise_hetero_gen_Prop Prop _ _ _ R t1 t2 x y
      := @interp_flat_type_rel_pointwise_hetero_iff_relb.

    Lemma interp_flat_type_rel_pointwise_hetero_iff {R t} x y
      : interp_flat_type_rel_pointwise (fun t => R t t) t x y
        <-> interp_flat_type_rel_pointwise_hetero R t t x y.
    Proof using Type. induction t; simpl; rewrite_hyp ?*; reflexivity. Qed.

    Lemma interp_flat_type_rel_pointwise_impl {R1 R2 : forall t, _ -> _ -> Prop} t x y
      : interp_flat_type_rel_pointwise (fun t x y => (R1 t x y -> R2 t x y)%type) t x y
        -> (interp_flat_type_rel_pointwise R1 t x y
            -> interp_flat_type_rel_pointwise R2 t x y).
    Proof using Type. induction t; simpl; intuition. Qed.

    Lemma interp_flat_type_rel_pointwise_always {R : forall t, _ -> _ -> Prop}
      : (forall t x y, R t x y)
        -> forall t x y, interp_flat_type_rel_pointwise R t x y.
    Proof using Type. induction t; simpl; intuition. Qed.
  End flat_type.
  Section flat_type_extra.
    Context {interp_base_type1 interp_base_type2 : base_type_code -> Type}.
    Lemma interp_flat_type_rel_pointwise_impl' {R1 R2 : forall t, _ -> _ -> Prop} t x y
      : @interp_flat_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => (R1 t y x -> R2 t x y)%type) t x y
        -> (interp_flat_type_rel_pointwise R1 t y x
            -> interp_flat_type_rel_pointwise R2 t x y).
    Proof using Type. induction t; simpl; intuition. Qed.

    Global Instance interp_flat_type_rel_pointwise_Reflexive {R : forall t, _ -> _ -> Prop} {H : forall t, Reflexive (R t)}
      : forall t, Reflexive (@interp_flat_type_rel_pointwise interp_base_type1 interp_base_type1 R t).
    Proof using Type.
      induction t; intro; simpl; try apply conj; try reflexivity.
    Qed.

    Lemma interp_flat_type_rel_pointwise_SmartVarfMap
          {interp_base_type1' interp_base_type2'}
          {R : forall t, _ -> _ -> Prop}
          t f g x y
      : @interp_flat_type_rel_pointwise interp_base_type1 interp_base_type2 R t (SmartVarfMap f x) (SmartVarfMap g y)
        <-> @interp_flat_type_rel_pointwise interp_base_type1' interp_base_type2' (fun t x y => R t (f _ x) (g _ y)) t x y.
    Proof using Type.
      induction t; simpl; try reflexivity.
      rewrite_hyp <- !*; reflexivity.
    Qed.
  End flat_type_extra.

  Section type.
    Section hetero.
      Context (interp_src1 interp_src2 : flat_type -> Type)
              (interp_dst1 interp_dst2 : flat_type -> Type).
      Section hetero.
        Context (Rsrc : forall t, interp_src1 t -> interp_src2 t -> Prop)
                (Rdst : forall t, interp_dst1 t -> interp_dst2 t -> Prop).

        Definition interp_type_gen_rel_pointwise_hetero (t : type)
          : interp_type_gen_hetero interp_src1 interp_dst1 t
            -> interp_type_gen_hetero interp_src2 interp_dst2 t
            -> Prop
          := @respectful_hetero _ _ _ _ (Rsrc _) (fun _ _ => Rdst _).
        Global Arguments interp_type_gen_rel_pointwise_hetero _ _ _ / .
      End hetero.
      Section hetero_hetero.
        Context (Rsrc : forall t1 t2, interp_src1 t1 -> interp_src2 t2 -> Prop)
                (Rdst : forall t1 t2, interp_dst1 t1 -> interp_dst2 t2 -> Prop).

        Fixpoint interp_type_gen_rel_pointwise_hetero_hetero (t1 t2 : type)
          : interp_type_gen_hetero interp_src1 interp_dst1 t1
            -> interp_type_gen_hetero interp_src2 interp_dst2 t2
            -> Prop
          := @respectful_hetero _ _ _ _ (Rsrc _ _) (fun _ _ => Rdst _ _).
        Global Arguments interp_type_gen_rel_pointwise_hetero_hetero _ _ _ _ / .
      End hetero_hetero.
    End hetero.

    Section partially_hetero.
      Context (interp_flat_type1 interp_flat_type2 : flat_type -> Type)
              (R : forall t, interp_flat_type1 t -> interp_flat_type2 t -> Prop).

      Definition interp_type_gen_rel_pointwise
        : forall t,
          interp_type_gen interp_flat_type1 t
          -> interp_type_gen interp_flat_type2 t
          -> Prop
        := interp_type_gen_rel_pointwise_hetero
             interp_flat_type1 interp_flat_type2
             interp_flat_type1 interp_flat_type2
             R R.
      Global Arguments interp_type_gen_rel_pointwise _ _ _ / .
    End partially_hetero.
  End type.

  Section specialized_type.
    Section hetero.
      Context (interp_base_type1 interp_base_type2 : base_type_code -> Type).
      Definition interp_type_rel_pointwise R
        : forall t, interp_type interp_base_type1 t
                    -> interp_type interp_base_type2 t
                    -> Prop
        := interp_type_gen_rel_pointwise _ _ (interp_flat_type_rel_pointwise R).
      Global Arguments interp_type_rel_pointwise _ !_ _ _ / .

      Definition interp_type_rel_pointwise_hetero R
        : forall t1 t2, interp_type interp_base_type1 t1
                        -> interp_type interp_base_type2 t2
                        -> Prop
        := interp_type_gen_rel_pointwise_hetero_hetero _ _ _ _ (interp_flat_type_rel_pointwise_hetero R) (interp_flat_type_rel_pointwise_hetero R).
      Global Arguments interp_type_rel_pointwise_hetero _ !_ !_ _ _ / .
    End hetero.
  End specialized_type.

  Section lifting.
    Context {interp_base_type1 interp_base_type2 : base_type_code -> Type}.
    Local Notation interp_flat_type1 := (interp_flat_type interp_base_type1).
    Local Notation interp_flat_type2 := (interp_flat_type interp_base_type2).
    Let Tbase := (@Tbase base_type_code).
    Local Coercion Tbase : base_type_code >-> flat_type.

    Section with_rel.
      Context (R : forall t, interp_flat_type1 t -> interp_flat_type2 t -> Prop)
              (RUnit : R Unit tt tt).
      Section RProd.
        Context (RProd : forall A B x y, R A (fst x) (fst y) /\ R B (snd x) (snd y) -> R (Prod A B) x y)
                (RProd' : forall A B x y, R (Prod A B) x y -> R A (fst x) (fst y) /\ R B (snd x) (snd y)).
        Lemma lift_interp_flat_type_rel_pointwise1 t (x : interp_flat_type1 t) (y : interp_flat_type2 t)
          : interp_flat_type_rel_pointwise R t x y -> R t x y.
        Proof using RProd RUnit. clear RProd'; induction t; simpl; destruct_head_hnf' unit; intuition. Qed.
        Lemma lift_interp_flat_type_rel_pointwise2 t (x : interp_flat_type1 t) (y : interp_flat_type2 t)
          : R t x y -> interp_flat_type_rel_pointwise R t x y.
        Proof using RProd'. clear RProd; induction t; simpl; destruct_head_hnf' unit; split_and; intuition. Qed.
      End RProd.
      Section RProd_iff.
        Context (RProd : forall A B x y, R A (fst x) (fst y) /\ R B (snd x) (snd y) <-> R (Prod A B) x y).
        Lemma lift_interp_flat_type_rel_pointwise t (x : interp_flat_type1 t) (y : interp_flat_type2 t)
          : interp_flat_type_rel_pointwise R t x y <-> R t x y.
        Proof using RProd RUnit.
          split_iff; split; auto using lift_interp_flat_type_rel_pointwise1, lift_interp_flat_type_rel_pointwise2.
        Qed.
      End RProd_iff.
    End with_rel.
    Lemma lift_interp_flat_type_rel_pointwise_f_eq {T} (f g : forall t, _ -> T t) t x y
      : @interp_flat_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => f t x = g t y)
          t x y
        <-> SmartVarfMap f x = SmartVarfMap g y.
    Proof using Type.
      induction t; unfold SmartVarfMap in *; simpl in *; destruct_head_hnf unit; try tauto.
      rewrite_hyp !*; intuition congruence.
    Qed.
    Lemma lift_interp_flat_type_rel_pointwise_f_eq_id1 (f : forall t, _ -> _) t x y
      : @interp_flat_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => x = f t y)
          t x y
        <-> x = SmartVarfMap f y.
    Proof using Type. rewrite lift_interp_flat_type_rel_pointwise_f_eq, SmartVarfMap_id; reflexivity. Qed.
    Lemma lift_interp_flat_type_rel_pointwise_f_eq_id2 (f : forall t, _ -> _) t x y
      : @interp_flat_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => f t x = y)
          t x y
        <-> SmartVarfMap f x = y.
    Proof using Type. rewrite lift_interp_flat_type_rel_pointwise_f_eq, SmartVarfMap_id; reflexivity. Qed.
    Lemma lift_interp_flat_type_rel_pointwise_f_eq2 {T} (f g : forall t, _ -> _ -> T t) t x y
      : @interp_flat_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => f t x y = g t x y)
          t x y
        <-> SmartVarfMap2 f x y = SmartVarfMap2 g x y.
    Proof using Type.
      induction t; unfold SmartVarfMap2 in *; simpl in *; destruct_head_hnf unit; try tauto.
      rewrite_hyp !*; intuition congruence.
    Qed.
    Lemma lift_interp_type_rel_pointwise_f_eq {T} (f g : forall t, _ -> T t) t x y
      : interp_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => f t x = g t y)
          t x y
        <-> (forall a b, SmartVarfMap f a = SmartVarfMap g b -> SmartVarfMap f (x a) = SmartVarfMap g (y b)).
    Proof using Type.
      destruct t; simpl; unfold interp_type_rel_pointwise, respectful_hetero.
      setoid_rewrite lift_interp_flat_type_rel_pointwise_f_eq; reflexivity.
    Qed.
    Lemma lift_interp_type_rel_pointwise_f_eq_id1 (f : forall t, _ -> _) t x y
      : interp_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => x = f t y)
          t x y
        <-> (forall a, x (SmartVarfMap f a) = SmartVarfMap f (y a)).
    Proof using Type. rewrite lift_interp_type_rel_pointwise_f_eq; setoid_rewrite SmartVarfMap_id; firstorder (subst; eauto). Qed.
    Lemma lift_interp_type_rel_pointwise_f_eq_id2 (f : forall t, _ -> _) t x y
      : interp_type_rel_pointwise
          interp_base_type1 interp_base_type2
          (fun t x y => f t x = y)
          t x y
        <-> (forall a, SmartVarfMap f (x a) = y (SmartVarfMap f a)).
    Proof using Type. rewrite lift_interp_type_rel_pointwise_f_eq; setoid_rewrite SmartVarfMap_id; firstorder (subst; eauto). Qed.
  End lifting.

  Local Ltac t :=
    repeat match goal with
           | _ => intro
           | [ H : False |- _ ] => exfalso; assumption
           | _ => progress subst
           | _ => assumption
           | _ => progress inversion_sigma
           | _ => progress inversion_prod
           | _ => progress simpl in *
           | _ => progress destruct_head_hnf' and
           | [ H : context[List.In _ (_ ++ _)] |- _ ]
             => rewrite List.in_app_iff in H
           | _ => progress destruct_head' or
           | _ => solve [ eauto ]
           end.

  Lemma interp_flat_type_rel_pointwise_flatten_binding_list
        {interp_base_type1 interp_base_type2 t T} R' e1 e2 v1 v2
        (H : List.In (existT _ t (v1, v2)%core) (flatten_binding_list e1 e2))
        (HR : @interp_flat_type_rel_pointwise interp_base_type1 interp_base_type2 R' T e1 e2)
    : R' t v1 v2.
  Proof using Type. induction T; t. Qed.

  Lemma interp_flat_type_rel_pointwise_hetero_flatten_binding_list2
        {interp_base_type1 interp_base_type2 t1 t2 T1 T2} R' e1 e2 v1 v2
        (H : List.In (existT _ (t1, t2)%core (v1, v2)%core) (flatten_binding_list2 e1 e2))
        (HR : @interp_flat_type_rel_pointwise_hetero interp_base_type1 interp_base_type2 R' T1 T2 e1 e2)
    : R' t1 t2 v1 v2.
  Proof using Type.
    revert dependent T2; induction T1, T2; t.
  Qed.
End language.

Global Arguments interp_type_rel_pointwise {_ _ _} R {t} _ _.
Global Arguments interp_type_rel_pointwise_hetero {_ _ _} R {t1 t2} _ _.
Global Arguments interp_type_gen_rel_pointwise_hetero_hetero {_ _ _ _ _} Rsrc Rdst {t1 t2} _ _.
Global Arguments interp_type_gen_rel_pointwise_hetero {_ _ _ _ _} Rsrc Rdst {t} _ _.
Global Arguments interp_type_gen_rel_pointwise {_ _ _} R {t} _ _.
Global Arguments interp_flat_type_rel_pointwise_gen_Prop {_ _ _ P} and True R {t} _ _.
Global Arguments interp_flat_type_rel_pointwise_hetero_gen_Prop {_ _ _ P} and True False R {t1 t2} _ _.
Global Arguments interp_flat_type_rel_pointwise_hetero {_ _ _} R {t1 t2} _ _.
Global Arguments interp_flat_type_relb_pointwise_hetero {_ _ _} R {t1 t2} _ _.
Global Arguments interp_flat_type_rel_pointwise1 {_ _} R {t} _.
Global Arguments interp_flat_type_relb_pointwise1 {_ _} R {t} _.
Global Arguments interp_flat_type_rel_pointwise {_ _ _} R {t} _ _.
Global Arguments interp_flat_type_relb_pointwise {_ _ _} R {t} _ _.

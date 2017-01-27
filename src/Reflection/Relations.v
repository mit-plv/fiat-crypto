Require Import Coq.Lists.List Coq.Classes.RelationClasses Coq.Classes.Morphisms.
Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Reflection.SmartMap.
Require Import Crypto.Reflection.Wf.
Require Import Crypto.Util.Tactics.
Require Import Crypto.Util.Prod.
Require Import Crypto.Util.Sigma.

Local Open Scope ctype_scope.
Section language.
  Context {base_type_code : Type}.

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).

  Section type.
    Context (interp_flat_type : flat_type -> Type)
            (R : forall t, interp_flat_type t -> interp_flat_type t -> Prop).
    Local Notation interp_type_gen := (interp_type_gen interp_flat_type).
    Fixpoint interp_type_gen_rel_pointwise (t : type)
      : interp_type_gen t -> interp_type_gen t -> Prop :=
      match t with
      | Tflat t => R t
      | Arrow _ y => fun f g => forall x, interp_type_gen_rel_pointwise y (f x) (g x)
      end.
    Global Instance interp_type_gen_rel_pointwise_Reflexive {H : forall t, Reflexive (R t)}
      : forall t, Reflexive (interp_type_gen_rel_pointwise t).
    Proof. induction t; repeat intro; reflexivity. Qed.
    Global Instance interp_type_gen_rel_pointwise_Symmetric {H : forall t, Symmetric (R t)}
      : forall t, Symmetric (interp_type_gen_rel_pointwise t).
    Proof. induction t; simpl; repeat intro; symmetry; eauto. Qed.
    Global Instance interp_type_gen_rel_pointwise_Transitive {H : forall t, Transitive (R t)}
      : forall t, Transitive (interp_type_gen_rel_pointwise t).
    Proof. induction t; simpl; repeat intro; etransitivity; eauto. Qed.
  End type.

  Section flat_type.
    Context {interp_base_type : base_type_code -> Type}
            (R : forall t, interp_base_type t -> interp_base_type t -> Prop).
    Local Notation interp_flat_type := (interp_flat_type interp_base_type).
    Fixpoint interp_flat_type_rel_pointwise (t : flat_type)
      : interp_flat_type t -> interp_flat_type t -> Prop :=
      match t with
      | Tbase t => R t
      | Unit => fun _ _ => True
      | Prod _ _ => fun x y => interp_flat_type_rel_pointwise _ (fst x) (fst y)
                               /\ interp_flat_type_rel_pointwise _ (snd x) (snd y)
      end.
    Definition interp_type_rel_pointwise
      := interp_type_gen_rel_pointwise _ interp_flat_type_rel_pointwise.
  End flat_type.

  Section rel_pointwise2.
    Section type.
      Section hetero_hetero.
        Context (interp_src1 interp_src2 : base_type_code -> Type)
                (interp_dst1 interp_dst2 : flat_type -> Type)
                (Rsrc : forall t1 t2, interp_src1 t1 -> interp_src2 t2 -> Prop)
                (Rdst : forall t1 t2, interp_dst1 t1 -> interp_dst2 t2 -> Prop).

        Fixpoint interp_type_gen_rel_pointwise2_hetero_hetero (t1 t2 : type)
          : interp_type_gen_hetero interp_src1 interp_dst1 t1
            -> interp_type_gen_hetero interp_src2 interp_dst2 t2
            -> Prop
          := match t1, t2 with
             | Tflat t1, Tflat t2 => Rdst t1 t2
             | Arrow src1 dst1, Arrow src2 dst2
               => @respectful_hetero _ _ _ _ (Rsrc src1 src2) (fun _ _ => interp_type_gen_rel_pointwise2_hetero_hetero dst1 dst2)
             | Tflat _, _
             | Arrow _ _, _
               => fun _ _ => False
             end.
        Global Arguments interp_type_gen_rel_pointwise2_hetero_hetero _ _ _ _ / .
      End hetero_hetero.
      Section hetero.
        Context (interp_src1 interp_src2 : base_type_code -> Type)
                (interp_dst1 interp_dst2 : flat_type -> Type)
                (Rsrc : forall t, interp_src1 t -> interp_src2 t -> Prop)
                (Rdst : forall t, interp_dst1 t -> interp_dst2 t -> Prop).

        Fixpoint interp_type_gen_rel_pointwise2_hetero (t : type)
          : interp_type_gen_hetero interp_src1 interp_dst1 t
            -> interp_type_gen_hetero interp_src2 interp_dst2 t
            -> Prop
          := match t with
             | Tflat t => Rdst t
             | Arrow src dst => @respectful_hetero _ _ _ _ (Rsrc src) (fun _ _ => interp_type_gen_rel_pointwise2_hetero dst)
             end.
        Global Arguments interp_type_gen_rel_pointwise2_hetero _ _ _ / .
      End hetero.
      Section homogenous.
        Context (interp_flat_type1 interp_flat_type2 : flat_type -> Type)
                (R : forall t, interp_flat_type1 t -> interp_flat_type2 t -> Prop).

        Let Tbase := (@Tbase base_type_code).
        Local Coercion Tbase : base_type_code >-> flat_type.

        Definition interp_type_gen_rel_pointwise2
          : forall t,
            interp_type_gen interp_flat_type1 t
            -> interp_type_gen interp_flat_type2 t
            -> Prop
          := interp_type_gen_rel_pointwise2_hetero interp_flat_type1 interp_flat_type2
                                                   interp_flat_type1 interp_flat_type2
                                                   R R.
      End homogenous.
      Global Arguments interp_type_gen_rel_pointwise2 _ _ _ _ _ _ / .
    End type.
    Section flat_type.
      Context (interp_base_type1 interp_base_type2 : base_type_code -> Type).
      Section gen_prop.
        Context (P : Type)
                (and : P -> P -> P)
                (True : P)
                (False : P).
        Section hetero.
          Context (R : forall t1 t2, interp_base_type1 t1 -> interp_base_type2 t2 -> P).

          Fixpoint interp_flat_type_rel_pointwise2_hetero_gen_Prop (t1 t2 : flat_type)
            : interp_flat_type interp_base_type1 t1 -> interp_flat_type interp_base_type2 t2 -> P
            := match t1, t2 with
               | Tbase t1, Tbase t2 => R t1 t2
               | Unit, Unit => fun _ _ => True
               | Prod x1 y1, Prod x2 y2
                 => fun a b => and (interp_flat_type_rel_pointwise2_hetero_gen_Prop x1 x2 (fst a) (fst b))
                                   (interp_flat_type_rel_pointwise2_hetero_gen_Prop y1 y2 (snd a) (snd b))
               | Tbase _, _
               | Unit, _
               | Prod _ _, _
                 => fun _ _ => False
               end.
        End hetero.
        Section homogenous.
          Context (R : forall t, interp_base_type1 t -> interp_base_type2 t -> P).

          Fixpoint interp_flat_type_rel_pointwise2_gen_Prop (t : flat_type)
            : interp_flat_type interp_base_type1 t -> interp_flat_type interp_base_type2 t -> P
            := match t with
               | Tbase t => R t
               | Unit => fun _ _ => True
               | Prod x y => fun a b => and (interp_flat_type_rel_pointwise2_gen_Prop x (fst a) (fst b))
                                            (interp_flat_type_rel_pointwise2_gen_Prop y (snd a) (snd b))
               end.
        End homogenous.
      End gen_prop.

      Definition interp_flat_type_rel_pointwise2_hetero
        := @interp_flat_type_rel_pointwise2_hetero_gen_Prop Prop and True False.
      Global Arguments interp_flat_type_rel_pointwise2_hetero _ !_ !_ _ _ / .

      Definition interp_flat_type_rel_pointwise2
        := @interp_flat_type_rel_pointwise2_gen_Prop Prop and True.
      Global Arguments interp_flat_type_rel_pointwise2 _ !_ _ _ / .

      Section with_coercion.
        Let Tbase := (@Tbase base_type_code).
        Local Coercion Tbase : base_type_code >-> flat_type.

        Definition interp_type_rel_pointwise2_hetero R
          : forall t1 t2, interp_type interp_base_type1 t1
                          -> interp_type interp_base_type2 t2
                          -> Prop
          := interp_type_gen_rel_pointwise2_hetero_hetero _ _ _ _ (interp_flat_type_rel_pointwise2_hetero R) (interp_flat_type_rel_pointwise2_hetero R).
      End with_coercion.
      Global Arguments interp_type_rel_pointwise2_hetero _ !_ !_ _ _ / .

      Definition interp_type_rel_pointwise2 R
        : forall t, interp_type interp_base_type1 t
                    -> interp_type interp_base_type2 t
                    -> Prop
        := interp_type_gen_rel_pointwise2 _ _ (interp_flat_type_rel_pointwise2 R).
      Global Arguments interp_type_rel_pointwise2 _ !_ _ _ / .
    End flat_type.
  End rel_pointwise2.

  Section lifting.
    Let Tbase := (@Tbase base_type_code).
    Local Coercion Tbase : base_type_code >-> flat_type.

    Section flat_type.
      Context {interp_base_type : base_type_code -> Type}.
      Local Notation interp_flat_type := (interp_flat_type interp_base_type).
      Context (R : forall t, interp_flat_type t -> interp_flat_type t -> Prop)
              (RUnit : R Unit tt tt).
      Section RProd.
        Context (RProd : forall A B x y, R A (fst x) (fst y) /\ R B (snd x) (snd y) -> R (Prod A B) x y)
                (RProd' : forall A B x y, R (Prod A B) x y -> R A (fst x) (fst y) /\ R B (snd x) (snd y)).
        Lemma lift_interp_flat_type_rel_pointwise1 t (x y : interp_flat_type t)
          : interp_flat_type_rel_pointwise R t x y -> R t x y.
        Proof. clear RProd'; induction t; simpl; destruct_head_hnf' unit; intuition. Qed.
        Lemma lift_interp_flat_type_rel_pointwise2 t (x y : interp_flat_type t)
          : R t x y -> interp_flat_type_rel_pointwise R t x y.
        Proof. clear RProd; induction t; simpl; destruct_head_hnf' unit; split_and; intuition. Qed.
      End RProd.
      Section RProd_iff.
        Context (RProd : forall A B x y, R A (fst x) (fst y) /\ R B (snd x) (snd y) <-> R (Prod A B) x y).
        Lemma lift_interp_flat_type_rel_pointwise t (x y : interp_flat_type t)
          : interp_flat_type_rel_pointwise R t x y <-> R t x y.
        Proof.
          split_iff; split; auto using lift_interp_flat_type_rel_pointwise1, lift_interp_flat_type_rel_pointwise2.
        Qed.
      End RProd_iff.
    End flat_type.
    Section flat_type2.
      Context {interp_base_type1 interp_base_type2 : base_type_code -> Type}.
      Lemma lift_interp_flat_type_rel_pointwise2_f_eq {T} (f g : forall t, _ -> T t) t x y
        : interp_flat_type_rel_pointwise2
            interp_base_type1 interp_base_type2
            (fun t x y => f t x = g t y)
            t x y
          <-> SmartVarfMap f x = SmartVarfMap g y.
      Proof.
        induction t; unfold SmartVarfMap in *; simpl in *; destruct_head_hnf unit; try tauto.
        rewrite_hyp !*; intuition congruence.
      Qed.
      Lemma lift_interp_flat_type_rel_pointwise2_f_eq_id1 (f : forall t, _ -> _) t x y
        : interp_flat_type_rel_pointwise2
            interp_base_type1 interp_base_type2
            (fun t x y => x = f t y)
            t x y
          <-> x = SmartVarfMap f y.
      Proof. rewrite lift_interp_flat_type_rel_pointwise2_f_eq, SmartVarfMap_id; reflexivity. Qed.
      Lemma lift_interp_flat_type_rel_pointwise2_f_eq_id2 (f : forall t, _ -> _) t x y
        : interp_flat_type_rel_pointwise2
            interp_base_type1 interp_base_type2
            (fun t x y => f t x = y)
            t x y
          <-> SmartVarfMap f x = y.
      Proof. rewrite lift_interp_flat_type_rel_pointwise2_f_eq, SmartVarfMap_id; reflexivity. Qed.
    End flat_type2.
  End lifting.

  Lemma interp_flat_type_rel_pointwise2_hetero_flatten_binding_list2
        {interp_base_type1 interp_base_type2 t1 t2 T1 T2} R' e1 e2 v1 v2
        (H : List.In (existT _ (t1, t2)%core (v1, v2)%core) (flatten_binding_list2 e1 e2))
        (HR : interp_flat_type_rel_pointwise2_hetero interp_base_type1 interp_base_type2 R' T1 T2 e1 e2)
    : R' t1 t2 v1 v2.
  Proof.
    revert dependent T2; induction T1, T2;
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
  Qed.
End language.

Global Arguments interp_type_rel_pointwise2 {_ _ _} R {t} _ _.
Global Arguments interp_type_rel_pointwise2_hetero {_ _ _} R {t1 t2} _ _.
Global Arguments interp_type_gen_rel_pointwise2_hetero_hetero {_ _ _ _ _} Rsrc Rdst {t1 t2} _ _.
Global Arguments interp_type_gen_rel_pointwise2_hetero {_ _ _ _ _} Rsrc Rdst {t} _ _.
Global Arguments interp_type_gen_rel_pointwise2 {_ _ _} R {t} _ _.
Global Arguments interp_flat_type_rel_pointwise2_gen_Prop {_ _ _ P} and True R {t} _ _.
Global Arguments interp_flat_type_rel_pointwise2_hetero_gen_Prop {_ _ _ P} and True False R {t1 t2} _ _.
Global Arguments interp_flat_type_rel_pointwise2_hetero {_ _ _} R {t1 t2} _ _.
Global Arguments interp_flat_type_rel_pointwise2 {_ _ _} R {t} _ _.
Global Arguments interp_flat_type_rel_pointwise {_} _ _ {_} _ _.
Global Arguments interp_type_rel_pointwise {_} _ _ {_} _ _.
Global Arguments interp_type_gen_rel_pointwise {_ _} _ {_} _ _.
Global Arguments interp_flat_type_rel_pointwise {_} _ _ {_} _ _.

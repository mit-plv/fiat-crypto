Require Import Crypto.Reflection.Syntax.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Util.FixCoqMistakes.

Section language.
  Context (base_type_code : Type)
          (eq_base_type_code : base_type_code -> base_type_code -> bool)
          (base_type_code_bl : forall x y, eq_base_type_code x y = true -> x = y)
          (base_type_code_lb : forall x y, x = y -> eq_base_type_code x y = true).

  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).

  Fixpoint flat_type_beq (X Y : flat_type) {struct X} : bool
    := match X, Y with
       | Tbase T, Tbase T0 => eq_base_type_code T T0
       | Unit, Unit => true
       | Prod A B, Prod A0 B0 => (flat_type_beq A A0 && flat_type_beq B B0)%bool
       | Tbase _, _
       | Prod _ _, _
       | Unit, _
         => false
       end.
  Local Ltac t :=
    repeat match goal with
           | _ => intro
           | _ => reflexivity
           | _ => assumption
           | _ => progress simpl in *
           | _ => solve [ eauto with nocore ]
           | [ H : False |- _ ] => exfalso; assumption
           | [ H : false = true |- _ ] => apply Bool.diff_false_true in H
           | [ |- Prod _ _ = Prod _ _ ] => apply f_equal2
           | [ |- Arrow _ _ = Arrow _ _ ] => apply f_equal2
           | [ |- Tbase _ = Tbase _ ] => apply f_equal
           | [ |- Tflat _ = Tflat _ ] => apply f_equal
           | [ H : forall Y, _ = true -> _ = Y |- _ = ?Y' ]
             => is_var Y'; apply H; solve [ t ]
           | [ H : forall X Y, X = Y -> _ = true |- _ = true ]
             => eapply H; solve [ t ]
           | [ H : true = true |- _ ] => clear H
           | [ H : andb ?x ?y = true |- _ ]
             => destruct x, y; simpl in H; solve [ t ]
           | [ H : andb ?x ?y = true |- _ ]
             => destruct x eqn:?; simpl in H
           | [ H : ?f ?x = true |- _ ] => destruct (f x); solve [ t ]
           | [ H : ?x = true |- andb _ ?x = true ]
             => destruct x
           | [ |- andb ?x _ = true ]
             => cut (x = true); [ destruct x; simpl | ]
           end.
  Lemma flat_type_dec_bl X : forall Y, flat_type_beq X Y = true -> X = Y.
  Proof. clear base_type_code_lb; induction X, Y; t. Defined.
  Lemma flat_type_dec_lb X : forall Y, X = Y -> flat_type_beq X Y = true.
  Proof. clear base_type_code_bl; intros; subst Y; induction X; t. Defined.
  Definition flat_type_eq_dec (X Y : flat_type) : {X = Y} + {X <> Y}
    := match Sumbool.sumbool_of_bool (flat_type_beq X Y) with
       | left pf => left (flat_type_dec_bl _ _ pf)
       | right pf => right (fun pf' => let pf'' := eq_sym (flat_type_dec_lb _ _ pf') in
                                       Bool.diff_true_false (eq_trans pf'' pf))
       end.
  Fixpoint type_beq (X Y : type) {struct X} : bool
    := match X, Y with
       | Tflat T, Tflat T0 => flat_type_beq T T0
       | Arrow A B, Arrow A0 B0 => (eq_base_type_code A A0 && type_beq B B0)%bool
       | Tflat _, _
       | Arrow _ _, _
         => false
       end.
  Lemma type_dec_bl X : forall Y, type_beq X Y = true -> X = Y.
  Proof. clear base_type_code_lb; pose proof flat_type_dec_bl; induction X, Y; t. Defined.
  Lemma type_dec_lb X : forall Y, X = Y -> type_beq X Y = true.
  Proof. clear base_type_code_bl; pose proof flat_type_dec_lb; intros; subst Y; induction X; t. Defined.
  Definition type_eq_dec (X Y : type) : {X = Y} + {X <> Y}
    := match Sumbool.sumbool_of_bool (type_beq X Y) with
       | left pf => left (type_dec_bl _ _ pf)
       | right pf => right (fun pf' => let pf'' := eq_sym (type_dec_lb _ _ pf') in
                                       Bool.diff_true_false (eq_trans pf'' pf))
       end.
End language.

Lemma dec_eq_flat_type {base_type_code} `{DecidableRel (@eq base_type_code)}
  : DecidableRel (@eq (flat_type base_type_code)).
Proof.
  repeat intro; hnf; decide equality; apply dec; auto.
Defined.
Hint Extern 1 (Decidable (@eq (flat_type ?base_type_code) ?x ?y))
=> simple apply (@dec_eq_flat_type base_type_code) : typeclass_instances.
Lemma dec_eq_type {base_type_code} `{DecidableRel (@eq base_type_code)}
  : DecidableRel (@eq (type base_type_code)).
Proof.
  repeat intro; hnf; decide equality; apply dec; typeclasses eauto.
Defined.
Hint Extern 1 (Decidable (@eq (type ?base_type_code) ?x ?y))
=> simple apply (@dec_eq_type base_type_code) : typeclass_instances.

Section encode_decode.
  Context {base_type_code : Type}.
  Local Notation flat_type := (flat_type base_type_code).
  Local Notation type := (type base_type_code).

  Definition flat_type_code (t1 t2 : flat_type)
    := match t1, t2 with
       | Tbase T1, Tbase T2 => T1 = T2
       | Unit, Unit => True
       | Prod A1 B1, Prod A2 B2 => A1 = A2 /\ B1 = B2
       | Tbase _, _
       | Unit, _
       | Prod _ _, _
         => False
       end.
  Definition flat_type_encode {t1 t2} : t1 = t2 -> flat_type_code t1 t2
    := match t1, t2 return t1 = t2 -> flat_type_code t1 t2 with
       | Tbase T1, Tbase T2 => fun H => match H with eq_refl => eq_refl end
       | Unit, Unit => fun _ => I
       | Prod A1 B1, Prod A2 B2
         => fun H => conj (match H with eq_refl => eq_refl end)
                          (match H with eq_refl => eq_refl end)
       | Tbase _, _
       | Unit, _
       | Prod _ _, _
         => fun H => match H with eq_refl => I end
       end.
  Definition flat_type_decode {t1 t2} : flat_type_code t1 t2 -> t1 = t2
    := match t1, t2 return flat_type_code t1 t2 -> t1 = t2 with
       | Tbase T1, Tbase T2 => fun H => f_equal Tbase H
       | Unit, Unit => fun _ => eq_refl
       | Prod A1 B1, Prod A2 B2
         => fun H => f_equal2 Prod (let (a, b) := H in a) (let (a, b) := H in b)
       | Tbase _, _
       | Unit, _
       | Prod _ _, _
         => fun H : False => match H with end
       end.
  Lemma flat_type_endecode {t1 t2} H : flat_type_decode (@flat_type_encode t1 t2 H) = H.
  Proof. subst t2; destruct t1; reflexivity. Defined.
  Lemma flat_type_deencode {t1 t2} H : flat_type_encode (@flat_type_decode t1 t2 H) = H.
  Proof. destruct t1, t2; destruct H; subst; reflexivity. Defined.

  Definition path_flat_type_rect {t1 t2 : flat_type} (P : t1 = t2 -> Type)
             (f : forall p, P (flat_type_decode p))
    : forall p, P p.
  Proof. intro p; specialize (f (flat_type_encode p)); destruct t1, p; exact f. Defined.

  Definition type_code (t1 t2 : type)
    := match t1, t2 with
       | Tflat T1, Tflat T2 => T1 = T2
       | Arrow A1 B1, Arrow A2 B2 => A1 = A2 /\ B1 = B2
       | Tflat _, _
       | Arrow _ _, _
         => False
       end.
  Definition type_encode {t1 t2} : t1 = t2 -> type_code t1 t2
    := match t1, t2 return t1 = t2 -> type_code t1 t2 with
       | Tflat T1, Tflat T2 => fun H => match H with eq_refl => eq_refl end
       | Arrow A1 B1, Arrow A2 B2
         => fun H => conj (match H with eq_refl => eq_refl end)
                          (match H with eq_refl => eq_refl end)
       | Tflat _, _
       | Arrow _ _, _
         => fun H => match H with eq_refl => I end
       end.
  Definition type_decode {t1 t2} : type_code t1 t2 -> t1 = t2
    := match t1, t2 return type_code t1 t2 -> t1 = t2 with
       | Tflat T1, Tflat T2 => fun H => f_equal Tflat H
       | Arrow A1 B1, Arrow A2 B2
         => fun H => f_equal2 Arrow (let (a, b) := H in a) (let (a, b) := H in b)
       | Tflat _, _
       | Arrow _ _, _
         => fun H : False => match H with end
       end.
  Lemma type_endecode {t1 t2} H : type_decode (@type_encode t1 t2 H) = H.
  Proof. subst t2; destruct t1; reflexivity. Defined.
  Lemma type_deencode {t1 t2} H : type_encode (@type_decode t1 t2 H) = H.
  Proof. destruct t1, t2; destruct H; subst; reflexivity. Defined.

  Definition path_type_rect {t1 t2 : type} (P : t1 = t2 -> Type)
             (f : forall p, P (type_decode p))
    : forall p, P p.
  Proof. intro p; specialize (f (type_encode p)); destruct t1, p; exact f. Defined.
End encode_decode.

Ltac induction_type_in_using H rect :=
  let H0 := fresh H in
  let H1 := fresh H in
  induction H as [H] using (rect _ _ _);
  cbv [type_code flat_type_code] in H;
  try match type of H with
      | False => exfalso; exact H
      | True => destruct H
      | _ /\ _ => destruct H as [H0 H1]
      end.
Ltac inversion_flat_type_step :=
  lazymatch goal with
  | [ H : _ = Tbase _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : Tbase _ = _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : _ = Prod _ _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : Prod _ _ = _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : _ = Unit |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  | [ H : Unit = _ |- _ ]
    => induction_type_in_using H @path_flat_type_rect
  end.
Ltac inversion_flat_type := repeat inversion_flat_type_step.

Ltac inversion_type_step :=
  lazymatch goal with
  | [ H : _ = Tflat _ |- _ ]
    => induction_type_in_using H @path_type_rect
  | [ H : Tflat _ = _ |- _ ]
    => induction_type_in_using H @path_type_rect
  | [ H : _ = Arrow _ _ |- _ ]
    => induction_type_in_using H @path_type_rect
  | [ H : Arrow _ _ = _ |- _ ]
    => induction_type_in_using H @path_type_rect
  end.
Ltac inversion_type := repeat inversion_type_step.

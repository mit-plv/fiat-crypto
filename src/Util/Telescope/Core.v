Require Import Coq.Relations.Relation_Definitions Coq.Classes.Morphisms.
Require Export Crypto.Util.FixCoqMistakes.

Module Export Telescope.
  Inductive Telescope := bottom | tele (A : Type) (B : A -> Telescope).

  Fixpoint flattenT (t : Telescope) (X : Type)
    := match t with
         | bottom => X
         | tele A B => forall a : A, flattenT (B a) X
       end.

  Global Arguments tele : clear implicits.

  Fixpoint flattenT_sig (t : Telescope)
    := match t return Type with
         | bottom => unit
         | tele A B => { a : A & flattenT_sig (B a) }
       end.

  Section R.
    Context {X : Type} (R : relation X).

    Fixpoint flattenT_R_relation {t : Telescope} : relation (flattenT t X)
      := match t return relation (flattenT t X) with
           | bottom => R
           | tele A B => forall_relation (fun a => flattenT_R_relation)
         end.
  End R.

  Definition flattenT_eq {X : Type} : forall {t : Telescope}, relation (flattenT t X)
    := Eval unfold flattenT_R_relation, forall_relation in @flattenT_R_relation X eq.

  Fixpoint flattenT_apply {t : Telescope} {X : Type}
  : flattenT t X -> flattenT_sig t -> X
    := match t return flattenT t X -> flattenT_sig t -> X with
         | bottom => fun x _ => x
         | tele A B => fun f p => flattenT_apply (f (projT1 p)) (projT2 p)
       end.

  Fixpoint flattenT_unapply {t : Telescope} {X : Type}
  : (flattenT_sig t -> X) -> flattenT t X
    := match t return (flattenT_sig t -> X) -> flattenT t X with
         | bottom => fun f => f tt
         | tele A B => fun f x => flattenT_unapply (fun p => f (existT (fun x' => flattenT_sig (B x')) x p))
       end.

  Fixpoint Telescope_append_nondep (t t' : Telescope)
  : Telescope
    := match t with
         | bottom => t'
         | tele A B => @tele A (fun a => Telescope_append_nondep (B a) t')
       end.

  Global Arguments Telescope_append_nondep : clear implicits.

  Fixpoint Telescope_append (t : Telescope)
  : flattenT t Type -> Telescope
    := match t return flattenT t _ -> _ with
         | bottom => fun X => @tele X (fun _ => bottom)
         | tele A B => fun X => @tele A (fun a => Telescope_append (B a) (X a))
       end.

  Global Arguments Telescope_append : clear implicits.

  Fixpoint flatten_forall {t : Telescope} : flattenT t Type -> Type
    := match t return flattenT t Type -> Type with
         | bottom => fun P => P
         | tele A B => fun P => forall a : A, flatten_forall (P a)
       end.

  Fixpoint flatten_forall_eq_rect {t : Telescope}
  : forall {P Q : flattenT t Type},
      flattenT_eq P Q
      -> flatten_forall P
      -> flatten_forall Q
    := match t return forall {P Q : flattenT t Type},
                        flattenT_eq P Q
                        -> flatten_forall P
                        -> flatten_forall Q
       with
         | bottom => fun P Q H k => eq_rect _ (fun x => x) k _ H
         | tele A B => fun P Q H k a => @flatten_forall_eq_rect (B a) (P a) (Q a) (H a) (k a)
       end.

  Fixpoint flatten_forall_eq_relation {t : Telescope}
  : forall {P : flattenT t Type},
      relation (flatten_forall P)
    := match t
             return forall {P : flattenT t _},
                      relation (flatten_forall P)
       with
         | bottom => fun P => eq
         | tele A B => fun P => forall_relation (fun a : A => @flatten_forall_eq_relation (B a) (P a))
       end.

  Definition flatten_forall_eq {t : Telescope}
  : forall {P : flattenT t Type}
           (f g : flatten_forall P),
      Prop
    := Eval unfold flatten_forall_eq_relation, forall_relation in @flatten_forall_eq_relation t.

  Fixpoint flatten_forall_eq_relation_with_assumption {t : Telescope}
  : forall {P : flattenT t Type}
           (Q : flattenT t Type),
      relation (flatten_forall P)
    := match t
             return forall {P : flattenT t _}
                           (Q : flattenT t Type),
                      relation (flatten_forall P)
       with
         | bottom => fun P Q => fun x y => Q -> x = y
         | tele A B => fun P Q => forall_relation (fun a : A => @flatten_forall_eq_relation_with_assumption (B a) (P a) (Q a))
       end.

  Definition flatten_forall_eq_with_assumption {t : Telescope}
  : forall {P : flattenT t Type}
           (Q : flattenT t Type)
           (f g : flatten_forall P),
      Prop
    := Eval unfold flatten_forall_eq_relation, forall_relation in @flatten_forall_eq_relation_with_assumption t.

  Fixpoint flatten_forall_apply {t : Telescope}
  : forall {P : flattenT t Type},
      flatten_forall P
      -> forall x : flattenT_sig t,
           flattenT_apply P x
    := match t
             return forall {P : flattenT t Type},
                      flatten_forall P
                      -> forall x : flattenT_sig t,
                           flattenT_apply P x
       with
         | bottom => fun X x _ => x
         | tele A B => fun P f x => @flatten_forall_apply (B (projT1 x)) _ (f (projT1 x)) (projT2 x)
       end.

  Fixpoint flatten_forall_unapply {t : Telescope}
  : forall {P : flattenT_sig t -> Type},
      (forall x : flattenT_sig t, P x)
      -> flatten_forall (flattenT_unapply P)
    := match t
             return forall {P : flattenT_sig t -> Type},
                      (forall x : flattenT_sig t, P x)
                      -> flatten_forall (flattenT_unapply P)
       with
         | bottom => fun X x => x tt
         | tele A B => fun P f x => @flatten_forall_unapply (B x) _ (fun x' => f _)
       end.

  Fixpoint flatten_forall_apply_of_unapply {t X} {struct t}
  : forall (f : flatten_forall
                  (flattenT_unapply
                     (fun _ : flattenT_sig t => X)))
           (x : flattenT_sig t),
      X
    := match t return forall (f : flatten_forall
                                    (flattenT_unapply
                                       (fun _ : flattenT_sig t => X)))
                             (x : flattenT_sig t),
                        X
       with
         | bottom => fun x _ => x
         | tele A B => fun f x => @flatten_forall_apply_of_unapply (B (projT1 x)) X (f (projT1 x)) (projT2 x)
       end.

  Fixpoint flatten_append_forall {t : Telescope}
  : forall {t' : flattenT t Type},
      flattenT (Telescope_append t t') Type -> flatten_forall t' -> Type
    := match t return forall {t' : flattenT t _},
                        flattenT (Telescope_append t t') Type
                        -> flatten_forall t'
                        -> Type
       with
         | bottom => fun t' P v => P v
         | tele A B => fun t' P v => forall a, @flatten_append_forall (B a) (t' a) (P a) (v a)
       end.
End Telescope.

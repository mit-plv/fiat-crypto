Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Definitions Coq.Classes.Morphisms.
Require Import Crypto.Util.Telescope.Core.
Require Import Crypto.Util.Telescope.Instances.
Require Import Crypto.Util.Equality.

Module Export Telescope.
  Fixpoint flattenT_apply_unapply {t : Telescope} {X : Type} {struct t}
  : forall (f : flattenT_sig t -> X)
           (x : flattenT_sig t),
      f x = flattenT_apply (flattenT_unapply f) x
    := match t return forall (f : flattenT_sig t -> X)
                             (x : flattenT_sig t),
                        f x = flattenT_apply (flattenT_unapply f) x
       with
         | bottom => fun f x => match x with
                                  | tt => eq_refl
                                end
         | tele A B => fun f x => eq_trans (f_equal f match x return x = existT (fun a => flattenT_sig (B a)) (projT1 x) (projT2 x) with
                                                        | existT _ _ => eq_refl
                                                      end)
                                           (@flattenT_apply_unapply
                                              (B (projT1 x)) X
                                              (fun p => f (existT (fun x' => flattenT_sig (B x')) (projT1 x) p))
                                              (projT2 x))
       end.

  Fixpoint flattenT_unapply_apply {t : Telescope} {X : Type} {struct t}
  : forall (f : flattenT t X),
      flattenT_eq f (flattenT_unapply (flattenT_apply f))
    := match t return forall (f : flattenT t X),
                        flattenT_eq f (flattenT_unapply (flattenT_apply f))
       with
         | bottom => fun f => eq_refl
         | tele A B => fun f x => @flattenT_unapply_apply (B x) X (f x)
       end.

  Fixpoint flatten_forall_apply_unapply {t : Telescope} {struct t}
  : forall {P : flattenT_sig t -> Type}
           (f : forall x, P x)
           (x : flattenT_sig t),
      eq_rect _ (fun Px => Px) (f x) _ (flattenT_apply_unapply P x)
      = flatten_forall_apply (flatten_forall_unapply f) x.
  Proof.
    refine match t return forall {P : flattenT_sig t -> Type}
                                 (f : forall x, P x)
                                 (x : flattenT_sig t),
                            eq_rect _ (fun Px => Px) (f x) _ (flattenT_apply_unapply P x)
                            = flatten_forall_apply (flatten_forall_unapply f) x
           with
             | bottom => fun f x ttt => match ttt with
                                          | tt => eq_refl
                                        end
             | tele A B => fun f x x' => eq_trans
                                           _
                                           (@flatten_forall_apply_unapply (B (projT1 x')) _ _ _)
           end.
    destruct x'; simpl in *.
    refine (f_equal _ (concat_1p _)).
  Defined.

  Fixpoint flatten_forall_unapply_apply {t : Telescope} {struct t}
  : forall {P : flattenT t Type}
           (f : flatten_forall P),
      flatten_forall_eq
        (flatten_forall_eq_rect (flattenT_unapply_apply P) f)
        (flatten_forall_unapply (flatten_forall_apply f))
    := match t return forall {P : flattenT t Type}
                             (f : flatten_forall P),
                        flatten_forall_eq
                          (flatten_forall_eq_rect (flattenT_unapply_apply P) f)
                          (flatten_forall_unapply (flatten_forall_apply f))
       with
         | bottom => fun P f => eq_refl
         | tele A B => fun P f a => @flatten_forall_unapply_apply (B a) (P a) (f a)
       end.

  Fixpoint flatten_forall_eq_rect_trans {t : Telescope}
  : forall {P Q R : flattenT t Type}
           (p : flattenT_eq P Q)
           (q : flattenT_eq Q R)
           (f : flatten_forall P),
      flatten_forall_eq (flatten_forall_eq_rect (transitivity p q) f)
                        (flatten_forall_eq_rect q (flatten_forall_eq_rect p f)).
  Proof.
    refine match t return forall {P Q R : flattenT t Type}
                                 (p : flattenT_eq P Q)
                                 (q : flattenT_eq Q R)
                                 (f : flatten_forall P),
                            flatten_forall_eq (flatten_forall_eq_rect (transitivity p q) f)
                                              (flatten_forall_eq_rect q (flatten_forall_eq_rect p f))
           with
             | bottom => fun P Q H k => _
             | tele A B => fun P Q R p q f a => @flatten_forall_eq_rect_trans (B a) _ _ _ _ _ _
           end;
    simpl in *.
    { intros; subst; simpl; reflexivity. }
  Defined.

  Fixpoint flatten_forall_eq_rect_flattenT_unapply_Proper {t}
  : forall {P Q : flattenT_sig t -> Type}
           (H : forall x, P x = Q x)
           (f : forall x, P x),
      flatten_forall_eq
        (flatten_forall_eq_rect (@flattenT_unapply_Proper t _ P (fun x => Q x) H) (flatten_forall_unapply f))
        (flatten_forall_unapply (fun x => eq_rect _ (fun P => P) (f x) _ (H x)))
    := match t return forall {P Q : flattenT_sig t -> Type}
                             (H : forall x, P x = Q x)
                             (f : forall x, P x),
                        flatten_forall_eq
                          (flatten_forall_eq_rect (@flattenT_unapply_Proper t _ P (fun x => Q x) H) (flatten_forall_unapply f))
                          (flatten_forall_unapply (fun x => eq_rect _ (fun P => P) (f x) _ (H x)))
       with
         | bottom => fun P Q H k => eq_refl
         | tele A B => fun P Q H f a => @flatten_forall_eq_rect_flattenT_unapply_Proper (B a) _ _ _ _
       end.

  Fixpoint eq_rect_symmetry_flattenT_apply_unapply {t}
  : forall {f x k},
      eq_rect _ (fun T => T) (flatten_forall_apply (flatten_forall_unapply k) x) _ (eq_sym (@flattenT_apply_unapply t Type f x))
      = k x
    := match t return forall {f x k},
                        eq_rect _ (fun T => T) (flatten_forall_apply (flatten_forall_unapply k) x) _ (eq_sym (@flattenT_apply_unapply t Type f x))
                        = k x
       with
         | bottom => fun f x k => match x with
                                    | tt => eq_refl
                                  end
         | tele A'' B'' => fun f x k =>
                             match x with
                               | existT x1 x2
                                 => eq_trans
                                      (y := eq_rect
                                              _ (fun T => T)
                                              (flatten_forall_apply
                                                 (flatten_forall_unapply (fun x' => k (existT (fun x'' => flattenT_sig (B'' x'')) x1 x')))
                                                 x2)
                                              _
                                              (eq_sym (flattenT_apply_unapply (fun p => f (existT (fun x' => flattenT_sig (B'' x')) x1 p)) x2)))
                                      (f_equal (fun p' => eq_rect
                                                            _ (fun T => T)
                                                            (flatten_forall_apply
                                                               (flatten_forall_unapply (fun x' => k (existT (fun x'' => flattenT_sig (B'' x'')) x1 x')))
                                                               x2)
                                                            _
                                                            (eq_sym p'))
                                               (concat_1p _))
                                      (@eq_rect_symmetry_flattenT_apply_unapply (B'' x1) (fun x2' => f (existT (fun a => flattenT_sig (B'' a)) x1 x2')) x2 (fun x2' => k (existT (fun a => flattenT_sig (B'' a)) x1 x2')))
                             end
       end.

  Fixpoint flatten_forall_eq_rect_symmetry_flattenT_unapply_apply {t}
  : forall {f k},
      flatten_forall_eq
        (flatten_forall_eq_rect
           (symmetry (@flattenT_unapply_apply t Type f))
           (flatten_forall_unapply (flatten_forall_apply k)))
        k
    := match t return forall {f k},
                        flatten_forall_eq
                          (flatten_forall_eq_rect
                             (symmetry (@flattenT_unapply_apply t Type f))
                             (flatten_forall_unapply (flatten_forall_apply k)))
                          k
       with
         | bottom => fun f k => eq_refl
         | tele A'' B'' => fun f k a => @flatten_forall_eq_rect_symmetry_flattenT_unapply_apply (B'' a) (f a) (k a)
       end.

  Lemma flatten_forall_apply_of_unapply_eq {t X}
        f x
  : eq_rect
      _
      (fun T : Type => T)
      (flatten_forall_apply f x)
      _
      (eq_sym
         (flattenT_apply_unapply (fun _ => X) _))
    = @flatten_forall_apply_of_unapply t X f x.
  Proof.
    induction t as [|A B IHt]; simpl in *.
    { destruct x; simpl; reflexivity. }
    { specialize (IHt (projT1 x) (f (projT1 x)) (projT2 x)).
      etransitivity; [ clear IHt | exact IHt ].
      repeat apply f_equal.
      etransitivity; [ | apply concat_1p ].
      apply f_equal2; [ | reflexivity ].
      apply ap_const. }
  Defined.
End Telescope.

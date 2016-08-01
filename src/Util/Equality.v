(** * Lemmas about [eq] *)
Require Import Crypto.Util.Isomorphism.
Require Import Crypto.Util.HProp.

Definition concat_1p {A x y} (p : x = y :> A) : eq_trans eq_refl p = p.
Proof. case p; reflexivity. Defined.
Definition concat_p1 {A x y} (p : x = y :> A) : eq_trans p eq_refl = p.
Proof. case p; reflexivity. Defined.
Definition concat_pV {A x y} (p : x = y :> A) : eq_trans p (eq_sym p) = eq_refl.
Proof. case p; reflexivity. Defined.
Definition concat_Vp {A x y} (p : x = y :> A) : eq_trans (eq_sym p) p = eq_refl.
Proof. case p; reflexivity. Defined.
Definition transport_pp {A} {P : A -> Type} {x y z} (p : x = y) (q : y = z) (k : P x)
: eq_rect _ P k _ (eq_trans p q) = eq_rect _ P (eq_rect _ P k _ p) _ q.
Proof. case q; simpl; reflexivity. Defined.
Lemma transport_const {A P x y} (p : x = y :> A) k
: eq_rect _ (fun _ : A => P) k _ p = k.
Proof. case p; reflexivity. Defined.
Lemma ap_const {A B x y} (b : B) (p : x = y :> A)
: f_equal (fun _ => b) p = eq_refl.
Proof. case p; reflexivity. Defined.
Lemma inv_pp {A x y z} (p : x = y :> A) (q : y = z :> A)
: eq_sym (eq_trans p q) = eq_trans (eq_sym q) (eq_sym p).
Proof. case q; case p; reflexivity. Defined.
Lemma inv_V {A x y} (p : x = y :> A)
: eq_sym (eq_sym p) = p.
Proof. case p; reflexivity. Defined.

Section gen.
  Context {A : Type} {x : A} (code : A -> Type)
          (encode : forall y, x = y -> code y)
          {code_hprop : IsHProp { a : A & code a } }.

  Definition decode' {y} (p : code y) : x = y
    := f_equal (@projT1 _ _) (code_hprop (existT _ x (encode x eq_refl)) (existT _ y p)).

  Definition decode {y} (H : code y) : x = y
    := eq_trans (eq_sym (decode' (encode x eq_refl))) (decode' H).

  Definition deencode {y} (H : x = y) : decode (encode y H) = H.
  Proof.
    destruct H.
    unfold decode.
    edestruct (@decode' x _).
    reflexivity.
  Defined.

  Global Instance isiso_encode {y} : IsIso (encode y).
  Proof.
    exists (@decode y).
    { intro H.
      unfold decode.
      set (yH := (existT _ y H)).
      change H with (projT2 yH).
      change y with (projT1 yH).
      clearbody yH; clear y H.
      destruct (code_hprop (existT _ x (encode x eq_refl)) yH); simpl.
      abstract (rewrite concat_Vp; reflexivity). }
    { intro p.
      apply deencode. }
  Defined.
End gen.

Section hprop.
  Context {A} `{IsHProp A}.

  Let hprop_encode {x y : A} (p : x = y) : unit := tt.

  Local Hint Resolve (fun x => @isiso_encode A x (fun _ => unit)) : typeclass_instances.

  Global Instance ishprop_path_hprop : IsHPropRel (@eq A).
  Proof.
    intros x y p q.
    pose proof (is_left_inv (@hprop_encode x y)) as H'.
    rewrite <- (H' p), <- (H' q).
    apply f_equal; apply allpath_hprop.
  Qed.
End hprop.

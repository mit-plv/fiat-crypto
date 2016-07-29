(** * Lemmas about [eq] *)

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

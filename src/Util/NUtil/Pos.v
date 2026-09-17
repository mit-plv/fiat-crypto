From Stdlib Require Import NArith Lia.
Require Import Crypto.Util.Pos.
#[local] Coercion N.pos : positive >-> N.

Module N.
  #[local] Open Scope N_scope.
  Definition lt_dec a b : {a<b}+{~a<b}. Proof. simple refine (
    match N.compare a b as c return {c = Lt} + {c <> Lt} with
    | Lt => left eq_refl | _ => right _
    end); abstract discriminate.
  Defined.

  Lemma pos_of_N n : N.pos (Pos.of_N n) = N.max 1 n.
  Proof. case n; cbn; lia. Qed.

  Lemma pos_of_N_pos n : N.lt 0 n -> N.pos (Pos.of_N n) = n.
  Proof. case n; cbn; lia. Qed.

  Lemma pos_mul a b : N.pos (a * b) = N.mul a b. Proof. lia. Qed.

  Lemma divide_pos_pos (a b : positive) : N.divide (N.pos a) (N.pos b) <-> Pos.divide a b.
  Proof.
    split.
    { intros [[|x] Hx]; [lia|]. exists x. lia. }
    { intros [x Hx]. exists (N.pos x). lia. }
  Qed.

  Lemma div_eucl_as_div_mod a b : N.div_eucl a b = (a / b, a mod b).
  Proof. apply surjective_pairing. Qed.

  Lemma pos_div_eucl_pos_as_div_mod a (b : positive) : N.pos_div_eucl a b = (a / b, a mod b).
  Proof. rewrite <- div_eucl_as_div_mod; trivial. Qed.
End N.

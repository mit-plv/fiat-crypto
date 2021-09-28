Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.

Module N.
  Lemma testbit_ones n i : N.testbit (N.ones n) i = N.ltb i n.
  Proof using Type.
    pose proof N.ones_spec_iff n i.
    destruct (N.testbit _ _) eqn:? in*; destruct (N.ltb_spec i n); trivial.
    { pose proof (proj1 H eq_refl); lia. }
    { pose proof (proj2 H H0). inversion H1. }
  Qed.

  Lemma ones_min m n : N.ones (N.min m n) = N.land (N.ones m) (N.ones n).
  Proof using Type.
    eapply N.bits_inj_iff; intro i.
    rewrite N.land_spec.
    rewrite !N.testbit_ones.
    destruct (N.ltb_spec0 i (N.min m n));
      destruct (N.ltb_spec0 i m);
      destruct (N.ltb_spec0 i n);
      try reflexivity;
      lia.
  Qed.
End N.

Require Import Coq.ZArith.ZArith Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.lattice.WeightedMultiplication.
Require Import Crypto.Util.ListUtil Crypto.Util.Tuple.
Require Import Crypto.Util.ZUtil.Tactics.LtbToLt.
Require Import Crypto.Util.ZUtil.Modulo.
Local Open Scope Z_scope.

Module Crypto.
  Section Crypto.
    Context {weight : nat -> Z} {n : nat}.

    Definition place (t:Z*Z) (i:nat) : Z * nat:=
      nat_rect
        (fun _ => unit -> (Z * nat)%type)
        (fun _ => (fst t * snd t, O))
        (fun i' place_i' _
         => let i := S i' in
            if (snd t mod weight i =? 0)
            then (let c := snd t / weight i in c * fst t, i)
            else place_i' tt)
        i
        tt.

    Lemma place_ok : forall t1 t2,
        snd t1 = snd t2 ->
        snd (place t1 n) = snd (place t2 n).
    Proof.
      cbv [place]. induction n; [reflexivity | ].
      intros; cbn.
      break_match; Z.ltb_to_lt; autorewrite with cancel_pair; try congruence.
      eauto.
    Qed.

    Lemma place_0 t : fst t = 0 -> fst (place t n) = 0.
    Proof.
      cbv [place]. intro Hfst. rewrite Hfst.
      induction n; [reflexivity | ].
      intros; cbn.
      break_match; Z.ltb_to_lt; autorewrite with cancel_pair; auto with lia.
    Qed.

    Instance weighted_mul_pre : @weighted_mul_preconditions Z Z.
    Proof.
      eapply Build_weighted_mul_preconditions with (lop := Z.mul) (lid := 1%Z) (index_to_loc := weight) (loc_to_index := fun x => place x n); try reflexivity; try (repeat econstructor; repeat intro; omega).
      { apply Ring.commutative_ring_Z. }
      { econstructor; try apply Ring.commutative_ring_Z. }
      { apply Ring.commutative_ring_Z. }
      { auto using place_0. }
      { auto using place_ok. }
    Admitted.

End Crypto.
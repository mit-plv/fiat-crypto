Require Import Crypto.BaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystem.
Require Import Crypto.ModularArithmetic.ModularBaseSystemProofs.
Require Import Crypto.BaseSystemProofs.
Require Import Crypto.Util.Tuple Crypto.Util.CaseUtil.
Require Import ZArith.
Require Import Crypto.Algebra.
Import Group.
Import PseudoMersenneBaseParams PseudoMersenneBaseParamProofs.

(* Wraps ModularBaseSystem operations in tuples *)
Generalizable All Variables.
Section s.
  Context `{prm:PseudoMersenneBaseParams m}.

  Definition fe := tuple Z (length base).

(* to have them in specific, we need them in interface. To put them in interface, we
   need to either

   a) define them in interface
   b) define them in opt
   c) define them in MBS
   d) define them in some kind of tuple wrapper for MBS which we then later unfold

abstractions:
- Fq
- MBS with list rep +length proofs
- MBS with tuple rep
    (do correctness of MBS here)
- optimized MBS
*)

  Definition mul  (x y:fe) : fe :=
    carry_mul k_ c (from_list_default 0%Z (length base))
      (to_list _ x) (to_list _ y).

  Definition add : fe -> fe -> fe.
    refine (on_tuple2 add_opt _).
    abstract (intros; rewrite add_opt_correct, add_length_exact; case_max; omega).
  Defined.

  Definition sub : fe -> fe -> fe.
    refine (on_tuple2 sub_opt _).
    abstract (intros; rewrite sub_opt_correct; apply length_sub; rewrite ?coeff_length; auto).
  Defined.

  Definition carry_simple i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (pow2_mod di (log_cap i)) us in
    add_to_nth (S i) (   (Z.shiftr di (log_cap i))) us'.

  Definition carry_and_reduce i := fun us =>
    let di := nth_default 0 us      i in
    let us' := set_nth i (pow2_mod di (log_cap i)) us in
    add_to_nth   0  (c * (Z.shiftr di (log_cap i))) us'.

  Definition carry i : digits -> digits :=
    if eq_nat_dec i (pred (length base))
    then carry_and_reduce i
    else carry_simple i.

  Definition carry_sequence is us := fold_right carry us is.

  Fixpoint make_chain i :=
    match i with
    | O => nil
    | S i' => i' :: make_chain i'
    end.

  Definition full_carry_chain := make_chain (length limb_widths).

  Definition carry_full := carry_sequence full_carry_chain.

  Definition carry_mul us vs := carry_full (mul us vs).

End CarryBasePow2.

Section Canonicalization.
  Context `{prm :PseudoMersenneBaseParams}.

  (* compute at compile time *)
  Definition max_ones := Z.ones (fold_right Z.max 0 limb_widths).

  Definition max_bound i := Z.ones (log_cap i).

  Fixpoint isFull' us full i :=
    match i with
    | O => andb (Z.ltb (max_bound 0 - c) (nth_default 0 us 0)) full
    | S i' => isFull' us (andb (Z.eqb (max_bound i) (nth_default 0 us i)) full) i'
    end.

  Definition isFull us := isFull' us true (length base - 1)%nat.

  Fixpoint modulus_digits' i :=
    match i with
    | O => max_bound i - c + 1 :: nil
    | S i' => modulus_digits' i' ++ max_bound i :: nil
    end.

  (* compute at compile time *)
  Definition modulus_digits := modulus_digits' (length base - 1).

  Definition and_term us := if isFull us then max_ones else 0.

  Definition freeze us :=
    let us' := carry_full (carry_full (carry_full us)) in
    let and_term := and_term us' in
    (* [and_term] is all ones if us' is full, so the subtractions subtract q overall.
       Otherwise, it's all zeroes, and the subtractions do nothing. *)
     map2 (fun x y => x - y) us' (map (Z.land and_term) modulus_digits).

End Canonicalization.


  Arguments to_list {_ _} _.
  Definition phi (a : fe) : ModularArithmetic.F m := decode (to_list a).
  Definition phi_inv (a : ModularArithmetic.F m) : fe :=
    from_list_default 0%Z _ (encode a).

  Lemma phi_inv_spec : forall a, phi (phi_inv a) = a.
  Proof.
    intros; cbv [phi_inv phi].
    erewrite from_list_default_eq.
    rewrite to_list_from_list.
    apply ModularBaseSystemProofs.encode_rep.
    Grab Existential Variables.
    apply ModularBaseSystemProofs.encode_rep.
  Qed.

  Definition eq (x y : fe) : Prop := phi x = phi y.

  Definition zero : fe := phi_inv (ModularArithmetic.ZToField 0).

  Definition opp (x : fe) : fe := phi_inv (ModularArithmetic.opp (phi x)).

  Lemma add_correct : forall a b,
    to_list (add a b) = BaseSystem.add (to_list a) (to_list b).
  Proof.
    intros; cbv [add on_tuple2].
    rewrite to_list_from_list.
    apply add_opt_correct.
  Qed.

  Lemma add_phi : forall a b : fe,
    phi (add a b) = ModularArithmetic.add (phi a) (phi b).
  Proof.
    intros; cbv [phi].
    rewrite add_correct.
    apply ModularBaseSystemProofs.add_rep; auto using decode_rep, length_to_list.
  Qed.

  Lemma mul_correct : forall a b,
    to_list (mul a b) = carry_mul (to_list a) (to_list b).
  Proof.
    intros; cbv [mul].
    rewrite carry_mul_opt_cps_correct by assumption.
    erewrite from_list_default_eq.
    apply to_list_from_list.
    Grab Existential Variables.
    apply carry_mul_length; apply length_to_list.
  Qed.

  Lemma mul_phi : forall a b : fe,
    phi (mul a b) = ModularArithmetic.mul (phi a) (phi b).
  Proof.
    intros; cbv beta delta [phi].
    rewrite mul_correct.
    apply carry_mul_rep; auto using decode_rep, length_to_list.
  Qed.

End s.
Require Import Zpower ZArith.
Require Import Crypto.Util.ListUtil.
Require Import Crypto.Util.ZUtil.
Require Crypto.BaseSystem.
Require Import Coq.Lists.List.

Local Open Scope Z_scope.

Section Pow2Base.
  Context (limb_widths : list Z).
  Local Notation "w[ i ]" := (nth_default 0 limb_widths i).

  Fixpoint base_from_limb_widths limb_widths :=
    match limb_widths with
    | nil => nil
    | w :: lw => 1 :: map (Z.mul (two_p w)) (base_from_limb_widths lw)
    end.

  Local Notation base := (base_from_limb_widths limb_widths).


  Definition bounded us := forall i, 0 <= nth_default 0 us i < 2 ^ w[i].

  Definition upper_bound := 2 ^ (sum_firstn limb_widths (length limb_widths)).

  Fixpoint decode_bitwise' us i acc :=
    match i with
    | O => acc
    | S i' => decode_bitwise' us i' (Z.lor (nth_default 0 us i') (Z.shiftl acc w[i']))
    end.

  Definition decode_bitwise us := decode_bitwise' us (length us) 0.

  (* i is current index, counts down *)
  Fixpoint encode' z i :=
    match i with
    | O => nil
    | S i' => let lw := sum_firstn limb_widths in
       encode' z i' ++ (Z.shiftr (Z.land z (Z.ones (lw i))) (lw i')) :: nil
    end.

  Definition encodeZ x:= encode' x (length limb_widths).

  (** ** Carrying *)
  Section carrying.
    (** Here we implement addition and multiplication with simple
        carrying. *)
    Notation log_cap i := (nth_default 0 limb_widths i).

    Definition add_to_nth n (x:Z) xs :=
      update_nth n (fun y => x + y) xs.
    Definition carry_single i := fun di =>
      (Z.pow2_mod di (log_cap i),
       Z.shiftr di (log_cap i)).

    (* [fi] is fed [length us] and [S i] and produces the index of
         the digit to which value should be added;
       [fc] modifies the carried value before adding it to that digit *)
    Definition carry_gen fc fi i := fun us =>
      let i := fi i in
      let di := nth_default 0 us      i in
      let '(di', ci) := carry_single i di in
      let us' := set_nth i di' us in
      add_to_nth (fi (S i)) (fc ci) us'.

    (* carry_simple does not modify the carried value, and always adds it
       to the digit with index [S i] *)
    Definition carry_simple := carry_gen (fun ci => ci) (fun i => i).

    Definition carry_simple_sequence is us := fold_right carry_simple us is.

    Fixpoint make_chain i :=
      match i with
      | O => nil
      | S i' => i' :: make_chain i'
      end.

    Definition full_carry_chain := make_chain (length limb_widths).

    Definition carry_simple_full := carry_simple_sequence full_carry_chain.

    Definition carry_simple_add us vs := carry_simple_full (BaseSystem.add us vs).

    Definition carry_simple_sub us vs := carry_simple_full (BaseSystem.sub us vs).

    Definition carry_simple_mul out_base us vs := carry_simple_full (BaseSystem.mul out_base us vs).
  End carrying.

End Pow2Base.

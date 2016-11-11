Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Crypto.Util.Tuple.
Require Import Crypto.Util.Notations.
Require Import Bedrock.Word.
Local Open Scope Z_scope.

Section conditional_subtract_modulus.
  Context {int_width num_limbs : nat}.
  Local Notation limb := (word int_width).
  Local Notation digits := (tuple limb num_limbs).
  Local Notation zero := (natToWord int_width 0).
  Local Notation one := (natToWord int_width 1).
  Local Notation "u [ i ]" := (nth_default zero u i).
  Context (modulus : digits).
  Context (ge_modulusW : digits -> limb) (negW : limb -> limb).

  Definition conditional_subtract_modulusW (us : digits) :=
    (* [and_term] is all ones if us' is full, so the subtractions subtract q overall.
       Otherwise, it's all zeroes, and the subtractions do nothing. *)
     map2 (fun x y => wminus x y) us (map (wand (negW (ge_modulusW us))) modulus).

End conditional_subtract_modulus.